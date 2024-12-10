%default total
data TyExp = Tnat | Tbool

Val : TyExp -> Type
Val Tnat = Nat
Val Tbool = Bool

data Exp : TyExp -> Type where
    ValExp : (v : Val t) -> Exp t
    PlusExp : (e1 : Exp Tnat) -> (e2 : Exp Tnat) -> Exp Tnat
    IfExp : (b : Exp Tbool) -> (e1 : Exp t) -> (e2 : Exp t) -> Exp t

eval : Exp t -> Val t
eval (ValExp v) = v
eval (PlusExp e1 e2) = eval e1 + eval e2
eval (IfExp b e1 e2) = if eval b then eval e1 else eval e2

example_prog : Nat
example_prog = eval (IfExp (ValExp False) (ValExp {t = Tnat} 3) (ValExp {t = Tnat} 2))

StackType : Type
StackType = List TyExp


infixr 10 |>
data Stack : (s: StackType) -> Type where
    Nil : Stack []
    (|>) : Val t -> Stack s -> Stack (t :: s)

SCons : Val t -> Stack s -> Stack (t :: s)
SCons = (|>)

top : (s : Stack (t :: s')) -> Val t
top (head |> _) = head

data Code : (s, s' : StackType) -> Type where
    Skip : Code s s
    (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
    PUSH : (v : Val t) -> Code s (t :: s)
    ADD : Code (Tnat :: Tnat :: s) (Tnat :: s)
    IF : (c1, c2 : Code s s') -> Code (Tbool :: s) s'

exec : (Code s s') -> (Stack s) -> (Stack s')
exec Skip s = s
exec (c1 ++ c2) s = exec c2 (exec c1 s)
exec (PUSH v) s = v |> s
exec ADD (n |> m |> s) = (n + m) |> s
exec (IF c1 c2) (True |> s) = exec c1 s
exec (IF c1 c2) (False |> s) = exec c2 s

compile : (Exp t) -> Code s (t :: s)
compile (ValExp v) = PUSH v
compile (PlusExp e1 e2) = compile e2 ++ compile e1 ++ ADD
compile (IfExp b e1 e2) = (compile b) ++ (IF (compile e1) (compile e2))

mutual
  correct : (e: Exp t) -> (s: Stack s') -> ((eval e) |> s) = exec (compile e) s
  correct (ValExp v) s = Refl
  correct (PlusExp e1 e2) s =
    let lhs = correct e1 ((eval e2) |> s)
        rhs = cong {f = \s' => exec (compile e1) s'} (correct e2 s)
    in
    cong {f = \s' => exec ADD s'} (trans lhs rhs)

  correct (IfExp b et ef) s =
    trans lhs rhs
    where
      lhs : (if eval b then eval et else eval ef) |> s =
           exec (IF (compile et) (compile ef)) (eval b |> s)
      lhs with (eval b)
        | True = correct et s
        | False = correct ef s

      rhs : exec (IF (compile et) (compile ef)) (eval b |> s) =
           exec (IF (compile et) (compile ef)) (exec (compile b) s)
      rhs = 
        cong {f = \s' => exec (IF (compile et) (compile ef)) s'} (correct b s)
