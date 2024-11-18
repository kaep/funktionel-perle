%default total
data TyExp = Tnat | Tbool

Val : TyExp -> Type
Val Tnat = Nat
Val Tbool = Bool

data Exp : TyExp -> Type where
    ValExp : (v : Val t) -> Exp t
    PlusExp : (e1 : Exp Tnat) -> (e2 : Exp Tnat) -> Exp Tnat
    IfExp : (b : Exp Tbool) -> (e1 : Exp t) -> (e2 : Exp t) -> Exp t
    SubExp : (e1 : Exp Tnat) -> (e2 : Exp Tnat) -> Exp Tnat

eval : Exp t -> Val t
eval (ValExp v) = v
eval (PlusExp e1 e2) = eval e1 + eval e2
eval (IfExp b e1 e2) = if eval b then eval e1 else eval e2
eval (SubExp e1 e2) = minus (eval e1) (eval e2)

example_prog : Nat
example_prog = eval (IfExp (ValExp False) (ValExp {t = Tnat} 3) (ValExp {t = Tnat} 2))



mutual 

    data Ty : Type where
      Enat : Ty
      Ebool : Ty
      Ehan : StackType -> StackType -> Ty
    
    El : Ty -> Type
    El Enat = Nat
    El Ebool = Bool
    El (Ehan s s') = Code s s'

    StackType : Type
    StackType = List Ty

    infixr 10 |>
    data Stack : (s: StackType) -> Type where
        Nil : Stack []
        (|>) : El t -> Stack s -> Stack (t :: s)


    data Elem = CST (Val t) | HAN (Code s s')

    data Code : (s, s' : StackType) -> Type where
        HALT : Code s s
        SKIP : Code s s
        (++) : (c1 : Code s1 s2) -> (c2 : Code s2 s3) -> Code s1 s3
        PUSH : (v : Val t) -> Code s ((stack_type t) :: s)
        ADD : Code (TEnat :: TEnat :: s) (TEnat :: s)
        IF : (c1, c2 : Code s s') -> Code (TEbool :: s) s'
        SUB : Code (TEnat :: TEnat :: s) (TEnat :: s)
        MARK : (c1 : Code s1 s2) -> (c2: Code s3 s4) -> Code s s
        UNMARK : (c1 : Code s1 s2) -> Code s s


exec : (Code s s') -> (Stack s) -> (Stack s')
exec HALT s = s
exec SKIP s = s
exec (c1 ++ c2) s = exec c2 (exec c1 s)
exec (PUSH v) s = v |> s
exec ADD (n |> m |> s) = (n + m) |> s
exec (IF c1 c2) (True |> s) = exec c1 s
exec (IF c1 c2) (False |> s) = exec c2 s
exec SUB (n |> m |> s) = (minus n m) |> s
exec (MARK c1 c2) s = ?m
exec (UNMARK c1) s = ?um


compile : (Exp t) -> Code s (t :: s)
compile (ValExp v) = PUSH v
compile (PlusExp e1 e2) = compile e2 ++ compile e1 ++ ADD
compile (IfExp b e1 e2) = (compile b) ++ (IF (compile e1) (compile e2))
compile (SubExp e1 e2) = compile e2 ++ compile e1 ++ SUB

{-

mutual
  trans_eval_compile : eval e1 |> (eval e2 |> s) = exec (compile e1) (exec (compile e2) s)
  trans_eval_compile {e1} {e2} {s} =
    let e2eval = (eval e2) |> s in
    let lhs = correct e1 e2eval in
    let rhs = cong {f = \s' => exec (compile e1) s'} (correct e2 s) in
    trans lhs rhs


  correct : (e: Exp t) -> (s: Stack s') -> ((eval e) |> s) = exec (compile e) s
  correct (ValExp v) s = Refl
  correct (PlusExp e1 e2) s =
    let exec_add = cong {f = \s' => exec ADD s'} (trans_eval_compile {s = s}) in
    trans Refl exec_add
  correct (IfExp b et ef) s =
    trans h1 h2
    where
      h1 : (if eval b then eval et else eval ef) |> s =
           exec (IF (compile et) (compile ef)) (eval b |> s)
      h1 with (eval b)
        | True = correct et s
        | False = correct ef s

      h2 : exec (IF (compile et) (compile ef)) (eval b |> s) =
           exec (IF (compile et) (compile ef)) (exec (compile b) s)
      h2 = 
        cong {f = \s' => exec (IF (compile et) (compile ef)) s'} (correct b s)
  correct (SubExp e1 e2) s = 
    let exec_sub = cong {f = \s' => exec SUB s'} (trans_eval_compile {s = s}) in
    trans Refl exec_sub

-}
