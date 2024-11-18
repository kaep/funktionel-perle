import Data.Vect
import Data.Fin

--%default total

using (context : Vect n TyExp)

  data TyExp = Tnat | Tbool

  Val : TyExp -> Type
  Val Tnat = Nat
  Val Tbool = Bool

  data HasType : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    Stop : HasType FZ (t :: context) t
    Pop : HasType k context t -> HasType (FS k) (u :: context) t

  data Exp : Vect n TyExp -> TyExp -> Type where
    ValExp : (v : Val t) -> Exp context t
    PlusExp : (e1 : Exp context Tnat) -> (e2 : Exp context Tnat) -> Exp context Tnat
    IfExp : (b : Exp context Tbool) -> (e1 : Exp context t) -> (e2 : Exp context t) -> Exp context t
    SubExp : (e1 : Exp context Tnat) -> (e2 : Exp context Tnat) -> Exp context Tnat
    VarExp : HasType i context t -> Exp context t
    LetExp : (rhs : Exp context t) -> (body : Exp (t:: context) t) -> Exp context t

  data Environment : Vect n TyExp -> Type where
    NilEnv : Environment Nil
    (::) : Val t -> Environment context -> Environment (t :: context)
  
  lookup : HasType i context t -> Environment context -> Val t
  lookup Stop (head :: tail) = head
  lookup (Pop x) (head :: tail) = lookup x tail

  eval : Environment context -> Exp context t -> Val t
  eval env (ValExp v) = v
  eval env (PlusExp e1 e2) = eval env e1 + eval env e2
  eval env (IfExp b e1 e2) = if eval env b then eval env e1 else eval env e2
  eval env (SubExp e1 e2) = minus (eval env e1) (eval env e2)
  eval env (VarExp i) = lookup i env
  eval env (LetExp rhs body) = let rhs' = eval env rhs in eval (rhs' :: env) body

example_prog : Nat
example_prog = eval NilEnv (IfExp (ValExp False) (ValExp {t = Tnat} 3) (ValExp {t = Tnat} 2))

example_let : Nat
example_let = eval NilEnv (LetExp (PlusExp (ValExp {t = Tnat} 37) (ValExp {t = Tnat} 3)) (PlusExp (ValExp {t = Tnat} 2) (VarExp Stop)))

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

indexTy : (i : Fin n) -> (s : StackType) -> TyExp
indexTy FZ (t :: _) = t
indexTy (FS k) (_ :: tail) = indexTy k tail


data Code : (s, s' : StackType) -> Type where
    Skip : Code s s
    (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
    PUSH : (v : Val t) -> Code s (t :: s)
    ADD : Code (Tnat :: Tnat :: s) (Tnat :: s)
    IF : (c1, c2 : Code s s') -> Code (Tbool :: s) s'
    SUB : Code (Tnat :: Tnat :: s) (Tnat :: s)
    POP : Code (t :: s) (s)
    SWAP : Code (x :: y :: s) (y :: x :: s)
    VAR : (i : Fin n) -> Code s (indexTy i s :: s) -- i is index, t is just an implicit type?
    -- we do not need an instruction for let.
    -- it just uses existing stuff + pop and swap

stackLookup : (i : Fin n) -> (Stack s) -> Val (indexTy i s)
stackLookup FZ (x |> _) = x
stackLookup (FS k) (_ |> xs) = stackLookup k xs

exec : (Code s s') -> (Stack s) -> (Stack s')
--exec {len} {otherLen} Skip s = case decEq len otherLen of
--  Yes Refl => s
--  No contra => ?nul
exec Skip s = s
exec (c1 ++ c2) s = exec c2 (exec c1 s)
exec (PUSH v) s = v |> s
exec ADD (n |> m |> s) = (n + m) |> s
exec (IF c1 c2) (True |> s) = exec c1 s
exec (IF c1 c2) (False |> s) = exec c2 s
exec SUB (n |> m |> s) = (minus n m) |> s
exec POP (t |> s) = s
exec SWAP (x |> y |> s) = y |> x |> s
exec (VAR i) s stack = let v = ?stacklookupneeded i stack in v |> stack
--exec (VAR i) stak = stak --let hanzo = ?funn i stak in ?hyggehul
-- this is a problem. we do not have the proof here..
-- we cant just use HasType since the stack is not a vect?
-- oooor, do we need to do some indexing/lookup in a stack?


{-
compile : (Exp context t) -> Code s (t :: s)
compile (ValExp v) = PUSH v
compile (PlusExp e1 e2) = compile e2 ++ compile e1 ++ ADD
compile (IfExp b e1 e2) = (compile b) ++ (IF (compile e1) (compile e2))
compile (SubExp e1 e2) = compile e2 ++ compile e1 ++ SUB
compile (VarExp Stop) = VAR 0
compile (VarExp (Pop x)) = ?varhul
compile (LetExp rhs body) = compile rhs ++ compile body ++ SWAP ++ POP
-}


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