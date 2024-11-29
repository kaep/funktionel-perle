import Data.Vect
import Data.Fin

%default total

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
    LetExp : (rhs : Exp context t) -> (body : Exp (t :: context) t') -> Exp context t'

  data Environment : Vect n TyExp -> Type where
    NilEnv : Environment Nil
    (::) : Val t -> Environment context -> Environment (t :: context)
  
  envLookup : HasType i context t -> Environment context -> Val t
  envLookup Stop (head :: tail) = head
  envLookup (Pop x) (head :: tail) = envLookup x tail

  eval : Environment context -> Exp context t -> Val t
  eval env (ValExp v) = v
  eval env (PlusExp e1 e2) = eval env e1 + eval env e2
  eval env (IfExp b e1 e2) = if eval env b then eval env e1 else eval env e2
  eval env (SubExp e1 e2) = minus (eval env e1) (eval env e2)
  eval env (VarExp i) = envLookup i env
  eval env (LetExp rhs body) = let rhs' = eval env rhs in eval (rhs' :: env) body

  example_prog : Nat
  example_prog = eval NilEnv (IfExp (ValExp False) (ValExp {t = Tnat} 3) (ValExp {t = Tnat} 2))

  example_let : Nat
  example_let = eval NilEnv (LetExp (PlusExp (ValExp {t = Tnat} 37) (ValExp {t = Tnat} 3)) (PlusExp (ValExp {t = Tnat} 2) (VarExp Stop)))

  example_let_deeper : Nat
  example_let_deeper = eval NilEnv (LetExp (PlusExp (ValExp {t = Tnat} 20) (ValExp {t = Tnat} 5)) (LetExp (PlusExp (ValExp {t = Tnat} 6) (ValExp {t = Tnat} 11)) (PlusExp (VarExp Stop) (VarExp (Pop Stop)))))

  StackType : Type
  StackType = List TyExp


  infixr 10 |>
  data Stack : (s: StackType) -> Type where
      NilStack : Stack []
      (|>) : Val t -> Stack s -> Stack (t :: s)

  SCons : Val t -> Stack s -> Stack (t :: s)
  SCons = (|>)

  top : (s : Stack (t :: s')) -> Val t
  top (head |> _) = head


  data HasTypeInStack : (i : Fin n) -> (s: StackType) -> TyExp -> Type where
    StopStack : HasTypeInStack FZ (t :: s) t
    PopStack : HasTypeInStack k s t -> HasTypeInStack (FS k) (u :: s) t

  data Code : (s, s' : StackType) -> Type where
      Skip : Code s s
      (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
      PUSH : (v : Val t) -> Code s (t :: s)
      ADD : Code (Tnat :: Tnat :: s) (Tnat :: s)
      IF : (c1, c2 : Code s s') -> Code (Tbool :: s) s'
      SUB : Code (Tnat :: Tnat :: s) (Tnat :: s)
      VAR : (HasTypeInStack i s t) -> Code s (t :: s)
      POP : Code (t :: s) (s)
      SWAP : Code (x :: y :: s) (y :: x :: s)

  {-
  envLookup : HasType i context t -> Environment context -> Val t
  envLookup Stop (head :: tail) = head
  envLookup (Pop x) (head :: tail) = envLookup x tail
  -}
  total
  stackLookup : (s : StackType) -> HasTypeInStack i s t -> (st : Stack s) -> Val t 
  stackLookup (t :: xs) StopStack (x |> y) = x
  stackLookup (t :: xs) (PopStack x) (hd |> tail) = stackLookup xs x tail
  --stackLookup StopStack [] = ?stackLookup_rhs_3
  --stackLookup StopStack (x :: xs) = ?kk
  --stackLookup (PopStack x) s = ?stackLookup_rhs_2

  total
  exec : (Code s s') -> Stack s -> Stack s'
  exec Skip st = st
  exec (c1 ++ c2) s = exec c2 (exec c1 s)
  exec (PUSH v) st = v |> st 
  exec ADD (n |> m |> st) = (n+m) |> st 
  exec (IF c1 c2) (True |> s) = exec c1 s
  exec (IF c1 c2) (False |> s) = exec c2 s
  exec SUB (n |> m |> s) = (minus n m) |> s
  exec {s} (VAR id) st = let hans = stackLookup s id st in hans |> st
  exec POP (hd |> st) = st
  exec SWAP (x |> y |> st) = y |> x |> st

  compile : Environment context -> (Exp context t) -> Code s (t :: s)
  compile env (ValExp v) = PUSH v
  compile env (PlusExp e1 e2) = compile env e2 ++ compile env e1 ++ ADD
  compile env (IfExp b e1 e2) = (compile env b) ++ (IF (compile env e1) (compile env e2))
  compile env (SubExp e1 e2) = compile env e2 ++ compile env e1 ++ SUB
  compile env (VarExp x) = let hans = envLookup x env in PUSH hans
  -- hvad gør en let binding? den udvider vel context?
  compile env (LetExp rhs body) = ?hullet --compile env rhs ++ compile env body ++ SWAP ++ POP
