import Data.Vect
import Data.Fin

--%default total

using (context : Vect n TyExp)

  data TyExp = Tnat --| Tbool

  Val : TyExp -> Type
  Val Tnat = Nat
  --Val Tbool = Bool

  data HasType : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    Stop : HasType FZ (t :: context) t
    Pop : HasType k context t -> HasType (FS k) (u :: context) t


  data BadExp : TyExp -> Type where
    BValExp : (v : Nat) -> BadExp Tnat
    BPlusExp : (e1 : BadExp Tnat) -> (e2 : BadExp Tnat) -> BadExp Tnat
    --BIfExp : (b : BadExp Tbool) -> (e1 : BadExp t) -> (e2 : BadExp t) -> BadExp t
    BSubExp : (e1 : BadExp Tnat) -> (e2 : BadExp Tnat) -> BadExp Tnat
    BVarExp : (name : String) -> BadExp t
    BLetExp : (name : String) -> (rhs : BadExp t) -> (body : BadExp t') -> BadExp t'


  {-
  examp : BadExp [] Tnat
  examp = BValExp {t = Tnat} 38

  examp2 : BadExp [] Tnat
  examp2 = BPlusExp (BValExp {t = Tnat} 38) (BValExp {t = Tnat} 5)

  -- vi går fra en context til en udvidet context til ikke-udvidet context igen.
  examp3 : BadExp [] Tnat
  examp3 = BLetExp ("x") (BValExp {t = Tnat} 38) (BPlusExp (BVarExp "x") (BValExp {t = Tnat} 5))

  -}
  data DeBruijnExp : (n : Nat) -> TyExp -> Type where
    DValExp : (v : Nat) -> DeBruijnExp n Tnat
    DPlusExp : (e1 : DeBruijnExp n Tnat) -> (e2 : DeBruijnExp n Tnat) -> DeBruijnExp n Tnat
    --DIfExp : (b : DeBruijnExp n Tbool) -> (e1 : DeBruijnExp n t) -> (e2 : DeBruijnExp n t) -> DeBruijnExp n t
    DSubExp : (e1 : DeBruijnExp n Tnat) -> (e2 : DeBruijnExp n Tnat) -> DeBruijnExp n Tnat
    -- a variable expression takes an index
    DVarExp : (idx : Fin n) -> DeBruijnExp n t
    DLetExp : (rhs : DeBruijnExp n t) -> (body : DeBruijnExp (S n) t') -> DeBruijnExp n t'
  
  --varEnvLookupHelper : (idx : Nat) -> (name : String) -> (varEnv : Vect n (String, TyExp)) -> Maybe (TyExp, Fin n)
  --varEnvLookupHelper idx name [] = Nothing
  --varEnvLookupHelper idx name ((name', ty) :: tail) = if name == name' then ?thenhul else ?elsehul --if name == name' then Just (ty, ?hulli) else varEnvLookupHelper ?hullo name tail --(S idx) name tail 
  
  varEnvLookup : (name : String) -> (varEnv : Vect n (String, TyExp)) -> Maybe (TyExp, Fin n)
  varEnvLookup name [] = Nothing
  varEnvLookup name ((name', ty) :: tail) = if name == name' then Just (ty, FZ) else let (ty', f) = !(varEnvLookup name tail) in Just (ty', FS f)

  --varEnvLookupW : {i : Fin n} -> {t : TyExp} -> (name : String) -> (varEnv : Vect n (String, TyExp)) -> Maybe (TyExp, Fin n, HasType i context t)
  --varEnvLookupW name [] = Nothing
  --varEnvLookupW name ((name', ty) :: tail) = if name == name' then Just (ty, FZ, Stop) else let (ty', f, prf) = !(varEnvLookupW name tail) in Just (ty', FS f, Pop prf)

  --idxToProof : (idx : Fin n) -> (t : TyExp) -> HasType idx context t
  --idxToProof FZ t = ?hullis --Stop
  --idxToProof (FS x) t = ?bullis --Pop (idxToProof x t)

  --honni : (ty : TyExp) -> (name : String) -> (varEnv : Vect n (String, TyExp)) -> HasType idx context t
  --honni ty name [] = Stop
  --honni ty name (x :: xs) = ?honni_rhs1_2

  bad_to_bruijn : (varEnv : Vect n (String)) -> (source : BadExp t) -> Maybe (DeBruijnExp n t)
  bad_to_bruijn varEnv (BValExp v) = Just $ DValExp v
  bad_to_bruijn varEnv (BPlusExp e1 e2) = Just $ DPlusExp (!(bad_to_bruijn varEnv e1)) (!(bad_to_bruijn varEnv e2))
  --bad_to_bruijn varEnv (BIfExp b e1 e2) = Just $ DIfExp (!(bad_to_bruijn varEnv b)) (!(bad_to_bruijn varEnv e1)) (!(bad_to_bruijn varEnv e2))
  bad_to_bruijn varEnv (BSubExp e1 e2) = Just $ DSubExp (!(bad_to_bruijn varEnv e1)) (!(bad_to_bruijn varEnv e2))
  bad_to_bruijn varEnv (BVarExp name) = case findIndex (== name) varEnv of
    Nothing => Nothing
    Just (idx) => Just $ (DVarExp idx)
  bad_to_bruijn varEnv (BLetExp name rhs body) = Just $ (DLetExp (!(bad_to_bruijn varEnv rhs)) (!(bad_to_bruijn (name :: varEnv) body)))

  lookilooki : (i : Fin n) -> Vect n (Val t) -> Val t 
  lookilooki FZ (hd :: tail) = ?hullan--hd 
  lookilooki (FS next) (_ :: tail) = lookilooki next tail

  data Environment : Vect n TyExp -> Type where
    NilEnv : Environment Nil
    (::) : Val t -> Environment context -> Environment (t :: context)

  lookienv : (i : Fin n) -> Environment context -> Val t
  lookienv FZ (hd :: _) = ?lookienv_rhs_3
  lookienv (FS y) x = ?lookienv_rhs_2

    
  EvalStackType : Nat -> Type
  EvalStackType n = Vect n TyExp 

  infixr 10 |$>
  data EvaloStack : (n : Nat) -> (s: EvalStackType n) -> Type where
      NiloStack : EvaloStack 0 []
      (|$>) : Val t -> EvaloStack n s -> EvaloStack (S n) (t :: s)
  
  
  --unwindEvalStackType : Fin len -> EvalStackType len -> EvalStackType len

  --indexEval : (i : Fin len) -> EvaloStack len s -> Val (Data.Vect.index i s)
  --indexEval FZ     (x |$> xs) = x
  --indexEval (FS k) (x |$> xs) = indexEval k xs


  -- evalueringsenv er nu bare et vector af længde n med tyexp aka en context
  -- kan nok sagtens genbruge environment context..
  bruijn_eval : Vect n Nat -> DeBruijnExp n t -> Nat
  bruijn_eval env (DValExp v) = v
  bruijn_eval env (DPlusExp e1 e2) = bruijn_eval env e1 + bruijn_eval env e2
  --bruijn_eval env (DIfExp b e1 e2) = if bruijn_eval env b then bruijn_eval env e1 else bruijn_eval env e2
  bruijn_eval env (DSubExp e1 e2) = minus (bruijn_eval env e1) (bruijn_eval env e2)
  bruijn_eval env (DVarExp idx) = index idx env --indexEval idx env --lookilooki idx env
  bruijn_eval env (DLetExp rhs body) = let rhs' = bruijn_eval env rhs in bruijn_eval (rhs' :: env) body

  data Exp : Vect n TyExp -> TyExp -> Type where
    ValExp : (v : Val t) -> Exp context t
    PlusExp : (e1 : Exp context Tnat) -> (e2 : Exp context Tnat) -> Exp context Tnat
    --IfExp : (b : Exp context Tbool) -> (e1 : Exp context t) -> (e2 : Exp context t) -> Exp context t
    SubExp : (e1 : Exp context Tnat) -> (e2 : Exp context Tnat) -> Exp context Tnat
    VarExp : HasType i context t -> Exp context t
    LetExp : (rhs : Exp context t) -> (body : Exp (t :: context) t') -> Exp context t'

  
  envLookup : HasType i context t -> Environment context -> Val t
  envLookup Stop (head :: tail) = head
  envLookup (Pop x) (head :: tail) = envLookup x tail

  eval : Environment context -> Exp context t -> Val t
  eval env (ValExp v) = v
  eval env (PlusExp e1 e2) = eval env e1 + eval env e2
  --eval env (IfExp b e1 e2) = if eval env b then eval env e1 else eval env e2
  eval env (SubExp e1 e2) = minus (eval env e1) (eval env e2)
  eval env (VarExp i) = envLookup i env
  eval env (LetExp rhs body) = let rhs' = eval env rhs in eval (rhs' :: env) body

  --example_prog : Nat
  --example_prog = eval NilEnv (IfExp (ValExp False) (ValExp {t = Tnat} 3) (ValExp {t = Tnat} 2))

  --example_let : Nat
  --example_let = eval NilEnv (LetExp (PlusExp (ValExp {t = Tnat} 37) (ValExp {t = Tnat} 3)) (PlusExp (ValExp {t = Tnat} 2) (VarExp Stop)))

  --example_let_deeper : Nat
  --example_let_deeper = eval NilEnv (LetExp (PlusExp (ValExp {t = Tnat} 20) (ValExp {t = Tnat} 5)) (LetExp (PlusExp (ValExp {t = Tnat} 6) (ValExp {t = Tnat} 11)) (PlusExp (VarExp Stop) (VarExp (Pop Stop)))))


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
      --IF : (c1, c2 : Code s s') -> Code (Tbool :: s) s'
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
  --exec (IF c1 c2) (True |> s) = exec c1 s
  --exec (IF c1 c2) (False |> s) = exec c2 s
  exec SUB (n |> m |> s) = (minus n m) |> s
  exec {s} (VAR id) st = let hans = stackLookup s id st in hans |> st
  exec POP (hd |> st) = st
  exec SWAP (x |> y |> st) = y |> x |> st

  compile : Environment context -> (Exp context t) -> Code s (t :: s)
  compile env (ValExp v) = PUSH v
  compile env (PlusExp e1 e2) = compile env e2 ++ compile env e1 ++ ADD
  --compile env (IfExp b e1 e2) = (compile env b) ++ (IF (compile env e1) (compile env e2))
  compile env (SubExp e1 e2) = compile env e2 ++ compile env e1 ++ SUB
  --compile env (VarExp x) = PUSH $ envLookup x env
  -- vent, det er jo forkert bare at skubbe variablen, er det ikke?
  -- vi skal jo skubbe en VAR instruktion.
  -- men vi har jo den ene type bevis og skal producere den anden type...
  -- det bliver problematisk?
  compile env (VarExp x) = ?h
  -- hvad gør en let binding? den udvider vel context?
  compile env (LetExp rhs body) = 
    -- problemet her er, at body er et exp med en context der er udvidet.
    -- letexp er bygget op omkring at body bruger en context der er udvidet
    -- med den type der produceres af rhs, men den kan vi ikke få fat i her.
    -- Sestoft bogen gør således:
    -- scomp rhs env ++ scomp body (Bound x :: env) ++ POP ++ SWAP
    -- hvor x er streng-navnet på variablen og Bound er en ctor
    -- der indikerer at noget er en bunden variabel.
    -- Han har flere "niveauer" af expressions, der compiler
    -- til hinanden. F.eks. har Let et string-navn i source-sprog,
    -- og det sprog compiler han til et andet sprog som bruger de brujin indices.
    -- i den oversættelse kan variabel-opslag fejle...
    -- MEN essensen er jo, at body oversættes i et env hvor navnet på let-bindingen
    -- forbindes med højresiden.
    -- hvis vi skal gøre det samme, skal vi jo på en eller anden måde markere



    --let compiled_rhs = compile env rhs in
    --let hanzo = compile (Tnat :: env) body in
    ?hher

