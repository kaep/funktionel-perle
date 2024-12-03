import Data.Vect
import Data.Fin

--%default total

using (context : Vect n TyExp)

  data TyExp = Tnat

  Val : TyExp -> Type
  Val Tnat = Nat

  data HasType : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    Stop : HasType FZ (t :: context) t
    Pop : HasType k context t -> HasType (FS k) (u :: context) t


  data BadExp : TyExp -> Type where
    BValExp : (v : Nat) -> BadExp Tnat
    BPlusExp : (e1 : BadExp Tnat) -> (e2 : BadExp Tnat) -> BadExp Tnat
    BSubExp : (e1 : BadExp Tnat) -> (e2 : BadExp Tnat) -> BadExp Tnat
    BVarExp : (name : String) -> BadExp t
    BLetExp : (name : String) -> (rhs : BadExp t) -> (body : BadExp t') -> BadExp t'


  data DeBruijnExp : (n : Nat) -> TyExp -> Type where
    DValExp : (v : Nat) -> DeBruijnExp n Tnat
    DPlusExp : (e1 : DeBruijnExp n Tnat) -> (e2 : DeBruijnExp n Tnat) -> DeBruijnExp n Tnat
    --DIfExp : (b : DeBruijnExp n Tbool) -> (e1 : DeBruijnExp n t) -> (e2 : DeBruijnExp n t) -> DeBruijnExp n t
    DSubExp : (e1 : DeBruijnExp n Tnat) -> (e2 : DeBruijnExp n Tnat) -> DeBruijnExp n Tnat
    -- a variable expression takes an index
    DVarExp : (idx : Fin n) -> DeBruijnExp n t
    DLetExp : (rhs : DeBruijnExp n t) -> (body : DeBruijnExp (S n) t') -> DeBruijnExp n t'
  
  varEnvLookup : (name : String) -> (varEnv : Vect n (String, TyExp)) -> Maybe (TyExp, Fin n)
  varEnvLookup name [] = Nothing
  varEnvLookup name ((name', ty) :: tail) = if name == name' then Just (ty, FZ) else let (ty', f) = !(varEnvLookup name tail) in Just (ty', FS f)

  bad_to_bruijn : (varEnv : Vect n (String)) -> (source : BadExp t) -> Maybe (DeBruijnExp n t)
  bad_to_bruijn varEnv (BValExp v) = Just $ DValExp v
  bad_to_bruijn varEnv (BPlusExp e1 e2) = Just $ DPlusExp (!(bad_to_bruijn varEnv e1)) (!(bad_to_bruijn varEnv e2))
  bad_to_bruijn varEnv (BSubExp e1 e2) = Just $ DSubExp (!(bad_to_bruijn varEnv e1)) (!(bad_to_bruijn varEnv e2))
  bad_to_bruijn varEnv (BVarExp name) = case findIndex (== name) varEnv of
    Nothing => Nothing
    Just (idx) => Just $ (DVarExp idx)
  bad_to_bruijn varEnv (BLetExp name rhs body) = Just $ (DLetExp (!(bad_to_bruijn varEnv rhs)) (!(bad_to_bruijn (name :: varEnv) body)))

  data Environment : Vect n TyExp -> Type where
    NilEnv : Environment Nil
    (::) : Val t -> Environment context -> Environment (t :: context)




  -- evalueringsenv er nu bare et vector af længde n med tyexp aka en context
  -- kan nok sagtens genbruge environment context..
  bruijn_eval : Vect n Nat -> DeBruijnExp n t -> Nat
  bruijn_eval env (DValExp v) = v
  bruijn_eval env (DPlusExp e1 e2) = bruijn_eval env e1 + bruijn_eval env e2
  bruijn_eval env (DSubExp e1 e2) = minus (bruijn_eval env e1) (bruijn_eval env e2)
  bruijn_eval env (DVarExp idx) = index idx env --indexEval idx env --lookilooki idx env
  bruijn_eval env (DLetExp rhs body) = let rhs' = bruijn_eval env rhs in bruijn_eval (rhs' :: env) body


  StackType : Type
  StackType = List TyExp

  infixr 10 |>
  data Stack : (s: StackType) -> Type where
      NilStack : Stack []
      (|>) : Val t -> Stack s -> Stack (t :: s)
  
  SCons : Val t -> Stack  s -> Stack  (t :: s)
  SCons = (|>)

  top : (s : Stack  (t :: s')) -> Val t
  top (head |> _) = head


  data HasTypeInStack : (i : Fin n) -> (s: StackType) -> TyExp -> Type where
    StopStack : HasTypeInStack FZ (t :: s) t
    PopStack : HasTypeInStack k s t -> HasTypeInStack (FS k) (u :: s) t

  data Code : (s, s' : StackType) -> Type where
      Skip : Code s s
      (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
      PUSH : (v : Val t) -> Code s (t :: s)
      ADD : Code (Tnat :: Tnat :: s) (Tnat :: s)
      SUB : Code (Tnat :: Tnat :: s) (Tnat :: s)
      --VAR : (HasTypeInStack i s t) -> Code s (t :: s)
      VAR : (idx : Nat) -> Code s (t :: s)
      POP : Code (t :: s) (s)
      SWAP : Code (x :: y :: s) (y :: x :: s)

  {-
  envLookup : HasType i context t -> Environment context -> Val t
  envLookup Stop (head :: tail) = head
  envLookup (Pop x) (head :: tail) = envLookup x tail
  -}
  {-
  total
  stackLookup : (s : StackType) -> HasTypeInStack i s t -> (st : Stack s) -> Val t 
  stackLookup (t :: xs) StopStack (x |> y) = x
  stackLookup (t :: xs) (PopStack x) (hd |> tail) = stackLookup xs x tail
  -}
  --stackLookup StopStack [] = ?stackLookup_rhs_3
  --stackLookup StopStack (x :: xs) = ?kk
  --stackLookup (PopStack x) s = ?stackLookup_rhs_2

  -- men i dette nye setup får jeg stadig et problem med at stakken
  -- kan være tom når jeg skal slå en variabel op...
  -- hvis jeg tilføjer et længde-arg til stak, ender jeg med at
  -- skulle overbevise idris om at n og n' er ens allerede i skip...

  genHasType : (i : Fin n) -> (conni : Vect n TyExp) -> HasType i conni (index i conni)
  genHasType FZ (x :: xs) = Stop
  genHasType (FS x) (hd :: conni') = Pop (genHasType x conni')

  total
  exec : (Code s s') -> Stack s -> Stack s'
  exec Skip st = st
  exec (c1 ++ c2) s = exec c2 (exec c1 s)
  exec (PUSH v) st = v |> st 
  exec ADD (n |> m |> st) = (n+m) |> st 
  --exec (IF c1 c2) (True |> s) = exec c1 s
  --exec (IF c1 c2) (False |> s) = exec c2 s
  exec SUB (n |> m |> s) = (minus n m) |> s
  --exec {s} (VAR id) st = let hans = stackLookup s id st in hans |> st
  exec (VAR idx) st = ?hullane
  exec POP (hd |> st) = st
  exec SWAP (x |> y |> st) = y |> x |> st

  compile : Vect n Nat -> (DeBruijnExp n t) -> Code s (t :: s)
  compile env (DValExp v) = PUSH v
  compile env (DPlusExp e1 e2) = compile env e2 ++ compile env e1 ++ ADD
  compile env (DSubExp e1 e2) = compile env e2 ++ compile env e1 ++ SUB
  compile env (DVarExp idx) = VAR (index idx env)
  compile env (DLetExp rhs body) = ?compile_rhs_5
  {-
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


    -}