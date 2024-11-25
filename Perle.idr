%default total
data TyExp = TNat

Val : TyExp -> Type
Val TNat = Nat

data Exp : TyExp -> Bool -> Type where
    ValExp : (v : Val t) -> Exp t False
    PlusExp : (e1 : Exp TNat throws_a) -> (e2 : Exp TNat throws_b) -> Exp TNat (throws_a || throws_b)
    Throw : Exp t True
    Catch : Exp t throws_a -> Exp t throws_b -> Exp t (throws_a && throws_b)

evalM : Exp t _ -> Maybe (Val t)
evalM (ValExp v) = Just v
evalM (PlusExp e1 e2) = Just (!(evalM e1) + !(evalM e2))
evalM Throw = Nothing
evalM (Catch x h) = maybe (evalM h) (Just) (evalM x)

eval : {auto prf : b = False} -> Exp t b -> Val t
eval {prf = Refl} Throw impossible
eval (ValExp v) = v
eval (PlusExp {throws_a = False} {throws_b = False} e1 e2) = eval e1 + eval e2
eval {prf} (PlusExp {throws_a = False} {throws_b = True} e1 e2) = absurd prf
eval {prf} (PlusExp {throws_a = True} {throws_b = False} e1 e2) = absurd prf
eval {prf} (PlusExp {throws_a = True} {throws_b = True} e1 e2) = absurd prf
eval (Catch {throws_a = False} x h) = eval x
eval (Catch {throws_a = True} {throws_b = False} x h) = maybe (eval h) (id) (evalM x)
eval {prf} (Catch {throws_a = True} {throws_b = True} x h) = absurd prf
  
  
data Ty : Type where
  EValue : TyExp -> Ty
  EHandler : TyExp -> Ty

StackType : Type
StackType = List Ty

mutual
    data Op : (s, s' : StackType) -> Type where
      PUSH   : (v : Val t) -> Op s (EValue t :: s)
      ADD    : Op (EValue TNat :: EValue TNat :: s) (EValue TNat :: s)
      MARK   : Op s (EHandler t :: s)
      UNMARK : Code s (EValue t :: s) -> Op (EValue t :: EHandler t :: s) (EValue t :: s)
      THROW  : Op s (EValue t :: s)

    Code : (s, s' : StackType) -> Type
    Code s s' = List (Op s s')

infixr 10 |>
data Stack : (s: StackType) -> Type where
    Nil  : Stack []
    (|>) : Val t -> Stack s -> Stack (EValue t :: s)
    Han  : Stack s -> Stack (EHandler t :: s)


unwindStackType : Nat -> StackType -> StackType
unwindStackType Z     (EHandler _ :: st) = st
unwindStackType (S n) (EHandler _ :: st) = unwindStackType n st
unwindStackType n     (EValue _   :: st) = unwindStackType n st
unwindStackType _     [] = []


data Execution : (s : StackType) -> Type where
    Run  : Stack s -> Execution s
    Exception : (n : Nat) -> Stack (unwindStackType n s) -> Execution s
  
execOp : (Op s s') -> (Execution s) -> (Execution s')
execOp (PUSH v) (Run st) = Run $ v |> st
execOp ADD (Run $ n1 |> n2 |> st) = Run $ (n1 + n2) |> st
execOp MARK (Run st) = Run $ Han st 
execOp (UNMARK _) (Run $ c |> Han st) = Run $ c |> st

execOp THROW (Run st) = Exception Z ?unwindStack

execOp MARK (Exception n st) = ?execOp_rhs_9
execOp (UNMARK _) (Exception (S n) st) = ?execOp_rhs_2
execOp (UNMARK h) (Exception Z st) = ?execOp_rhs_1

execOp (PUSH v) (Exception n st) = ?execOp_rhs_7
execOp ADD (Exception n st) = ?execOp_rhs_8
execOp THROW (Exception n st) = ?execOp_rhs_11


--unwindStack : (n : Nat) -> Stack s -> Stack $ unwindStackType n s
--unwindStack Z      (Han st)  = st
--unwindStack (S n) (Han st)  = unwindStack n st
--unwindStack n (x |> st)  = unwindStack n (x |> st)
--unwindStack _      Nil       = Nil

