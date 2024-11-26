%default total
data TyExp = TNat

TyVal : TyExp -> Type
TyVal TNat = Nat

data Exp : TyExp -> Bool -> Type where
    ValExp : (v : TyVal t) -> Exp t False
    PlusExp : (e1 : Exp TNat throws_a) -> (e2 : Exp TNat throws_b) -> Exp TNat (throws_a || throws_b)
    Throw : Exp t True
    Catch : Exp t throws_a -> Exp t throws_b -> Exp t (throws_a && throws_b)

evalM : Exp t _ -> Maybe (TyVal t)
evalM (ValExp v) = Just v
evalM (PlusExp e1 e2) = Just (!(evalM e1) + !(evalM e2))
evalM Throw = Nothing
evalM (Catch x h) = maybe (evalM h) (Just) (evalM x)

eval : {auto prf : b = False} -> Exp t b -> TyVal t
eval {prf = Refl} Throw impossible
eval (ValExp v) = v
eval (PlusExp {throws_a = False} {throws_b = False} e1 e2) = eval e1 + eval e2
eval {prf} (PlusExp {throws_a = False} {throws_b = True} e1 e2) = absurd prf
eval {prf} (PlusExp {throws_a = True} {throws_b = False} e1 e2) = absurd prf
eval {prf} (PlusExp {throws_a = True} {throws_b = True} e1 e2) = absurd prf
eval (Catch {throws_a = False} x h) = eval x
eval (Catch {throws_a = True} {throws_b = False} x h) = maybe (eval h) (id) (evalM x)
eval {prf} (Catch {throws_a = True} {throws_b = True} x h) = absurd prf

data Item = Val u | Han u

StackType : Type
StackType = List Item

data Stack : StackType -> Type where
  Nil : Stack []
  Cons : TyVal t -> Stack s -> Stack (Val t :: s)
  HanCons: Stack s -> Stack (Han t :: s)

data Path : (t -> t -> Type) -> t -> t -> Type where
  Empty : Path g i i
  (::)  : g i j -> Path g j k -> Path g i k

(++) : Path g i j -> Path g j k -> Path g i k
(++) Empty ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)


mutual
    data Op : StackType -> StackType -> Type where
        PUSH : TyVal t -> Op s (Val t :: s)
        ADD : Op ((Val TNat) :: (Val TNat) :: s) (Val TNat :: s)
        MARK : Op s (Han u :: s)
        UNMARK : Code s (Val u :: s) -> Op (Val u :: Han u :: s) (Val u :: s)
        THROW : Op s (Val u :: s)

    Code : (s, s' : StackType) -> Type
    Code = Path Op

unwindShape : StackType -> Nat -> StackType
unwindShape (Han _ :: xs) Z = xs
unwindShape (Han _ :: xs) (S n) = unwindShape xs n
unwindShape (Val _ :: xs) n = unwindShape xs n
unwindShape [] _ = []

unwindStack : Stack s -> (n : Nat) -> Stack (unwindShape s n)
unwindStack (HanCons xs) Z = xs
unwindStack (HanCons xs) (S n) = unwindStack xs n
unwindStack (Cons _ xs) n = unwindStack xs n
unwindStack Nil _ = Nil

data State : StackType -> Type where
    Normal : Stack s -> State s
    Exceptional : (n : Nat) -> Stack (unwindShape s n) -> State s

mutual

    execInstr : Op s s' -> State s -> State s'

    execInstr ADD (Normal (Cons x (Cons y st))) = Normal (Cons (x + y) st)
    execInstr (UNMARK _) (Normal (Cons x (HanCons st))) = Normal (Cons x st)
    execInstr (PUSH x) (Normal st) = Normal (Cons x st)
    execInstr MARK (Normal st) = Normal (HanCons st)

    execInstr THROW (Normal st) = Exceptional Z (unwindStack st Z)

    execInstr MARK (Exceptional n st) = Exceptional (S n) st
    execInstr (UNMARK _) (Exceptional (S n) st) = Exceptional n st
    execInstr (UNMARK h) (Exceptional Z st) = execCode h (Normal st)

    execInstr THROW (Exceptional n st) = Exceptional n st
    execInstr ADD (Exceptional n st) = Exceptional n st
    execInstr (PUSH _) (Exceptional n st) = Exceptional n st


    execCode : Code s s' -> State s -> State s'
    execCode Empty st = st
    execCode (i :: is) st = execCode is (execInstr i st)

sc : Op s s' -> Code s s'
sc op = op :: Empty 

compile : (Exp t b) -> Code s (Val t :: s)
compile (ValExp v) = sc $ PUSH v
compile (PlusExp e1 e2) = (compile e2) ++ (compile e1) ++ (sc $ ADD)
compile Throw = sc $ THROW
compile (Catch e h) = (sc $ MARK) ++ (compile e) ++ (sc $ UNMARK $ compile h)
 
