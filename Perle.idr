import Syntax.PreorderReasoning

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

unwindStackType : StackType -> Nat -> StackType
unwindStackType (Han _ :: xs) Z = xs
unwindStackType (Han _ :: xs) (S n) = unwindStackType xs n
unwindStackType (Val _ :: xs) n = unwindStackType xs n
unwindStackType [] _ = []

unwindStack : Stack s -> (n : Nat) -> Stack (unwindStackType s n)
unwindStack (HanCons xs) Z = xs
unwindStack (HanCons xs) (S n) = unwindStack xs n
unwindStack (Cons _ xs) n = unwindStack xs n
unwindStack Nil _ = Nil

data State : StackType -> Type where
    Normal : Stack s -> State s
    Exceptional : (n : Nat) -> Stack (unwindStackType s n) -> State s

mutual

    execOp : Op s s' -> State s -> State s'

    execOp ADD (Normal (Cons x (Cons y st))) = Normal (Cons (x + y) st)
    execOp (UNMARK _) (Normal (Cons x (HanCons st))) = Normal (Cons x st)
    execOp (PUSH x) (Normal st) = Normal (Cons x st)
    execOp MARK (Normal st) = Normal (HanCons st)

    execOp THROW (Normal st) = Exceptional Z (unwindStack st Z)

    execOp MARK (Exceptional n st) = Exceptional (S n) st
    execOp (UNMARK _) (Exceptional (S n) st) = Exceptional n st
    execOp (UNMARK h) (Exceptional Z st) = execCode h (Normal st)

    execOp THROW (Exceptional n st) = Exceptional n st
    execOp ADD (Exceptional n st) = Exceptional n st
    execOp (PUSH _) (Exceptional n st) = Exceptional n st


    execCode : Code s s' -> State s -> State s'
    execCode Empty st = st
    execCode (i :: is) st = execCode is (execOp i st)

syntax "[(" [op] ")]" = (op) :: Empty

compile : (Exp t b) -> Code s (Val t :: s)
compile (ValExp v) = [(PUSH v)]
compile (PlusExp e1 e2) = (compile e2) ++ (compile e1) ++ [(ADD)]
compile Throw = [(THROW)]
compile (Catch e h) = [(MARK)] ++ (compile e) ++ [(UNMARK $ compile h)]


    {-

    Example:

let prog = Catch (Throw) (PlusExp (ValExp {t = TNat} 5) (ValExp 42)) in let comp = compile {s = []} prog in execCode comp (Normal [])

    -}

distribute : (st: State s) -> (a : Code s t) -> (b : Code t u) -> execCode (a ++ b) st = execCode b (execCode a st)
distribute st Empty b = Refl
distribute st (x :: xs) b = rewrite distribute (execOp x st) xs b in Refl

infixr 7 |>|
-- State stack pushing
(|>|) : Maybe (TyVal t) -> State s -> State (Val t :: s)
(|>|) (Just v) (Normal st) = Normal (Cons v st)
(|>|) Nothing  (Exceptional n st) = Exceptional n st
(|>|) (Just _) (Exceptional n st) = Exceptional n st
(|>|) Nothing  (Normal st) = Exceptional Z (unwindStack st Z)

calcExp : Exp t b -> Maybe (TyVal t)
calcExp Throw = Nothing
calcExp (ValExp v) = Just v
calcExp (PlusExp e1 e2) with (calcExp e1)
    calcExp (PlusExp e1 e2) | Nothing = Nothing
    calcExp (PlusExp e1 e2) | Just v1 with (calcExp e2)
        calcExp (PlusExp e1 e2) | Just v1 | Just v2 = Just (v1 + v2)
        calcExp (PlusExp e1 e2) | _ | _  = Nothing
calcExp (Catch x h) with (calcExp x)
    calcExp (Catch x h) | Just v = Just v
    calcExp (Catch x h) | Nothing = calcExp h

catchLemma : (e : Exp u b1) -> (h : Exp u b2) -> (st : State s) -> ((st' : State s) -> execCode (compile h) st' = (calcExp h) |>| st') -> execOp (UNMARK (compile h)) (calcExp e |>| execOp MARK st) = (calcExp (Catch e h) |>| st)
catchLemma e h st pf with (calcExp e)
    catchLemma e h (Normal y) pf | Just x = Refl
    catchLemma e h (Exceptional n st) pf | Just x = Refl
    catchLemma e h (Normal st) pf | Nothing with (calcExp h)
        catchLemma e h (Normal st) pf | Nothing | Just x = pf (Normal st)
        catchLemma e h (Normal st) pf | Nothing | Nothing = pf (Normal st)
    catchLemma e h (Exceptional n st) pf | Nothing with (calcExp h)
        catchLemma e h (Exceptional n st) pf | Nothing | Just x = Refl
        catchLemma e h (Exceptional n st) pf | Nothing | Nothing = Refl

plusLemma : (l : Exp TNat throws_a) -> (r : Exp TNat throws_b) -> (st : State s) ->
            execOp ADD ((calcExp l) |>| ((calcExp r) |>| st)) = (calcExp (PlusExp l r)) |>| st
plusLemma l r (Normal st) with (calcExp l)
    plusLemma l r (Normal st) | Just x with (calcExp r)
        plusLemma l r (Normal st) | Just x | Just y = Refl
        plusLemma l r (Normal st) | Just x | Nothing = Refl
    plusLemma l r (Normal st) | Nothing with (calcExp r)
        plusLemma l r (Normal st) | Nothing | Just y = Refl
        plusLemma l r (Normal st) | Nothing | Nothing = Refl
plusLemma l r (Exceptional n st) with (calcExp l)
    plusLemma l r (Exceptional n st) | Just x with (calcExp r)
        plusLemma l r (Exceptional n st) | Just x | Just y = Refl
        plusLemma l r (Exceptional n st) | Just x | Nothing = Refl
    plusLemma l r (Exceptional n st) | Nothing with (calcExp r)
        plusLemma l r (Exceptional n st) | Nothing | Just y = Refl
        plusLemma l r (Exceptional n st) | Nothing | Nothing = Refl

correct : (e: Exp t b) -> (st: State s) -> execCode (compile e) st = ((calcExp e) |>| st)
correct (ValExp v) (Normal x) = Refl
correct (ValExp v) (Exceptional n x) = Refl
correct Throw (Normal x) = Refl
correct Throw (Exceptional n x) = Refl

correct (Catch e h) st =
    let
        step1 = distribute (execOp MARK st) (compile e) [(UNMARK (compile h))]
        step2 = cong {f = \x => execOp (UNMARK (compile h)) x} (correct e (execOp MARK st))
        step3 = catchLemma e h st (correct h)
    in
    (execCode ([(MARK)] ++ compile e ++ [(UNMARK (compile h))]) st)
    ={ Refl }=
    (execCode (compile e ++ [(UNMARK (compile h))]) (execOp MARK st))
    ={ step1 }=
    (execCode [(UNMARK (compile h))] (execCode (compile e) (execOp MARK st)))
    ={ step2 }=
    (execOp (UNMARK (compile h)) ((calcExp e) |>| execOp MARK st))
    ={ step3 }=
    ((calcExp (Catch e h)) |>| st)
    QED

correct (PlusExp l r) st =
    let
        h_compile = cong {f = execCode (compile l)} (correct r st)
        h_correct = correct l ((calcExp r) |>| st)
    in
    (execCode (compile r ++ compile l ++ [(ADD)]) st)
        ={ distribute _ (compile r) _ }=
    (execCode (compile l ++ [(ADD)]) (execCode (compile r) st))
        ={ distribute _ (compile l) _ }=
    (execCode [(ADD)] (execCode (compile l) (execCode (compile r) st)))
        ={ cong {f = execCode [(ADD)]} h_compile }=
    (execCode [(ADD)] (execCode (compile l) ((calcExp r) |>| st)))
        ={ cong {f = execCode [(ADD)]} h_correct }=
    (execCode [(ADD)] ((calcExp l) |>| ((calcExp r) |>| st)))
        ={ plusLemma l r st }=
    ((calcExp (PlusExp l r)) |>| st)
    QED
