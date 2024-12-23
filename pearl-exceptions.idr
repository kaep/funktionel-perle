import Syntax.PreorderReasoning

%default total
data TyExp = TNat

TyVal : TyExp -> Type
TyVal TNat = Nat

data Exp : TyExp -> Bool -> Type where
  ValExp : (v : TyVal t) -> Exp t False
  PlusExp : (l : Exp TNat throws_a) -> (r : Exp TNat throws_b) -> Exp TNat (throws_a || throws_b)
  Throw : Exp t True
  Catch : Exp t throws_a -> Exp t throws_b -> Exp t (throws_a && throws_b)

eval : Exp t b -> Maybe (TyVal t)
eval Throw = Nothing
eval (ValExp v) = Just v
eval (PlusExp l r) with (eval l)
  eval (PlusExp l r) | Nothing = Nothing
  eval (PlusExp l r) | Just v1 with (eval r)
    eval (PlusExp l r) | Just v1 | Just v2 = Just (v1 + v2)
    eval (PlusExp l r) | _ | _  = Nothing
eval (Catch x h) with (eval x)
  eval (Catch x h) | Just v = Just v
  eval (Catch x h) | Nothing = eval h

data Item = Val TyExp | Han TyExp

StackType : Type
StackType = List Item

infixr 7 |>
data Stack : StackType -> Type where
  Nil : Stack []
  (|>) : TyVal t -> Stack s -> Stack (Val t :: s)
  HanCons: Stack s -> Stack (Han t :: s)

syntax "[->" [xs] = HanCons xs;

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
    MARK : Op s (Han t :: s)
    UNMARK : Code s (Val t :: s) -> Op (Val t :: Han t :: s) (Val t :: s)
    THROW : Op s (Val t :: s)

  Code : (s, s' : StackType) -> Type
  Code = Path Op

unwindStackType : StackType -> Nat -> StackType
unwindStackType (Han _ :: xs) Z = xs
unwindStackType (Han _ :: xs) (S n) = unwindStackType xs n
unwindStackType (Val _ :: xs) n = unwindStackType xs n
unwindStackType [] _ = []

unwindStack : Stack s -> (n : Nat) -> Stack (unwindStackType s n)
unwindStack ([-> xs) Z = xs
unwindStack ([-> xs) (S n) = unwindStack xs n
unwindStack (v |> xs) n = unwindStack xs n
unwindStack Nil _ = Nil

data State : StackType -> Type where
  Normal : Stack s -> State s
  Except : (n : Nat) -> Stack (unwindStackType s n) -> State s

mutual
  execOp : Op s s' -> State s -> State s'

  execOp ADD (Normal (x |> (y |> st))) = Normal ((x + y) |> st)
  execOp (UNMARK _) (Normal (x |> ([-> st))) = Normal (x |> st)
  execOp (PUSH x) (Normal st) = Normal (x |> st)
  execOp MARK (Normal st) = Normal ([-> st)

  execOp THROW (Normal st) = Except Z (unwindStack st Z)

  execOp MARK (Except n st) = Except (S n) st
  execOp (UNMARK _) (Except (S n) st) = Except n st
  execOp (UNMARK h) (Except Z st) = execCode h (Normal st)

  execOp THROW (Except n st) = Except n st
  execOp ADD (Except n st) = Except n st
  execOp (PUSH _) (Except n st) = Except n st


  execCode : Code s s' -> State s -> State s'
  execCode Empty st = st
  execCode (i :: is) st = execCode is (execOp i st)

syntax "[(" [op] ")]" = (op) :: Empty

compile : (Exp t b) -> Code s (Val t :: s)
compile (ValExp v) = [(PUSH v)]
compile (PlusExp e1 e2) = (compile e2) ++ (compile e1) ++ [(ADD)]
compile Throw = [(THROW)]
compile (Catch e h) = [(MARK)] ++ (compile e) ++ [(UNMARK $ compile h)]

distribute : (st: State s) -> (a : Code s t) -> (b : Code t u)
            -> execCode (a ++ b) st = execCode b (execCode a st)
distribute st Empty b = Refl
distribute st (x :: xs) b = rewrite distribute (execOp x st) xs b in Refl

infixr 7 |>|
-- State stack pushing
(|>|) : Maybe (TyVal t) -> State s -> State (Val t :: s)
(|>|) (Just v) (Normal st) = Normal (v |> st)
(|>|) Nothing  (Except n st) = Except n st
(|>|) (Just _) (Except n st) = Except n st
(|>|) Nothing  (Normal st) = Except Z (unwindStack st Z)

correct : (e: Exp t b) -> (st: State s) -> execCode (compile e) st = ((eval e) |>| st)
correct (ValExp v) (Normal x) = Refl
correct (ValExp v) (Except n x) = Refl
correct Throw (Normal x) = Refl
correct Throw (Except n x) = Refl

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
  (execOp (UNMARK (compile h)) ((eval e) |>| execOp MARK st))
  ={ step3 }=
  ((eval (Catch e h)) |>| st)
  QED
  where
    catchLemma : (e : Exp u _) -> (h : Exp u _) -> (st : State s)
                 -> ((st' : State s) -> execCode (compile h) st' = (eval h) |>| st')
                 -> execOp (UNMARK (compile h)) (eval e |>| execOp MARK st) = (eval (Catch e h) |>| st)
    catchLemma e h st pf with (eval e)
      catchLemma e h (Normal y) pf | Just x = Refl
      catchLemma e h (Except n st) pf | Just x = Refl
      catchLemma e h (Normal st) pf | Nothing with (eval h)
        catchLemma e h (Normal st) pf | Nothing | Just x = pf (Normal st)
        catchLemma e h (Normal st) pf | Nothing | Nothing = pf (Normal st)
      catchLemma e h (Except n st) pf | Nothing with (eval h)
        catchLemma e h (Except n st) pf | Nothing | Just x = Refl
        catchLemma e h (Except n st) pf | Nothing | Nothing = Refl

  correct (PlusExp l r) st =
    let
      h_compile = cong {f = execCode (compile l)} (correct r st)
      h_correct = correct l ((eval r) |>| st)
      step1 = distribute _ (compile r) _
      step2 = distribute _ (compile l) _
      step3 = cong {f = execCode [(ADD)]} h_compile
      step4 = cong {f = execCode [(ADD)]} h_correct
      step5 = plusLemma l r st
    in
    (execCode (compile r ++ compile l ++ [(ADD)]) st)
      ={ step1 }=
    (execCode (compile l ++ [(ADD)]) (execCode (compile r) st))
      ={ step2 }=
    (execCode [(ADD)] (execCode (compile l) (execCode (compile r) st)))
      ={ step3 }=
    (execCode [(ADD)] (execCode (compile l) ((eval r) |>| st)))
      ={ step4 }=
    (execCode [(ADD)] ((eval l) |>| ((eval r) |>| st)))
      ={ step5 }=
    ((eval (PlusExp l r)) |>| st)
    QED
  where
    plusLemma : (l : Exp TNat throws_a) -> (r : Exp TNat throws_b) -> (st : State s)
                -> execOp ADD ((eval l) |>| ((eval r) |>| st)) = (eval (PlusExp l r)) |>| st
    plusLemma l r (Normal st) with (eval l)
      plusLemma l r (Normal st) | Just x with (eval r)
        plusLemma l r (Normal st) | Just x | Just y = Refl
        plusLemma l r (Normal st) | Just x | Nothing = Refl
      plusLemma l r (Normal st) | Nothing with (eval r)
        plusLemma l r (Normal st) | Nothing | Just y = Refl
        plusLemma l r (Normal st) | Nothing | Nothing = Refl
    plusLemma l r (Except n st) with (eval l)
      plusLemma l r (Except n st) | Just x with (eval r)
        plusLemma l r (Except n st) | Just x | Just y = Refl
        plusLemma l r (Except n st) | Just x | Nothing = Refl
      plusLemma l r (Except n st) | Nothing with (eval r)
        plusLemma l r (Except n st) | Nothing | Just y = Refl
        plusLemma l r (Except n st) | Nothing | Nothing = Refl


checkProgram : Exp t b -> Bool
checkProgram prog =
  let comp = compile {s = []} prog in
  case (eval prog, execCode comp (Normal [])) of
    (Just v1, Normal (v2|>_)) => True
    (Nothing, Except _ _) => True
    _ => False

testProgram1 : Bool
testProgram1 =
  let prog = Catch
              (PlusExp
                (ValExp 3)
                (Catch
                  Throw
                  (ValExp 8)))
              (PlusExp
                (ValExp 5)
                (ValExp 42)) in
  checkProgram prog

testProgram2 : Bool
testProgram2 =
  let prog = Catch
              (PlusExp
                (PlusExp
                  (ValExp 10)
                  (Catch Throw (ValExp 20)))
                (Catch
                  (PlusExp (ValExp 5) Throw)
                  (ValExp 30)))
              (ValExp 100) in
  checkProgram prog

testProgram3 : Bool
testProgram3 =
  let prog = Catch
              (PlusExp
                (Catch
                  (PlusExp Throw (ValExp 1))
                  (PlusExp (ValExp 2) Throw))
                (Catch
                  (PlusExp (ValExp 3) Throw)
                  (PlusExp Throw (ValExp 4))))
              Throw in
  checkProgram prog

testProgram4 : Bool
testProgram4 =
  let prog = PlusExp
              (Catch
                (PlusExp
                  (Catch Throw (ValExp 10))
                  (Catch
                    (PlusExp (ValExp 20) Throw)
                    (ValExp 30)))
                (ValExp 40))
              (Catch
                (PlusExp Throw
                  (Catch
                    (PlusExp (ValExp 50) Throw)
                    (ValExp 60)))
                (ValExp 70)) in
  checkProgram prog

testProgram5 : Bool
testProgram5 =
  let prog = Catch
              (Catch
                (Catch
                  (PlusExp
                    (Catch Throw (ValExp 1))
                    (Catch Throw (ValExp 2)))
                  (PlusExp
                    (Catch Throw (ValExp 3))
                    (Catch Throw (ValExp 4))))
                (PlusExp
                  (Catch Throw (ValExp 5))
                  (Catch Throw (ValExp 6))))
              (ValExp 7) in
  checkProgram prog


simpleExample : Exp TNat False
simpleExample = Catch
                  (PlusExp (ValExp 3)
                          (Catch Throw (ValExp 8)))
                  (PlusExp (ValExp 5) (ValExp 42))

nestedExample : Exp TNat False
nestedExample = Catch
                 (PlusExp
                   (PlusExp (ValExp 10)
                           (Catch Throw (ValExp 20)))
                   (Catch (PlusExp (ValExp 5) Throw)
                         (ValExp 30)))
                 (ValExp 100)

uncaughtExample : Exp TNat True
uncaughtExample = Catch
                   (PlusExp
                     (Catch
                       (PlusExp Throw (ValExp 1))
                       (PlusExp (ValExp 2) Throw))
                     (Catch
                       (PlusExp (ValExp 3) Throw)
                       (PlusExp Throw (ValExp 4))))
                   Throw
