%default total
data TyExp = Tnat | Tbool

Val : TyExp -> Type
Val Tnat = Nat
Val Tbool = Bool

data Exp : TyExp -> Bool -> Type where
    ValExp : (v : Val t) -> Exp t False
    PlusExp : (e1 : Exp Tnat throws_a) -> (e2 : Exp Tnat throws_b) -> Exp Tnat (throws_a || throws_b)
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

--example_progtc : Maybe Nat
--example_progtc = evalM (Catch {t = Tnat} 
--                        (PlusExp {throws_b = False} (ValExp {t = Tnat} 6) (Throw))
--                        (ValExp {t = Tnat} 3)
--                       )

-- example_prog : Maybe Nat
-- example_prog = eval (IfExp (ValExp False) (ValExp {t = Tnat} 3) 
--                                           (Catch {t = Tnat}
--                                             (PlusExp (ValExp {t = Tnat} 6) (Throw))
--                                             (ValExp {t = Tnat} 3)
--                                            ))



mutual 

    data Ty : Type where
      Enat : Ty
      Ehan : StackType -> StackType -> Ty
    
    El : Ty -> Type
    El Enat = Nat
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
        PUSH : (v : El t) -> Code (t :: s) s' -> Code s s'
        ADD : Code (Enat :: s) s' -> Code (Enat :: Enat :: s) s'
        MARK : (h : Code s s') -> (c: Code (Ehan s s' :: s) s') -> Code s s'
        UNMARK : Code (t :: s) s' -> Code (t :: Ehan s s' :: s) s'
        THROW : Code (s'' ++ Ehan s s' :: s) s'
       
mutual 
 
    exec : (Code s s') -> (Stack s) -> (Stack s')
    exec HALT st = st
    exec (PUSH v c) st = exec c (v |> st)
    exec (ADD c) (n |> m |> st) = exec c ((n + m) |> st)
    exec (MARK h c) s = exec c (h |> s)
    exec (UNMARK c) (x |> _ |> s) = exec c (x |> s)
    exec THROW stakken = fejl stakken
  
    fejl : Stack (s'' ++ (Ehan s s' :: s)) -> Stack s'
    fejl {s'' = []} (h' |> stack) = exec h' stack
    fejl {s'' = _::_} (n |> stack) = fejl stack
  
  
comp : Exp _ _ -> Code (t :: (s'' ++ Ehan s s' :: s)) s' -> Code (s'' ++ Ehan s s' :: s) s'
--comp (ValExp v) c = PUSH v c
--comp (PlusExp e1 e2) y = ?comp_rhs_2
--comp (IfExp b e1 e2) y = ?comp_rhs_3

{-

compile : (Exp t _) -> Code s (t :: s)
compile (ValExp v) = PUSH v
compile (PlusExp e1 e2) = compile e2 ++ compile e1 ++ ADD
compile (IfExp b e1 e2) = (compile b) ++ (IF (compile e1) (compile e2))
compile (SubExp e1 e2) = compile e2 ++ compile e1 ++ SUB

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
