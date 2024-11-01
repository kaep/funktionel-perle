data TyExp = Tnat | Tbool

-- data Val : TyExp -> Type where
--     ValNat : Val Tnat -> Nat
--     ValBool : Val Tbool -> Bool

Val : TyExp -> Type
Val Tnat = Nat
Val Tbool = Bool

data Exp : TyExp -> Type where
    ValExp : (v : Val t) -> Exp t
    PlusExp : (e1 : Exp Tnat) -> (e2 : Exp Tnat) -> Exp Tnat
    IfExp : (b : Exp Tbool) -> (e1 : Exp t) -> (e2 : Exp t) -> Exp t

eval : Exp t -> Val t
eval (ValExp v) = v 
eval (PlusExp e1 e2) = eval e1 + eval e2
eval (IfExp b e1 e2) = if eval b then eval e1 else eval e2
