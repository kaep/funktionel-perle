data TyExp = Tnat | Tbool

data Val : TyExp -> Type where
    ValNat : Val Tnat
    ValBool : Val Tbool

data Exp : TyExp -> Type where
    ValExp : (v : Val t) -> Exp t
    PlusExp : (e1 : Exp Tnat) -> (e2 : Exp Tnat) -> Exp Tnat
    IfExp : (b : Exp Tbool) -> (e1 : Exp t) -> (e2 : Exp t) -> Exp t


val_type : Val t -> Type
val_type ValNat = Bool
val_type ValBool = Nat

-- We have a problem with Val here
-- because we should be able to add 
-- the result of eval e1 and eval e2
-- but e.g. Val Tnat cannot be added
-- So we somehow encoded Val wrong
eval : Exp t -> Val t
eval (ValExp v) = v 
eval (PlusExp e1 e2) = ?eval_rhs
eval (IfExp b e1 e2) = ?eval_rhs_3
