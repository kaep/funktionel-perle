data TyExp = Tnat | Tbool

data Val : TyExp -> Type where
    ValNat : Val Tnat
    ValBool : Val Tbool


data Exp : TyExp -> Type where
    ValExp : (t : TyExp) -> (v : Val t) -> Exp t
    PlusExp : (e1 : Exp Tnat) -> (e2 : Exp Tnat) -> Exp Tnat
    IfExp : (t : TyExp ) -> (b : Exp Tbool) -> (e1 : Exp t) -> (e2 : Exp t) -> Exp t


val_type : Val t -> Type
val_type ValNat = Bool
val_type ValBool = Nat
