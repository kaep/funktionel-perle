import Data.Fin
import Data.Vect

%default total

data TyExp = Tnat | Tbool

Val : TyExp -> Type
Val Tnat = Nat
Val Tbool = Bool

data Exp : (n : Nat) -> TyExp -> Type where
    ValExp : (v : Val t) -> Exp n t
    PlusExp : (e1 : Exp n Tnat) -> (e2 : Exp n Tnat) -> Exp n Tnat
    SubExp : (e1 : Exp n Tnat) -> (e2 : Exp n Tnat) -> Exp n Tnat
    IfExp : (b : Exp n Tbool) -> (e1 : Exp n t) -> (e2 : Exp n t) -> Exp n t
    LetExp : (rhs : Exp n t) -> (body : Exp (S n) t) -> Exp n t
    VarExp : (idx : Fin n) -> Exp n t


StackType : Type
StackType = List TyExp
  
infixr 10 |>
data Stack : (len : Nat) -> (s: StackType) -> Type where
    Nil : Stack len []
    (|>) : Val t -> Stack len s -> Stack (S len) (t :: s)

top : (s : Stack _ (t :: s')) -> Val t
top (head |> _) = head
  
index : Fin len -> Stack len s -> Val t
index FZ     (x |> xs) = ?x
index (FS k) (x |> xs) = index k xs

{-
eval : {n : Nat} -> Stack {bound = n} s -> Exp n t -> Val t
eval s (ValExp v) = v
eval s (PlusExp e1 e2) = eval s e1 + eval s e2
eval s (SubExp e1 e2) = minus (eval s e1) (eval s e2)
eval s (IfExp b e1 e2) = if eval s b then eval s e1 else eval s e2
eval s (LetExp rhs body) = 
  let rhs' = eval s rhs in
  eval (rhs' |> s) body
eval {n} s (VarExp idx) = 
  let found = indexS {bound = n} idx s in 
  ?a
  
-}
