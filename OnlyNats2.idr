import Data.Vect
import Data.Fin

data Exp : Nat -> Type where
    ValExp : Nat -> Exp c
    PlusExp : Exp c -> Exp c -> Exp c 
    VarExp : (idx : Fin c) -> Exp c
    LetExp : (rhs : Exp c)  -> (body : Exp (S c)) -> Exp c

total
eval : Vect c Nat -> Exp c -> Nat
eval st (ValExp v) = v
eval st (PlusExp e1 e2) = eval st e1 + eval st e2
eval st (VarExp idx) = index idx st
eval st (LetExp rhs body) = let rhs' = eval st rhs in eval (rhs' :: st) body

data StackValue = STemp | SBound

infixr 10 |>
infixr 10 $>
data Stack : List StackValue -> Nat -> Type where
    EmptyStack : Stack [] 0
    (|>) : (n : Nat) -> Stack typ vars -> Stack (STemp :: typ) vars
    ($>) : (n : Nat) -> Stack typ vars -> Stack (SBound :: typ) (S vars)

total
countSBound : (List StackValue) -> Nat
countSBound [] = 0
countSBound (STemp :: tail) = countSBound tail
countSBound (SBound :: tail) = S (countSBound tail)

data Code : (typ : List StackValue) -> (typ' : List StackValue) -> Type where
    Skip : Code typ typ
    (++) : (c1 : Code typ st1) -> (c2 : Code st1 typ') -> Code typ typ'
    PUSH : (n : Nat) -> Code typ (STemp :: typ)
    ADD : Code (STemp :: STemp :: typ) (STemp :: typ)
    VAR : (idx : Fin (countSBound typ)) -> Code typ (STemp :: typ)
    LET : (rhs_code : Code typ (STemp :: typ)) -> (body_code : Code (SBound :: typ) (STemp :: typ)) -> Code typ (STemp :: typ)
    --POPBODY : Code (SBound :: typ) (STemp :: SBound :: typ) -> Code (SBound :: typ) (STemp :: typ)
    POP : Code (top :: typ) typ 
    SWAP : Code (top :: next :: typ) (next :: top :: typ)
    --POPVAR : Code (STemp :: SBound :: typ) (STemp :: typ)

total
indexStack : (idx : Fin vars) -> (Stack typ vars) -> Nat
indexStack FZ (_ |> tail) = indexStack FZ tail
indexStack FZ (hd $> _) = hd
indexStack (FS next) (_ |> tail) = indexStack (FS next) tail
indexStack (FS next) (_ $> tail) = indexStack next tail

total
exec : (Code typ typ') -> (st : Stack typ (countSBound typ)) -> (Stack typ' (countSBound typ'))
exec Skip st = st
exec (c1 ++ c2) st = exec c2 (exec c1 st)
exec (PUSH n) st = n |> st
exec ADD (n |> m |> st) = (n+m) |> st
exec (VAR idx) st = let found = indexStack idx st in found |> st
exec (LET rhs_code body_code) st = let (val |> st')  = exec rhs_code st in exec body_code (val $> st')
exec POP (_ |> tail) = tail
exec POP (_ $> tail) = tail
exec SWAP (hd |> next $> tail) = next $> hd |> tail
exec SWAP (hd |> next |> tail) = next |> hd |> tail
exec SWAP (hd $> next $> tail) = next $> hd $> tail
exec SWAP (hd $> next |> tail) = next |> hd $> tail

total
compile : (Exp (countSBound typ)) -> Code typ (STemp :: typ)
compile (ValExp v) = PUSH v
compile (PlusExp n m) = compile n ++ compile m ++ ADD
compile (VarExp idx) = VAR idx
compile {typ} (LetExp rhs body) = let rhs' = compile rhs in let body' = compile {typ = SBound :: typ} body in 
    let swapped = body' ++ SWAP in
    let popped = swapped ++ POP in
    LET rhs' popped