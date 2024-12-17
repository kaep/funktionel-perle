import Data.Vect
import Data.Fin

data Exp : Nat -> Type where
    ValExp : Nat -> Exp c
    PlusExp : Exp c -> Exp c -> Exp c
    VarExp : (idx : Fin c) -> Exp c
    LetExp : (rhs : Exp c)  -> (body : Exp (S c)) -> Exp c

data StackValue = STemp | SBound

infixr 10 |>
infixr 10 $>
data Stack : List StackValue -> Nat -> Type where
    EmptyStack : Stack [] 0
    (|>) : (n : Nat) -> Stack typ vars -> Stack (STemp :: typ) vars
    ($>) : (n : Nat) -> Stack typ vars -> Stack (SBound :: typ) (S vars)


total
indexStack : (idx : Fin vars) -> (Stack typ vars) -> Nat
indexStack FZ (_ |> tail) = indexStack FZ tail
indexStack FZ (hd $> _) = hd
indexStack (FS next) (_ |> tail) = indexStack (FS next) tail
indexStack (FS next) (_ $> tail) = indexStack next tail

total
countSBound : (List StackValue) -> Nat
countSBound [] = 0
countSBound (STemp :: tail) = countSBound tail
countSBound (SBound :: tail) = S (countSBound tail)

total
dropSTemp : List StackValue -> List StackValue
dropSTemp [] = []
dropSTemp (STemp :: xs) = dropSTemp xs
dropSTemp (SBound :: xs) = SBound :: dropSTemp xs

total
--eval : (Stack typ (countSBound typ)) -> Exp (countSBound typ) -> Nat
eval : (Stack typ (countSBound typ)) -> Exp (countSBound typ) -> Stack (STemp :: typ) (countSBound typ)
eval st (ValExp v) = v |> st
eval st (PlusExp e1 e2) = let (top |> st) = eval st e1 in let (top' |> st) = eval st e2 in  (top + top') |> st 
eval st (VarExp idx) = (indexStack idx st) |> st
eval st (LetExp rhs body) = let (top |> st) = eval st rhs in let (top' |> rhsVar $> st) = (eval (top $> st) body) in top' |> st

data Code : (typ : List StackValue) -> (typ' : List StackValue) -> Type where
    Skip : Code typ typ
    (++) : (c1 : Code typ st1) -> (c2 : Code st1 typ') -> Code typ typ'
    PUSH : (n : Nat) -> Code typ (STemp :: typ)
    ADD : Code (STemp :: STemp :: typ) (STemp :: typ)
    VAR : (idx : Fin (countSBound typ)) -> Code typ (STemp :: typ)
    LET : (rhs_code : Code typ (STemp :: typ)) -> (body_code : Code (SBound :: typ) (STemp :: typ)) -> Code typ (STemp :: typ)
    POP : Code (top :: typ) typ
    SWAP : Code (top :: next :: typ) (next :: top :: typ)

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
compile (PlusExp e1 e2) = compile e2 ++ compile e1 ++ ADD
compile (VarExp idx) = VAR idx
compile {typ} (LetExp rhs body) = let rhs' = compile rhs in let body' = compile {typ = SBound :: typ} body in
    let swapped = body' ++ SWAP in
    let popped = swapped ++ POP in
    LET rhs' popped


total
correct : (e: Exp (countSBound typ)) -> (st: Stack typ (countSBound typ)) -> (eval st e) = exec (compile e) st
correct (ValExp v) st = Refl
correct (PlusExp e1 e2) st = ?huller

{-
correct (PlusExp e1 e2) st with (eval st e1)
  correct (PlusExp e1 e2) st | (|>) top rest with (eval rest e2)
    correct (PlusExp e1 e2) st | (|>) top rest | (|>) top' rest' = let rhs = cong {f = \st' => exec (compile e1) st'} (correct e2 st) in
      let lhs = correct e1 (eval st e2) in 
      ?huller
      -}
correct (VarExp idx) st = Refl
correct (LetExp rhs body) st = ?correct_rhs_4
{-
let lhs = correct e1 ((eval evalEnv e2) |> st) evalEnv
                                             rhs = cong {f = \st' => exec (compile e1) st'} (correct e2 st evalEnv)
                                         in
                                            cong {f = \st' => exec ADD st'} (trans lhs rhs)


                                            
correct (PlusExp e1 e2) st = let lhs = correct e1 ((eval st e2)) in
                             let rhs = cong {f = \st' => exec (compile e1) st'} (correct e2 st) in
                              let blabber = eval st e1 in
                             ?baban
                                         -}

