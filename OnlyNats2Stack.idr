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
eval : (Stack typ (countSBound typ)) -> Exp (countSBound typ) -> Nat
eval st (ValExp v) = v
eval st (PlusExp e1 e2) = eval st e1 + eval st e2
eval st (VarExp idx) = indexStack idx st
eval st (LetExp rhs body) = let rhs' = eval st rhs in eval (rhs' $> st) body

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


evalWithTemp : (st: Stack typ (countSBound typ)) ->
              (e: Exp (countSBound typ)) -> (n: Nat) ->
              eval (n |> st) e = eval st e

evalWithTemp st (ValExp x) n = Refl
evalWithTemp st (PlusExp x y) n =
  rewrite evalWithTemp st x n in
  rewrite evalWithTemp st y n in
  Refl
evalWithTemp st (VarExp idx) n = evalVar idx st
where
  evalVar : (idx : Fin vars) -> (st : Stack typ vars) -> indexStack idx (n |> st) = indexStack idx st
  evalVar FZ _ = Refl
  evalVar (FS x) _ = Refl

total
correct : (e: Exp (countSBound typ)) -> (st: Stack typ (countSBound typ)) -> ((eval st e) |> st) = exec (compile e) st
correct (ValExp _) st = Refl
correct (PlusExp e1 e2) st =
    let temp_eq = sym $ evalWithTemp st e1 (eval st e2) in
    let lhs = correct e1 ((eval st e2) |> st) in
    let rhs = cong {f = \st' => exec (compile e1) st'} (correct e2 st) in
    let conni = cong {f = \st' => exec ADD st'} (trans lhs rhs) in
    let step1 = cong {f = \x => (plus x (eval st e2)) |> st} temp_eq in
    trans step1 conni

correct (VarExp idx) st = Refl
correct (LetExp rhs body) st =
  let rhs_val = eval st rhs in
  let ih1 = correct rhs st in
  let ih2 = correct body (rhs_val $> st) in
  ?blah
