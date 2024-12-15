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
    POP : Code (top :: typ) typ 
    SWAP : Code (top :: next :: typ) (next :: top :: typ)

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

-- kan vi rent faktisk danne udtryk som kan oversættes og bytekode-fortolkes til værdier?

mutual
    indexing : (index idx evalEnv) |> st = (indexStack idx st) |> st
    -- index zero but empty env and stack, this is impossible
    indexing {idx = FZ} {evalEnv = []} {st = EmptyStack} impossible
    -- index non-zero but empty env and stack, this is impossible
    indexing {idx = (FS _)} {evalEnv = []} {st = EmptyStack} impossible
    -- we have elements in both env and stack
    -- and stack has a value not a var
    indexing {idx = FZ} {evalEnv = (y :: xs)} {st = (_ |> x)} = ?hul 
    indexing {idx = (FS y)} {evalEnv = evalEnv} {st = (n |> x)} = ?hul_4
    -- we have elements in both env and stack
    -- and stack has a var not a value

    -- when the index is FZ we need the final var.
    -- we need convince idris that y = n here, but that wont be possible right?
    -- because y is not the final element? case split xs!
    -- now we know that y is the final element and that n is the final variable (because "vars" of x is 0)
    -- we just need some lemma
    -- to show that y indeed does equal n in this case..
    indexing {idx = FZ} {evalEnv = (y :: [])} {st = (n $> x)} = ?hul_1
    -- 
    indexing {idx = FZ} {evalEnv = (y :: (z :: xs))} {st = (n $> x)} = ?hul_5
    -- recursive case for stack with variable top
    -- we should be able to use next and both tails because we saw var, but no..
    indexing {idx = (FS next)} {evalEnv = (_ :: xs)} {st = (_ $> x)} = ?hw--indexing {idx = next} {evalEnv = xs} {st = x}

    correct : (e: Exp (countSBound typ)) -> (st: Stack typ (countSBound typ)) -> (evalEnv : Vect (countSBound typ) Nat) -> ((eval evalEnv e) |> st) = exec (compile e) st
    correct (ValExp v) st evalEnv = Refl
    correct (PlusExp x y) st evalEnv = ?correct_rhs_2
    correct (VarExp idx) st evalEnv = indexing
    correct (LetExp rhs body) st evalEnv = ?correct_rhs_4
