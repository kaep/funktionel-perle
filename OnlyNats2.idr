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

plusExample : Exp 0
plusExample = PlusExp (ValExp 40) (ValExp 2)
plusEval : Nat
plusEval = eval [] plusExample

-- The let binding goes out of scope
-- which is why the binding count is 0
letExample : Exp 0
letExample = LetExp (ValExp 2) (PlusExp (VarExp 0) (ValExp 40))
letEval : Nat
letEval = eval [] letExample

nestedLetExample : Exp 0
nestedLetExample = LetExp (ValExp 2) (LetExp (ValExp 40) (PlusExp (VarExp 0) (VarExp 1)))
nestedLetEval : Nat
nestedLetEval = eval [] nestedLetExample

data StackValue = STemp | SBound

infixr 10 |>
infixr 10 $>
data Stack : List StackValue -> Nat -> Type where
    EmptyStack : Stack [] 0
    (|>) : (n : Nat) -> Stack typ vars -> Stack (STemp :: typ) vars
    ($>) : (n : Nat) -> Stack typ vars -> Stack (SBound :: typ) (S vars)

total
nextVar : (s : Stack typ (S count)) -> Nat 
nextVar (_ |> x) = nextVar x
nextVar (var $> _) = var

-- Denne funktion er vel egentlig for generel, er den ikke?
-- den vil jo også være korrekt hvis jeg bare returnerer emptylist
-- hele tiden..
total
typAfterVarPop : List StackValue -> List StackValue
typAfterVarPop [] = []
typAfterVarPop (STemp :: tail) = typAfterVarPop tail
typAfterVarPop (SBound :: tail) = tail


total
varTail : (s : Stack typ (S varCount)) -> Stack (typAfterVarPop typ) varCount
varTail (_ |> tail) = varTail tail
varTail (_ $> tail) = tail

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
compile (PlusExp n m) = compile m ++ compile n ++ ADD
compile (VarExp idx) = VAR idx
compile {typ} (LetExp rhs body) = let rhs' = compile rhs in let body' = compile {typ = SBound :: typ} body in 
    let swapped = body' ++ SWAP in
    let popped = swapped ++ POP in
    LET rhs' popped

-- Compiling plusExample from earlier 
-- results in code that goes from nothing to a single STemp on the stack
plusComp : Code [] [STemp]
plusComp = compile plusExample

-- Same applies here
-- the resulting stack has 0 bindings and a single value
-- Using the REPL we can observe that this
-- results in ```42 |> EmptyStack``
plusExec : Stack [STemp] 0
plusExec = exec plusComp EmptyStack

-- Compiling letExample is the same
-- as the let binding goes out of scope
letComp : Code [] [STemp]
letComp = compile letExample

-- Using the REPL we can observe that this
-- results in ```42 |> EmptyStack``
letExec : Stack [STemp] 0
letExec = exec letComp EmptyStack


nestedLetComp : Code [] [STemp]
nestedLetComp = compile nestedLetExample

nestedLetExec : Stack [STemp] 0
nestedLetExec = exec nestedLetComp EmptyStack

-- TODO skal det være deceq?
-- jeg kan jo ikke implementere deceq for to helt vilkårlige typer som
-- Vect c Nat og Stack typ c...
-- men jeg kan eventuelt bruge en type der afhænger af denne funktion, ligesom simon gay?
-- men det er jo ikke så idris-lækkert...
-- jeg har behov for en type jo..
total
evalEnvIsTheSameAsStack : (evalEnv : Vect c Nat) ->  (st : Stack typ c) -> Bool
-- Base case: both are empty, they are the same
evalEnvIsTheSameAsStack [] EmptyStack = True
-- Empty evaluation environment and a stack with no more vars, they are the same
evalEnvIsTheSameAsStack [] (n |> emptyTail) = True
-- Here envHead and next var in the stack must be equal && the tails 
evalEnvIsTheSameAsStack (envHead :: envTail) (_ |> stackTail) = let next = nextVar stackTail in (envHead == next) && evalEnvIsTheSameAsStack envTail (varTail stackTail)
-- Here heads must be equal && the tails must be equal
evalEnvIsTheSameAsStack (envHead :: envTail) (stackHead $> stackTail) = (envHead == stackHead) && evalEnvIsTheSameAsStack envTail stackTail


data EnvStackProof : (env : Vect c Nat) -> (st : Stack typ c) -> Type where
    -- The empty env and empty stack are the same
    NilProof : EnvStackProof [] EmptyStack
    -- If env and st are the same, then var::env and var $> st are the same
    VarConsProof : (var : Nat) -> (prevProof : EnvStackProof env st) -> EnvStackProof (var :: env) (var $> st)
    -- We can add arbitrarily many STemps to the stack without changing the proof
    SkipProof : (val : Nat) -> (prevProof : EnvStackProof env st) -> EnvStackProof env (val |> st)

-- Can this help idris infer the proof for correct?
createPrf : (env : Vect c Nat) -> (st: Stack typ c) -> EnvStackProof env st 
createPrf [] EmptyStack = NilProof
createPrf (x :: xs) (n |> y) = ?hul
createPrf (x :: xs) (n $> y) = ?createPrf_rhs_3

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

    -- Selvom jeg giver beviset eksplicit er der stadig ikke noget information
    -- til at udlede at dét gælder for env og st..
    --correct : (prf : EnvStackProof evalEnv st) -> (e: Exp (countSBound typ)) -> (st: Stack typ (countSBound typ)) -> (evalEnv : Vect (countSBound typ) Nat) -> ((eval evalEnv e) |> st) = exec (compile e) st
    correct : (e: Exp (countSBound typ)) -> (st: Stack typ (countSBound typ)) -> (evalEnv : Vect (countSBound typ) Nat) -> ((eval evalEnv e) |> st) = exec (compile e) st
    correct (ValExp v) st evalEnv = Refl
    correct (PlusExp e1 e2) st evalEnv = let lhs = correct e1 ((eval evalEnv e2) |> st) evalEnv
                                             rhs = cong {f = \st' => exec (compile e1) st'} (correct e2 st evalEnv)
                                         in
                                            cong {f = \st' => exec ADD st'} (trans lhs rhs)
    correct (VarExp idx) st evalEnv = ?correct_rhs_3
    correct (LetExp rhs body) st evalEnv = ?correct_rhs_4

    --correct (ValExp v) st evalEnv = Refl
    --correct (PlusExp x y) st evalEnv = ?correct_rhs_2
    --correct (VarExp idx) st evalEnv = indexing
    --correct (LetExp rhs body) st evalEnv = ?correct_rhs_4
