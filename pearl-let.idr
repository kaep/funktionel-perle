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
countSBound : (List StackValue) -> Nat
countSBound [] = 0
countSBound (STemp :: tail) = countSBound tail
countSBound (SBound :: tail) = S (countSBound tail)

total
indexStack :  (idx : Fin vars) -> (Stack typ vars) -> Nat
indexStack FZ (_ |> tail) = indexStack FZ tail
indexStack FZ (hd $> _) = hd
indexStack (FS next) (_ |> tail) = indexStack (FS next) tail
indexStack (FS next) (_ $> tail) = indexStack next tail

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


indexSkipsPreTemp : indexStack idx (n |> st) = indexStack idx st
indexSkipsPreTemp {idx = FZ} = Refl
indexSkipsPreTemp {idx = (FS x)} = Refl

indexSkipsPostTemp : indexStack idx (bound $> n |> st) = indexStack idx (bound $> st)
indexSkipsPostTemp {idx = FZ} = Refl
indexSkipsPostTemp {idx = (FS x)} {st} = indexSkipsPreTemp

indexCommutes : indexStack idx (bound $> n |> st) = indexStack idx (n |> bound $> st)
indexCommutes {idx = FZ} = Refl
indexCommutes {idx = (FS x)} = indexSkipsPreTemp

stackOrderEquiv : (st : Stack typ (countSBound typ)) -> (bound, temp, val : Nat) ->
                 eval (val $> bound $> temp |> st) body =
                 eval (val $> temp |> bound $> st) body
stackOrderEquiv {body} st bound temp val with (body)
  stackOrderEquiv st bound temp val | (ValExp x) = Refl
  stackOrderEquiv st bound temp val | (PlusExp e1 e2) = 
    let ih1 = stackOrderEquiv st bound temp val {body = e1} in
    let ih2 = stackOrderEquiv st bound temp val {body = e2} in
    rewrite ih1 in
    rewrite ih2 in
    Refl
  stackOrderEquiv st bound temp val | (VarExp FZ) = Refl
  stackOrderEquiv st bound temp val | (VarExp (FS x)) = indexCommutes
  stackOrderEquiv st bound temp val | (LetExp rhs body') = ?not_done_order_equiv

evalBoundWithTemp : (st : Stack typ (countSBound typ)) ->
                    (e : Exp (S $ countSBound typ)) ->
                    (bound : Nat) ->
                    (temp : Nat) ->
                    eval (bound $> temp |> st) e = eval (bound $> st) e
evalBoundWithTemp st (ValExp x) bound temp = Refl
evalBoundWithTemp st (PlusExp x y) bound temp =
    rewrite evalBoundWithTemp st x bound temp in
    rewrite evalBoundWithTemp st y bound temp in
    Refl
evalBoundWithTemp st (VarExp idx) bound temp = indexSkipsPostTemp
evalBoundWithTemp st (LetExp rhs body) bound temp =
  let rhs' = evalBoundWithTemp st rhs bound temp in
  let body' = evalBoundWithTemp (bound $> st) body (eval (bound $> st) rhs) temp in
  rewrite rhs' in
  rewrite sym body' in
  stackOrderEquiv st bound temp (eval (bound $> st) rhs)

evalWithTemp : (st: Stack typ (countSBound typ)) ->
              (e: Exp (countSBound typ)) -> (n: Nat) ->
              eval (n |> st) e = eval st e

evalWithTemp st (ValExp x) n = Refl
evalWithTemp st (PlusExp x y) n =
  rewrite evalWithTemp st x n in
  rewrite evalWithTemp st y n in
  Refl
evalWithTemp st (VarExp idx) n = indexSkipsPreTemp
evalWithTemp st (LetExp rhs body) n = evalLet st rhs body n
where
  evalLet : (st : Stack typ (countSBound typ)) ->
            (rhs : Exp (countSBound typ)) ->
            (body : Exp (S (countSBound typ))) ->
            (n : Nat) ->
            eval ((eval (n |> st) rhs) $> (n |> st)) body
            = eval ((eval st rhs) $> st) body
  evalLet st rhs body n =
    let rhs' = evalWithTemp st rhs n in
    rewrite rhs' in
    evalBoundWithTemp st body (eval st rhs) n

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
  ?not_done_correct