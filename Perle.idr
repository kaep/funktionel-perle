import Data.Vect
import Data.Fin

--%default total

using (context : Vect n TyExp)

  data TyExp = Tnat | Tbool

  Val : TyExp -> Type
  Val Tnat = Nat
  Val Tbool = Bool

  data HasType : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    Stop : HasType FZ (t :: context) t
    Pop : HasType k context t -> HasType (FS k) (u :: context) t

  data Exp : Vect n TyExp -> TyExp -> Type where
    ValExp : (v : Val t) -> Exp context t
    PlusExp : (e1 : Exp context Tnat) -> (e2 : Exp context Tnat) -> Exp context Tnat
    IfExp : (b : Exp context Tbool) -> (e1 : Exp context t) -> (e2 : Exp context t) -> Exp context t
    SubExp : (e1 : Exp context Tnat) -> (e2 : Exp context Tnat) -> Exp context Tnat
    VarExp : HasType i context t -> Exp context t
    LetExp : (rhs : Exp context t) -> (body : Exp (t:: context) t') -> Exp context t'

  data Environment : Vect n TyExp -> Type where
    NilEnv : Environment Nil
    (::) : Val t -> Environment context -> Environment (t :: context)
  
  lookup : HasType i context t -> Environment context -> Val t
  lookup Stop (head :: tail) = head
  lookup (Pop x) (head :: tail) = lookup x tail

  eval : Environment context -> Exp context t -> Val t
  eval env (ValExp v) = v
  eval env (PlusExp e1 e2) = eval env e1 + eval env e2
  eval env (IfExp b e1 e2) = if eval env b then eval env e1 else eval env e2
  eval env (SubExp e1 e2) = minus (eval env e1) (eval env e2)
  eval env (VarExp i) = lookup i env
  eval env (LetExp rhs body) = let rhs' = eval env rhs in eval (rhs' :: env) body

example_prog : Nat
example_prog = eval NilEnv (IfExp (ValExp False) (ValExp {t = Tnat} 3) (ValExp {t = Tnat} 2))

example_let : Nat
example_let = eval NilEnv (LetExp (PlusExp (ValExp {t = Tnat} 37) (ValExp {t = Tnat} 3)) (PlusExp (ValExp {t = Tnat} 2) (VarExp Stop)))

example_let_deeper : Nat
example_let_deeper = eval NilEnv (LetExp (PlusExp (ValExp {t = Tnat} 20) (ValExp {t = Tnat} 5)) (LetExp (PlusExp (ValExp {t = Tnat} 6) (ValExp {t = Tnat} 11)) (PlusExp (VarExp Stop) (VarExp (Pop Stop)))))


data StackType : Nat -> List TyExp -> Type where
  Nil : StackType 0 []
  Cons : (t : TyExp) -> StackType n l -> StackType n (t :: l)
  ConsVar : (t : TyExp) -> StackType n l -> StackType (S n) (t :: l)


infixr 10 |>
infixr 11 $>
data Stack : (s : StackType n l) -> Type where
  EmptyStack : Stack Nil
  (|>) : Val t -> Stack s -> Stack (Cons t s)
  ($>) : Val t -> Stack s -> Stack (ConsVar t s)
  --EmptyStack : Stack (Nil 0 [])
  --(|>) : Val t -> Stack s -> Stack Cons t
  --VarStack : Stack n s -> 


total
indexVar : (i : Fin n) -> (s : StackType n l) -> TyExp
-- FZ betyder at vi har talt ned og nu er ved den var vi skal bruge
-- match på s for at få den ud
-- i dette tilfælde vil vi bare gerne have t? nej vent.
-- vi har talt ned til nul og ser ikke en variabel... det er jo et problem...
-- eller er det? betyder det ikke bare at vi skal tage den næste variabel?
-- jo, korrekt.
indexVar FZ (Cons hd remaining_stack) = indexVar FZ remaining_stack
-- i dette tilfælde har vi talt ned til nul og står nu med en variabel, så vi returnerer bare t 
indexVar FZ (ConsVar hd remaining_stack) = hd
-- her nederst har vi stadig ikke talt helt ned, så vi bliver nødt til at
-- matche s for at se hvad vi skal gøre.
-- i første omgang møder vi ikke en variabel, så vi kalder rekursivt uden at tælle ned
indexVar (FS x) (Cons hd remaining) = indexVar (FS x) remaining
-- vi har mødt en variabel men er stadig ikke i bund,
-- så vi tæller ned og kalder rekursivt
indexVar (FS x) (ConsVar hd remaining) = indexVar x remaining

-- indexTy med Fin n skal tage en stackype af længden m,
-- der skal jo ikke være sammenhæng mellem hvor mange vars
-- der er på stakken og det index. det er vel kun hvis vi specifkt vil finde en var
indexTy : (i : Fin n) -> (s : StackType m l) -> TyExp
indexTy FZ (Cons t remaining_types) = t
-- the case below is shadowing? or is it? do we even want to handle this?
indexTy FZ (ConsVar t remaining_types) = t
indexTy (FS next) (Cons t remaining) = ?hullerne_1 --jeg skal have fat i noget fra remaining der er mindre jo... eller er det fordi stacktype ikke skal bindes af n?
indexTy (FS next) (ConsVar t remaining) = ?hullerne_2 --indexTy next remaining --indexTy next remaining_types 

--indexTy FZ (t :: _) = t
--indexTy (FS k) (_ :: tail) = indexTy k tail

data Code : (s : StackType n l) -> (s' : StackType n' l') -> Type where
  Skip : Code s s
  (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
  PUSH : (v : Val t) -> Code s (Cons t s)
  ADD : Code (Cons Tnat (Cons Tnat s)) (Cons Tnat s)
  SUB : Code (Cons Tnat (Cons Tnat s)) (Cons Tnat s)
  POP : Code (Cons t s) (s)
  -- VAR er spændende. En VAR instruktion skal gøre hvad? skubbe en variabel på jo!
  -- Jeg skal stadig bruge noget der kan finde dens type. det er indexVar.
  --VAR : (i : Fin nat) -> Code s (ConsVar (indexVar i s) s) 
  -- OBS: en var instruktion efterlader jo selvfølgelig en værdi på stakken, ikke en variabel
  VAR : (i : Fin nat) -> Code s (Cons (indexVar i s) s) 
  --PUSHVAR : (t : TyExp) -> Code s (ConsVar t s)

  --ADDVar : Code () (Cons)
  -- det kan ikke være rigtigt at vi skal definere add flere gange.
  -- det kræver nok bare at en variabel kan hentes somehow, inden den bruges i arith. ja. 

total
stackVarLookup : (i : Fin n) -> (st : Stack s) -> Val (indexVar i s)
-- I FZ case har vi nu set alle de variable vi skal og er klar til at returnere næste
-- i første tilfælde møder vi ikke en var, så vi kalder rekursivt
stackVarLookup FZ (hd |> remaining) = stackVarLookup FZ remaining
-- i næste tilfælde har vi mødt en var og skal returnere den
stackVarLookup FZ (var $> remaining) = var
-- i FS x casen skal vi splitte på state for at håndtere hhv. cons og consvar korrekt
-- hvis det ikke er en var, så kalder vi rekursivt uden at tælle ned
stackVarLookup (FS x) (val |> remaining) = stackVarLookup (FS x) remaining
-- hvis det er en var, så kalder vi rekursivt og tæller ned
stackVarLookup (FS x) (var $> remaining) = stackVarLookup x remaining

-- lad os prøve at definere exec.
total
exec : (Code s s') -> Stack s -> Stack s'
exec Skip st = st
exec (c1 ++ c2) st = exec c2 (exec c1 st)
exec (PUSH v) st = v |> st
exec ADD (n |> m |> st) = (n+m) |> st
exec SUB (n |> m |> st) = (minus n m) |> st
exec POP (hd |> st) = st
-- en variabel instruktion med i indikerer at vi skal finde variabel nummer i på stakken
-- som jo har n variable, hvor i er Fin n.
-- så skal vi bruge noge stacklookup igen? ja det er nok det.
--exec (VAR i) st = stackVarLookup i st $> st

-- marker ikke som variabel - det er bare en værdi
exec (VAR i) st = stackVarLookup i st |> st
--exec (PUSHVAR ty) st = ?pushvarhul


-- så kan vi definere compile
-- signaturen må være den samme: givet et exp med en context og en type, producer noget kode hvor den type er tilføjet
-- det er dog lidt mere verbose. og jeg kan ikke få lov at skrive de to stacktypes midt i code inkl. navn, så det bliver implicit
-- vi skal nok også have et env med her.

{-
codeChangeByExp : (Exp context t) -> (s: StackType n l) -> Type where
codeChangeByExp (ValExp v) s = PUSH v
codeChangeByExp (PlusExp e1 e2) s = ?codeChangeByExp_rhs_2
codeChangeByExp (IfExp b e1 e2) s = ?codeChangeByExp_rhs_3
codeChangeByExp (SubExp e1 e2) s = ?codeChangeByExp_rhs_4
codeChangeByExp (VarExp x) s = ?codeChangeByExp_rhs_5
codeChangeByExp (LetExp rhs body) s = ?codeChangeByExp_rhs_6
-}

-- can i somehow give the subproofs here?
data CodeChangeByType : (Exp context t) -> (s: StackType n l) -> (s': StackType n' l') -> Type where
  ValExpChange : CodeChangeByType (ValExp {t} v) s (Cons t s)
  --PlusExpChange : CodeChangeByType (PlusExp e1 e2) s (Cons Tnat s)
  PlusExpChange : (prf1 : CodeChangeByType e1 s (Cons Tnat s)) -> (prf2 : CodeChangeByType e2 (Cons Tnat s) (Cons Tnat (Cons Tnat s))) -> CodeChangeByType (PlusExp e1 e2) s (Cons Tnat s)
  
  --PlusExpChange : (prf1 : CodeChangeByType e1 s0 s1) -> CodeChangeByType (PlusExp e1 e2) s (Cons Tnat s)
  --PlusExpChange : (prf1 : CodeChangeByType e1 s s') -> CodeChangeByType (PlusExp e1 e2) s (Cons Tnat s)
  SubExpChange : CodeChangeByType (SubExp e1 e2) s (Cons Tnat s)
  VarExpChange : CodeChangeByType (VarExp {t} {i} prf) s (ConsVar (indexVar i s) s)
  -- a let expression pushes t' on the stack
  -- buuut, we dont really know about that in terms of consvar or cons...
  -- i guess that is semantics? a let expression will end up pushing a value
  -- right? not a variable.
  LetExpChange :  CodeChangeByType (LetExp rhs body {t'}) s (Cons t' s)
  --IfExpChange : CodeChangeByType (IfExp b e1 e2) s (Cons Tnat s)
  

--ATTEMPT WITH AUTO IMPLICIT PROOF TO MAKE RECURSION manageable
-- does not work...

{-
compile : Environment context -> (e : Exp context t) -> {auto prf : CodeChangeByType e s s' }-> Code s s'
compile {prf = ValExpChange} env (ValExp v) = PUSH v
compile {prf = PlusExpChange} env (PlusExp e1 e2) = --let hans = compile env e1 {prf} in ?ans --compile env e2 ++ compile env e1 ++ ADD
compile env (IfExp b e1 e2) = ?compile_rhs_3
compile env (SubExp e1 e2) = ?compile_rhs_4
compile env (VarExp x) = ?compile_rhs_5
compile env (LetExp rhs body) = ?compile_rhs_6
-}

--codeChangeByExp : (e : Exp context t) -> (s : StackType n l) -> (s' : StackType n' l') -> CodeChangeByType e s s'
--codeChangeByExp : (e : Exp context t) -> CodeChangeByType e s s'

codieWodie : (e : Exp context t) -> (s : StackType n l) -> Code s s'
codieWodie (ValExp v) s = ?codieWodie_rhs_1
codieWodie (PlusExp e1 e2) s = ?codieWodie_rhs_2
codieWodie (IfExp b e1 e2) s = ?codieWodie_rhs_3
codieWodie (SubExp e1 e2) s = ?codieWodie_rhs_4
codieWodie (VarExp x) s = ?codieWodie_rhs_5
codieWodie (LetExp rhs body) s = ?codieWodie_rhs_6

codeChangeByExp : (e : Exp context t) -> (s : StackType n l) -> (s' : StackType n' l') -> CodeChangeByType e s s'
codeChangeByExp e s s' = ?codeChangeByExp_rhs

infixr 10 :|:
data CompileEnvironment : (n : Nat) -> Vect n TyExp -> Type where
  NilCompEnv : CompileEnvironment 0 Nil
  (:|:) : (t : TyExp) -> CompileEnvironment n context -> CompileEnvironment (S n) (t :: context)


{-
total
lookupT : HasType i context t -> CompileEnvironment context -> TyExp
lookupT Stop (t :|: _) = t
lookupT (Pop x) (_ :|: tail) = lookupT x tail
--lookupT Stop (head :: tail) = head
--lookupT (Pop x) (head :: tail) = lookup x tail
-}

-- er dette problematisk fordi jeg kan returnere vilkårlige tyexp?
total
extractType : HasType i context t -> Environment context -> TyExp
extractType {t} Stop (hd :: tail) = t
extractType (Pop next_prf) (_ :: tail) = extractType next_prf tail

total
extractExprType : (Exp context t) -> TyExp
extractExprType {t} exp = t

total
contextIdxToStackIdxHelper : (counter : Nat) -> (ctx_idx : Fin n) -> (s : StackType n l) -> Nat
-- vi har set alle variable vi skal men er ved en værdi,
-- vi kalder rekursivt
contextIdxToStackIdxHelper counter FZ (Cons _ rest) = contextIdxToStackIdxHelper (S counter) FZ rest
-- vi har set alle variable vi skal og møder en, her giver vi counter tilbage
-- fordi vi er nået til det index i stakken vi skal bruge
contextIdxToStackIdxHelper counter FZ (ConsVar _ _) = counter
-- vi er en værdi, men er ikke færdige endnu
-- der er stadig ligeså mange variable
contextIdxToStackIdxHelper counter (FS next) (Cons _ rest) = contextIdxToStackIdxHelper (S counter) (FS next) rest
-- vi ser en variabel, men er ikke færdige endnu
contextIdxToStackIdxHelper counter (FS next) (ConsVar _ rest) = contextIdxToStackIdxHelper (S counter) next rest

total
contextIdxToStackIdx : (ctx_idx : Fin n) -> (s : StackType n l) -> Nat
contextIdxToStackIdx ctx_idx s = contextIdxToStackIdxHelper 0 ctx_idx s


-- dette er problematisk fordi jeg jo har behov for værdier
-- og ikke bare typer, når jeg pusher ifm. VAR.
-- men jeg kan lave en PUSHVAR instruktion som
-- udvider stacktype uden at tage en val?
-- ja det kan jeg godt, men så får jeg et problem i exec fordi
-- jeg jo netop har behov for værdier og ikke kun typer, når
-- jeg skal skubbe på stakken...
-- MEN! jeg skal ikke skubbe værdier på stakken ifm var jo..
compileHanzo : {s : StackType n l} -> CompileEnvironment n context -> (Exp context t) -> Code s (Cons t s)
compileHanzo env (ValExp v) = PUSH v
compileHanzo env (PlusExp e1 e2) = compileHanzo env e2 ++ compileHanzo env e1 ++ ADD
compileHanzo env (IfExp b e1 e2) = ?compileHanzo_rhs_3
compileHanzo env (SubExp e1 e2) = compileHanzo env e2 ++ compileHanzo env e1 ++ SUB
-- stackidx is a nat not bounded by anything.
-- VAR instruction wants a Fin bounded by "nat" which is not given from anywhere...
-- i would have to add another arg to stacktype, referring to the total number of elements...
-- that could/would make sense though...
compileHanzo {s} env (VarExp {i} prf) = let stackidx = contextIdxToStackIdx i s in ?hund
compileHanzo env (LetExp rhs body) = ?compileHanzo_rhs_6

data CompTimeEnv : Vect n TyExp -> Type where
  NilCompTimeEnv : CompTimeEnv Nil
  CompCons : Val t -> CompTimeEnv context -> CompTimeEnv (t :: context)
  CompConsVar : (t : TyExp) -> CompTimeEnv context -> CompTimeEnv (t :: context)

-- det går vidst ikke helt det her...
-- jeg har et bevis for at variablen på det i'te indeks har typen t
-- i konteksten..
-- den case jeg mangler herunder handler om, at vi har kigget
-- igennem og set så mange variable vi skal, så den næste vi finder skal vi
-- have værdien af. men det går jo ikke, for jeg skal jo bruge en værdi..
-- så er det bedre at have kontekst og kunne trække "t" ud fra en val t.
compTimelookupVal : HasType i context t -> CompTimeEnv context -> Val t
compTimelookupVal Stop (CompCons val _) = val
compTimelookupVal Stop (CompConsVar t x) = ?erer
compTimelookupVal (Pop x) (CompCons hd rest) = compTimelookupVal x rest
compTimelookupVal (Pop x) (CompConsVar u y) = compTimelookupVal x y

compileTheNewest : CompTimeEnv context -> (Exp context t) -> Code s (Cons t s)
compileTheNewest env (ValExp v) = PUSH v
compileTheNewest env (PlusExp e1 e2) = compileTheNewest env e2 ++ compileTheNewest env e1 ++ ADD
compileTheNewest env (IfExp b e1 e2) = ?compileTheNewest_rhs_3
compileTheNewest env (SubExp e1 e2) = compileTheNewest env e2 ++ compileTheNewest env e1 ++ SUB
compileTheNewest env (VarExp x) = ?compileTheNewest_rhs_5
compileTheNewest env (LetExp rhs body) = ?compileTheNewest_rhs_6

-- oversættelse af et udtryk efterlader altid en værdi, aldrig en var. derfor er cons t s ok.
-- jeg har stadig behov for at markere at elementet på toppen af stakken er en variabel, når jeg 
-- oversætter en let binding.
compileBetter : Environment context -> (Exp context t) -> Code s (Cons t s)
compileBetter env (ValExp v) = PUSH v
compileBetter env (PlusExp e1 e2) = compileBetter env e2 ++ compileBetter env e1 ++ ADD
--compileBetter env (IfExp b e1 e2) = ?compileBetter_rhs_3
compileBetter env (SubExp e1 e2) = compileBetter env e2 ++ compileBetter env e1 ++ SUB
-- hvordan oversættes et varexp?
-- Vi finder variablen og skubber den på stakken.
-- nej vi gør da ej? vi skal have en "VAR i" instruktion, skal vi ikke?
--compileBetter env (VarExp prf) = PUSH (lookup prf env)
compileBetter env (VarExp prf) = ?hulvar
-- hvad gør en let binding?
-- compile rhs og ++ det med compile body men hvor 
-- en var nu er øverst på stakken
-- uuh men også environment jo.
-- hmm. t' er jo en type og ikke en værdi, så den kan jeg ikke lægge i konteksten.. 
-- mit problem lige nu er at jeg ikke kan udvide kontekst ordentligt.
-- MEN! jeg behøver vel heller ikke kontekst til compile, gør jeg?
-- Kan jeg droppe kontekst helt? nej nok ikke, for så får jeg et problem
-- med VarExp hvor jeg har behov for lookup, ikke?
-- og jeg kan jo ikke bruge en stacktype alene til at at slå noget op vel?
-- MEN, code beskæftiger sig jo ikke med værdier, kun typer. right?
-- hvis jeg skal udvide Environment context SKAL jeg bruge en værdi. men kontekst alene
-- er jo bare typer...
-- men jeg skal jo give env med i det rekursive kald..
compileBetter {context} env (LetExp rhs {t} {t'} body) = 
  -- compile rhs in the given context/environment
  let rhs' = compileBetter env rhs in
  -- rhs_type er ikke nok, jeg har behov for en værdi for at udvide context...
  let rhs_type = extractExprType rhs in
  let hanzobob = rhs_type :: context in
  let ny_context = t :: context in
  -- then compile body with the expanded context from rhs.
  -- BUT: Environment concerns values... i need something non-value, only types..
  let body' = compileBetter ?envhul body in ?hamburger
  --let hanzo = t' :: context in let hammi = compileBetter hanzo body in ?hhweww
  
  --let rhs' = compileBetter env rhs in let body' = compileBetter (t' :: env) body in ?hul
  --let rhs' = compileBetter env rhs in ?huller

total
stackTypeVarLookup : (i : Fin n) -> (s : StackType n l) -> TyExp
stackTypeVarLookup FZ (Cons _ remaining) = stackTypeVarLookup FZ remaining
stackTypeVarLookup FZ (ConsVar t _) = t
stackTypeVarLookup (FS next) (Cons _ remaining) = stackTypeVarLookup (FS next) remaining
stackTypeVarLookup (FS next) (ConsVar _ remaining) = stackTypeVarLookup next remaining

-- er det bedre hvis jeg helt fjerner context fra exp? og giver det som eksplicit arg
-- ifm. var?
-- jeg har jo behov for kontekst og beviset for at kunne forene typerne ifm. et var opslag..
compileyWiley : (Exp context t) -> Code s (Cons t s)
compileyWiley (ValExp v) = PUSH v
compileyWiley (PlusExp e1 e2) = compileyWiley e2 ++ compileyWiley e1 ++ ADD
--compileyWiley (IfExp b e1 e2) = compileyWiley e2 ++ compileyWiley e1 ++SUB 
compileyWiley (SubExp e1 e2) = compileyWiley e2 ++ compileyWiley e1 ++ SUB
compileyWiley {s} (VarExp {i} prf) = ?wewe --let idx = indexVar i s in ?hullets --let lookie = stackTypeVarLookup i s in ?hulanp
compileyWiley {context} (LetExp rhs {t'} body) = ?hamburger --compileyWiley rhs ++ compileyWiley body


--compile : Environment context -> (e : Exp context t) -> Code s s'
-- this is very cool but does not support recursive calls...
-- i need a function that can give me the code change based on the type...
-- it really would be nice if this was auto implicit..
-- also, a function to generate these proofs would also not work, because subexpressions work on substacks, right?
{-
compile : Environment context -> (e : Exp context t) -> (change : CodeChangeByType e s s') -> Code s s'
compile env (ValExp v) ValExpChange = PUSH v
-- well, siden at jeg bare kan slippe afsted med add her, har jeg jo tydeligvis et problem med def af pluxexpchange...
-- men jeg skal jo egentlig bare ende med en tnat på stakken, så jeg kan måske godt slippe afsted med 
-- bare at gå fra "s" i plusexpchange? men har jeg så fjernet noget af typesikkerheden?
-- det her er helt sikkert ikke korrekt...
compile env (PlusExp e1 e2) (PlusExpChange prf1 prf2) = let e1' = compile env e1 prf1 in let e2' = compile env e2 prf2 in let added = e1' ++ e2' in added ++ ADD--let e2' = compile env e2 prf2 in let e1' = compile env e1 prf1 in e2' ++ ADD --e1' ++ e2' ++ ADD --e2' ++ e1' ++ ADD
--compile env (PlusExp e1 e2) PlusExpChange = ?erwer
--compile env (PlusExp e1 e2) PlusExpChange = let e1' = compile env e1 prf1 in ?hh
compile env (IfExp b e1 e2) change = ?compile_rhs_3
compile env (SubExp e1 e2) SubExpChange = ?compile_rhs_1
compile env (VarExp {i} prf) VarExpChange = VAR i
compile env (LetExp rhs body) LetExpChange = ?compile_rhs_2
-}

--compile : {s : StackType n l} -> {s' : StackType n' l'} -> Environment context -> (Exp context t) -> Code s s'
{-
compile env (ValExp v) = let hanzo = PUSH v in ?banan
compile env (PlusExp e1 e2) = ?compile_rhs_2
compile env (IfExp b e1 e2) = ?compile_rhs_3
compile env (SubExp e1 e2) = ?compile_rhs_4
-- VarExp stop betyder den første variabel i context, så compile til VAR 0
-- det kan jeg dog ikke, fordi jeg ikke ved om den er in bounds for fin..
compile env (VarExp Stop) = ?h
compile env (VarExp (Pop x)) = let valli = lookup (Pop x) env in ?hul_2 --jeg skal compile til VAR ?? 
compile env (LetExp rhs body) = ?compile_rhs_6
-}



{-
infixr 10 |>
data Stack : (s: StackType) -> Type where
    Nil : Stack []
    (|>) : Val t -> Stack s -> Stack (t :: s)

SCons : Val t -> Stack s -> Stack (t :: s)
SCons = (|>)

top : (s : Stack (t :: s')) -> Val t
top (head |> _) = head

indexTy : (i : Fin n) -> (s : StackType) -> TyExp
indexTy FZ (t :: _) = t
indexTy (FS k) (_ :: tail) = indexTy k tail


data Code : (s, s' : StackType) -> Type where
    Skip : Code s s
    (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
    PUSH : (v : Val t) -> Code s (t :: s)
    ADD : Code (Tnat :: Tnat :: s) (Tnat :: s)
    IF : (c1, c2 : Code s s') -> Code (Tbool :: s) s'
    SUB : Code (Tnat :: Tnat :: s) (Tnat :: s)
    POP : Code (t :: s) (s)
    SWAP : Code (x :: y :: s) (y :: x :: s)
    VAR : (i : Fin n) -> Code s (indexTy i s :: s) -- i is index, t is just an implicit type?
    -- we do not need an instruction for let.
    -- it just uses existing stuff + pop and swap

-}