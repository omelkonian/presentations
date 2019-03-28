%include polycode.fmt
%include stylish.lhs

\def\commentbegin{}
\def\commentend{}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                  UTxO                                      %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand\UTXObasicTypes{
\begin{myagda}\begin{code}
Address  = ℕ
Value    = ℕ

record State : Set where
  field  height : ℕ
         VDOTS

postulate
  UNDERL HASH : forall {A : Set} -> A -> Address
  ^^^ HASH -injective : forall {x y : A} -> x HASH ≡ y HASH -> x ≡ y
\end{code}\end{myagda}
}

\newcommand\UTXOinsOutRefs{
\begin{myagda}\begin{code}
record TxOutputRef : Set where
  constructor UNDERL at UNDERR
  field  id     : Address
         index  : ℕ

record TxInput {R D : Set} : Set where
  field  outputRef  : TxOutputRef
         redeemer   : State -> R
         validator  : State ->  Value ->  R ->  D ->  Bool
\end{code}\end{myagda}
}

\newcommand\UTXOoutTx{
\begin{myagda}\begin{code}
module UTxO (addresses : List Address) where

record TxOutput {D : Set} : Set where
  field  value       : Value
         address     : Index addresses
         dataScript  : State -> D

record Tx : Set where
  field  inputs   : Set⟨ TxInput ⟩
         outputs  : List TxOutput
         forge    : Value
         fee      : Value

Ledger : Set
Ledger = List Tx
\end{code}\end{myagda}
}

\newcommand\UTXOutxo{
\begin{myagda}\begin{code}
unspentOutputs : Ledger -> Set⟨ TxOutputRef ⟩
unspentOutputs []           = ∅
unspentOutputs (tx :: txs)  = (unspentOutputs txs ∖ spentOutputsTx tx)
                            ∪ unspentOutputsTx tx
  where
    spentOutputsTx, unspentOutputsTx : Tx -> Set⟨ TxOutputRef ⟩
    spentOutputsTx       = (outputRef <$$> UNDERR) ∘ inputs
    unspentOutputsTx tx  = ((tx HASH) ^^ at UNDERR) <$$> (indices (outputs tx))
##
runValidation  :   (i : TxInput) -> (o : TxOutput)
               ->  D i ≡ D o -> State -> Bool
runValidation i o refl st =
  validator i st (value o) (redeemer i st) (dataScript o st)
\end{code}\end{myagda}
}

\newcommand\UTXOvalidA{
\savecolumns
\begin{myagda}\begin{code}
record IsValidTx (tx : Tx) (l : Ledger) : Set where
field
  validTxRefs : forall i -> i ∈ inputs tx ->
    Any (λ t -> t HASH ≡ id (outputRef i)) l

  validOutputIndices : forall i -> (iin : ^^ i ∈ inputs tx) ->
    index (outputRef i) <
      length (outputs (lookupTx l (outputRef i) (validTxRefs i iin)))

  validOutputRefs : forall i -> i ∈ inputs tx ->
    outputRef i ∈ unspentOutputs l

  validDataScriptTypes : forall i -> (iin : ^^ i ∈ inputs tx) ->
    D i ≡ D (lookupOutput l (outputRef i)  (validTxRefs i iin)
                                           (validOutputIndices i iin))
\end{code}\end{myagda}
}
\newcommand\UTXOvalidB{
\restorecolumns
\begin{myagda}\begin{code}
  preservesValues :
    forge tx + sum (mapWith∈ (inputs tx) λ {i} iin ->
                     lookupValue l i (validTxRefs i iin) (validOutputIndices i iin))
      ≡
    fee tx + sum (value <$$> outputs tx)

  noDoubleSpending :
    noDuplicates (outputRef <$$> inputs tx)

  allInputsValidate : forall i -> (iin : ^^ i ∈ inputs tx) ->
    let  out = lookupOutput l (outputRef i) (validTxRefs i iin)
                                            (validOutputIndices i iin)
    in    forall (st : State) ->
            T (runValidation i out (validDataScriptTypes i iin) st)
       ×  toℕ (address out) ≡ (validator i) HASH
\end{code}\end{myagda}
}

\newcommand\UTXOvalidLedgers{
\begin{myagda}\begin{code}
data ValidLedger : Ledger → Set where

  ∙ UNDER ∶- UNDER  :  (t : Tx)
                    →  IsValidTx t []
                    → ValidLedger [ t ]

  UNDER ⊕ UNDER ∶- UNDER  :  ValidLedger l
                          →  (t : Tx)
                          →  IsValidTx t l
                          →  ValidLedger (t ∷ l)
\end{code}\end{myagda}
}

\newcommand\UTXOweakening{
\begin{myagda}\begin{code}
Ledger PRIME : List Address -> Set
Ledger PRIME as = Ledger where open import UTxO as
VDOTS

weakenTxOutput : Prefix as bs -> TxOutput PRIME as -> TxOutput PRIME bs
weakenTxOutput pr txOut = txOut { address = inject≤ DOTS }
  where open import UTxO bs

weakening : forall {as bs : List Address} {tx : Tx PRIME as} {l : Ledger PRIME as}
  ->  (pr : Prefix as bs)
  ->  IsValidTx PRIME as tx l
      {- $\inferLarge$ -}
  ->  IsValidTx PRIME bs (weakenTx pr tx) (weakenLedger pr l)

weakening = DOTS
\end{code}\end{myagda}
}

\newcommand\UTXOexampleSetup{
\savecolumns
\begin{myagda}\begin{code}
addresses : List Address
addresses = 1 :: 2 :: 3 :: []

open import UTxO addresses

withScripts : TxOutputRef -> TxInput
withScripts tin = record  { outputRef  = tin
                          ; redeemer   = λ _ -> 0
                          ; validator  = λ _ _ _ _ -> true }

BIT UNDERL at UNDERR : Value -> Index addresses -> TxOutput
BIT v at addr = record  { value       = v
                        ; address     = addr
                        ; dataScript  = λ _ -> 0 }
\end{code}\end{myagda}
}

\newcommand\UTXOexampleAA{
\begin{myagda}\begin{code}
t1 , t2 , t3 , t4 , t5 , t6 : Tx
t1 = record  { inputs   = []
             ; outputs  = [ BIT 1000 at 0 ]
             ; forge    = BIT 1000
             ; fee      = BIT 0 }
t2 = record  { inputs   = [ withScripts t₁₀ ]
             ; outputs  = BIT 800 at 1 :: BIT 200 at 0 :: []
             ; forge    = BIT 0
             ; fee      = BIT 0 }
t3 = record  { inputs   = [ withScripts t₂₁ ]
             ; outputs  = [ BIT 199 at 2 ]
             ; forge    = BIT 0
             ; fee      = BIT 1 }
\end{code}\end{myagda}
}
\newcommand\UTXOexampleAB{
\begin{myagda}\begin{code}
t4 = record  { inputs   = [ withScripts t₃₀ ]
             ; outputs  = [ BIT 207 at 1 ]
             ; forge    = BIT 10
             ; fee      = BIT 2 }
t5 = record  { inputs   = withScripts t₂₀ :: withScripts t₄₀ :: []
             ; outputs  = BIT 500 at 1 :: BIT 500 at 2 :: []
             ; forge    = BIT 0
             ; fee      = BIT 7 }
t6 = record  { inputs   = withScripts t₅₀ :: withScripts t₅₁ :: []
             ; outputs  = [ BIT 999 at 2 ]
             ; forge    = BIT 0
             ; fee      = BIT 1 }
\end{code}\end{myagda}
}

\newcommand\UTXOexampleB{
\begin{myagda}\begin{code}
ex-ledger : Ledger
ex-ledger =  ∙ t1 ∶- record  { validTxRefs           = λ i ()
                             ; validOutputIndices    = λ i ()
                             ; validOutputRefs       = λ i ()
                             ; validDataScriptTypes  = λ i ()
                             ; preservesValues       = refl
                             ; noDoubleSpending      = tt
                             ; allInputsValidate     = λ i () }
             ⊕  t2 ∶- record { DOTS }
                VDOTS
             ⊕  t6 ∶- record { DOTS }
##
utxo : list (unspentOutputs ex-ledger) ≡ [ t₆₀ ]
utxo = refl
\end{code}\end{myagda}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                 BitML                                      %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand\BITbasicTypes{
\begin{myagda}\begin{code}
module Types (Participant : Set) (Honest : List SUPPLUS Participant) where
##
Time     = ℕ
Value    = ℕ
Secret   = String
Deposit  = Participant × Value

data Arith : List Secret → Set where DOTS
⟦ UNDER ⟧ SUBN : Arith s → ℕ
⟦ UNDER ⟧ SUBN = DOTS

data Predicate : List Secret → Set where DOTS
⟦ UNDER ⟧ SUBB : Predicate s → Bool
⟦ UNDER ⟧ SUBB = DOTS
\end{code}\end{myagda}
}

\newcommand\BITpreconditions{
\begin{myagda}\begin{code}
data Precondition  :  List Value -- volatile deposits
                   →  List Value -- persistent deposits
                   →  Set where
  -- volatile deposit
  UNDER ? UNDER : Participant → (v : Value) → Precondition [ v ] []
  -- persistent deposit
  UNDER ! UNDER : Participant → (v : Value) → Precondition [] [ v ]
  -- committed secret
  UNDERL HASH UNDERR : Participant → Secret → Precondition [] []
  -- conjunction
  UNDER ∧ UNDER  :  Precondition vs SUBV vs SUBP → Precondition vs SUBV PRIME vs SUBP PRIME
                 →  Precondition (vs SUBV ++ vs SUBV PRIME) (vs SUBP ++ vs SUBP PRIME)
\end{code}\end{myagda}
}

\newcommand\BITcontractsA{
\savecolumns
\begin{myagda}\begin{code}
data Contract  :  Value   -- the monetary value it carries
               →  Values  -- the (volatile) deposits it presumes
               →  Set where
##
  -- collect deposits and secrets
  put UNDER reveal UNDER if UNDER ⇒ UNDER ∶- UNDER :
    (vs : List Value) → (s : Secrets) → Predicate s PRIME
    → Contract (v + sum vs) vs PRIME → s PRIME ⊆ s
    → Contract v (Interleave vs PRIME vs)
##
  -- transfer the remaining balance to a participant
  withdraw : Participant → Contract v vs
\end{code}\end{myagda}
}

\newcommand\BITcontractsB{
\restorecolumns
\begin{myagda}\begin{code}
  -- split the balance across different branches
  split :  (cs : List (exists v RP ^^ Contract v vs))
        →  Contract (sum (proj₁ <$$> cs)) vs
##
  -- wait for participant's authorization
  UNDER : UNDER : Participant → Contract v vs → Contract v vs
##
  -- wait until some time passes
  after UNDER : UNDER : Time → Contract v vs → Contract v vs
\end{code}\end{myagda}
}

\newcommand\BITadvertisements{
\begin{myagda}\begin{code}
record Advertisement (v : Value) (vs SUPC vs SUPV vs SUPP : List Value) : Set where
  constructor UNDER ⟨ UNDER ⟩∶- UNDER
  field  G      :  Precondition vs SUPV vs SUPP
         C      :  List (Contract v vs SUPC)
         valid  :  length vs SUPC ≤ length vs SUPV
                ×  participants SUPG G ++ participants SUPC C
                     ⊆
                   (participant <$$> persistentDeposits SUPP G)
                ×  v ≡ sum vs SUPP
\end{code}\end{myagda}
}

\newcommand\BITexampleAdvertisement{
\begin{myagda}\begin{code}
open BitML (A | B) [ A ] SUPPLUS

ex-ad : Advertisement 5 [ 200 ] [ 200 ] (3 ∷ 2 ∷ [])
ex-ad =  ⟨  B ! 3 ∧ A ! 2 ∧ A ^^ ? ^^ 200 ^^ ⟩
          split  (  2 ⊸ withdraw B
                 ⊕  2 ⊸ after 42 COL withdraw A
                 ⊕  1 ⊸ put [ 200 ] ⇒ B COL withdraw {201} A
                 )
          ∶- DOTS
\end{code}\end{myagda}
}

\newcommand\BITactionsA{
\savecolumns
\begin{myagda}\begin{code}
AdvertisedContracts = List (exists v , DOTS , vs SUPP RP ^^ Advertisement v DOTS vs SUPP)
ActiveContracts = List (exists v , vs RP ^^ List (Contract v vs))
##
data Action (p : Participant)  -- the participant that authorises this action
  :  AdvertisedContracts       -- the contract advertisments it requires
  →  ActiveContracts           -- the active contracts it requires
  →  Values                    -- the deposits it requires from this participant
  →  List Deposit              -- the deposits it produces
  →  Set where
\end{code}\end{myagda}
}
\newcommand\BITactionsB{
\restorecolumns
\begin{myagda}\begin{code}
  -- commit secrets to stipulate an advertisement
  HTRI UNDERR  :  (ad : Advertisement v vs SUPC vs SUPV vs SUPP)
               →  Action p [ v , vs SUPC , vs SUPV , vs SUPP , ad ] [] [] []

  -- spend x to stipulate an advertisement
  UNDER STRI UNDERR  :  (ad : Advertisement v vs SUPC vs SUPV vs SUPP)
                     →  (i : Index vs SUPP)
                     →  Action p [ v , vs SUPC , vs SUPV , vs SUPP , ad ] [] [ vs SUPP ‼ i ] []

  -- pick a branch
  UNDER BTRI UNDERR  :  (c : List (Contract v vs))
                     →  (i : Index c)
                     →  Action p [] [ v , vs , c ] [] []
  VDOTS
\end{code}\end{myagda}
}

\newcommand\BITactionExample{
\begin{myagda}\begin{code}
ex-spend : Action A [ 5 , [ 200 ] , [ 200 ] , 3 ∷ 2 ∷ [] , ex-ad ] [] [ 2 ] []
ex-spend = ex-ad STRI 1
\end{code}\end{myagda}
}

\newcommand\BITconfigurationsA{
\savecolumns
\begin{myagda}\begin{code}
data Configuration PRIME  :  -- $\hspace{22pt}$ current $\hspace{23pt}$ $\times$ $\hspace{15pt}$ required
                             AdvertisedContracts  × AdvertisedContracts
                          →  ActiveContracts      × ActiveContracts
                          →  List Deposit         × List Deposit
                          →  Set where

  -- empty
  ∅ : Configuration PRIME ([] , []) ([] , []) ([] , [])

  -- contract advertisement
  ` UNDER  :  (ad : Advertisement v vs SUPC vs SUPV vs SUPP)
           →  Configuration PRIME ([ v , vs SUPC , vs SUPV , vs SUPP , ad ] , []) ([] , []) ([] , [])

  -- active contract
  ⟨ UNDER , UNDER ⟩ SUPCC  :  (c : List (Contract v vs)) → Value
                           →  Configuration PRIME ([] , []) ([ v , vs , c ] , []) ([] , [])
\end{code}\end{myagda}
}

\newcommand\BITconfigurationsB{
\restorecolumns
\begin{myagda}\begin{code}
  -- deposit redeemable by a participant
  ⟨ UNDERR , UNDER ⟩ SUPD  :  (p : Participant) → (v : Value)
                           →  Configuration PRIME ([] , []) ([] , []) ([ p has v ] , [])

  -- authorization to perform an action
  UNDERL [ UNDER ]  :  (p : Participant) → Action p ads cs vs ds
                    →  Configuration PRIME ([] , ads) ([] , cs) (ds , ((p has UNDER) <$$> vs))

  -- committed secret
  ⟨ UNDER COL UNDERL HASH UNDERR ⟩  :  Participant → Secret →  ℕ ⊎ ⊥
                                    →  Configuration PRIME ([] , []) ([] , []) ([] , [])
  -- revealed secret
  UNDER COL UNDERL HASH UNDERR  :  Participant → Secret → ℕ
                                →  Configuration PRIME ([] , []) ([] , []) ([] , [])
\end{code}\end{myagda}
}

\newcommand\BITconfigurationsC{
\restorecolumns
\begin{myagda}\begin{code}
  -- parallel composition
  UNDER | UNDER  :  Configuration PRIME  (ads SUPL , rads SUPL) (cs SUPL , rcs SUPL) (ds SUPL , rds SUPL)
                 →  Configuration PRIME  (ads SUPR , rads SUPR) (cs SUPR , rcs SUPR) (ds SUPR , rds SUPR)
                 →  Configuration PRIME  (ads SUPL ++ ads SUPR             , rads SUPL ++ (rads SUPR ∖ ads SUPL))
                                         (cs SUPL ++ cs SUPR               , rcs SUPL ++ (rcs SUPR ∖ cs SUPL))
                                         ((ds SUPL ∖ rds SUPR) ++ ds SUPR  , rds SUPL ++ (rds SUPR ∖ ds SUPL))
\end{code}\end{myagda}
}

\newcommand\BITclosedConfigurations{
\begin{myagda}\begin{code}
Configuration ads cs ds = Configuration PRIME (ads , []) (cs , []) (ds , [])
\end{code}\end{myagda}
}

\newcommand\BITrulesA{
\savecolumns
\begin{myagda}\begin{code}
data UNDER —→ UNDER  :  Configuration ads cs ds → Configuration ads PRIME cs PRIME ds PRIME
                     →  Set where
  DEP-AuthJoin :
    ⟨ A , v ⟩ SUPD | ⟨ A , v PRIME ⟩ SUPD | Γ —→ ⟨ A , v ⟩ SUPD | ⟨ A , v PRIME ⟩ SUPD | A [ 0 ↔ 1 ] | Γ
##
  DEP-Join :
    ⟨ A , v ⟩ SUPD | ⟨ A , v PRIME ⟩ SUPD | A [ 0 ↔ 1 ] | Γ —→ ⟨ A , v + v PRIME ⟩ SUPD | Γ
##
  C-Advertise : forall {Γ ad}
    →  exists p ∈ participants SUPG (G ad) RP p ∈ Hon
       {- $\inferLarge$ -}
    →  Γ —→ ` ad | Γ
\end{code}\end{myagda}
}

\newcommand\BITrulesB{
\restorecolumns
\begin{myagda}\begin{code}
  C-AuthCommit : forall {A ad Γ}
    →  secrets (G ad) ≡ a₁ DOTS aₙ
    →  (A ∈ Hon → forall[ i ∈ 1 DOTS n ] a SUBI ≢ ⊥)
       {- $\inferLarge$ -}
    →  ` ad | Γ —→ ` ad | Γ | DOTS ⟨ A : a SUBI HASH N SUBI ⟩ DOTS ^^ BAR ^^ A [ HASH ▷ ^^ ad ]
##
  C-Control : forall {Γ C i D}
    →  C ‼ i ≡ A₁ : DOTS : Aₙ : D
       {- $\inferLarge$ -}
    →  ⟨ C , v ⟩ SUPCC | DOTS A SUBI [ C BTRI i ] DOTS | Γ —→ ⟨ D , v ⟩ SUPCC | Γ
  VDOTS
\end{code}\end{myagda}
}

\newcommand\BITtimedRulesA{
\savecolumns
\begin{myagda}\begin{code}
record Configuration SUPT ads cs ds : Set where
  constructor UNDER at UNDER
  field  cfg   : Configuration ads cs ds
         time  : Time

data UNDER —→ SUBT UNDER  :  Configuration SUPT ads cs ds → Configuration SUPT ads PRIME cs PRIME ds PRIME
                          →  Set where
  Action : forall {Γ Γ PRIME t}
    →  Γ —→ Γ PRIME
       {- $\inferSmall$ -}
    →  Γ at t —→ SUBT Γ PRIME at t
##
  Delay : forall {Γ t δ}
       {- $\inferMedium$ -}
    →  Γ at t —→ SUBT Γ at (t + δ)
\end{code}\end{myagda}
}

\newcommand\BITtimedRulesB{
\restorecolumns
\begin{myagda}\begin{code}
  Timeout : forall {Γ Γ PRIME t i contract}
       -- all time constraints are satisfied
    →  All (UNDER ≤ t) (timeDecorations (contract ‼ i))
       -- resulting state if we pick this branch
    →  ⟨ [ contract ‼ i ] , v ⟩ SUPCC | Γ —→ Γ PRIME
       {- $\inferMedium$ -}
    →  (⟨ contract , v ⟩ SUPCC | Γ) at t —→ SUBT Γ PRIME at t
\end{code}\end{myagda}
}

\newcommand\BITeqReasoning{
\begin{myagda}\begin{code}
data UNDER —↠ UNDER : Configuration ads cs ds → Configuration ads PRIME cs PRIME ds PRIME → Set where

  UNDER ∎ : (M : Configuration ads cs ds) → M —↠ M

  UNDER —→⟨ UNDER ⟩ UNDER : forall {L PRIME M M PRIME N} (L : Configuration ads cs ds)
    →  {L ≈ L PRIME × M ≈ M PRIME}
    →  L PRIME —→ M PRIME
    →  M —↠ N
       {- $\inferMedium$ -}
    →  L —↠ N

begin UNDER : forall {M N} → M —↠ N → M —↠ N
\end{code}\end{myagda}
}

\newcommand\BITexampleA{
\begin{myagda}\begin{code}
tc : Advertisement 1 [] [] (1 ∷ 0 ∷ [])
tc =  ⟨ A ! 1 ∧ A HASH a ∧ B ! 0 ⟩
         reveal [ a ] ⇒ withdraw A ∶- DOTS
      ⊕  after t COL withdraw B
\end{code}\end{myagda}
}

\newcommand\BITexampleB{
\begin{myagda}\begin{code}
tc-semantics : ⟨ A , 1 ⟩ SUPD —↠ ⟨ A , 1 ⟩ SUPD | A COL a HASH 6
tc-semantics =      ⟨ A , 1 ⟩ SUPD
—→⟨ C-Advertise ⟩   ` tc | ⟨ A , 1 ⟩ SUPD
—→⟨ C-AuthCommit ⟩  ` tc | ⟨ A , 1 ⟩ SUPD | ⟨A COL a HASH 6⟩ | A [ HTRI tc ]
—→⟨ C-AuthInit ⟩    ` tc | ⟨ A , 1 ⟩ SUPD | ⟨A COL a HASH 6⟩ | A [ HTRI tc ] | A [ tc STRI 0 ]
—→⟨ C-Init ⟩        ⟨ tc , 1 ⟩ SUPCC | ⟨ A COL a HASH inj₁ 6 ⟩
—→⟨ C-AuthRev ⟩     ⟨ tc , 1 ⟩ SUPCC | A COL a HASH 6
—→⟨ C-Control ⟩     ⟨ [ reveal DOTS ] , 1 ⟩ SUPCC | A COL a HASH 6
—→⟨ C-PutRev ⟩      ⟨ [ withdraw A ] , 1 ⟩ SUPCC | A COL a HASH 6
—→⟨ C-Withdraw ⟩    ⟨ A , 1 ⟩ SUPD | A COL a HASH 6
∎
\end{code}\end{myagda}
}

\newcommand\BITreordering{
\begin{myagda}\begin{code}
UNDER ≈ UNDER : Configuration ads cs ds → Configuration ads cs ds → Set
c ≈ c PRIME = cfgToList c ↭ cfgToList c PRIME
  where
    open import Data.List.Permutation using (UNDER ↭ UNDER)
    cfgToList  ∅                 = []
    cfgToList  (l | r)           = cfgToList l ++ cfgToList r
    cfgToList  {p₁} {p₂} {p₃} c  = [ p₁ , p₂ , p₃ , c ]
\end{code}\end{myagda}
}

\newcommand\BITgeneralRule{
\begin{myagda}\begin{code}
  DEP-AuthJoin :
       Configuration ads cs (A has v ∷ A has v PRIME ∷ ds) ∋
         Γ PRIME ≈ ⟨ A , v ⟩ SUPD | ⟨ A , v PRIME ⟩ SUPD | Γ
    →  Configuration ads cs (A has (v + v PRIME) ∷ ds) ∋
         Γ DPRIME ≈ ⟨ A , v ⟩ SUPD | ⟨ A , v PRIME ⟩ SUPD | A [ 0 ↔ 1 ] | Γ
       {- $\inferLarge$ -}
    →  Γ PRIME —→ Γ DPRIME
\end{code}\end{myagda}
}
