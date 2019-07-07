\section{BitML}

\subsection{Contracts}

\begin{frame}{Basic Types}
\begin{agda}\begin{code}
module BitML  (Participant : Set)
              (_ ≟ SUBP _ : Decidable {A = Participant} _ ≡ _)
              (Honest : List SPLUS Participant) where
Time     = ℕ
Value    = ℕ
Secret   = String
Deposit  = Participant × Value
\end{code}\end{agda}
\end{frame}

\begin{frame}{Contract Preconditions}
\begin{agda}\begin{code}
data Precondition  :  List Value -- volatile deposits
                   →  List Value -- persistent deposits
                   →  Set where
  -- volatile deposit
  _ ? _ : Participant → (v : Value) → Precondition [ v ] []
  -- persistent deposit
  _ ! _ : Participant → (v : Value) → Precondition [] [ v ]
  -- committed secret
  _ ♯ _ : Participant → Secret → Precondition [] []
  -- conjunction
  _ ∧ _  :  Precondition vs SUBV vs SUBP → Precondition vs SUBV PRIME vs SUBP PRIME
         →  Precondition (vs SUBV ++ vs SUBV PRIME) (vs SUBP ++ vs SUBP PRIME)
\end{code}\end{agda}
\end{frame}

\begin{frame}{Contracts I}
\savecolumns
\begin{agda}\begin{code}
data Contract  :  Value   -- the monetary value it carries
               →  Values  -- the volatile deposits it presumes
               →  Set where

  -- collect deposits and secrets
  put _ reveal _ if _ ⇒ _ ∶- _ :
       (vs : List Value) → (s : Secrets) → Predicate s PRIME
    →  Contract (v + sum vs) vs PRIME → s PRIME ⊆ s
    →  Contract v (vs PRIME ++ vs)

  -- transfer the remaining balance to a participant
  withdraw : ∀ {v vs} → Participant → Contract v vs
\end{code}\end{agda}
\end{frame}

\begin{frame}{Contracts II}
\restorecolumns
\begin{agda}\begin{code}
  -- split the balance across different branches
  split :  ∀ {vs} → (cs : List (∃[ v ] Contract v vs))
        →  Contract (sum (proj SUBONE ⟨$⟩ cs)) vs

  -- wait for participant's authorization
  _ ∶ _ : Participant → Contract v vs → Contract v vs

  -- wait until some time passes
  after _ : _ : Time → Contract v vs → Contract v vs
\end{code}\end{agda}
\end{frame}

\begin{frame}{Advertisements}
\begin{agda}\begin{code}
record Advertisement (v : Value) (vs SC vs SV vs SP : List Value) : Set where
  constructor _ ⟨ _ ⟩∶- _
  field  G      :  Precondition vs SV vs SP
         C      :  Contracts v vs SC
         valid  :  length vs SC ≤ length vs SV
                ×  participants SG G ++ participants SC C
                     ⊆
                   participant ⟨$⟩ persistentDeposits G
                ×  v ≡ sum vs SP
\end{code}\end{agda}
\end{frame}

\begin{frame}{Example Advertisement}
\begin{agda}\begin{code}
open BitML (A | B) DOTS [ A ] SPLUS

ex-ad : Advertisement 5 [ 200 ] [ 200 ] [ 3 , 2 ]
ex-ad =  ⟨  B ! 3 ∧ A ! 2 ∧ A ? 200 ⟩
          split  (  2 ⊸ withdraw B
                 ⊕  2 ⊸ after 42 ∶ withdraw A
                 ⊕  1 ⊸ put [ 200 ] ⇒ B ∶ withdraw {201} A ^^ )
          ∶- DOTS
\end{code}\end{agda}
\end{frame}

\subsection{Small-step Semantics}

\begin{frame}{Small-step Semantics: Actions I}
\begin{agda}\begin{code}
AdvertisedContracts  = List (∃[ v , DOTS , vs SP ] ^^ Advertisement v DOTS vs SP)
ActiveContracts      = List (∃[ v , vs ] ^^ Contracts v vs)
##
data Action (p : Participant)  -- the participant that authorizes this action
  :  AdvertisedContracts       -- contract advertisements it requires
  →  ActiveContracts           -- active contracts it requires
  →  Values                    -- deposits it requires from the participant
  →  Deposits                  -- deposits it produces
  →  Set where
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Actions II}
\begin{agda}\begin{code}
  -- join two deposits deposits
  _ ↔ _  : ∀ {vs} →  (i : Index vs) →  (j : Index vs)
         → Action p [] [] vs (p has UR ^^ ⟨$⟩ merge i j vs)
  -- commit secrets to stipulate an advertisement
  HTRI _  : (ad : Advertisement v vs SC vs SV vs SP)
          → Action p [ v , vs SC , vs SV , vs SP , ad ] [] [] []
  -- spend x to stipulate an advertisement
  _ STRI _  : (ad : Advertisement v vs SC vs SV vs SP) → (i : Index vs SP)
            → Action p [ v , vs SC , vs SV , vs SP , ad ] [] [ vs SP ‼ i ] []
  -- pick a branch
  _ BTRI _   : (c : Contracts v vs) → (i : Index c)
             → Action p [] [ v , vs , c ] [] []
  VDOTS
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Actions Example}
\begin{agda}\begin{code}
-- A spends the required {\bitcoin~ 2}, as stated in the pre-condition
ex-spend : Action A [ 5 , [ 200 ] , [ 200 ] , [ 3 , 2 ] , ex-ad ] [] [ 2 ] []
ex-spend = ex-ad STRI 1
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Configurations I}
\begin{agda}\begin{code}
data Configuration PRIME  :  -- $\hspace{19pt}$ current $\hspace{19pt}$ $\times$ $\hspace{19pt}$ required
                             AdvertisedContracts  × AdvertisedContracts
                          →  ActiveContracts      × ActiveContracts
                          →  Deposits             × Deposits
                          →  Set where

  -- empty
  ∅ : Configuration PRIME ([] , []) ([] , []) ([] , [])

  -- contract advertisement
  ` _  : (ad : Advertisement v vs SC vs SV vs SP)
       → Configuration PRIME ([ v , vs SC , vs SV , vs SP , ad ] , []) ([] , []) ([] , [])

  -- active contract
  ⟨ _ , _ ⟩ SCC  : (c : Contracts v vs) → Value
                 → Configuration PRIME ([] , []) ([ v , vs , c ] , []) ([] , [])
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Configurations II}
\restorecolumns
\begin{agda}\begin{code}
  -- deposit redeemable by a participant
  ⟨ _ , _ ⟩ SDD  :  (p : Participant) → (v : Value)
                 →  Configuration PRIME ([] , []) ([] , []) ([ p has v ] , [])

  -- authorization to perform an action
  _ [ _ ]  :  (p : Participant) → Action p ads cs vs ds
           →  Configuration PRIME ([] , ads) ([] , cs) (ds , ((p has _) ⟨$⟩ vs))

  -- committed secret
  ⟨ _ ∶ _ ♯ _ ⟩  :  Participant → Secret →  ℕ ⊎ ⊥
                 →  Configuration PRIME ([] , []) ([] , []) ([] , [])
  -- revealed secret
  _ ∶ _ ♯ _  :  Participant → Secret → ℕ
             →  Configuration PRIME ([] , []) ([] , []) ([] , [])
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Configurations III}
\restorecolumns
\begin{agda}\begin{code}
  -- parallel composition
  _ | _  :  Configuration PRIME  (ads SL , rads SL) (cs SL , rcs SL) (ds SL , rds SL)
         →  Configuration PRIME  (ads SR , rads SR) (cs SR , rcs SR) (ds SR , rds SR)
         →  Configuration PRIME  (ads SL ++ ads SR           , rads SL  ++ (rads SR ∖ ads SL))
                                 (cs SL ++ cs SR             , rcs SL ++ (rcs SR ∖ cs SL))
                                 ((ds SL ∖ rds SR) ++ ds SR  , rds SL ++ (rds SR ∖ ds SL))
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Closed Configurations}
\begin{agda}\begin{code}
Configuration ads cs ds = Configuration PRIME (ads , []) (cs , []) (ds , [])
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Inference Rules I}
\savecolumns
\begin{agda}\begin{code}
data _ —→ _  :  Configuration ads cs ds → Configuration ads PRIME cs PRIME ds PRIME
             →  Set where
  DEP-AuthJoin :
    ⟨ A , v ⟩ SDD | ⟨ A , v PRIME ⟩ SDD | Γ —→ ⟨ A , v ⟩ SDD | ⟨ A , v PRIME ⟩ SDD | A [ 0 ↔ 1 ] | Γ
##
  DEP-Join :
    ⟨ A , v ⟩ SDD | ⟨ A , v PRIME ⟩ SDD | A [ 0 LR 1 ] | Γ —→ ⟨ A , v + v PRIME ⟩ SDD | Γ
##
  C-Advertise : ∀ {Γ ad}
    →  ∃[ p ∈ participants SG (G ad) ] p ∈ Hon
       {-\inferLine{6cm}-}
    →  Γ —→ ` ad | Γ
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Inference Rules II}
\restorecolumns
\begin{agda}\begin{code}
  C-AuthCommit : ∀ {A ad Γ}
    →  secrets (G ad) ≡ a SUBONE DOTS a SUBN
    →  (A ∈ Hon → ∀[ i ∈ 1 DOTS n ] a SUBI ≢ ⊥)
       {-\inferLine{8cm}-}
    →  ` ad | Γ —→ ` ad | Γ | DOTS ⟨ A : a SUBI ♯ N SUBI ⟩ DOTS ^^ BAR ^^ A [ ♯ ▷ ^^ ad ]
##
  C-Control : ∀ {Γ C i D}
    →  C ‼ i ≡ A SUBONE : DOTS : A SUBN : D
       {-\inferLine{8cm}-}
    →  ⟨ C , v ⟩ SCC | DOTS A SUBI [ C BTRI i ] DOTS | Γ —→ ⟨ D , v ⟩ SCC | Γ
  VDOTS
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Timed Inference Rules I}
\savecolumns
\begin{agda}\begin{code}
record Configuration ST ads cs ds : Set where
  constructor _ at _
  field  cfg   : Configuration ads cs ds
         time  : Time

data _ —→ SUBT _  :  Configuration ST ads cs ds → Configuration ST ads PRIME cs PRIME ds PRIME
                  →  Set where
  Action : ∀ {Γ Γ PRIME t}
    →  Γ —→ Γ PRIME
       {-\inferLine{3cm}-}
    →  Γ at t —→ SUBT Γ PRIME at t
##
  Delay : ∀ {Γ t δ}
       {-\inferLine{4cm}-}
    →  Γ at t —→ SUBT Γ at (t + δ)
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Timed Inference Rules II}
\restorecolumns
\begin{agda}\begin{code}
  Timeout : ∀ {Γ Γ PRIME t i contract}
       -- all time constraints are satisfied
    →  All (_ ≤ t) (timeDecorations (contract ‼ i))
       -- resulting state if we pick this branch
    →  ⟨ [ contract ‼ i ] , v ⟩ SCC | Γ —→ Γ PRIME
       {-\inferLine{6cm}-}
    →  (⟨ contract , v ⟩ SCC | Γ) at t —→ SUBT Γ PRIME at t
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Reordering I}
\begin{agda}\begin{code}
_ ≈ _ : Configuration ads cs ds → Configuration ads cs ds → Set
c ≈ c PRIME = cfgToList c ↭ cfgToList c PRIME
  where
    open import Data.List.Permutation using (_ ↭ _)
    cfgToList  ∅                                     = []
    cfgToList  (l | r)                               = cfgToList l ++ cfgToList r
    cfgToList  {p SUBONE} {p SUBTWO} {p SUBTHREE} c  = [ p SUBONE , p SUBTWO , p SUBTHREE , c ]
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Reordering II}
\begin{agda}\begin{code}
  DEP-AuthJoin :
       Configuration ads cs (A has v ∷ A has v PRIME ∷ ds) ∋
         Γ PRIME ≈ ⟨ A , v ⟩ SDD | ⟨ A , v PRIME ⟩ SDD | Γ
    →  Configuration ads cs (A has (v + v PRIME) ∷ ds) ∋
         Γ DPRIME ≈ ⟨ A , v ⟩ SDD | ⟨ A , v PRIME ⟩ SDD | A [ 0 ↔ 1 ] | Γ
       {-\inferLine{8cm}-}
    →  Γ PRIME —→ Γ DPRIME
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Equational Reasoning}
\begin{agda}\begin{code}
data _ —↠ _  :  Configuration ads cs ds → Configuration ads PRIME cs PRIME ds PRIME
             →  Set where

  _ ∎ : (M : Configuration ads cs ds) → M —↠ M

  _ —→⟨ _ ⟩ _ : ∀ {L PRIME M M PRIME N} (L : Configuration ads cs ds)
    →  {L ≈ L PRIME × M ≈ M PRIME}
    →  L PRIME —→ M PRIME
    →  M —↠ N
       {-\inferLine{4cm}-}
    →  L —↠ N

begin _ : ∀ {M N} → M —↠ N → M —↠ N
\end{code}\end{agda}
\end{frame}

\subsection{Example}
\begin{frame}{Small-step Semantics: Example (contract)}

\begin{alertblock}{Timed-commitment Protocol}
|A| promises to reveal a secret, otherwise loses deposit.
\end{alertblock}

\begin{agda}\begin{code}
tc : Advertisement 1 [] [] [ 1 , 0 ])
tc =  ⟨ A ! 1 ∧ A ♯ a ∧ B ! 0 ⟩
         reveal [ a ] ⇒ withdraw A ∶- DOTS
      ⊕  after t ∶ withdraw B
\end{code}\end{agda}
\end{frame}

\begin{frame}{Small-step Semantics: Example (derivation)}
\begin{agda}\begin{code}
tc-semantics : ⟨ A , 1 ⟩ SDD —↠ ⟨ A , 1 ⟩ SDD | A ∶ a ♯ 6
tc-semantics =      ⟨ A , 1 ⟩ SDD
—→⟨ C-Advertise ⟩   ` tc | ⟨ A , 1 ⟩ SDD
—→⟨ C-AuthCommit ⟩  ` tc | ⟨ A , 1 ⟩ SDD | ⟨A ∶ a ♯♯ 6⟩ | A [ HTRI tc ]
—→⟨ C-AuthInit ⟩    ` tc | ⟨ A , 1 ⟩ SDD | ⟨A ∶ a ♯♯ 6⟩ | A [ HTRI tc ] | A [ tc STRI 0 ]
—→⟨ C-Init ⟩        ⟨ tc , 1 ⟩ SCC | ⟨ A ∶ a ♯♯ inj SUBONE 6 ⟩
—→⟨ C-AuthRev ⟩     ⟨ tc , 1 ⟩ SCC | A ∶ a ♯♯ 6
—→⟨ C-Control ⟩     ⟨ [ reveal DOTS ] , 1 ⟩ SCC | A ∶ a ♯♯ 6
—→⟨ C-PutRev ⟩      ⟨ [ withdraw A ] , 1 ⟩ SCC | A ∶ a ♯♯ 6
—→⟨ C-Withdraw ⟩    ⟨ A , 1 ⟩ SDD | A ∶ a ♯♯ 6
∎
\end{code}\end{agda}
\end{frame}

\subsection{Symbolic Model}
\begin{frame}{Symbolic Model: Labelled step relation}
\begin{agda}\begin{code}
data _ —→⟦ _ ⟧ _  :  Configuration ads cs ds
                  →  Label
                  →  Configuration ads′ cs′ ds′
                  →  Set where
  VDOTS
  DEP-AuthJoin :
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | Γ
  —→⟦ auth-join[ A , 0 ↔ 1 ] ⟧
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | A [ 0 ↔ 1 ] | Γ
  VDOTS
\end{code}\end{agda}
\end{frame}

\begin{frame}{Symbolic Model: Traces}
\begin{agda}\begin{code}
data Trace : Set where
  _ ∙         :  ∃TimedConfiguration → Trace

  _ ∷⟦ _ ⟧ _  :  ∃TimedConfiguration → Label → Trace → Trace
##
_ ——→⟦ _ ⟧ _ : Trace → Label → ∃TimedConfiguration → Set
R ——→⟦ α ⟧ (_ , _ , _ , tc′)
  = proj SUBTWO (proj SUBTWO (proj SUBTWO (lastCfg R))) —→⟦ α ⟧ tc′
\end{code}\end{agda}
\end{frame}

\begin{frame}{Symbolic Model: Strategies (honest participant)}
\begin{agda}\begin{code}
record HonestStrategy (A : Participant) : Set where
  field
    strategy  :  Trace → List Label

    valid     :  A ∈ Hon
              ×  (∀ R α → α ∈ strategy ^^ R ∗ →
                   ∃[ R′ ] (R ——→⟦ α ⟧ R′))
              ×  (∀ R α → α ∈ strategy ^^ R ∗ →
                   Allₘ (_≡ A) (authDecoration α))
              VDOTS
##
HonestStrategies = ∀ {A} → A ∈ Hon → HonestStrategy A
\end{code}\end{agda}
\end{frame}

\begin{frame}{Symbolic Model: Strategies (adversary)}
\begin{agda}\begin{code}
record AdversarialStrategy (Adv : Participant) : Set where
  field
    strategy  :  Trace → List (Participant × List Label) → Label

    valid     :  Adv ∉ Hon
              ×  ∀ {R : Trace} {moves : List (Participant × List Label)} →
                  let α = strategy ^^ R ∗ ^^ moves in
                  (  ∃[ A ]  (  A ∈ Hon
                             ×  authDecoration α ≡ just A
                             ×  α ∈ concatMap proj SUBTWO moves ^^ )
                  ⊎  (  authDecoration α ≡ nothing
                     ×  (∀ δ → α ≢ delay[ δ ])
                     ×  ∃[ R′ ] (R ——→⟦ α ⟧ R′) )
                  VDOTS
                  )
\end{code}\end{agda}
\end{frame}

\begin{frame}{Symbolic Model: Adversary makes final choice}
\begin{agda}\begin{code}
runAdversary : Strategies → Trace → Label
runAdversary (S† , S) R = strategy ^^ S† ^^ R ∗ ^^ honestMoves
  where
    honestMoves = mapWithE Hon (λ {A} p → A , strategy ^^ (S p) ^^ R ∗)
\end{code}\end{agda}
\end{frame}

\begin{frame}{Symbolic Model: Conformance}
\begin{agda}\begin{code}
data _ ^^ -conforms-to- ^^ _ : Trace → Strategies → Set where
##
    base : ∀ {Γ : Configuration ads cs ds} {SS : Strategies}

      →  Initial Γ
         {-\inferLine{6cm}-}
      →  (ads , cs , ds , Γ at 0) ∙ ^^ -conforms-to- ^^ SS
##
    step : ∀ {R : Trace} {T′ : ∃TimedConfiguration} {SS : Strategies}
      →  R ^^ -conforms-to- ^^ SS
      →  R ——→⟦ runAdversary SS R ⟧ T′
         {-\inferLine{7cm}-}
      →  (T′ ∷⟦ runAdversary SS R ⟧ R) ^^ -conforms-to- ^^ SS
\end{code}\end{agda}
\end{frame}

\begin{frame}{Symbolic Model: Meta-theory}
\begin{itemize}
\item \begin{agda}\begin{code}
strip-preserves-semantics :
  (∀ A s     → α ≢ auth-rev[ A , s ]) →
  (∀ A ad Δ  → α ≢ auth-commit[ A , ad , Δ ])
  →  ( ∀ T′  →  R   ——→⟦ α ⟧ T′
                {-\inferLine{2.5cm}-}
             →  R ∗ ——→⟦ α ⟧ T′ ∗ )

  ×  ( ∀ T′  →  R ∗ ——→⟦ α ⟧ T′
                {-\inferLine{5cm}-}
             →  ∃[ T″ ] (R ——→⟦ α ⟧ T″) × (T′ ∗ ≡ T″ ∗ )
\end{code}\end{agda}
\item \begin{agda}\begin{code}
adversarial-move-is-semantic :
  ∃[ T′ ] ( R ——→⟦ runAdversary (S† , S) R ⟧ T′)
\end{code}\end{agda}
\end{itemize}
\end{frame}

\begin{frame}{BitML Paper Fixes}

\begin{alertblock}{Discrepancies in inference rules}
e.g. forgetting surrounding context |Γ|
\end{alertblock}
\vfill
\begin{alertblock}{Non-linear derivations}
If one of the hypothesis is another step, we lose equational-style linearity. \\
\alert{Solution:} Move result state of the hypothesis to the result of the rule.
\end{alertblock}
\vfill
\begin{alertblock}{Missed assumptions}
The original formulation of the |strip-preserves-semantics| lemma required only that the action does not reveal secrets (|C-AuthRev|), but it should not commit secrets either (|C-AuthCommit|).
\end{alertblock}

\end{frame}
