\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
open import Data.Nat.Properties using (+-0-commutativeMonoid; +-0-monoid)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)

open import Tactic.Derive.DecEq
open import Tactic.MkRecord

open import Ledger.Prelude hiding (yes; no)
open import Ledger.Types.GovStructure

module Ledger.GovernanceActions (gs : _) (open GovStructure gs) where

defer : ℚ
defer = 1ℚ Data.Rational.+ 1ℚ

-- TODO: this could be generic
maximum : ℙ ℚ → ℚ
maximum x = foldl Data.Rational._⊔_ 0ℚ (proj₁ $ finiteness x)
\end{code}

\begin{minipage}{.3\textwidth}
\begin{code}
GovActionID = TxId × ℕ
\end{code}
\end{minipage}
\begin{minipage}{.3\textwidth}
\begin{code}
data GovRole : Type where
  CC DRep SPO : GovRole
\end{code}
\end{minipage}
\begin{code}[hide]
record Anchor : Type where
  field  url   : String
         hash  : DocHash

data VDeleg : Type where
  credVoter        : GovRole → Credential →  VDeleg
  abstainRep       :                         VDeleg
  noConfidenceRep  :                         VDeleg
\end{code}

\begin{code}
data GovAction : Type where
  NoConfidence     :                                           GovAction
  NewCommittee     : Credential ⇀ Epoch → ℙ Credential → ℚ  →  GovAction
  NewConstitution  : DocHash → Maybe ScriptHash             →  GovAction
  TriggerHF        : ProtVer                                →  GovAction
  ChangePParams    : PParamsUpdate                          →  GovAction
  TreasuryWdrl     : (RwdAddr ⇀ Coin)                       →  GovAction
  Info             :                                           GovAction
\end{code}
For the meaning of these individual actions, see \cite{cip1694}.

\begin{code}[hide]
actionWellFormed : GovAction → Bool
actionWellFormed (ChangePParams x)  = ppdWellFormed x
actionWellFormed _                  = true

private
  ∣_∣_∣_∣ : {A : Type} → A → A → A → GovRole → A
  ∣ q₁ ∣ q₂ ∣ q₃ ∣ = λ { CC → q₁ ; DRep → q₂ ; SPO → q₃ }
\end{code}
\newcommand\govThreshold{%
\begin{code}
threshold : PParams → Maybe ℚ → GovAction → GovRole → Maybe ℚ
threshold pp ccThreshold' = λ where
    NoConfidence           → ∣ noVote            ∣ vote P1      ∣ vote Q1      ∣
    (NewCommittee _ _ _)   → case ccThreshold' of λ where
      (just _)             → ∣ noVote            ∣ vote P2a     ∣ vote Q2a     ∣
      nothing              → ∣ noVote            ∣ vote P2b     ∣ vote Q2b     ∣
    (NewConstitution _ _)  → ∣ vote ccThreshold  ∣ vote P3      ∣ noVote       ∣
    (TriggerHF _)          → ∣ vote ccThreshold  ∣ vote P4      ∣ vote Q4      ∣
    (ChangePParams x)      → ∣ vote ccThreshold  ∣ vote (P5 x)  ∣ noVote       ∣
    (TreasuryWdrl _)       → ∣ vote ccThreshold  ∣ vote P6      ∣ noVote       ∣
    Info                   → ∣ vote defer        ∣ vote defer   ∣ vote defer   ∣
  where
    open PParams pp
    open DrepThresholds drepThresholds
    open PoolThresholds poolThresholds

    ccThreshold : ℚ
    ccThreshold = case ccThreshold' of λ where
      (just x)  → x
      nothing   → defer   -- (defer > 1 ⇒ unreachable threshold ⇒ not yet enactable)

    pparamThreshold : PParamGroup → ℚ
    pparamThreshold NetworkGroup     = P5a
    pparamThreshold EconomicGroup    = P5b
    pparamThreshold TechnicalGroup   = P5c
    pparamThreshold GovernanceGroup  = P5d

    P5 : PParamsUpdate → ℚ
    P5 ppu = maximum $ mapˢ pparamThreshold (updateGroups ppu)

    noVote : Maybe ℚ
    noVote = nothing

    vote : ℚ → Maybe ℚ
    vote = just

canVote : PParams → GovAction → GovRole → Type
canVote pp a r = Is-just (threshold pp nothing a r)
\end{code}
}

\newcommand\govNeedsHash{%

The design of the hash protection mechanism is elaborated here. The
issue at hand is that different actions of the same type may override
each other, and they allow for partial modifications to the state. So
if arbitrary actions were allowed to be applied, the system may end up
in a particular state that was never intended and voted for.

In the original design of the governance system, the fix for this
issue was to allow only a single governance action of each type to be
enacted per epoch. This restriction is a potentially severe limitation
and may open the door to some types of attacks.

The final design instead requires some types of governance actions to
reference the ID of the parent they are building on, similar to a
Merkle tree. Then, in a single epoch the system can take arbitrarily
many steps down that tree, and since IDs are unforgeable, the system
is only ever in a state that was publically known prior to voting.

There are two governance actions where this mechanism is not required,
because they either commute naturally or they do not actually affect
the state. For these it is more convenient to not enforce
dependencies.

\begin{code}
NeedsHash : GovAction → Type
NeedsHash NoConfidence           = GovActionID
NeedsHash (NewCommittee _ _ _)   = GovActionID
NeedsHash (NewConstitution _ _)  = GovActionID
NeedsHash (TriggerHF _)          = GovActionID
NeedsHash (ChangePParams _)      = GovActionID
NeedsHash (TreasuryWdrl _)       = ⊤
NeedsHash Info                   = ⊤

HashProtected : Type → Type
HashProtected A = A × GovActionID
\end{code}
}

\begin{minipage}{.23\textwidth}
\begin{code}
data Vote : Type where
  yes no abstain  : Vote
\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.33\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record GovVote : Type where
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    gid         : GovActionID
    role        : GovRole
    credential  : Credential
    vote        : Vote
\end{code}
\begin{code}[hide]
    anchor      : Maybe Anchor
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.33\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record GovProposal : Type where
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    action      : GovAction
    deposit     : Coin
    returnAddr  : RwdAddr
\end{code}
\begin{code}[hide]
    prevAction  : NeedsHash action
    anchor      : Anchor
\end{code}
\end{AgdaMultiCode}
\end{minipage}

% \subsection{Protocol parameters and governance actions}
% \label{sec:protocol-parameters-and-governance-actions}
% Recall from Section~\ref{sec:protocol-parameters}, parameters used in the Cardano ledger are grouped according to
% the general purpose that each parameter serves (see Figure~\ref{fig:protocol-parameter-declarations}).
% Specifically, we have \NetworkGroup, \EconomicGroup, \TechnicalGroup, and \GovernanceGroup.
% This allows voting/ratification thresholds to be set by group, though we do not require that each protocol
% parameter governance action be confined to a single group. In case a governance action carries updates
% for multiple parameters from different groups, the maximum threshold of all the groups involved will
% apply to any given such governance action.

\subsection{Enactment}
\label{sec:enactment}

Enactment of a governance action is carried out via the ENACT state
machine. We just show two example rules for this state machine---there
is one corresponding to each constructor of \GovAction. For an
explanation of the hash protection scheme, see
Appendix~\ref{appendix:governance}.

\begin{minipage}{.25\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   EnactEnv : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⟧ᵉ
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    gid       : GovActionID
    treasury  : Coin
    epoch     : Epoch
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.6\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   EnactState : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⊗_⊗_⟧ᵉ
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    cc            : HashProtected (Maybe ((Credential ⇀ Epoch) × ℚ))
    constitution  : HashProtected (DocHash × Maybe ScriptHash)
    pv            : HashProtected ProtVer
    pparams       : HashProtected PParams
    withdrawals   : RwdAddr ⇀ Coin
\end{code}
\end{AgdaMultiCode}
\end{minipage}

\begin{code}[hide]
ccCreds : HashProtected (Maybe ((Credential ⇀ Epoch) × ℚ)) → ℙ Credential
ccCreds (just x  , _)  = dom (x .proj₁)
ccCreds (nothing , _)  = ∅

open EnactState

private variable
  s : EnactState
  up : PParamsUpdate
  new : Credential ⇀ Epoch
  rem : ℙ Credential
  q : ℚ
  dh : DocHash
  sh : Maybe ScriptHash
  h : PPHash
  v : ProtVer
  wdrl : RwdAddr ⇀ Coin
  t : Coin
  gid : GovActionID
  e : Epoch

instance
  _ = +-0-monoid
  _ = +-0-commutativeMonoid
  unquoteDecl DecEq-GovRole = derive-DecEq ((quote GovRole , DecEq-GovRole) ∷ [])
  unquoteDecl DecEq-Vote    = derive-DecEq ((quote Vote    , DecEq-Vote)    ∷ [])
  unquoteDecl DecEq-VDeleg  = derive-DecEq ((quote VDeleg  , DecEq-VDeleg)  ∷ [])
\end{code}

\begin{code}[hide]
data _⊢_⇀⦇_,ENACT⦈_ : EnactEnv → EnactState → GovAction → EnactState → Type where
\end{code}
\hrule
\begin{AgdaMultiCode}
\begin{code}[hide]
  Enact-NoConf :
    ───────────────────────────────────────
    ⟦ gid ⊗ t ⊗ e ⟧ ⊢   s ⇀⦇ NoConfidence ,ENACT⦈
                record  s { cc = nothing , gid }

  Enact-NewComm : let old      = maybe proj₁ ∅ (s .EnactState.cc .proj₁)
                      maxTerm  = s .pparams .proj₁ .PParams.ccMaxTermLength +ᵉ e
                  in
    ∀[ term ∈ range new ] term ≤ maxTerm
    ───────────────────────────────────────
    ⟦ gid ⊗ t ⊗ e ⟧ ⊢  s ⇀⦇ NewCommittee new rem q ,ENACT⦈
               record  s { cc = just ((new ∪ˡ old) ∣ rem ᶜ , q) , gid }
\end{code}
\begin{code}
  Enact-NewConst :
    ───────────────────────────────────────
    ⟦ gid ⊗ t ⊗ e ⟧ ⊢ s ⇀⦇ NewConstitution dh sh ,ENACT⦈ record s { constitution = (dh , sh) , gid }
\end{code}
\begin{code}[hide]
  Enact-HF :
    ───────────────────────────────────────
    ⟦ gid ⊗ t ⊗ e ⟧ ⊢   s ⇀⦇ TriggerHF v ,ENACT⦈
                record  s { pv = v , gid }

  Enact-PParams :
    ───────────────────────────────────────
    ⟦ gid ⊗ t ⊗ e ⟧ ⊢  s ⇀⦇ ChangePParams up ,ENACT⦈
               record  s { pparams = applyUpdate (s .pparams .proj₁) up , gid }
\end{code}
\begin{code}

  Enact-Wdrl :
    let newWdrls = s .withdrawals ∪⁺ wdrl in ∑[ x ← newWdrls ᶠᵐ ] x ≤ t
    ───────────────────────────────────────
    ⟦ gid ⊗ t ⊗ e ⟧ ⊢ s ⇀⦇ TreasuryWdrl wdrl  ,ENACT⦈ record s { withdrawals  = newWdrls }
\end{code}
\begin{code}[hide]
  Enact-Info :
    ───────────────────────────────────────
    ⟦ gid ⊗ t ⊗ e ⟧ ⊢  s ⇀⦇ Info  ,ENACT⦈ s
\end{code}
\end{AgdaMultiCode}
