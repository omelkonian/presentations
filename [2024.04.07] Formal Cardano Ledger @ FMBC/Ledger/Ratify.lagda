Governance actions are \defn{ratified} through on-chain voting actions.
Different kinds of governance actions have different ratification requirements
but always involve at least \textit{two of the three} governance bodies.
The voting power of the \DRep and \SPO roles is proportional to the stake
delegated to them, while the constitutional committee has individually
elected members where each member has the same voting power.

Some actions take priority over others and, when enacted, delay all
further ratification to the next epoch boundary. This allows a changed
government to reevaluate existing proposals.

% \subsection{Ratification requirements}
% \label{sec:ratification-requirements}
% Figure~\ref{fig:ratification-requirements} details the ratification requirements for each
% governance action scenario. The columns represent
% \begin{itemize}
% \item
%   \GovAction: the action under consideration;
% \item
%   \CC: a \ding{51} indicates that the constitutional committee must approve this action;
%   a - symbol means that constitutional committee votes do not apply;
% \item
%   \DRep: the vote threshold that must be met as a percentage of \totalStake;
% \item
%   \SPO: the vote threshold that must be met as a percentage of the stake held by
%   all stake pools; a - symbol means that \SPO votes do not apply.
% \end{itemize}
% \begin{longtable}[]{@{}
%   >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.65}}
%   >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.11}}
%   >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.12}}
%   >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.12}}@{}}
% \GovAction  & \CC  &  \DRep & \SPO \\
% \hline
% \endhead
% 1. Motion of no-confidence & - & \Pone & \Qone \\
% 2a. New committee/threshold (\emph{normal state}) & - & \Ptwoa & \Qtwoa \\
% 2b. New committee/threshold (\emph{state of no-confidence}) & - & \Ptwob & \Qtwob \\
% 3. Update to the Constitution & \ding{51} & \Pthree & - \\
% 4. Hard-fork initiation & \ding{51} & \Pfour & \Qfour \\
% 5a. Changes to protocol parameters in the \NetworkGroup & \ding{51} & \Pfivea & - \\
% 5b. Changes to protocol parameters in the \EconomicGroup & \ding{51} & \Pfiveb & - \\
% 5c. Changes to protocol parameters in the \TechnicalGroup & \ding{51} & \Pfivec & - \\
% 5d. Changes to protocol parameters in the \GovernanceGroup & \ding{51} & \Pfived & - \\
% 6. Treasury withdrawal & \ding{51} & \Psix & - \\
% 7. Info & \ding{51} & \(100\) & \(100\) \\
% \end{longtable}
% Each of these thresholds is a governance parameter.  The two thresholds for the \Info
% action are set to 100\% since setting it any lower would result in not being able to poll
% above the threshold.

\subsection{Ratification restrictions}
\label{sec:ratification-restrictions}
\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
import Data.Integer as ℤ
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Nat.Properties hiding (_≟_; _≤?_)
open import Data.Nat.Properties.Ext

open import Ledger.Prelude hiding (_∧_)
open import Ledger.Transaction hiding (Vote)

module Ledger.Ratify (txs : _) (open TransactionStructure txs) where

open import Ledger.GovernanceActions govStructure using (Vote)
open import Ledger.Gov govStructure

infixr 2 _∧_
_∧_ = _×_

instance
  _ = +-0-commutativeMonoid
  _ = +-0-monoid

record StakeDistrs : Type where
  field stakeDistr  : VDeleg ⇀ Coin
\end{code}

\begin{minipage}{.3\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   RatifyEnv : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⊗_⊗_⟧ʳ
  field
\end{code}
\begin{code}
    stakeDistrs   : StakeDistrs
    currentEpoch  : Epoch
    dreps         : Credential ⇀ Epoch
\end{code}
\begin{code}[hide]
    ccHotKeys     : Credential ⇀ Maybe Credential
    treasury      : Coin
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.5\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   RatifyState : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⟧ʳ
  field
\end{code}
\begin{code}
    es              : EnactState
    removed         : ℙ (GovActionID × GovActionState)
    delay           : Bool
\end{code}
\end{AgdaMultiCode}
\end{minipage}

\newcommand\ratifyHelpers{%
\begin{code}
CCData : Type
CCData = Maybe ((Credential ⇀ Epoch) × ℚ)

govRole : VDeleg → GovRole
govRole (credVoter gv _)  = gv
govRole abstainRep        = DRep
govRole noConfidenceRep   = DRep

IsCC IsDRep IsSPO : VDeleg → Type
IsCC    v = govRole v ≡ CC
IsDRep  v = govRole v ≡ DRep
IsSPO   v = govRole v ≡ SPO
\end{code}
}

\begin{code}[hide]
open StakeDistrs

-- TODO: remove these or put them into RatifyState
coinThreshold rankThreshold : ℕ
coinThreshold = 1000000000
rankThreshold = 1000

-- DReps with at least `c` coins
mostStakeDRepDist : Credential ⇀ Coin → Coin → Credential ⇀ Coin
mostStakeDRepDist dist c = dist ↾' (_≥ c)

-- mostStakeDRepDist-homomorphic : ∀ {dist} → Homomorphic₂ _ _ _>_ (_⊆_ on _ˢ) (mostStakeDRepDist dist)
-- mostStakeDRepDist-homomorphic x>y = impl⇒cores⊆ _ _ {!!} --(<-trans x>y)

mostStakeDRepDist-0 : ∀ {dist} → mostStakeDRepDist dist 0 ≡ᵉᵐ dist
mostStakeDRepDist-0 = (proj₂ ∘ Equivalence.from ∈-filter)
                    , λ x → Equivalence.to ∈-filter (z≤n , x)

-- TODO: maybe this can be proven easier with the maximum?
mostStakeDRepDist-∅ : ∀ {dist} → ∃[ N ] mostStakeDRepDist dist N ˢ ≡ᵉ ∅
mostStakeDRepDist-∅ {dist} = suc (∑[ x ← dist ᶠᵐ ] x) , Properties.∅-least
  (⊥-elim ∘ uncurry helper ∘ Equivalence.from ∈-filter)
  where
    open ≤-Reasoning

    helper : ∀ {k v} → v > ∑[ x ← dist ᶠᵐ ] x → (k , v) ∉ dist
    helper {k} {v} v>sum kv∈dist = 1+n≰n $ begin-strict
      v
        ≡˘⟨ indexedSum-singleton' $ finiteness ❴ k , v ❵ ⟩
      ∑[ x ← ❴ k , v ❵ ᶠᵐ ] x
        ≡˘⟨ indexedSumᵐ-cong {x = (dist ∣ ❴ k ❵) ᶠᵐ} {y = ❴ k , v ❵ ᶠᵐ}
          $ res-singleton' {m = dist} kv∈dist ⟩
      ∑[ x ← (dist ∣ ❴ k ❵) ᶠᵐ ] x
        ≤⟨ m≤m+n _ _ ⟩
      ∑[ x ← (dist ∣ ❴ k ❵) ᶠᵐ ] x +ℕ ∑[ x ← (dist ∣ ❴ k ❵ ᶜ) ᶠᵐ ] x
        ≡˘⟨ indexedSumᵐ-partition {m = dist ᶠᵐ} {(dist ∣ ❴ k ❵) ᶠᵐ} {(dist ∣ ❴ k ❵ ᶜ) ᶠᵐ}
          $ res-ex-disj-∪ Properties.Dec-∈-singleton ⟩
      ∑[ x ← dist ᶠᵐ ] x
        <⟨ v>sum ⟩
      v ∎

∃topNDRepDist : ∀ {n dist} → n ≤ lengthˢ (dist ˢ) → n > 0
                → ∃[ c ] n ≤ lengthˢ (mostStakeDRepDist dist c ˢ)
                       × lengthˢ (mostStakeDRepDist dist (suc c) ˢ) < n
∃topNDRepDist {n} {dist} length≥n n>0 =
  let
    c , h , h' =
      negInduction (λ _ → _ ≥? n)
        (subst (n ≤_) (sym $ lengthˢ-≡ᵉ _ _ (mostStakeDRepDist-0 {dist})) length≥n)
        (map₂′ (λ h h'
                  → ≤⇒≯ (subst (n ≤_) (trans (lengthˢ-≡ᵉ _ _ h) lengthˢ-∅) h') n>0)
               (mostStakeDRepDist-∅ {dist}))
  in
   c , h , ≰⇒> h'

topNDRepDist : ℕ → Credential ⇀ Coin → Credential ⇀ Coin
topNDRepDist n dist = case (lengthˢ (dist ˢ) ≥? n) ,′ (n >? 0) of λ where
  (_     , no  _)  → ∅ᵐ
  (no _  , yes _)  → dist
  (yes p , yes p₁) → mostStakeDRepDist dist (proj₁ (∃topNDRepDist {dist = dist} p p₁))

-- restrict the DRep stake distribution
-- commented out for now, since we don't know if that'll actually be implemented
restrictedDists : ℕ → ℕ → StakeDistrs → StakeDistrs
restrictedDists coins rank dists = dists
  -- record dists { drepStakeDistr = restrict drepStakeDistr }
  where open StakeDistrs dists
        -- one always includes the other
        restrict : Credential ⇀ Coin → Credential ⇀ Coin
        restrict dist = topNDRepDist rank dist ∪ˡ mostStakeDRepDist dist coins
\end{code}

\newcommand\ratifyVoteCalculation{%
\begin{AgdaAlign}
\begin{code}
actualPDRepVotes : GovAction → VDeleg ⇀ Vote
actualPDRepVotes NoConfidence  =   ❴ abstainRep , Vote.abstain ❵
                               ∪ˡ  ❴ noConfidenceRep , Vote.yes ❵
actualPDRepVotes _             =   ❴ abstainRep , Vote.abstain ❵
                               ∪ˡ  ❴ noConfidenceRep , Vote.no ❵

actualVotes  : RatifyEnv → PParams → CCData → GovAction
             → GovRole × Credential ⇀ Vote → VDeleg ⇀ Vote
actualVotes Γ pparams cc ga votes  =   mapKeys (credVoter CC) (actualCCVotes cc)
                                   ∪ˡ  actualPDRepVotes ga
                                   ∪ˡ  actualDRepVotes
                                   ∪ˡ  actualSPOVotes ga
  where
  open RatifyEnv Γ
  open PParams pparams

  activeDReps : ℙ Credential
  activeDReps = dom $ filterᵐ (λ x → currentEpoch ≤ (proj₂ x)) dreps

  activeCC : CCData → ℙ Credential
  activeCC (just (cc , _))  = dom $ filterᵐ (Is-just ∘ proj₂) (ccHotKeys ∣ dom cc)
  activeCC nothing          = ∅

  spos : ℙ VDeleg
  spos = filterˢ IsSPO $ dom (stakeDistr stakeDistrs)

  actualCCVote : Credential → Epoch → Vote
  actualCCVote c e = case ¿ currentEpoch ≤ e ¿ᵇ , lookupᵐ? ccHotKeys c of
    λ where  (true , just (just c'))  → maybe id Vote.no $ lookupᵐ? votes (CC , c')
             _                        → Vote.abstain -- expired, no hot key or resigned

  actualCCVotes : CCData → Credential ⇀ Vote
  actualCCVotes nothing          =  ∅
  actualCCVotes (just (cc , q))  =  ifᵈ (ccMinSize ≤ lengthˢ (activeCC $ just (cc , q)))
                                    then mapWithKey actualCCVote cc
                                    else constMap (dom cc) Vote.no

  roleVotes : GovRole → VDeleg ⇀ Vote
  roleVotes r = mapKeys (uncurry credVoter) $ filterᵐ ((r ≡_) ∘ proj₁ ∘ proj₁) votes

  actualSPOVotes : GovAction → VDeleg ⇀ Vote
  actualSPOVotes (TriggerHF _)  = roleVotes GovRole.SPO ∪ˡ constMap spos Vote.no
  actualSPOVotes _              = roleVotes GovRole.SPO ∪ˡ constMap spos Vote.abstain

  actualDRepVotes : VDeleg ⇀ Vote
  actualDRepVotes  =   roleVotes GovRole.DRep
                   ∪ˡ  constMap (mapˢ (credVoter DRep) activeDReps) Vote.no
\end{code}
\end{AgdaAlign}
}

\newcommand\ratifyVoteHelpers{%
\begin{code}
votedHashes : Vote → (VDeleg ⇀ Vote) → GovRole → ℙ VDeleg
votedHashes v votes r = votes ⁻¹ v

votedYesHashes : (VDeleg ⇀ Vote) → GovRole → ℙ VDeleg
votedYesHashes = votedHashes Vote.yes

votedAbstainHashes participatingHashes : (VDeleg ⇀ Vote) → GovRole → ℙ VDeleg
votedAbstainHashes = votedHashes Vote.abstain
participatingHashes votes r = votedYesHashes votes r ∪ votedHashes Vote.no votes r
\end{code}

The code in Figure~\ref{fig:defs:ratify-ii} defines \votedHashes, which returns the set of delegates who voted a certain way on the given governance role.
\begin{code}[hide]
abstract
  -- unused, keep until we know for sure that there'll be no minimum AVS
  -- activeVotingStake : ℙ VDeleg → StakeDistrs → (VDeleg ⇀ Vote) → Coin
  -- activeVotingStake cc dists votes =
  --   ∑[ x  ← getStakeDist DRep cc dists ∣ dom votes ᶜ ᶠᵐ ] x

  -- TODO: explain this notation in the prose and it's purpose:
  -- if there's no stake, accept only if threshold is zero
  _/₀_ : ℕ → ℕ → ℚ
  x /₀ 0 = 0ℚ
  x /₀ y@(suc _) = ℤ.+ x ℚ./ y
\end{code}
\begin{code}
  getStakeDist : GovRole → ℙ VDeleg → StakeDistrs → VDeleg ⇀ Coin
  getStakeDist CC    cc  sd  = constMap (filterˢ IsCC cc) 1
  getStakeDist DRep  _   sd  = filterKeys IsDRep (sd .stakeDistr)
  getStakeDist SPO   _   sd  = filterKeys IsSPO  (sd .stakeDistr)

  acceptedStakeRatio : GovRole → ℙ VDeleg → StakeDistrs → (VDeleg ⇀ Vote) → ℚ
  acceptedStakeRatio r cc dists votes = acceptedStake /₀ totalStake
    where
      acceptedStake totalStake : Coin
      acceptedStake = ∑[ x ← (getStakeDist r cc dists ∣ votedYesHashes votes r) ᶠᵐ ]      x
      totalStake    = ∑[ x ←  getStakeDist r cc dists ∣ votedAbstainHashes votes r ᶜ ᶠᵐ ] x

  acceptedBy : RatifyEnv → EnactState → GovActionState → GovRole → Type
  acceptedBy Γ (record { cc = cc , _; pparams = pparams , _ }) gs role =
    let open GovActionState gs
        votes'  = actualVotes Γ pparams cc action votes
        t       = maybe id 0ℚ $ threshold pparams (proj₂ <$> cc) action role
    in acceptedStakeRatio role (dom votes') (RatifyEnv.stakeDistrs Γ) votes' ℚ.≥ t

  accepted : RatifyEnv → EnactState → GovActionState → Type
  accepted Γ es gs = acceptedBy Γ es gs CC ∧ acceptedBy Γ es gs DRep ∧ acceptedBy Γ es gs SPO

  expired : Epoch → GovActionState → Type
  expired current record { expiresIn = expiresIn } = expiresIn < current
\end{code}
}

\begin{code}[hide]
open EnactState
\end{code}
\newcommand\ratifyVerifyPrev{%
\begin{code}
verifyPrev : (a : GovAction) → NeedsHash a → EnactState → Type
verifyPrev NoConfidence           h es  = h ≡ es .cc .proj₂
verifyPrev (NewCommittee _ _ _)   h es  = h ≡ es .cc .proj₂
verifyPrev (NewConstitution _ _)  h es  = h ≡ es .constitution .proj₂
verifyPrev (TriggerHF _)          h es  = h ≡ es .pv .proj₂
verifyPrev (ChangePParams _)      h es  = h ≡ es .pparams .proj₂
verifyPrev (TreasuryWdrl _)       _ _   = ⊤
verifyPrev Info                   _ _   = ⊤

delayingAction : GovAction → Bool
delayingAction NoConfidence           = true
delayingAction (NewCommittee _ _ _)   = true
delayingAction (NewConstitution _ _)  = true
delayingAction (TriggerHF _)          = true
delayingAction (ChangePParams _)      = false
delayingAction (TreasuryWdrl _)       = false
delayingAction Info                   = false

delayed : (a : GovAction) → NeedsHash a → EnactState → Bool → Type
delayed a h es d = ¬ verifyPrev a h es ⊎ d ≡ true
\end{code}
}
\begin{code}[hide]
abstract
  verifyPrev? : ∀ a h es → Dec (verifyPrev a h es)
  verifyPrev? NoConfidence           h es = dec
  verifyPrev? (NewCommittee x x₁ x₂) h es = dec
  verifyPrev? (NewConstitution x x₁) h es = dec
  verifyPrev? (TriggerHF x)          h es = dec
  verifyPrev? (ChangePParams x)      h es = dec
  verifyPrev? (TreasuryWdrl x)       h es = dec
  verifyPrev? Info                   h es = dec

  delayed? : ∀ a h es d → Dec (delayed a h es d)
  delayed? a h es d = let instance _ = ⁇ verifyPrev? a h es in dec

  acceptedBy? : ∀ Γ es st role → Dec (acceptedBy Γ es st role)
  acceptedBy? Γ record{ cc = cc , _ ; pparams = pparams , _ } st role = _ ℚ.≤? _

  accepted? : ∀ Γ es st → Dec (accepted Γ es st)
  accepted? Γ es st = let instance _ = ⁇¹ acceptedBy? Γ es st in dec

  expired? : ∀ e st → Dec (expired e st)
  expired? e st = ¿ expired e st ¿

private variable
  Γ : RatifyEnv
  es es' : EnactState
  a : GovActionID × GovActionState
  removed : ℙ (GovActionID × GovActionState)
  d : Bool
\end{code}
\hrule
\begin{AgdaMultiCode}
\begin{code}[hide]
data  _⊢_⇀⦇_,RATIFY⦈_ : RatifyEnv → RatifyState → GovActionID × GovActionState → RatifyState → Type where
\end{code}
\begin{code}
  RATIFY-Accept :
\end{code}
\begin{code}[hide]
   let open RatifyEnv Γ; st = a .proj₂; open GovActionState st in
\end{code}
\begin{code}
      ∙  accepted Γ es st  ∙  ¬ delayed action prevAction es d
      ∙  ⟦ a .proj₁ ⊗ treasury ⊗ currentEpoch ⟧ᵉ ⊢ es ⇀⦇ action ,ENACT⦈ es'
         ────────────────────────────────
         Γ ⊢  ⟦ es   ⊗ removed          ⊗ d                      ⟧ʳ ⇀⦇ a ,RATIFY⦈
              ⟦ es'  ⊗ ❴ a ❵ ∪ removed  ⊗ delayingAction action  ⟧ʳ
\end{code}
\begin{code}

  RATIFY-Reject :
\end{code}
\begin{code}[hide]
    let open RatifyEnv Γ; st = a .proj₂ in
\end{code}
\begin{code}
      ∙  ¬ accepted Γ es st  ∙  expired currentEpoch st
         ────────────────────────────────
         Γ ⊢ ⟦ es ⊗ removed ⊗ d ⟧ʳ ⇀⦇ a ,RATIFY⦈ ⟦ es ⊗ ❴ a ❵ ∪ removed ⊗ d ⟧ʳ
\end{code}
\begin{code}

  RATIFY-Continue :
\end{code}
\begin{code}[hide]
    let open RatifyEnv Γ; st = a .proj₂; open GovActionState st in
\end{code}
\begin{code}
         (  ∙ ¬ accepted Γ es st  ∙ ¬ expired currentEpoch st)
      ⊎  (  ∙ accepted Γ es st
            ∙  (  delayed action prevAction es d
               ⊎  (∀ es' → ¬ ⟦ a .proj₁ ⊗ treasury ⊗ currentEpoch ⟧ᵉ ⊢ es ⇀⦇ action ,ENACT⦈ es')))
         ────────────────────────────────
         Γ ⊢ ⟦ es ⊗ removed ⊗ d ⟧ʳ ⇀⦇ a ,RATIFY⦈ ⟦ es ⊗ removed ⊗ d ⟧ʳ
\end{code}
\end{AgdaMultiCode}
\begin{code}[hide]
_⊢_⇀⦇_,RATIFY∗⦈_  : RatifyEnv → RatifyState → List (GovActionID × GovActionState)
                 → RatifyState → Type
_⊢_⇀⦇_,RATIFY∗⦈_ = ReflexiveTransitiveClosure _⊢_⇀⦇_,RATIFY⦈_
\end{code}

The main new ingredients for the rules of this state machine are:
\begin{itemize}
\item \accepted, which is the property that there are sufficient votes
  from the required bodies to pass this action,
\item \delayed, which expresses whether an action is delayed, and
\item \expired, which becomes true a certain number of epochs after
  the action has been proposed.
\end{itemize}

The three RATIFY rules correspond to the cases where an action can be
ratified and enacted (in which case it is), or it is expired and can
be removed, or, otherwise it will be kept around for the future. This
means that all governance actions eventually either get accepted and
enacted via \RATIFYAccept or rejected via \RATIFYReject. It is not
possible to remove actions by voting against them, one has to wait for
the action to expire.
