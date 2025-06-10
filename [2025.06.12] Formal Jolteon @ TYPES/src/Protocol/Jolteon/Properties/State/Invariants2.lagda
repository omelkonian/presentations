\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
  hiding (_⊆_)
open import Hash
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Properties.State.Invariants2 (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon ⋯
open import Protocol.Jolteon.Decidability.Core ⋯
open import Protocol.Jolteon.Properties.Core ⋯
open import Protocol.Jolteon.Properties.State.Messages ⋯
open import Protocol.Jolteon.Properties.State.Invariants ⋯

open L.Mem

private _⊆_ = _⊆ˢ_
\end{code}
\newcommand\historyCompleteType{%
\begin{code}[hide]
module _ {p} ⦃ hp : Honest p ⦄ where
\end{code}
\begin{code}
  history-complete : ∀ {s} → Reachable s →
    (s ＠ p) .db ⊆ s .history
\end{code}
}
\newcommand\historyCompleteProof{%
\begin{code}
  history-complete (_ , refl , (_ ∎)) m∈ rewrite pLookup-replicate p initLocalState = contradict m∈
  history-complete (_ , s-init , _ ⟨ st ∣ s ⟩←— tr) m∈
    using  Rs ← (_ , s-init , tr)
    using  sm ← s .stateMap
    with   IH ← history-complete Rs
    with   IH-inbox ← inbox⊆history {p = p} Rs
    with   st
  ... | WaitUntil _ _ _ = IH m∈
  ... | Deliver {tpm} _ rewrite receiveMsg-db {s = sm} (honestTPMessage tpm) = IH m∈
  ... | DishonestLocalStep _ _ = there $ IH m∈
  ... | LocalStep {p = p′} {ls′ = ls′}  st
    with   p ≟ p′
  ... | no p≢     rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) sm = ∈-++⁺ʳ _ (IH m∈)
  ... | yes refl  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} sm
    with   st
  ... | InitNoTC _ _  = IH m∈
  ... | InitTC _ _    = there $ IH m∈
\end{code}
\hspace{1cm}$\vdots$
\begin{code}
  ... | RegisterProposal m∈inbox _ _ _ _ = go
    where go : _; go with ⟫ m∈
          ... | ⟫ here refl  = IH-inbox m∈inbox
          ... | ⟫ there m∈   = IH m∈
\end{code}
\begin{code}[hide]
  ... | ProposeBlock _ _ = there $ IH m∈
  ... | ProposeBlockNoOp _ _ = IH m∈
  ... | EnoughTimeouts _ _ _ _ = there $ IH m∈
  ... | TimerExpired _ _ = there $ IH m∈
  ... | RegisterTimeout m∈inbox _ _ _ = QED
    where QED : _; QED with ⟫ m∈
          ... | ⟫ here refl  = IH-inbox m∈inbox
          ... | ⟫ there m∈   = IH m∈
  ... | RegisterTC m∈inbox _ _ _ = QED
    where QED : _; QED with ⟫ m∈
          ... | ⟫ here refl  = IH-inbox m∈inbox
          ... | ⟫ there m∈   = IH m∈
  ... | RegisterVote m∈inbox _ _ _ _ _ = go
    where go : _; go with ⟫ m∈
          ... | ⟫ here refl  = IH-inbox m∈inbox
          ... | ⟫ there m∈   = IH m∈
  ... | AdvanceRoundQC _ _ _ = IH m∈
  ... | AdvanceRoundTC _ _ _ = IH m∈
  ... | AdvanceRoundNoOp _ _ _ = IH m∈
  ... | Lock _ _ = IH m∈
  ... | Commit _ _ = IH m∈
  ... | CommitNoOp _ _ = IH m∈
  ... | VoteBlock _ _ _ = there $ IH m∈
  ... | VoteBlockNoOp _ _ = IH m∈
\end{code}
}
