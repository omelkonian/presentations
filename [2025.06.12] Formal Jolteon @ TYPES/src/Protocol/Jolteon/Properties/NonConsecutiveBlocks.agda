{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Properties.NonConsecutiveBlocks (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon ⋯
open import Protocol.Jolteon.Properties.Core ⋯
open import Protocol.Jolteon.Properties.State ⋯
open import Protocol.Jolteon.Properties.Steps ⋯
open import Protocol.Jolteon.Properties.Votes ⋯

nonConsecutivePointer : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ → let ms = s .history in
  ∙ b .blockQC ≡ qc
  ∙ 1 + qc ∙round < b ∙round
  ∙ p ∈ votes b ms
    ─────────────────────────────────────────────────────────
    ∃[ tc ∈ b ∙tc? ] (b ∙round ≡ 1 + tc ∙round) × (tc ∙∈ ms)
nonConsecutivePointer {s = s} Rs ⦃ hp ⦄ refl qc< p∈
  with stv ← honest∈votes⇒StepVotes Rs hp p∈
  with _ , _ , _ , qc∨tc ← StepVotes⇒ShouldVote Rs stv
  with just {tc} (tc≡ , _) ← Sum.fromInj₂ (λ r≡ → ⊥-elim (Nat.<⇒≢ qc< (sym r≡))) qc∨tc
  = just (tc≡ , tc∈)
  where
  m∈ : Propose _ ∈ s .history
  m∈ = db⊆history Rs $ StepVotes⇒db∋ Rs stv

  tc∈ : tc ∙∈ s .history
  tc∈ = receivedTC (L.Any.map (λ where refl → tc∈-Propose refl) m∈)

nonConsecutiveBlocks : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ → let ms = s .history in
  ∙ b ←— b′
  ∙ 1 + b ∙round < b′ ∙round
  ∙ p ∈ votes b′ ms
    ──────────────────────────────────────────────────────────
    ∃[ tc ∈ b′ ∙tc? ] (b′ ∙round ≡ 1 + tc ∙round) × (tc ∙∈ ms)
nonConsecutiveBlocks Rs (refl , refl) r< p∈ = nonConsecutivePointer Rs refl r< p∈
