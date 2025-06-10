\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Properties.Safety.Consistency (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon ⋯
open import Protocol.Jolteon.Properties.Core ⋯
open import Protocol.Jolteon.Properties.Steps ⋯

open import Protocol.Jolteon.Properties.Safety.Core ⋯
open import Protocol.Jolteon.Properties.Safety.Lemma1 ⋯
open import Protocol.Jolteon.Properties.Safety.Lemma3 ⋯

-- Theorem 2
safetyG : ∀ {s} → Reachable s →
  -- For every two globally direct-committed blocks B, B′...
  ∙ GloballyDirectCommitted s b
  ∙ GloballyDirectCommitted s b′
    ────────────────────────────
  -- ...either B ←—∗ B′ or B′ ←—∗ B.
    (b ←—∗ b′) ⊎ (b′ ←—∗ b)
safetyG {b = b}{b′}{s} Rs dcb dcb′
  with ¿ b ∙round ≤ b′ ∙round ¿
  -- As a corollary of Lemma3...
... | yes r≤ = inj₁ $ safetyLemma Rs cb′ r≤ dcb
  -- ...and the fact that every globally direct-committed block is certified.
  where cb′ = GDB⇒GCB Rs dcb′
... | no  r≰ = inj₂ $ safetyLemma Rs cb (Nat.≰⇒≥ r≰) dcb′
  where cb  = GDB⇒GCB Rs  dcb

-- Theorem 4
consistency′ : ∀ {s} → (Rs : Reachable s) →
  -- For every two committed blocks B, B′...
  ∙ Rs ∋⋯ StepCommits b
  ∙ Rs ∋⋯ StepCommits b′
    ───────────────────────
  -- ...either B ←—∗ B′ or B′ ←—∗ B.
    (b ←—∗ b′) ⊎ (b′ ←—∗ b)
consistency′ {b = b}{b′}{s} Rs cb cb′ =
  safetyG Rs (Commit⇒GlobalDirectCommit Rs cb) (Commit⇒GlobalDirectCommit Rs cb′)

-- A more immediate formulation of Theorem 4.
consistency : ∀ {s} → (Rs : Reachable s) →
  -- For every two committed blocks B, B′...
  ∙ (∃ λ p → ∃ λ (hp : Honest p) → b  ∈ (s ＠ʰ hp) .finalChain)
  ∙ (∃ λ p → ∃ λ (hp : Honest p) → b′ ∈ (s ＠ʰ hp) .finalChain)
    ──────────────────────────────────
  -- ...either B ←—∗ B′ or B′ ←—∗ B.
    (b ←—∗ b′) ⊎ (b′ ←—∗ b)
consistency Rs cb cb′ =
  let b̂  , cb̂  , b←b̂   = getCommitPoint Rs (ch∈⇒StepCommits∈ Rs cb)
      b̂′ , cb̂′ , b′←b̂′ = getCommitPoint Rs (ch∈⇒StepCommits∈ Rs cb′)
  in
    case consistency′ Rs cb̂ cb̂′ of λ where
      (inj₁ b̂←b̂′) → ←∗-factor (←∗-trans b←b̂ b̂←b̂′) b′←b̂′
      (inj₂ b̂′←b̂) → ←∗-factor b←b̂ (←∗-trans b′←b̂′ b̂′←b̂)
\end{code}
\newcommand\safety{%
\begin{code}[hide]
module _ ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ where
\end{code}
\begin{code}
  safety : ∀ {s} → Reachable s →
    ∙ b   ∈ (s ＠ p)   .finalChain
    ∙ b′  ∈ (s ＠ p′)  .finalChain
      ────────────────────────────
      (b ←—∗ b′) ⊎ (b′ ←—∗ b)
\end{code}
\begin{code}[hide]
  safety Rs b∈ b∈′ = consistency Rs (-, it , b∈) (-, it , b∈′)
\end{code}
}
