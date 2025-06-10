{-# OPTIONS --safe #-}
{-# OPTIONS --with-K #-}
open import Prelude
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Global.Trace.Factor (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon.Global.State ⋯

open import Protocol.Jolteon.Global.Trace.Core ⋯
open import Protocol.Jolteon.Global.Trace.Extension ⋯

open TraceExtension

factorRs : ∀ (Rs : Reachable s)
  (trE₁ trE₂ : TraceExtension Rs) →
  ─────────────────────────────────────
  let s₁ = trE₁ .intState
      s₂ = trE₂ .intState
  in (s₁ ↞— s₂) ⊎ (s₂ ↞— s₁)
factorRs Rs
  ⟨ s₁ , (_ , _ , tr₁) , ext₁ , refl ⟩
  ⟨ s₂ , (_ , _ , tr₂) , ext₂ , eq₂ ⟩
  with refl ← cong proj₁ eq₂
  = factor tr₁ ext₁ tr₂ ext₂ (Reachable-inj eq₂)

open import Data.Product.Properties.WithK using (,-injectiveʳ)
open TraceExtension⁺

factorRs⁺ : ∀ (Rs : Reachable s) → let open TraceExtension⁺ in
  (tr tr′ : TraceExtension⁺ Rs) →
  ────────────────────────────
    (step tr ≡ step tr′)
  ⊎ (tr′ .x ↞— tr  .y)
  ⊎ (tr  .x ↞— tr′ .y)
factorRs⁺ Rs
  trE@(⟨ (_ , init , tr)  , (st  ⊣ᴸ refl) , st∗  , refl ⟩)
  trE′@(⟨ (_ , _   , tr′) , (st′ ⊣ᴸ refl) , st∗′ , eq₃ ⟩)
  with refl ← cong proj₁ eq₃
  with refl ← cong proj₁ $ ,-injectiveʳ eq₃
  with eq   ← ,-injectiveʳ  $ ,-injectiveʳ eq₃
  with factor⁺ tr (y¹←x trE) st∗ tr′ (y¹←x trE′) st∗′
               (Reachable-inj $ cong (_ ,_) $ cong (init ,_) eq)
... | inj₁ st≡      = inj₁ $ step≡-TE⁺ Rs trE trE′ st≡
... | inj₂ (inj₁ P) = inj₂ $ inj₂ P
... | inj₂ (inj₂ P) = inj₂ $ inj₁ P
