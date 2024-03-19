open import Ledger.Prelude
open import Ledger.Transaction

module Ledger.Ratify.Properties (txs : _) (open TransactionStructure txs) where

open import Ledger.Gov govStructure
open import Ledger.GovernanceActions.Properties govStructure
open import Ledger.Ratify txs

open Computational ⦃...⦄ hiding (computeProof; completeness)

module _ {a b} {A : Set a} {B : Set b} where
  caseMaybe_∣_∣_ : (ma : Maybe A) → (∀ {a} → ma ≡ just a → B) → (ma ≡ nothing → B) → B
  caseMaybe ma ∣ f ∣ g with ma
  ... | just _  = f refl
  ... | nothing = g refl

  caseMaybe-just : ∀ {a} {ma : Maybe A} {f : ∀ {a} → ma ≡ just a → B} {g : ma ≡ nothing → B}
    → (eq : ma ≡ just a)
    → caseMaybe ma ∣ f ∣ g ≡ f eq
  caseMaybe-just refl = refl

  caseMaybe-nothing : ∀ {ma : Maybe A} {f : ∀ {a} → ma ≡ just a → B} {g : ma ≡ nothing → B}
    → (eq : ma ≡ nothing)
    → caseMaybe ma ∣ f ∣ g ≡ g eq
  caseMaybe-nothing refl = refl

pattern RATIFY-Continue₁  x y = RATIFY-Continue (inj₁ (x , y))
pattern RATIFY-Continue₂  x y = RATIFY-Continue (inj₂ (x , y))
pattern RATIFY-Continue₂₁ x y = RATIFY-Continue₂ x (inj₁ y)
pattern RATIFY-Continue₂₂ x y = RATIFY-Continue₂ x (inj₂ y)

postulate instance
  Computational-RATIFY : Computational _⊢_⇀⦇_,RATIFY⦈_

Computational-RATIFY∗ : Computational _⊢_⇀⦇_,RATIFY∗⦈_
Computational-RATIFY∗ = it

postulate
  RATIFY∗-total : ∀ {Γ s sig} → ∃[ s' ] Γ ⊢ s ⇀⦇ sig ,RATIFY∗⦈ s'

RATIFY∗-complete : ∀ {Γ s sig s'} →
  Γ ⊢ s ⇀⦇ sig ,RATIFY∗⦈ s' → RATIFY∗-total {Γ} {s} {sig} .proj₁ ≡ s'
RATIFY∗-complete = computational⇒rightUnique it (RATIFY∗-total .proj₂)
