{-# OPTIONS --safe #-}
open import Prelude
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Properties.NoForging (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon ⋯
open import Protocol.Jolteon.Global.NoForging ⋯

Propose-∈ᴹ⇒∈ :
  Any (sb -∈ᴹ-_) ms
  ─────────────────
  Propose sb ∈ ms
Propose-∈ᴹ⇒∈ = λ where
  (here ∈-Propose) → here refl
  (here (∈-Propose-TC sb∈TC)) →
    let _ , sb∈TC = M.Any.satisfied sb∈TC
    in ⊥-elim $ sb∉-TC sb∈TC
  (here (∈-TCFormed sb∈TC)) → ⊥-elim $ sb∉-TC sb∈TC
  (here (∈-Timeout-TC sb∈TC)) →
    let _ , sb∈TC = M.Any.satisfied sb∈TC
    in ⊥-elim $ sb∉-TC sb∈TC
  (there m∈) → there $ Propose-∈ᴹ⇒∈ m∈
 where
  sb∉-TE : ¬ (sb -∈-TE- te)
  sb∉-TE ()

  sb∉-TC : ¬ (sb -∈-TC- tc)
  sb∉-TC (∈-TC sb∈TE) = L.Any.⊥↔Any⊥ .Inverse.from $ L.Any.map sb∉-TE sb∈TE
