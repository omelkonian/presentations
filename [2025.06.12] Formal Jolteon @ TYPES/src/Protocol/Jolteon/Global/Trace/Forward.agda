{-# OPTIONS --safe #-}
open import Prelude

open import Protocol.Jolteon.Base
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Global.Trace.Forward (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon.Block ⋯
open import Protocol.Jolteon.Message ⋯
open import Protocol.Jolteon.Local.State ⋯
open import Protocol.Jolteon.Local.Step ⋯
open import Protocol.Jolteon.Global.State ⋯
open import Protocol.Jolteon.Global.Step ⋯

open import Protocol.Jolteon.Global.Trace.Core ⋯
open import Protocol.Jolteon.Global.Trace.Extension ⋯

-- ** forward traces

allLocalSteps˘ : (s —↠ s′) → List Step
-- allLocalSteps˘ = L.reverse ∘ allLocalSteps ∘ viewLeft
allLocalSteps˘ = λ where
  (_ ∎) → []
  (_ —→⟨ LocalStep st ⟩ tr) → (_ ⊢ st) ∷ allLocalSteps˘ tr
  (_ —→⟨ _ ⟩ tr) → allLocalSteps˘ tr

NotLocal : (s′ ¹←— s) → Type
NotLocal = λ where
  (LocalStep _) → ⊥
  _ → ⊤

allLocalSteps≡-¬Local :
  ∀ {st : s′ ¹←— s} {tr : s″ ↞— s′} → ⦃ _ : NotLocal st ⦄ →
  allLocalSteps (_ `—→⟨ st ⟩ tr) ≡ allLocalSteps tr
allLocalSteps≡-¬Local {st = DishonestLocalStep _ _} {tr = _ ∎} = refl
allLocalSteps≡-¬Local {st = Deliver _} {tr = _ ∎} = refl
allLocalSteps≡-¬Local {st = WaitUntil _ _ _} {tr = _ ∎} = refl
allLocalSteps≡-¬Local {st = st} {tr = _ ⟨ WaitUntil _ _ _ ⟩←— tr} =
  allLocalSteps≡-¬Local {st = st} {tr = tr}
allLocalSteps≡-¬Local {st = st} {tr = _ ⟨ Deliver _ ⟩←— tr} =
  allLocalSteps≡-¬Local {st = st} {tr = tr}
allLocalSteps≡-¬Local {st = st} {tr = _ ⟨ DishonestLocalStep _ _ ⟩←— tr} =
  allLocalSteps≡-¬Local {st = st} {tr = tr}
allLocalSteps≡-¬Local {st = st} {tr = _ ⟨ LocalStep st′ ⟩←— tr} =
  let open ≡-Reasoning in
  ≡-Reasoning.begin
    allLocalSteps (_ `—→⟨ st ⟩ (_ ⟨ LocalStep st′ ⟩←— tr))
  ≡⟨⟩
    allLocalSteps (_ ⟨ LocalStep st′ ⟩←— _ `—→⟨ st ⟩ tr)
  ≡⟨⟩
    (_ ⊢ st′) ∷ allLocalSteps (_ `—→⟨ st ⟩ tr)
    ≡⟨ cong (_ ∷_) $ allLocalSteps≡-¬Local {st = st} {tr = tr} ⟩
    (_ ⊢ st′) ∷ allLocalSteps tr
  ≡⟨⟩
    allLocalSteps (_ ⟨ LocalStep st′ ⟩←— tr)
  ≡-Reasoning.∎

allLocalSteps≡ : ∀ ⦃ _ : Honest p ⦄ → let t = s .currentTime in
  ∀ {st : p ⦂ t ⊢ s ＠ p — menv —→ ls′} {tr : s″ ↞— broadcast t menv (s ＠ p ≔ ls′)} →
  allLocalSteps (_ `—→⟨ LocalStep st ⟩ tr) ≡ allLocalSteps tr L.∷ʳ (_ ⊢ st)
allLocalSteps≡ {st = st} {tr = _ ∎} = refl
allLocalSteps≡ {st = st} {tr = _ ⟨ LocalStep st′ ⟩←— tr} =
  let open ≡-Reasoning in
  ≡-Reasoning.begin
    allLocalSteps (_ `—→⟨ LocalStep st ⟩ (_ ⟨ LocalStep st′ ⟩←— tr))
  ≡⟨⟩
    allLocalSteps (_ ⟨ LocalStep st′ ⟩←— _ `—→⟨ LocalStep st ⟩ tr)
  ≡⟨⟩
    (_ ⊢ st′) ∷ allLocalSteps (_ `—→⟨ LocalStep st ⟩ tr)
  ≡⟨ cong (_ ∷_) $ allLocalSteps≡ {tr = tr} ⟩
    (_ ⊢ st′) ∷ allLocalSteps tr L.∷ʳ (_ ⊢ st)
  ≡⟨⟩
    allLocalSteps (_ ⟨ LocalStep st′ ⟩←— tr) L.∷ʳ (_ ⊢ st)
  ≡-Reasoning.∎
allLocalSteps≡ {st = st} {tr = _ ⟨ WaitUntil _ _ _ ⟩←— tr} = allLocalSteps≡ {st = st} {tr = tr}
allLocalSteps≡ {st = st} {tr = _ ⟨ Deliver _ ⟩←— tr} = allLocalSteps≡ {st = st} {tr = tr}
allLocalSteps≡ {st = st} {tr = _ ⟨ DishonestLocalStep _ _ ⟩←— tr} = allLocalSteps≡ {st = st} {tr = tr}

allLocalSteps˘≡ : ∀ {tr : s —↠ s′} → allLocalSteps˘ tr ≡ L.reverse (allLocalSteps (viewLeft tr))
allLocalSteps˘≡ {tr = _ ∎} = refl
allLocalSteps˘≡ {tr = _ —→⟨ st@(WaitUntil _ _ _) ⟩ tr} =
  let open ≡-Reasoning in
  ≡-Reasoning.begin
    allLocalSteps˘ (_ —→⟨ st ⟩ tr)
  ≡⟨⟩
    allLocalSteps˘ tr
  ≡⟨ allLocalSteps˘≡ {tr = tr} ⟩
    L.reverse (allLocalSteps $ viewLeft tr)
  ≡˘⟨ cong L.reverse $ allLocalSteps≡-¬Local {tr = viewLeft tr} ⟩
    L.reverse (allLocalSteps (_ `—→⟨ st ⟩ viewLeft tr))
  ≡-Reasoning.∎
allLocalSteps˘≡ {tr = _ —→⟨ st@(DishonestLocalStep _ _) ⟩ tr} =
  let open ≡-Reasoning in
  ≡-Reasoning.begin
    allLocalSteps˘ (_ —→⟨ st ⟩ tr)
  ≡⟨⟩
    allLocalSteps˘ tr
  ≡⟨ allLocalSteps˘≡ {tr = tr} ⟩
    L.reverse (allLocalSteps $ viewLeft tr)
  ≡˘⟨ cong L.reverse $ allLocalSteps≡-¬Local {tr = viewLeft tr} ⟩
    L.reverse (allLocalSteps (_ `—→⟨ st ⟩ viewLeft tr))
  ≡-Reasoning.∎
allLocalSteps˘≡ {tr = _ —→⟨ st@(Deliver _) ⟩ tr} =
  let open ≡-Reasoning in
  ≡-Reasoning.begin
    allLocalSteps˘ (_ —→⟨ st ⟩ tr)
  ≡⟨⟩
    allLocalSteps˘ tr
  ≡⟨ allLocalSteps˘≡ {tr = tr} ⟩
    L.reverse (allLocalSteps $ viewLeft tr)
  ≡˘⟨ cong L.reverse $ allLocalSteps≡-¬Local {tr = viewLeft tr} ⟩
    L.reverse (allLocalSteps (_ `—→⟨ st ⟩ viewLeft tr))
  ≡-Reasoning.∎
allLocalSteps˘≡ {tr = _ —→⟨ LocalStep st ⟩ tr} =
  let open ≡-Reasoning in
  ≡-Reasoning.begin
    allLocalSteps˘ (_ —→⟨ LocalStep st ⟩ tr)
  ≡⟨⟩
    _ ∷ allLocalSteps˘ tr
  ≡⟨ cong (_ ∷_) $ allLocalSteps˘≡ {tr = tr} ⟩
    _ ∷ L.reverse (allLocalSteps $ viewLeft tr)
  ≡˘⟨ reverse-∷ʳ _ (allLocalSteps $ viewLeft tr) ⟩
    L.reverse (allLocalSteps (viewLeft tr) L.∷ʳ _)
  ≡˘⟨ cong L.reverse $ allLocalSteps≡ {st = st} {tr = viewLeft tr} ⟩
    L.reverse (allLocalSteps (_ `—→⟨ LocalStep st ⟩ viewLeft tr))
  ≡-Reasoning.∎

_∋⋯˘_ : (s —↠ s′) → LocalStepProperty → Type
tr ∋⋯˘ P = Any P (allLocalSteps˘ tr)

tr˘ : ∀ {P} (tr : s′ ↞— s) → viewRight tr ∋⋯˘ P → tr ∋⋯′ P
tr˘ tr tr∋
  rewrite allLocalSteps˘≡ {tr = viewRight tr}
        | viewLeft∘viewRight {tr = tr}
        = L.Any.reverse⁻ tr∋
