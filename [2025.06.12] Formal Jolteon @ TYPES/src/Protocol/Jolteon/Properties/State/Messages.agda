{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Properties.State.Messages (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon ⋯
open import Protocol.Jolteon.Decidability.Core ⋯
open import Protocol.Jolteon.Properties.Core ⋯

open L.Mem

-- ** receiveMsg

receiveMsg-ls≡ : ∀ ⦃ _ : Honest p ⦄ {s} mhm →
  let s' = receiveMsg s mhm in
  (s' ＠ᵐ p) ≡ record (s ＠ᵐ p) {inbox = (s' ＠ᵐ p) .inbox}
receiveMsg-ls≡ nothing = refl
receiveMsg-ls≡ {p} ⦃ hp ⦄ {s} (just ((p′ ,· hp′) , m))
  with p ≟ p′
... | yes refl
  rewrite pLookup∘updateAt p {receiveMessage m} s
  = refl
... | no p≢
  rewrite pLookup∘updateAt′ p p′ ⦃ toRelevant hp′ ⦄ {receiveMessage m} (p≢ ∘ ↑-injective) s
  = refl

module _ {p} ⦃ _ : Honest p ⦄ {s} mhm (let ls≡ = receiveMsg-ls≡ {p}{s} mhm) where
  receiveMsg-db     = cong db ls≡
  receiveMsg-tcLast = cong tc-last ls≡
  receiveMsg-rCur   = cong r-cur ls≡
  receiveMsg-qcHigh = cong qc-high ls≡
  receiveMsg-phase  = cong phase ls≡
  receiveMsg-roundA = cong roundAdvanced? ls≡
  receiveMsg-final  = cong finalChain ls≡

receiveMsg-m⊆ : ∀ {sm} ⦃ _ : Honest p ⦄ mhm →
  (sm ＠ᵐ p) .inbox ⊆ˢ (receiveMsg sm mhm ＠ᵐ p) .inbox
receiveMsg-m⊆ nothing m∈ = m∈
receiveMsg-m⊆ {p = p} {sm = sm} (just ((p′ ,· hp′) , m′)) {m} m∈
  with p ≟ p′
... | yes refl
  = subst (_ ∈_)
          (sym $ cong inbox $ pLookup∘updateAt p {receiveMessage m′} sm)
          (L.Mem.∈-++⁺ˡ m∈)
... | no p≢
  rewrite let instance _ = toRelevant hp′ in
          pLookup∘updateAt′ p p′ {receiveMessage m′} (p≢ ∘ ↑-injective) sm
  = m∈

registerMessage-m⊆ : ⦃ _ : Honest p ⦄ (m∈ : m ∈ (s ＠ p) .inbox) →
  ∀ {m′} → m′ ≢ m →
    m′ ∈ (s ＠ p) .inbox
    ────────────────────────────────────────────────────────
    m′ ∈ ((s ＠ p ≔ registerMessage (s ＠ p) m∈) ＠ p) .inbox
registerMessage-m⊆ {p = p} {m = m} {s = s} m∈ {m′} m≢ m∈′
  = subst (_ ∈_)
          (sym $ cong inbox $ pLookup∘updateAt p {const _} (s .stateMap))
          (∈-removeAt⁺ m∈ m≢ m∈′)

-- ** broadcasts

expandBroadcasts-message :
  (t′ , p , m) ∈ expandBroadcasts t env
  ─────────────────────────────────────
  m ≡ env ∙message
expandBroadcasts-message {t = t}{[ _m ⟩} tpm∈
  with _ , _ , refl ← ∈-map⁻ (λ p → (t , p , _m)) tpm∈
  = refl
expandBroadcasts-message {env = [ _ ∣ _m ⟩} (here refl) = refl

broadcast-m⊆ : ⦃ _ : Honest p ⦄ →
  (s ＠ p) .inbox ⊆ˢ (broadcast t menv s ＠ p) .inbox
broadcast-m⊆ {p = p} {s = s} {m} m∈
  = m∈

-- ** enterRound

enterRound-m⊆ : ⦃ _ : Honest p ⦄ →
  (s ＠ p) .inbox ⊆ˢ ((s ＠ p ≔ enterRound t (s ＠ p)) ＠ p) .inbox
enterRound-m⊆ {p = p} {s = s} {t = t} {m} m∈
  = subst (_ ∈_)
          (sym $ cong inbox $ pLookup∘updateAt p {const _} (s .stateMap))
          m∈
