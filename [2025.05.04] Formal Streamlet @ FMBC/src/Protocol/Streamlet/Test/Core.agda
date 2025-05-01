module Protocol.Streamlet.Test.Core where

open import Prelude
open import Hash
open import DummyHashing
open import Protocol.Streamlet.Assumptions

pattern 𝕃 = fzero
pattern 𝔸 = fsuc fzero
pattern 𝔹 = fsuc (fsuc fzero)

⋯ : Assumptions
⋯ = record {go; honest-majority = auto; Honest-irr = λ _ _ → refl} where module go where

  hashes = DummyHashing
  open HashAssumptions hashes

  signatures = DummySigning (λ _ _ _ → true)
  open SignatureAssumptions signatures

  nodes       = 3
  nodes⁺      = Nat.s≤s Nat.z≤n
  epochLeader = const 𝕃
  Honest      = const ⊤
  Dec-Honest  = ⁇ dec

  Transaction = ⊤
  DecEq-Tx    = DecEq    Transaction ∋ it
  Hashable-Tx = Hashable Transaction ∋ it

  keys : Fin nodes → KeyPair
  keys = λ where
    𝕃 → mk-keyPair (fromℕ 0) (fromℕ 0)
    𝔸 → mk-keyPair (fromℕ 1) (fromℕ 1)
    𝔹 → mk-keyPair (fromℕ 2) (fromℕ 2)

open Assumptions ⋯ public
open import Protocol.Streamlet ⋯ public
open import Protocol.Streamlet.Decidability ⋯ public

b₁ b₂ b₃ b₅ b₆ b₇ : Block
b₁ = ⟨ genesisChain     ♯ , 1 , [] ⟩
b₂ = ⟨ genesisChain     ♯ , 2 , [] ⟩
b₃ = ⟨ [ b₁ ]           ♯ , 3 , [] ⟩
b₅ = ⟨ [ b₂ ]           ♯ , 5 , [] ⟩
b₆ = ⟨ [ b₅ ⨾ b₂ ]      ♯ , 6 , [] ⟩
b₇ = ⟨ [ b₆ ⨾ b₅ ⨾ b₂ ] ♯ , 7 , [] ⟩

_ = (b₁ ♯) ≡ 1
  ∋ refl
_ = (b₂ ♯) ≡ 2
  ∋ refl
_ = (b₃ ♯) ≡ 4
  ∋ refl
_ = (b₅ ♯) ≡ 7
  ∋ refl
_ = (b₆ ♯) ≡ 15
  ∋ refl
_ = (b₇ ♯) ≡ 31
  ∋ refl

p₁ v₁ p₂ v₂ p₃ v₃ p₅ v₅ p₆ v₆ p₇ v₇ : Message
p₁ = Propose (sign 𝕃 b₁)
v₁ = Vote    (sign 𝔹 b₁)
p₂ = Propose (sign 𝕃 b₂)
v₂ = Vote    (sign 𝔸 b₂)
p₃ = Propose (sign 𝕃 b₃)
v₃ = Vote    (sign 𝔹 b₃)
p₅ = Propose (sign 𝕃 b₅)
v₅ = Vote    (sign 𝔸 b₅)
p₆ = Propose (sign 𝕃 b₆)
v₆ = Vote    (sign 𝔸 b₆)
p₇ = Propose (sign 𝕃 b₇)
v₇ = Vote    (sign 𝔸 b₇)
