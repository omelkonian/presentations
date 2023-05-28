\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{Adding Partiality}
\begin{code}[hide]
open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.InferenceRules
open import Prelude.Apartness
open import Prelude.Monad
open import Prelude.Lists hiding (_↦_)

open import ValueSepExact.Maps

module _ (Part : Type) ⦃ _ : DecEq Part ⦄ where

Map⟨_↦_⟩ : Set → Set → Set
Map⟨ K ↦ _ ⟩ = Map⟨ K ↦ℕ⟩

postulate TODO : ∀ {A : Set ℓ} → A

variable
  A B C D : Part
  v v′ v″ : ℕ
\end{code}
\begin{code}
S = Map⟨ Part ↦ ℕ ⟩

\end{code}
\begin{code}[hide]
record Tx : Type where
  constructor _—→⟨_⟩_
  field
    sender   : Part
    value    : ℕ
    receiver : Part
open Tx public
unquoteDecl DecEq-Tx = DERIVE DecEq [ quote Tx , DecEq-Tx ]

L = List Tx

variable
  s s′ s″ s₁ s₁′ s₁″ s₂ s₂′ s₂″ s₃ s₃′ s₃″ s₂₃ s₂₃′ s₂₃″ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

  ms ms′ ms″ : Maybe S
  mls mls′ mls″ : Maybe (L × S)
\end{code}
\begin{code}
Domain = S → Maybe S

\end{code}
\begin{code}[hide]
record Denotable (A : Type) : Type where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

Domain₀ = S → S

record Denotable₀ (A : Type) : Type where
  field ⟦_⟧₀ : A → Domain₀
open Denotable₀ ⦃...⦄ public
IsValidTx : Tx → S → Type
IsValidTx (A —→⟨ v ⟩ _) s = v ≤ s A

data IsValidTx′ : Tx → S → Type where

  mkValid :

    v ≤ s A
    ──────────────────────────
    IsValidTx′ (A —→⟨ v ⟩ B) s

isValidTx? : Decidable² IsValidTx
isValidTx? = dec²

isValidTx : Tx → S → Bool
isValidTx t s = ⌊ isValidTx? t s ⌋

-- Express the action of tranferring values between keys in a map.
-- NB: a transaction goes through only when:
--   1. both participants are present in the domain
--   2. the sender holds sufficient funds
instance
  -- we denote a transaction as the map transformation that implements the transfer
  ⟦Tx⟧₀ : Denotable₀ Tx
  ⟦Tx⟧₀ .⟦_⟧₀ (A —→⟨ v ⟩ B) s = s [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]

  ⟦L⟧₀ : Denotable₀ L
  ⟦L⟧₀ .⟦_⟧₀ []      = id
  ⟦L⟧₀ .⟦_⟧₀ (t ∷ l) = ⟦ l ⟧₀ ∘ ⟦ t ⟧₀
\end{code}
\begin{code}
  ⟦T⟧ : Denotable Tx
  ⟦T⟧ .⟦_⟧ t s = M.when (isValidTx t s) (⟦ t ⟧₀ s)

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = just s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ t ⟧ >=> ⟦ l ⟧
\end{code}
\begin{code}[hide]
comp₀ : ∀ x → ⟦ l ++ l′ ⟧₀ x ≡ (⟦ l′ ⟧₀ ∘ ⟦ l ⟧₀) x
comp₀ {l = []}    _ = refl
comp₀ {l = t ∷ l} x = comp₀ {l} (⟦ t ⟧₀ x)
\end{code}
\begin{code}

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l ⟧ >=> ⟦ l′ ⟧) x
\end{code}
\begin{code}[hide]
comp {l = []}    x = refl
comp {l = t ∷ l} x with ⟦ t ⟧ x
... | nothing = refl
... | just s  = comp {l} s

-- Executing transactions never introduces new keys in the resulting map out-of-thin-air.
-- ** Operational semantics
-- We model configurations of the transition system as pairs of a ledger and its current state.
\end{code}
\end{frame}
\begin{frame}{Adding Partiality: Operational Semantics}
\begin{code}
infix 0 _—→_
data _—→_ : L × S → S → Type where

  base :
    ────────────
    ε , s —→ s

  step :
    ∙ IsValidTx t s
    ∙ l , ⟦ t ⟧₀ s —→ s′
      ──────────────────
      t ∷ l , s —→ s′
\end{code}
\begin{code}[hide]
oper-comp :
  ∙ l       , s  —→ s′
  ∙ l′      , s′ —→ s″
    ──────────────────
    l ++ l′ , s  —→ s″
oper-comp {l = []}    base                   s′→s″ = s′→s″
oper-comp {l = _ ∷ _} (step v≤ s→s′) s′→s″ = step v≤ (oper-comp s→s′ s′→s″)

oper-comp˘ :
    l ++ l′ , s  —→ s″
    ────────────────────────
    ∃ λ s′
      → (l       , s  —→ s′)
      × (l′      , s′ —→ s″)
oper-comp˘ {l = []} {l′ = l′} p = -, base , p
oper-comp˘ {l = _ ∷ l} {l′ = l′} (step v≤ s→s′) =
  let _ , s→ , →s′ = oper-comp˘ {l}{l′} s→s′
  in -, step v≤ s→ , →s′

-- ** Relating denotational and operational semantics.
denot⇒oper :
  ⟦ l ⟧ s ≡ just s′
  ─────────────────
  l , s —→ s′
denot⇒oper {l = []} refl = base
denot⇒oper {l = A —→⟨ v ⟩ B ∷ l}{s} l≡
  with yes v≤ ← v ≤? s A
  = step v≤ (denot⇒oper l≡)

oper⇒denot :
  l , s —→ s′
  ─────────────────
  ⟦ l ⟧ s ≡ just s′
oper⇒denot {l = .[]} base = refl
oper⇒denot {l = A —→⟨ v ⟩ B ∷ _}{s} (step v≤ p)
  rewrite dec-yes (v ≤? s A) v≤ .proj₂
  = oper⇒denot p
\end{code}

\begin{code}
denot⇔oper :
  ⟦ l ⟧ s ≡ just s′
  ═════════════════
  l , s —→ s′
\end{code}
\begin{code}[hide]
denot⇔oper = denot⇒oper , oper⇒denot

oper⇒denot₀ :
  l , s —→ s′
  ─────────────
  s′ ≡ ⟦ l ⟧₀ s
oper⇒denot₀ {l = []} base = refl
oper⇒denot₀ {l = _ ∷ _} (step _ l→) = oper⇒denot₀ l→
\end{code}
\end{frame}
\begin{frame}{Adding Partiality: Lifting Predicates for Hoare Logic}
\begin{code}[hide]
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

emp : Assertion
emp m = ∀ k → m k ≡ 0

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ◇ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : Part → ℕ → Assertion
p ↦ n = _[ p ↦ n ]∅

infixr 10 _∗_
infix  11 _↦_
infixl 4 _↑∘_
\end{code}
\begin{code}
weak↑ strong↑ : Pred₀ S → Pred₀ (Maybe S)
weak↑    = M.All.All
strong↑  = M.Any.Any

_↑∘_ : Pred₀ S → (S → Maybe S) → Pred₀ S
P ↑∘ f = strong↑ P ∘ f
\end{code}
\begin{code}[hide]
lift↑ = strong↑
pattern ret↑ x = M.Any.just x
\end{code}

\begin{code}
⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ↑∘ ⟦ l ⟧
\end{code}
\end{frame}
\begin{frame}{Adding Partiality: Frame Rule}
\begin{code}
◇-⟦⟧ : ∀ s₁′ →
  ∙ ⟦ l ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────
    (⟨ s₁′ ◇ s₂ ⟩≡_ ↑∘ ⟦ l ⟧) s
\end{code}
\begin{code}[hide]
◇-⟦⟧ = TODO
\end{code}

\begin{code}
[FRAME] : ∀ R →
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
\end{code}
\begin{code}[hide]
[FRAME] {P}{l}{Q} R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂)
  with ⟦ l ⟧ s₁ in s₁≡ | PlQ Ps₁
... | .just s₁′ | ret↑ Qs₁′
  with ⟦ l ⟧ s in s≡ | ◇-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
... | .just s′ | ret↑ ≡s′
  = ret↑ (s₁′ , s₂ , ≡s′ , Qs₁′ , Rs₂)
\end{code}
\end{frame}
\begin{frame}{Adding Partiality: Parallel Rule}
\begin{code}
◇-interleave :
  ∙ (l₁ ∥ l₂ ≡ l)
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
  ∙ ⟦ l₁ ⟧ s₁ ≡ just s₁′
  ∙ ⟦ l₂ ⟧ s₂ ≡ just s₂′
    ───────────────────────────
    ∃ λ s′ → (⟦ l ⟧ s ≡ just s′)
           × (⟨ s₁′ ◇ s₂′ ⟩≡ s′)
\end{code}
\begin{code}[hide]
◇-interleave = TODO
\end{code}

\begin{code}
[PAR] :
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  ∙ ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
    ─────────────────────────
    ⟨ P₁ ∗ P₂ ⟩ l ⟨ Q₁ ∗ Q₂ ⟩
\end{code}
\begin{code}[hide]
[PAR] {l₁} {l₂} {l} ≡l Pl₁Q Pl₂Q {s} (s₁ , s₂ , ≡s , Ps₁ , Ps₂)
  with ⟦ l₁ ⟧ s₁ in ls₁ | Pl₁Q Ps₁
... | just s₁′ | M.Any.just Qs₁′
  with ⟦ l₂ ⟧ s₂ in ls₂ | Pl₂Q Ps₂
... | just s₂′ | M.Any.just Qs₂′
  with s′ , ls , ≡s′ ← ◇-interleave ≡l ≡s ls₁ ls₂
  rewrite ls
  = M.Any.just (s₁′ , s₂′ , ≡s′ , Qs₁′ , Qs₂′)
\end{code}
\end{frame}
\end{document}
