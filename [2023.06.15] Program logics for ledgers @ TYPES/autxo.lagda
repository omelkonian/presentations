\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{Abstract UTxO: Setup}
\begin{code}[hide]
open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.FromList; open import Prelude.ToList
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Apartness
open import Prelude.Monad
open import Prelude.Membership
open import Prelude.Setoid
open import Prelude.Lists using (_∥_≡_)

open import Prelude.Bags hiding (_⊣_)
instance
  Sℕ  = Semigroup-ℕ-+; Sℕ⁺ = SemigroupLaws-ℕ-+
  Mℕ  = Monoid-ℕ-+;    Mℕ⁺ = MonoidLaws-ℕ-+

open import Common public
TxOutputRef = TxOutput
open CommonInfo TxOutputRef public

postulate ⋯ : ∀ {A : Set ℓ} → A
\end{code}
\begin{code}
S = Bag⟨ TxOutput ⟩
\end{code}
\begin{code}[hide]
stxoTx utxoTx : Tx → S
stxoTx = fromList ∘ outputRefs
utxoTx = fromList ∘ outputs

resolved : ∀ tx → Resolved tx
resolved _ {r} _ = r
\end{code}
\begin{AgdaMultiCode}
\begin{code}
record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    validOutputRefs :
      stxoTx tx ⊆ˢ utxos

    preservesValues :
      tx .forge + ∑ (tx .inputs) (value ∘ outputRef) ≡ ∑ (tx .outputs) value
\end{code}
\begin{code}[hide]
  txInfo = mkTxInfo tx (resolved tx)
  field
\end{code}
\begin{code}

    allInputsValidate :
      ∀[ i ∈ tx .inputs ] T (i .validator txInfo (i .redeemer))

    validateValidHashes :
      ∀[ i ∈ tx .inputs ] (i .outputRef .address ≡ i .validator ♯)
\end{code}
\end{AgdaMultiCode}
\end{frame}
\begin{frame}[fragile]{Abstract UTxO: Denotational Semantics}
\begin{code}[hide]
open IsValidTx public

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? _ _ with dec
... | no ¬p = no (¬p ∘ validOutputRefs)
... | yes vor with dec
... | no ¬p = no (¬p ∘ preservesValues)
... | yes pv with dec
... | no ¬p = no (¬p ∘ allInputsValidate)
... | yes aiv with dec
... | no ¬p = no (¬p ∘ validateValidHashes)
... | yes vvh = yes record
  { validOutputRefs = vor
  ; preservesValues = pv
  ; allInputsValidate = aiv
  ; validateValidHashes = vvh }

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋

variable
  s s′ s″ s₁ s₁′ s₁″ s₂ s₂′ s₂″ s₃ s₃′ s₃″ s₂₃ s₂₃′ s₂₃″ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

  ms ms′ ms″ : Maybe S
  mls mls′ mls″ : Maybe (L × S)

-- ** Denotational semantics

Domain = S → Maybe S

record Denotable (A : Type) : Type where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

Domain₀ = S → S

record Denotable₀ (A : Type) : Type where
  field ⟦_⟧₀ : A → Domain₀
open Denotable₀ ⦃...⦄ public

instance
  ⟦T⟧₀ : Denotable₀ Tx
  ⟦T⟧₀ .⟦_⟧₀ tx utxos = (utxos ─ stxoTx tx) ∪ utxoTx tx
\end{code}
\begin{code}
instance
  ⟦T⟧ : Denotable Tx
  ⟦T⟧ .⟦_⟧ tx s = M.when (isValidTx tx s) (s ─ stxoTx tx ∪ utxoTx tx)

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = just s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ t ⟧ >=> ⟦ l ⟧
\end{code}
\begin{code}[hide]
  ⟦L⟧₀ : Denotable₀ L
  ⟦L⟧₀ .⟦_⟧₀ []      = id
  ⟦L⟧₀ .⟦_⟧₀ (t ∷ l) = ⟦ l ⟧₀ ∘ ⟦ t ⟧₀

comp₀ : ∀ x → ⟦ l ++ l′ ⟧₀ x ≡ (⟦ l′ ⟧₀ ∘ ⟦ l ⟧₀) x
comp₀ {l = []}    _ = refl
comp₀ {l = t ∷ l} x = comp₀ {l} (⟦ t ⟧₀ x)

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l ⟧ >=> ⟦ l′ ⟧) x
comp {l = []}    x = refl
comp {l = t ∷ l} x with ⟦ t ⟧ x
... | nothing = refl
... | just s  = comp {l} s

-- valid ledgers w.r.t. a given initial state
data VL : S → L → Type where
  [] : VL s []
  _⊣_∷_ : ∀ tx →
    ∙ IsValidTx tx s
    ∙ VL (⟦ tx ⟧₀ s) l
      ────────────────
      VL s (tx ∷ l)

-- ** Operational semantics

infix 0 _—→_
data _—→_ : L × S → S → Type where

  base :
    ───────────
    [] , s —→ s

  step :
    ∙ IsValidTx t s
    ∙ l , ⟦ t ⟧₀ s —→ s′
      ──────────────────
      t ∷ l , s —→ s′

oper-comp :
  ∙ l       , s  —→ s′
  ∙ l′      , s′ —→ s″
    ──────────────────
    l ++ l′ , s  —→ s″
oper-comp {l = []}    base              s′→s″ = s′→s″
oper-comp {l = _ ∷ _} (step valid s→s′) s′→s″ = step valid (oper-comp s→s′ s′→s″)

-- ** Relating denotational and operational semantics.
denot⇒oper :
  ⟦ l ⟧ s ≡ just s′
  ─────────────────
  l , s —→ s′
denot⇒oper {l = []} refl = base
denot⇒oper {l = t ∷ l}{s} l≡
  with yes valid ← isValidTx? t s
  = step valid (denot⇒oper l≡)

oper⇒denot :
  l , s —→ s′
  ─────────────────
  ⟦ l ⟧ s ≡ just s′
oper⇒denot {l = .[]} base = refl
oper⇒denot {l = t ∷ _}{s} (step valid p)
  rewrite dec-yes (isValidTx? t s) valid .proj₂
  = oper⇒denot p

denot⇔oper :
  ⟦ l ⟧ s ≡ just s′
  ═════════════════
  l , s —→ s′
denot⇔oper = denot⇒oper , oper⇒denot
\end{code}
\end{frame}
\begin{frame}{Abstract UTxO: Monoidal Separation once again}
\begin{code}[hide]
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

private variable K V₁ V₂ : Type

emp : Assertion
emp m = ∀ k → k ∉ˢ m
\end{code}
\begin{code}
_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ◇ s₂ ⟩≡ s × P s₁ × Q s₂
\end{code}
\begin{code}[hide]
_↦_ : Address → Value → Assertion
(f ↦ v) m = m ≈ˢ singleton (f at v)

infixr 10 _∗_
infix  11 _↦_

-- ** Hoare triples.
weak↑ strong↑ : Pred₀ S → Pred₀ (Maybe S)
weak↑   = M.All.All
strong↑ = M.Any.Any

infixl 4 _↑∘_
_↑∘_ : Pred₀ S → (S → Maybe S) → Pred₀ S
P ↑∘ f = strong↑ P ∘ f

lift↑ = strong↑
pattern ret↑ x = M.Any.just x

map↑ : P ⊆¹ Q → lift↑ P ⊆¹ lift↑ Q
map↑ = M.Any.map

⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ↑∘ ⟦ l ⟧

⟨_⟩_⟨_⟩＠_ : Assertion → L → Assertion → S → Type
⟨ P ⟩ l ⟨ Q ⟩＠ s = P s → (Q ↑∘ ⟦ l ⟧) s

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base = ret↑

module _ (f : S → Maybe S) where
  lift∘>>= : ∀ {ms}
    → lift↑ (lift↑ P ∘ f) ms
    → lift↑ P (ms >>= f)
  lift∘>>= (ret↑ p) = p

  lift∘>>=˘ : ∀ {ms : Maybe S}
    → lift↑ P (ms >>= f)
    → lift↑ (lift↑ P ∘ f) ms
  lift∘>>=˘ {ms = just s} p = ret↑ p

  lift∘=<<  = lift∘>>=
  lift∘=<<˘ = lift∘>>=˘

module _ (f g : S → Maybe S) where
  lift²∘>=> : (P ↑∘ g ↑∘ f) ⊢ (P ↑∘ (f >=> g))
  lift²∘>=> = lift∘=<< _

  lift²∘>=>˘ : (P ↑∘ (f >=> g)) ⊢ (P ↑∘ g ↑∘ f)
  lift²∘>=>˘ = lift∘=<<˘ _

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ──────────────────────────
  ⟨ P ↑∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ Q ⟩
hoare-step {t = t} PlQ {s} = lift²∘>=> ⟦ t ⟧ _ {x = s} ∘ map↑ PlQ

consequence :
  ∙ P′ ⊢ P   -- ^ weakening the pre-condition
  ∙ Q  ⊢ Q′  -- ^ strengthening the post-condition
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ = map↑ Q⊢ ∘ PlQ ∘ ⊢P

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken {l = l} H = consequence {l = l} H id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen {l = l} H = consequence {l = l} id H

axiom-base⋆ : ⟨ P ↑∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []} = weaken {P′ = P ↑∘ ⟦ [] ⟧} {l = []} (λ where (ret↑ p) → p) hoare-base
axiom-base⋆ {P = P} {l = t ∷ l} = map↑ id

-- Derived alternative formulation for step, using list concatenation.

hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR
--   {s} Ps rewrite comp {l}{l′} s
--   with ⟦ l ⟧ s | PlQ Ps
-- ... | .(just _) | ret↑ Qs′ = QlR Qs′
  = begin
    P
  ⊢⟨ PlQ  ⟩
    Q ↑∘ ⟦ l ⟧
  ⊢⟨ map↑ QlR ⟩
    R ↑∘ ⟦ l′ ⟧ ↑∘ ⟦ l ⟧
  ⊢⟨ lift²∘>=> ⟦ l ⟧ ⟦ l′ ⟧  ⟩
    R ↑∘ (⟦ l ⟧ >=> ⟦ l′ ⟧)
  ≗˘⟨ cong (lift↑ R) ∘ comp {l}{l′} ⟩
    R ↑∘ ⟦ l ++ l′ ⟧
  ∎ where open ⊢-Reasoning

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where
  -- Reasoning newtype (for better type inference).
  record ℝ⟨_⟩_⟨_⟩ (P : Assertion) (l : L) (Q : Assertion) : Type where
    constructor mkℝ_
    field begin_ : ⟨ P ⟩ l ⟨ Q ⟩
    infix -2 begin_
  open ℝ⟨_⟩_⟨_⟩ public
  infix  -2 mkℝ_
  infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩++_
  infix  0  _∎

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ⟨ R ⟩
  _~⟪_⟩_ {l = l} _ H PlR = mkℝ weaken {l = l} H (begin PlR)

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _~⟨_⟫_ {l = l} _ H PlR = strengthen {l = l} H PlR

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ t → ℝ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  _~⟨_∶-_⟩_ {l = l} {R = R} P′ t H PlR = mkℝ go
    where
      go : P′ ⊢ R ↑∘ ⟦ t ∷ l ⟧
      go {s} P′s with ⟦ t ⟧ s | (begin H) P′s
      ... | just _ | ret↑ Ps′ = (begin PlR) Ps′

  -- step′ syntax
  _~⟨_∶-_⟩++_ : ∀ P′ → (l : L) → ℝ⟨ P′ ⟩ l ⟨ P ⟩ → ℝ⟨ P ⟩ l′ ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩++ PlR = mkℝ hoare-step′ {l = l} (begin H) (begin PlR)

  _∎ : ∀ P → ℝ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = mkℝ hoare-base {P = p}
\end{code}
\begin{code}

∗↔ : P ∗ Q ⊢ Q ∗ P
∗↔ {x = s} (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ◇≡-comm {s = s}{s₁}{s₂} ≡s , Qs₂ , Ps₁

∗↝ : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  let ≡s₁₂ = ◇≈-assocʳ {s₁ = s₁}{s₂₃}{s}{s₂}{s₃} ≡s ≡s₂₃ in
  (s₁ ◇ s₂) , s₃ , ≡s₁₂ , (s₁ , s₂ , ≈-refl {x = s₁ ∪ s₂} , Ps₁ , Qs₂) , Rs₃

↜∗ : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  let ≡s₂₃ = ◇≈-assocˡ {s₁₂ = s₁₂}{s₃}{s}{s₁}{s₂} ≡s ≡s₁₂ in
  s₁ , s₂ ◇ s₃ , ≡s₂₃ , Ps₁ , (s₂ , s₃ , ≈-refl {x = s₂ ∪ s₃}, Qs₂ , Rs₃)
\end{code}
\end{frame}
\begin{frame}{Abstract UTxO: Separation Logic Rules}
\begin{minipage}{.3\textwidth}
\begin{code}
[FRAME] : ∀ R →
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────
  ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
\end{code}
\begin{code}[hide]
[FRAME] = ⋯
\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.6\textwidth}
\begin{code}
[PAR] :
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  ∙ ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
    ───────────────────────────
    ⟨ P₁ ∗ P₂ ⟩ l ⟨ Q₁ ∗ Q₂ ⟩
\end{code}
\begin{code}[hide]
[PAR] = ⋯
\end{code}
\end{minipage}
\end{frame}
\end{document}
