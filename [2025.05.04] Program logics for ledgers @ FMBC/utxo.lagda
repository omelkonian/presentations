\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{UTxO: Barebones Setup}
\begin{code}[hide]
open import Prelude.Init; open SetAsType
open L.Mem hiding (_─_)
open import Prelude.General
open import Prelude.Maybes
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Lists hiding (_⁉_; _‼_; map↦; _↦_)
open import Prelude.Lists.Dec
open import Prelude.Lists.WithK
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.FromList
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Irrelevance hiding (_─_)
open import Prelude.Apartness
open import Prelude.Maps as Map hiding (_⊣_)
open import Prelude.Monad
open import Prelude.InferenceRules
open import Prelude.Allable hiding (All)

open import Common public

record TxOutputRef : Type where
  constructor _indexed-at_
  field txId  : HashId
        index : ℕ
open TxOutputRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxOutputRef , DecEq-TxOR ]

open CommonInfo TxOutputRef public

postulate TODO : ∀ {A : Set ℓ} → A

module _ {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where
  open import Prelude.ToList
  import Prelude.Sets as S
  import Prelude.Bags as B

  _‼_ : {k : K} (m : Map⟨ K ↦ V ⟩) → k ∈ᵈ m → V
  m ‼ k∈ = destruct-Is-just (∈ᵈ⇒⁉ m k∈) .proj₁

  _─ᵏˢ_ : Map⟨ K ↦ V ⟩ → List K → Map⟨ K ↦ V ⟩
  m ─ᵏˢ ks = filterK (_∉? ks) m

  _─_ = _─ᵏˢ_

  keys : Map⟨ K ↦ V ⟩ → List K
  keys = map proj₁ ∘ toList

  keysˢ : Map⟨ K ↦ V ⟩ → B.Bag⟨ K ⟩
  keysˢ = fromList ∘ keys

  values⊑ : (m : Map⟨ K ↦ V ⟩) → ∃ $ All (_∈ᵈ m) → List V
  values⊑ m (ks , ks⊆) = mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆)

  values values′ : Map⟨ K ↦ V ⟩ → List V
  values = map proj₂ ∘ toList
  values′ m = values⊑ m (keys m , L.All.tabulate id)

  values⊑ˢ : (m : Map⟨ K ↦ V ⟩) → ∃ $ All (_∈ᵈ m) → B.Bag⟨ V ⟩
  values⊑ˢ = fromList ∘₂ values⊑

  valuesˢ valuesˢ′ : Map⟨ K ↦ V ⟩ → B.Bag⟨ V ⟩
  valuesˢ = fromList ∘ map proj₂ ∘ toList
  valuesˢ′ m = values⊑ˢ m (keys m , L.All.tabulate id)

  open ≡-Reasoning
  private variable
    m m′ : Map⟨ K ↦ V ⟩
    ks : List K; kvs : List (K × V)

  open import Prelude.Lists.Dec
  open import Prelude.Apartness

  -- basic list properties
  postulate
    nubBy-from∘to : ∀ {A B : Type} ⦃ _ : DecEq B ⦄ {f : A → B} {xs : List A} →
      Unique (map f xs) → nubBy f xs ≡ xs
    Unique-proj₁ : ∀ {A B : Type} {xys : List (A × B)} →
      Unique (map proj₁ xys) → Unique xys
    Disjoint-proj₁ : ∀ {A B : Type} {xys xys′ : List (A × B)} →
      map proj₁ xys ♯ map proj₁ xys′ → xys ♯ xys′

  nub∘nubBy-from∘to : ∀ {A B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄
    {f : A → B} {xs : List A} →
    Unique (map f xs) →
      nub (nubBy f xs) ≡ xs
  nub∘nubBy-from∘to {f = f}{xs} uniq =
    begin
      nub (nubBy f xs)
    ≡⟨ nub-from∘to $ Unique-nubBy f xs ⟩
      nubBy f xs
    ≡⟨ nubBy-from∘to uniq ⟩
      xs
    ∎

  toList-∪ : keys m ♯ keys m′ →  toList (m ∪ m′) ≡ toList m ++ toList m′
  toList-∪ {m@(_ Map.⊣ ·uniq-m)}{m′@(_ Map.⊣ ·uniq-m′)} m♯m′ =
    begin
      toList (m ∪ m′)
    ≡⟨⟩
      nub (nubBy proj₁ (toList m ++ toList m′))
    ≡⟨ cong nub $ nubBy-from∘to uniq-proj₁-++ ⟩
      nub (toList m ++ toList m′)
    ≡⟨ nub-from∘to uniq-++ ⟩
      toList m ++ toList m′
    ∎
    where
      uniq-m  = recompute dec ·uniq-m
      uniq-m′ = recompute dec ·uniq-m′

      uniq-++ : Unique (toList m ++ toList m′)
      uniq-++ = L.Uniq.++⁺ (Unique-proj₁ uniq-m) (Unique-proj₁ uniq-m′)
                           (Disjoint-proj₁ m♯m′)

      uniq-proj₁-++ : Unique $ map proj₁ (toList m ++ toList m′)
      uniq-proj₁-++ rewrite L.map-++-commute proj₁ (toList m) (toList m′)
        = L.Uniq.++⁺ uniq-m uniq-m′ m♯m′

  module _ m m′ (m♯m′ : keys m ♯ keys m′) where
    valuesˢ-∪ : valuesˢ (m ∪ m′) ≡ valuesˢ m B.∪ valuesˢ m′
    valuesˢ-∪ =
      begin
        valuesˢ (m ∪ m′)
      ≡⟨⟩
        fromList (proj₂ <$> toList (m ∪ m′))
      ≡⟨ cong (fromList ∘ map proj₂) $ toList-∪ {m}{m′} m♯m′ ⟩
        fromList (proj₂ <$> (toList m ++ toList m′))
      ≡⟨ cong fromList $ L.map-++-commute proj₂ (toList m) (toList m′) ⟩
        fromList ((proj₂ <$> toList m) ++ (proj₂ <$> toList m′))
      ≡⟨⟩
        fromList (proj₂ <$> toList m) B.∪ fromList (proj₂ <$> toList m′)
      ≡⟨⟩
        valuesˢ m B.∪ valuesˢ m′
      ∎

  valuesˢ∘fromList : Unique (proj₁ <$> kvs) →
    valuesˢ (fromList kvs) ≡ fromList (proj₂ <$> kvs)
  valuesˢ∘fromList = cong (fromList ∘ map proj₂) ∘ nub∘nubBy-from∘to

  valuesˢ-─ : ∀ m (p : ∃ $ All (_∈ᵈ m)) →
    valuesˢ (m ─ᵏˢ p .proj₁) ≡ valuesˢ m B.─ values⊑ˢ m p
  valuesˢ-─ m (ks , ks⊆) =
    begin
      valuesˢ (m ─ᵏˢ ks)
    ≡⟨⟩
      fromList (proj₂ <$> toList (m ─ᵏˢ ks))
    ≡⟨⟩
      fromList (proj₂ <$> filter ((_∉? ks) ∘ proj₁) (toList m))
    ≡⟨ cong fromList H ⟩
      fromList
        (map proj₂ (toList m) ∸[bag] (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆)))
    ≡⟨⟩
      fromList (proj₂ <$> toList m)
        B.─
      fromList (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆))
    ≡⟨⟩
      fromList (proj₂ <$> toList m) B.─ fromList (values⊑ m (-, ks⊆))
    ≡⟨⟩
      valuesˢ m B.─ values⊑ˢ m (-, ks⊆)
    ∎
    where
      postulate
        H : map proj₂ (filter ((_∉? ks) ∘ proj₁) (toList m))
          ≡ map proj₂ (toList m) ∸[bag] (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆))


  postulate
    values⊆⇒⊆[bag] : ∀ m (p : ∃ $ All (_∈ᵈ m)) → values⊑ m p ⊆[bag] values m

  values⊆⇒⊆ˢ : ∀ m (p : ∃ $ All (_∈ᵈ m)) → values⊑ˢ m p B.⊆ˢ valuesˢ m
  values⊆⇒⊆ˢ = values⊆⇒⊆[bag]
\end{code}
\begin{code}
S = Map⟨ TxOutputRef ↦ TxOutput ⟩
\end{code}
\vfill\hrule\vfill
\begin{code}[hide]
mkUtxo : ∀ {out} tx → out L.Mem.∈ outputs tx → TxOutputRef × TxOutput
mkUtxo {out} tx out∈ = (tx ♯) indexed-at toℕ (L.Any.index out∈) , out

postulate Unique-mkUtxo : ∀ t → Unique $ map proj₁ $ mapWith∈ (t .outputs) (mkUtxo t)

utxoTx : Tx → S
utxoTx tx = fromList $ L.Mem.mapWith∈ (tx .outputs) (mkUtxo tx)
\end{code}
\begin{AgdaMultiCode}
\begin{code}
record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    noDoubleSpending :
      ·Unique (outputRefs tx)

    validOutputRefs :
      ∀[ ref ∈ outputRefs tx ] (ref ∈ᵈ utxos)
\end{code}
\begin{code}[hide]
  resolved : Resolved tx
  resolved = (utxos ‼_) ∘ L.All.lookup validOutputRefs

  txInfo = mkTxInfo tx resolved
  resolvedInputs = resolveInputs tx resolved
  field
\end{code}
\begin{code}
    preservesValues :
      tx .forge + ∑ resolvedInputs (value ∘ proj₂) ≡ ∑ (tx .outputs) value

    allInputsValidate :
      ∀[ i ∈ tx .inputs ] T (i .validator txInfo (i .redeemer))

    validateValidHashes :
      ∀[ (i , o) ∈ resolvedInputs ] (o .address ≡ i .validator ♯)
\end{code}
\end{AgdaMultiCode}
\end{frame}
\begin{frame}[fragile]{UTxO: Denotational Semantics}
\begin{code}[hide]
open IsValidTx public

postulate isValidTx? : ∀ tx s → Dec (IsValidTx tx s)

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
  ⟦T⟧₀ .⟦_⟧₀ tx utxos = (utxos ─ᵏˢ outputRefs tx) ∪ utxoTx tx
\end{code}
\begin{code}
instance
  ⟦T⟧ : Denotable Tx
  ⟦T⟧ .⟦_⟧ tx s = M.when (isValidTx tx s) (s ─ outputRefs tx ∪ utxoTx tx)

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧  []       s  = just s
  ⟦L⟧ .⟦_⟧  (t ∷ l)  =  ⟦ t ⟧ >=> ⟦ l ⟧

\end{code}
\vfill\hrule\vfill
\begin{code}[hide]
  ⟦L⟧₀ : Denotable₀ L
  ⟦L⟧₀ .⟦_⟧₀ []      = id
  ⟦L⟧₀ .⟦_⟧₀ (t ∷ l) = ⟦ l ⟧₀ ∘ ⟦ t ⟧₀

comp₀ : ∀ x → ⟦ l ++ l′ ⟧₀ x ≡ (⟦ l′ ⟧₀ ∘ ⟦ l ⟧₀) x
comp₀ {l = []}    _ = refl
comp₀ {l = t ∷ l} x = comp₀ {l} (⟦ t ⟧₀ x)
\end{code}
\begin{code}
comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l ⟧ >=> ⟦ l′ ⟧) x
comp {[]}     _  = refl
comp {t ∷ l}  x  with ⟦ t ⟧ x
... | nothing  = refl
... | just s   = comp {l} s
\end{code}
\begin{code}[hide]
-- valid ledgers w.r.t. a given initial state
data VL : S → L → Type where
  [] : VL s []
  _⊣_∷_ : ∀ tx →
    ∙ IsValidTx tx s
    ∙ VL (⟦ tx ⟧₀ s) l
      ────────────────
      VL s (tx ∷ l)

VL⇒Resolved : VL s l → All Resolved l
VL⇒Resolved [] = []
VL⇒Resolved (tx ⊣ p ∷ l) = resolved p ∷ VL⇒Resolved l

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
\begin{frame}{UTxO: Separation via Disjointness}
\begin{code}[hide]
_[_↦_]∅ : S → TxOutputRef → TxOutput → Type
m [ k ↦ v ]∅ = m [ k ↦ v ] × ∀ k′ → k′ ≢ k → k′ ∉ᵈ m

Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

private variable K V₁ V₂ : Type

emp : Assertion
emp m = ∀ k → k ∉ᵈ m
\end{code}
\begin{code}
_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ⊎ s₂ ⟩≡ s × P s₁ × Q s₂
\end{code}
\vfill\hrule\vfill
\begin{code}[hide]
_↦_ : TxOutputRef → TxOutput → Assertion
or ↦ o = _[ or ↦ o ]∅

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

\begin{minipage}{.4\textwidth}
\begin{code}
⊎-⟦⟧ : ∀ s₁′ →
  ∙ ⟦ l ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ⊎ s₂ ⟩≡ s
    ────────────────────────────
    (⟨ s₁′ ⊎ s₂ ⟩≡_ ↑∘ ⟦ l ⟧) s
\end{code}
\begin{code}[hide]
⊎-⟦⟧ = TODO
postulate instance
  Apart-L : L //^⦅ 0ℓ ⦆ Assertion
\end{code}

\begin{code}

[FRAME] : ∀ R →
  ∙ l ♯ R
  ∙ ⟨ P ⟩ l ⟨ Q ⟩
    ─────────────────
    ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
\end{code}
\begin{code}[hide]
[FRAME] {l}{P}{Q} R l♯R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂)
  with ⟦ l ⟧ s₁ in s₁≡ | PlQ Ps₁
... | .just s₁′ | ret↑ Qs₁′
  with ⟦ l ⟧ s in s≡ | ⊎-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
... | .just s′ | ret↑ ≡s′
    = ret↑ (s₁′ , s₂ , ≡s′ , Qs₁′ , Rs₂)
\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.5\textwidth}
\begin{code}
[PAR] :
  ∙ l₁ ♯ P₂
  ∙ l₂ ♯ P₁
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  ∙ ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
    ───────────────────────────
    ⟨ P₁ ∗ P₂ ⟩ l ⟨ Q₁ ∗ Q₂ ⟩
\end{code}
\begin{code}[hide]
[PAR] = TODO
\end{code}
\end{minipage}
\end{frame}
\end{document}
