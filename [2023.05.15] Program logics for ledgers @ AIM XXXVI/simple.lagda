\documentclass[main]{subfiles}
\begin{code}[hide]
open import Prelude.Init hiding (_+_); open SetAsType
open Integer
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Setoid
open import Prelude.Lists hiding (_↦_)
open import ValueSepInt.Maps
\end{code}

\begin{document}
\begin{frame}[fragile]{Simple Model}
\begin{code}
module _ (Part : Type) ⦃ _ : DecEq Part ⦄ where


\end{code}
\begin{code}[hide]
instance
  Sℤ  = Semigroup-ℤ-+
  Sℤ⁺ = SemigroupLaws-ℤ-+
  Mℤ  = Monoid-ℤ-+
  Mℤ⁺ = MonoidLaws-ℤ-+

postulate TODO : ∀ {A : Type ℓ} → A
\end{code}

\begin{code}
S = Map⟨ Part ↦ ℤ ⟩

record Tx : Type where
  constructor _—→⟨_⟩_
  field sender    : Part
        value     : ℤ
        receiver  : Part
open Tx public
unquoteDecl DecEq-Tx = DERIVE DecEq [ quote Tx , DecEq-Tx ]

L = List Tx
\end{code}
\begin{code}[hide]
variable
  A B C D : Part
  v v′ v″ : ℤ
  s s′ s″ s₁ s₁′ s₁″ s₂ s₂′ s₂″ s₃ s₃′ s₃″ s₂₃ s₂₃′ s₂₃″ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

  ms ms′ ms″ : Maybe S
  mls mls′ mls″ : Maybe (L × S)
\end{code}
\end{frame}
\begin{frame}[fragile]{Simple Model: Denotational Semantics}
\begin{code}
Domain = S → S

record Denotable (A : Type) : Type where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

instance
  ⟦T⟧ : Denotable Tx
  ⟦T⟧ .⟦_⟧ (A —→⟨ v ⟩ B) s = s [ A ↝ _- v ] [ B ↝ _+ v ]

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      = id
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ l ⟧ ∘ ⟦ t ⟧

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l′ ⟧ ∘ ⟦ l ⟧) x
comp {l = []}    _ = refl
comp {l = t ∷ l} x = comp {l} (⟦ t ⟧ x)
\end{code}
\end{frame}
\begin{frame}[fragile]{Simple Model: Operational Semantics}
\begin{minipage}{.4\textwidth}
\begin{code}
infix 0 _—→_
data _—→_ : L × S → S → Type where

  base :
    ───────────
    ε , s —→ s

  step : let t = A —→⟨ v ⟩ B in

    l , ⟦ t ⟧ s —→ s′
    ─────────────────
    t ∷ l , s —→ s′
\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.4\textwidth}
\begin{code}[hide]
denot⇒oper :
  ⟦ l ⟧ s ≡ s′
  ────────────
  l , s —→ s′
denot⇒oper {l = []} refl = base
denot⇒oper {l = A —→⟨ v ⟩ B ∷ l}{s} l≡ = step (denot⇒oper l≡)

oper⇒denot :
  l , s —→ s′
  ────────────
  ⟦ l ⟧ s ≡ s′
oper⇒denot {l = .[]} base = refl
oper⇒denot {l = A —→⟨ v ⟩ B ∷ _}{s} (step p) = oper⇒denot p
\end{code}
\begin{code}
denot⇔oper :
  ⟦ l ⟧ s ≡ s′
  ════════════
  l , s —→ s′
\end{code}
\begin{code}[hide]
denot⇔oper = denot⇒oper , oper⇒denot
\end{code}
\begin{code}
oper-comp :
  ∙ l        , s   —→ s′
  ∙ l′       , s′  —→ s″
    ──────────────────
    l ++ l′  , s   —→ s″
\end{code}
\begin{code}[hide]
oper-comp = TODO
\end{code}
\end{minipage}
\end{frame}
\begin{frame}[fragile]{Simple Model: Axiomatic Semantics (Hoare Logic)}
\begin{code}
Assertion = Pred₀ S
\end{code}
\begin{code}[hide]
variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion
\end{code}
\begin{code}
⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ∘ ⟦ l ⟧

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base = id

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ──────────────────────────
  ⟨ P ∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ Q ⟩
hoare-step PlQ {_} = PlQ
\end{code}
\end{frame}
\begin{frame}[fragile]{Simple Model: Axiomatic Semantics (Hoare Logic)}
\begin{minipage}{.3\textwidth}
\begin{code}
consequence :
  ∙ P′ ⊢ P
  ∙ Q  ⊢ Q′
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ
          = Q⊢ ∘ PlQ ∘ ⊢P
\end{code}
\end{minipage}
~~~\vrule~~~
\begin{minipage}{.6\textwidth}
\begin{code}
hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR =
  begin P                     ⊢⟨ PlQ ⟩
        Q ∘ ⟦ l ⟧             ⊢⟨ QlR ⟩
        R ∘ (⟦ l′ ⟧ ∘ ⟦ l ⟧)  ≗˘⟨ cong R ∘ comp {l} {l′} ⟩
        R ∘ ⟦ l ++ l′ ⟧       ∎ where open ⊢-Reasoning
\end{code}
\end{minipage}
\end{frame}
\begin{frame}[fragile]{Simple Model: Separation Logic}
\begin{code}[hide]
infixr 10 _∗_
\end{code}
\begin{code}
emp : Assertion
emp m = ∀ k → m k ≡ ε

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ◇ s₂ ⟩≡ s × P s₁ × Q s₂


∗↔ : P ∗ Q ⊢ Q ∗ P
∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ◇≡-comm {x = s₁}{s₂} ≡s , Qs₂ , Ps₁

∗↝ : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  (s₁ ◇ s₂) , s₃ , ◇≈-assocʳ {m₁ = s₁} ≡s ≡s₂₃ , (s₁ , s₂ , ≈-refl , Ps₁ , Qs₂) , Rs₃

↜∗ : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  s₁ , s₂ ◇ s₃ , ◇≈-assocˡ {m₁ = s₁}{s₂} ≡s ≡s₁₂  , Ps₁ , (s₂ , s₃ , ≈-refl , Qs₂ , Rs₃)
\end{code}
\end{frame}
\begin{frame}{Simple Model: Frame Rule}
\begin{code}
◇-⟦⟧ :
  ⟨ s₁ ◇ s₂ ⟩≡ s
  ─────────────────────
  ⟨ ⟦ l ⟧ s₁ ◇ s₂ ⟩≡ ⟦ l ⟧ s
\end{code}
\begin{code}[hide]
◇-⟦⟧ = TODO
\end{code}

\begin{code}
[FRAME] :
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
[FRAME] {l = l} PlQ (s₁ , s₂ , ≡s , Ps₁ , Rs₂) =
  ⟦ l ⟧ s₁ , s₂ , ◇-⟦⟧ {l = l} ≡s , PlQ Ps₁ , Rs₂
\end{code}
\end{frame}
\begin{frame}[fragile]{Simple Model: Concurrent Separation Logic}
\begin{code}
◇-interleave :
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ──────────────────────────────────
    ⟨ ⟦ l₁ ⟧ s₁ ◇ ⟦ l₂ ⟧ s₂ ⟩≡ ⟦ l ⟧ s
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
[PAR] {l₁} {l₂} {l} ≡l Pl₁Q Pl₂Q {s} (s₁ , s₂ , ≡s , Ps₁ , Ps₂) =
  ⟦ l₁ ⟧ s₁ , ⟦ l₂ ⟧ s₂ , ◇-interleave ≡l ≡s , Pl₁Q Ps₁ , Pl₂Q Ps₂
\end{code}
\end{frame}
\end{document}
