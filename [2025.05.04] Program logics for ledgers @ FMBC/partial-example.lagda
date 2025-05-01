\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{Adding Partiality: Example derivation (monolithic)}
\begin{code}[hide]
open import Prelude.Init; open SetAsType
open Nat
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists.Dec
open import Prelude.Lists hiding (_↦_)
open import Prelude.Monoid
open import Prelude.Nary
open import Prelude.InferenceRules

data Part : Type where
\end{code}
\begin{code}
  A B C D : Part
\end{code}
\begin{code}[hide]
unquoteDecl DecEq-Part = DERIVE DecEq [ quote Part , DecEq-Part ]

open import ValueSepExact.Maps
open import ValueSepExact.Ledger Part hiding (A; B; C; D; ⟦_⟧)
open import ValueSepExact.HoareLogic Part
open import ValueSepExact.HoareProperties Part
open import ValueSepExact.SL Part using () renaming (ℝ[FRAME] to [FRAME])
-- open import ValueSepExact.CSL Part using () renaming (ℝ[PAR] to [PAR])
open HoareReasoning
postulate
  [PAR] :
    ∙ l₁ ∥ l₂ ≡ l
    ∙ ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
    ∙ ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
      ─────────────────────────
      ℝ⟨ P₁ ∗ P₂ ⟩ l ⟨ Q₁ ∗ Q₂ ⟩

_↝_ : ∀ A B → ℝ⟨ A ↦ v ∗ B ↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ (v′ + v) ⟩
_↝_ = mkℝ_ ∘₂ _↝⁰_
_↜_ : ∀ A B → ℝ⟨ A ↦ v′ ∗ B ↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (v′ + v) ∗ B ↦ 0 ⟩
_↜_ = mkℝ_ ∘₂ _↜⁰_
\end{code}
\begin{code}

t₁ = A —→⟨ 1 ⟩ B; t₂ = D —→⟨ 1 ⟩ C; t₃ = B —→⟨ 1 ⟩ A; t₄ = C —→⟨ 1 ⟩ D
t₁-₄ = L ∋ ⟦ t₁ , t₂ , t₃ , t₄ ⟧

_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩ t₁-₄ ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0    ∗ C ↦ 0 ∗ D ↦ 1  ~⟪ ∗↝ ⟩
          (A ↦ 1 ∗ B ↦ 0)  ∗ C ↦ 0 ∗ D ↦ 1  ~⟨ t₁ ∶- [FRAME] (C ↦ 0 ∗ D ↦ 1) (A ↝ B) ⟩
          (A ↦ 0 ∗ B ↦ 1)  ∗ C ↦ 0 ∗ D ↦ 1  ~⟪ ∗↔ ⟩
          (C ↦ 0 ∗ D ↦ 1)  ∗ A ↦ 0 ∗ B ↦ 1  ~⟨ t₂ ∶- [FRAME] (A ↦ 0 ∗ B ↦ 1) (C ↜ D) ⟩
          (C ↦ 1 ∗ D ↦ 0)  ∗ A ↦ 0 ∗ B ↦ 1  ~⟪ ∗↔ ⟩
          (A ↦ 0 ∗ B ↦ 1)  ∗ C ↦ 1 ∗ D ↦ 0  ~⟨ t₃ ∶- [FRAME] (C ↦ 1 ∗ D ↦ 0) (A ↜ B) ⟩
          (A ↦ 1 ∗ B ↦ 0)  ∗ C ↦ 1 ∗ D ↦ 0  ~⟪ ∗↔ ⟩
          (C ↦ 1 ∗ D ↦ 0)  ∗ A ↦ 1 ∗ B ↦ 0  ~⟨ t₄ ∶- [FRAME] (A ↦ 1 ∗ B ↦ 0) (C ↝ D) ⟩
          (C ↦ 0 ∗ D ↦ 1)  ∗ A ↦ 1 ∗ B ↦ 0  ~⟪ ∗↔ ⟩
          (A ↦ 1 ∗ B ↦ 0)  ∗ C ↦ 0 ∗ D ↦ 1  ~⟪ ↜∗ ⟩
          A ↦ 1 ∗ B ↦ 0    ∗ C ↦ 0 ∗ D ↦ 1  ∎
\end{code}
\end{frame}
\begin{frame}[fragile]{Adding Partiality: Example derivation (modular)}
\begin{code}
_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩ t₁-₄ ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0    ∗ C ↦ 0 ∗ D ↦ 1  ~⟪ ∗↝ ⟩
          (A ↦ 1 ∗ B ↦ 0)  ∗ C ↦ 0 ∗ D ↦ 1  ~⟨ t₁-₄ ∶- [PAR] auto H₁ H₂ ⟩++
          (A ↦ 1 ∗ B ↦ 0)  ∗ C ↦ 0 ∗ D ↦ 1  ~⟪ ↜∗ ⟩
          A ↦ 1 ∗ B ↦ 0    ∗ C ↦ 0 ∗ D ↦ 1  ∎
  where
    H₁ : ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ t₁ ∷ t₃ ∷ [] ⟨ A ↦ 1 ∗ B ↦ 0 ⟩
    H₁ = begin A ↦ 1 ∗ B ↦ 0 ~⟨ t₁ ∶- A ↝ B ⟩
               A ↦ 0 ∗ B ↦ 1 ~⟨ t₃ ∶- A ↜ B ⟩
               A ↦ 1 ∗ B ↦ 0 ∎
    H₂ : ⟨ C ↦ 0 ∗ D ↦ 1 ⟩ t₂ ∷ t₄ ∷ [] ⟨ C ↦ 0 ∗ D ↦ 1 ⟩
    H₂ = begin C ↦ 0 ∗ D ↦ 1 ~⟨ t₂ ∶- C ↜ D ⟩
               C ↦ 1 ∗ D ↦ 0 ~⟨ t₄ ∶- C ↝ D ⟩
               C ↦ 0 ∗ D ↦ 1 ∎
\end{code}
\end{frame}
\end{document}
