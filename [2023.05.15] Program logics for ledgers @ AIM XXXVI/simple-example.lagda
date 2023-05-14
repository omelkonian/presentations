\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{Simple Model: Example derivation (monolithic)}
\begin{code}[hide]
open import Prelude.Init hiding (_+_); open SetAsType
open Integer
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists.Dec
open import Prelude.Monoid
open import Prelude.Nary

data Part : Type where
\end{code}
\begin{code}
  A B C D : Part
\end{code}
\begin{code}[hide]
unquoteDecl DecEq-Part = DERIVE DecEq [ quote Part , DecEq-Part ]

open import ValueSepInt.Maps
open import ValueSepInt.Ledger Part hiding (A; B; C; D; ⟦_⟧)
open import ValueSepInt.HoareLogic Part
open import ValueSepInt.HoareProperties Part
open import ValueSepInt.SL Part using () renaming (ℝ[FRAME] to [FRAME])
open import ValueSepInt.CSL Part using () renaming (ℝ[PAR] to [PAR])
open HoareReasoning

_↝_ : ∀ A B → ℝ⟨ A ↦ v ∗ B ↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ ε ∗ B ↦ (v′ + v) ⟩
_↝_ = mkℝ_ ∘₂ _↝⁰_
_↜_ : ∀ A B → ℝ⟨ A ↦ v′ ∗ B ↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (v′ + v) ∗ B ↦ 0ℤ ⟩
_↜_ = mkℝ_ ∘₂ _↜⁰_
\end{code}
\begin{code}
t₁ = A —→⟨ 1ℤ ⟩ B; t₂ = D —→⟨ 1ℤ ⟩ C; t₃ = B —→⟨ 1ℤ ⟩ A; t₄ = C —→⟨ 1ℤ ⟩ D
t₁-₄ = L ∋ ⟦ t₁ , t₂ , t₃ , t₄ ⟧

_ : ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩ t₁-₄ ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
_ = begin A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ~⟪ ∗↝ ⟩
          (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟨ t₁ ∶- [FRAME] (C ↦ 0ℤ ∗ D ↦ 1ℤ) (A ↝ B) ⟩
          (A ↦ 0ℤ ∗ B ↦ 1ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟪ ∗↔ ⟩
          (C ↦ 0ℤ ∗ D ↦ 1ℤ) ∗ A ↦ 0ℤ ∗ B ↦ 1ℤ ~⟨ t₂ ∶- [FRAME] (A ↦ 0ℤ ∗ B ↦ 1ℤ) (C ↜ D) ⟩
          (C ↦ 1ℤ ∗ D ↦ 0ℤ) ∗ A ↦ 0ℤ ∗ B ↦ 1ℤ ~⟪ ∗↔ ⟩
          (A ↦ 0ℤ ∗ B ↦ 1ℤ) ∗ C ↦ 1ℤ ∗ D ↦ 0ℤ ~⟨ t₃ ∶- [FRAME] (C ↦ 1ℤ ∗ D ↦ 0ℤ) (A ↜ B) ⟩
          (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 1ℤ ∗ D ↦ 0ℤ ~⟪ ∗↔ ⟩
          (C ↦ 1ℤ ∗ D ↦ 0ℤ) ∗ A ↦ 1ℤ ∗ B ↦ 0ℤ ~⟨ t₄ ∶- [FRAME] (A ↦ 1ℤ ∗ B ↦ 0ℤ) (C ↝ D) ⟩
          (C ↦ 0ℤ ∗ D ↦ 1ℤ) ∗ A ↦ 1ℤ ∗ B ↦ 0ℤ ~⟪ ∗↔ ⟩
          (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟪ ↜∗ ⟩
          A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ∎
\end{code}
\end{frame}
\begin{frame}[fragile]{Simple Model: Example derivation (modular)}
\begin{code}
_ : ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩ t₁-₄ ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
_ = begin A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ~⟪ ∗↝ ⟩
          (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟨ t₁-₄ ∶- [PAR] auto H₁ H₂ ⟩++
          (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟪ ↜∗ ⟩
          A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ∎
  where
    H₁ : ℝ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ⟩ t₁ ∷ t₃ ∷ [] ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ⟩
    H₁ = A ↦ 1ℤ ∗ B ↦ 0ℤ ~⟨ t₁ ∶- A ↝ B ⟩
         A ↦ 0ℤ ∗ B ↦ 1ℤ ~⟨ t₃ ∶- A ↜ B ⟩
         A ↦ 1ℤ ∗ B ↦ 0ℤ ∎
    H₂ : ℝ⟨ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩ t₂ ∷ t₄ ∷ [] ⟨ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
    H₂ = C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟨ t₂ ∶- C ↜ D ⟩
         C ↦ 1ℤ ∗ D ↦ 0ℤ ~⟨ t₄ ∶- C ↝ D ⟩
         C ↦ 0ℤ ∗ D ↦ 1ℤ ∎
\end{code}
\end{frame}
\end{document}
