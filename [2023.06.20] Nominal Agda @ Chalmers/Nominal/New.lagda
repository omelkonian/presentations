\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{The ``new'' (И) quantifier}
\begin{code}[hide]
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq

module Nominal.New (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

-- ** The И "new" quantifier.
\end{code}
\begin{code}
И : Pred (Pred Atom ℓ) ℓ
И φ = ∃ λ (xs : List Atom) → (∀ y → y ∉ xs → φ y)
\end{code}
\begin{code}[hide]
И⅁ : Pred (Atom → Atom → Type ℓ) ℓ
И⅁ φ = ∃ λ (xs : List Atom) →
   (∀ y z → y ∉ xs → z ∈ xs → φ y z)

-- И∗ : Pred (Pred (List Atom) ℓ) ℓ
-- И∗ φ = ∃ λ (xs : List Atom) → (∀ ys → All (_∉ xs) ys → φ ys)

И^_ : (n : ℕ) → Pred (Pred (Vec Atom n) ℓ) ℓ
(И^ n) φ = ∃ λ (xs : List Atom) → (∀ ys → V.All.All (_∉ xs) ys → φ ys)

И² : Pred (Atom → Atom → Type ℓ) ℓ
-- И² φ = (И^ 2) λ where (x ∷ y ∷ []) → φ x y
И² φ = ∃ λ (xs : List Atom) → (∀ y z → y ∉ xs → z ∉ xs → φ y z)

И³ : Pred (Atom → Atom → Atom → Type ℓ) ℓ
-- И³ φ = (И^ 3) λ where (x ∷ y ∷ z ∷ []) → φ x y z
И³ φ = ∃ λ (xs : List Atom) → (∀ y z w → y ∉ xs → z ∉ xs → w ∉ xs → φ y z w)

-- ** the co-finite construction leads to issues with universe levels.
-- open import Cofinite.agda
-- И : Pred (Pred Atom ℓ) (lsuc ℓ)
-- И P = powᶜᵒᶠ P
\end{code}
\end{frame}
\end{document}
