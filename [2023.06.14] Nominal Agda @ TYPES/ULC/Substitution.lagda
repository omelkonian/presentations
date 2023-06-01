\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{Nominal substitution}
\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --auto-inline #-}
open import Prelude.Init hiding ([_]); open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.DecEq
-- open import Prelude.Lists.Dec
-- open import Prelude.Measurable
open import Prelude.InfEnumerable
open import Prelude.Setoid
open import Prelude.InferenceRules

-- ** Substitution.
module ULC.Substitution (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base    Atom ⦃ it ⦄ hiding (y)
open import ULC.Measure Atom ⦃ it ⦄ ⦃ it ⦄
open import ULC.Alpha   Atom ⦃ it ⦄ ⦃ it ⦄
open import Nominal Atom
open import Nominal.Product Atom

infix 60 _[_/_]
{-# TERMINATING #-}
\end{code}
\begin{code}
_[_/_] : Term → Atom → Term → Term
(` x)    [ 𝕒 / N ]  = if x == 𝕒 then N else ` x
(L · M)  [ 𝕒 / N ]  = L [ 𝕒 / N ] · M [ 𝕒 / N ]
(ƛ t̂)    [ 𝕒 / N ]  = ƛ y ⇒ conc t̂ y [ 𝕒 / N ]
  where y = fresh-var (𝕒 , t̂ , N)

\end{code}
\begin{code}[hide]
private variable y : Atom
postulate
\end{code}
\begin{code}
  swap-subst     : Equivariant _[_/_]
  subst-commute  : N [ x / L ] [ y / M [ x / L ] ] ≈ N [ y / M ] [ x / L ]
  cong-subst     : t ≈ t′ → t [ x / M ] ≈ t′ [ x / M ]
  swap∘subst     : swap y x N [ y / M ] ≈ N [ x / M ]
\end{code}
\end{frame}
\end{document}
