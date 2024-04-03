\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Agda.Primitive renaming (Set to Type)

import Data.Maybe as Maybe
open import Data.Maybe.Properties
open import Interface.STS hiding (_⊢_⇀⟦_⟧*_)
open import Relation.Binary.PropositionalEquality

private variable
  C S Sig : Type
  Γ : C
  s s' s'' : S
  b sig : Sig
  sigs : List Sig
\end{code}
\newcommand\computational{%
\begin{code}
record Computational (_⊢_⇀⦇_,X⦈_ : C → S → Sig → S → Type) : Type where
  field  compute          : C → S → Sig → Maybe S
         compute-correct  : compute Γ s b ≡ just s' ⇔ Γ ⊢ s ⇀⦇ b ,X⦈ s'
\end{code}
}
