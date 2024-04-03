\begin{code}[hide]
{-# OPTIONS --safe #-}

module Ledger.Introduction where

open import Prelude
open import Agda.Primitive renaming (Set to Type)

import Data.Maybe as Maybe
open import Data.Maybe.Properties
open import Interface.STS hiding (_⊢_⇀⟦_⟧*_)
open import Relation.Binary.PropositionalEquality

private variable
  Env State Signal : Type
  Γ : Env
  s s' s'' : State
  b : Signal
  bs : List Signal
\end{code}

\begin{code}[hide]
module _
  (
\end{code}
\newcommand\transitionType{%
\begin{code}
  _⊢_⇀⦉_⦊_ : Env → State → Signal → State → Type
\end{code}
}
\begin{code}[hide]
  ) where
\end{code}
\newcommand\rtClosure{%
\begin{AgdaAlign}
\begin{code}
  data _⊢_⇀⦉_⦊*_ : Env → State → List Signal → State → Type where
\end{code}
\AgdaNoSpaceAroundCode{}
\begin{minipage}{.35\textwidth}
\begin{code}
    base :
         ────────────
         Γ ⊢ s ⇀⦉ []  ⦊* s
\end{code}
\end{minipage}
\begin{minipage}{.6\textwidth}
\begin{code}
    step :
      ∙  Γ ⊢ s   ⇀⦉ b       ⦊   s'
      ∙  Γ ⊢ s'  ⇀⦉ bs      ⦊*  s''
         ───────────────────────────
         Γ ⊢ s   ⇀⦉ b ∷ bs  ⦊*  s''
\end{code}
\end{minipage}
\end{AgdaAlign}
}

\begin{code}[hide]
module _ (ℙ_ : Type → Type) (_∈_ : ∀ {A} → A → ℙ A → Type) where
\end{code}
\newcommand\setTheory{%
\begin{code}
  _⊆_ _≡ᵉ_ : {A : Type} → ℙ A → ℙ A → Type
  X ⊆   Y = ∀ {x} → x ∈ X → x ∈ Y
  X ≡ᵉ  Y = X ⊆ Y × Y ⊆ X
\end{code}
}
\newcommand\setTheoryMaps{%
\begin{code}
  _⇀_ : Type → Type → Type
  A ⇀ B = ∃ λ (ℛ : ℙ (A × B)) →
    ∀ {a b b'} → (a , b) ∈ ℛ → (a , b') ∈ ℛ → b ≡ b'
\end{code}
}
