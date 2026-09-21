\begin{code}[hide]
module LevelOne where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Rules.Core
  using (Flat; single; none; all)
\end{code}

\begin{code}[hide]
vowels : Syllable → ℕ
vowels = length ∘ filter⁺ {P = Vowel} dec¹
\end{code}

\newcommand\complies{%
\begin{code}
record _-compliesWith-_ (A B : Type) : Type₁ where
  infix 0 _~_
  field _~_ : A → B → Type

  _≁_ : A → B → Type
  _≁_ = ¬_ ∘₂ _~_

  NonDerivable : A → Type
  NonDerivable a = ∀ b → a ≁ b
\end{code}
\begin{code}[hide]
open _-compliesWith-_ ⦃ ... ⦄ public
\end{code}
}

\newcommand\levelOne{
\begin{AgdaMultiCode}
\begin{code}[hide]
instance
\end{code}
\begin{code}
  Sy-Q : Syllable -compliesWith- Quantity
  Sy-Q ._~_ = _~′_
\end{code}
\begin{code}[hide]
   module ∣Sy-Q∣
\end{code}
\begin{code}
    where
    data _~′_ : Syllable → Quantity → Type where

      longByNature :
        ( Any× Diphthong sy
        ⊎ Any ─Vowel sy
        ⊎ Any HasCircumflex sy )
        ────────────────────────
        sy ~′ ─

      shortByNature :
        ∀ (v∈ : Any ·Vowel sy) →
        ∙ vowels sy ≡ 1
          ─────────────
          sy ~′ ·
\end{code}
\end{AgdaMultiCode}
}

\newcommand\levelOneFlat{
\begin{AgdaMultiCode}
\begin{code}
  Sy-MQ : Syllable -compliesWith- Flat Quantity
  Sy-MQ ._~_ = _~′_
\end{code}
\begin{code}[hide]
   module ∣Sy-MQ∣
\end{code}
\begin{code}
    where
    data _~′_ : Syllable → Flat Quantity → Type where

      byNature :
        sy ~ q
        ──────────────
        sy ~′ single q

      doubtful :
        NonDerivable {B = Quantity} sy
        ──────────────────────────────
        sy ~′ none
\end{code}
\end{AgdaMultiCode}
}
