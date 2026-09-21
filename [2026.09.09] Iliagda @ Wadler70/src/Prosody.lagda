\begin{code}[hide]
module Prosody where

open import Iliagda.Init
open import Iliagda.Morphology
\end{code}

\newcommand\prosodyQuantity{%
\begin{code}
data Quantity : Type where
  ·  {- short -}  : Quantity
  ─  {- long  -}  : Quantity
\end{code}
}

\newcommand\prosodyVowels{%
\begin{code}
─Vowel ·Vowel Doubtful : Pred₀ Letter
─Vowel = _∈  [ η ⨾ Ἠ ⨾ ἠ ⨾ Ἤ ⨾ ἤ ⨾ ᾔ ⨾ ἢ ⨾ ἦ ⨾ ᾖ ⨾ ᾐ ⨾ Ἡ ⨾ ἡ ⨾ Ἥ ⨾ ἥ ⨾ ᾕ ⨾ ἣ ⨾ ἧ ⨾ ᾗ ⨾ ή ⨾ ῄ ⨾ ὴ ⨾ ῂ ⨾ ῆ ⨾ ῇ ⨾ ῃ ]
          ◇  [ ω ⨾ Ὠ ⨾ ὠ ⨾ Ὤ ⨾ ὤ ⨾ ᾤ ⨾ ὢ ⨾ Ὦ ⨾ ὦ ⨾ ᾦ ⨾ ᾠ ⨾ ὡ ⨾ ὥ ⨾ ὣ ⨾ Ὧ ⨾ ὧ ⨾ ᾧ ⨾ ώ ⨾ ῴ ⨾ ὼ ⨾ ῶ ⨾ ῷ ⨾ ῳ ]
          ◇  [ ᾳ ]
·Vowel = _∈  [ Ε ⨾ ε ⨾ Ἐ ⨾ ἐ ⨾ Ἔ ⨾ ἔ ⨾ Ἑ ⨾ ἑ ⨾ Ἕ ⨾ ἕ ⨾ ἓ ⨾ έ ⨾ ὲ ]
          ◇  [ Ο ⨾ ο ⨾ Ὀ ⨾ ὀ ⨾ Ὄ ⨾ ὄ ⨾ ὁ ⨾ ὅ ⨾ ὃ ⨾ ό ⨾ ὸ ]
          ◇  [ Ᾰ ⨾ ᾰ ⨾ Ῐ ⨾ ῐ ⨾ Ῠ ⨾ ῠ ]
Doubtful = (¬_ ∘ ─Vowel) ∩¹ (¬_ ∘ ·Vowel)
\end{code}
}

\newcommand\prosodyFoot{%
\begin{code}
data Foot : (n : ℕ) → Vec Quantity n → Type where
  ─··  {- dactyl  -}  : Foot 3 (─ ∷ · ∷ · ∷ [])
  ──   {- spondee -}  : Foot 2 (─ ∷ ─ ∷ [])
\end{code}
\begin{code}[hide]
∃∃Foot = ∃ (∃ ∘ Foot)

Feet = List ∃∃Foot
\end{code}
}

\newcommand\prosodyMeter{%
\begin{code}
data Meter : ℕ → ℕ {- feet -} → Type where
  mkPM : (fs : Feet) → Meter (∑₁ fs) (length fs)

Hexameter : ℕ → Type
Hexameter n = Meter n 6
\end{code}
}
