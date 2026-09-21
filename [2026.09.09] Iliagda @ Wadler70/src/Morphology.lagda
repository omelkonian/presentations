\begin{code}[hide]
module Morphology where

open import Iliagda.Init
\end{code}

\newcommand\morphLetters{%
\begin{AgdaMultiCode}
\begin{code}
data Letter : Type where
  -- vowels
  Α α Ἀ ἀ Ἄ ἄ ἂ Ἆ ἆ Ἁ ἁ Ἅ ἅ ἃ ά ὰ ᾶ ᾷ ᾳ Ᾰ ᾰ : Letter
\end{code}
\begin{code}[hide]
  Ε ε Ἐ ἐ Ἔ ἔ Ἑ ἑ Ἕ ἕ ἓ έ ὲ : Letter
  η Ἠ ἠ Ἤ ἤ ᾔ ἢ ἦ ᾖ ᾐ Ἡ ἡ Ἥ ἥ ᾕ ἣ ἧ ᾗ ή ῄ ὴ ῂ ῆ ῇ ῃ : Letter
  ι Ἰ ἰ Ἴ ἴ ἲ Ἶ ἶ Ἱ ἱ ἵ ἳ ἷ ί ὶ ῖ ϊ ΐ ῒ ῗ Ῐ ῐ : Letter
  Ο ο Ὀ ὀ Ὄ ὄ ὁ ὅ ὃ ό ὸ : Letter
  υ ὐ ὔ ὖ Ὑ ὑ Ὕ ὕ ὓ ὗ ύ ὺ ῦ ϋ ΰ ῢ Ῠ ῠ : Letter
  ω Ὠ ὠ Ὤ ὤ ᾤ ὢ Ὦ ὦ ᾦ ᾠ ὡ ὥ ὣ Ὧ ὧ ᾧ ώ ῴ ὼ ῶ ῷ ῳ : Letter
\end{code}
\vdotsCode
\begin{code}
  -- consonants
  Β β Γ γ Δ δ Ζ ζ Θ θ Κ κ Λ ƛ Μ μ Ν ν Ξ ξ : Letter
\end{code}
\begin{code}[hide]
  Π π Ρ ρ Ῥ ῥ Σ σ ς Τ τ Φ φ Χ χ Ψ ψ : Letter
\end{code}
\vdotsCode
\begin{code}
  -- special symbols
  ᾽  {- apostrophe -}  : Letter
  ϝ  {- digamma    -}  : Letter
\end{code}
\end{AgdaMultiCode}
}

\newcommand\morphPreds{%
\begin{code}
Consonant Vowel Apostrophe Digamma HasDiaeresis : Pred₀ Letter
Consonant = _∈
  ( Β ∷ β ∷ Γ ∷ γ ∷ Δ ∷ δ ∷ Ζ ∷ ζ
\end{code}
\begin{code}[hide]
  ∷ Θ ∷ θ ∷ Κ ∷ κ ∷ Λ ∷ ƛ ∷ Μ ∷ μ ∷ Ν ∷ ν
  ∷ Ξ ∷ ξ ∷ Π ∷ π ∷ Ρ ∷ ρ ∷ Ῥ ∷ ῥ ∷ Σ ∷ σ ∷ ς
  ∷ Τ ∷ τ ∷ Φ ∷ φ ∷ Χ ∷ χ ∷ Ψ ∷ ψ
  ∷ ϝ -- digamma
  ∷ [])
Vowel = _∈
  ( Α ∷ α ∷ Ἀ ∷ ἀ ∷ Ἄ ∷ ἄ ∷ ἂ ∷ Ἆ ∷ ἆ ∷ Ἁ ∷ ἁ ∷ Ἅ ∷ ἅ ∷ ἃ ∷ ά ∷ ὰ ∷ ᾶ ∷ ᾷ ∷ ᾳ ∷ Ᾰ ∷ ᾰ
  ∷ Ε ∷ ε ∷ Ἐ ∷ ἐ ∷ Ἔ ∷ ἔ ∷ Ἑ ∷ ἑ ∷ Ἕ ∷ ἕ ∷ ἓ ∷ έ ∷ ὲ
  ∷ η ∷ Ἠ ∷ ἠ ∷ Ἤ ∷ ἤ ∷ ᾔ ∷ ἢ ∷ ἦ ∷ ᾖ ∷ ᾐ ∷ Ἡ ∷ ἡ ∷ Ἥ ∷ ἥ ∷ ᾕ ∷ ἣ ∷ ἧ ∷ ᾗ ∷ ή ∷ ῄ ∷ ὴ ∷ ῂ ∷ ῆ ∷ ῇ ∷ ῃ
  ∷ ι ∷ Ἰ ∷ ἰ ∷ Ἴ ∷ ἴ ∷ ἲ ∷ Ἶ ∷ ἶ ∷ Ἱ ∷ ἱ ∷ ἵ ∷ ἳ ∷ ἷ ∷ ί ∷ ὶ ∷ ῖ ∷ ϊ ∷ ΐ ∷ ῒ ∷ ῗ ∷ Ῐ ∷ ῐ
  ∷ Ο ∷ ο ∷ Ὀ ∷ ὀ ∷ Ὄ ∷ ὄ ∷ ὁ ∷ ὅ ∷ ὃ ∷ ό ∷ ὸ
  ∷ υ ∷ ὐ ∷ ὔ ∷ ὖ ∷ Ὑ ∷ ὑ ∷ Ὕ ∷ ὕ ∷ ὓ ∷ ὗ ∷ ύ ∷ ὺ ∷ ῦ ∷ ϋ ∷ ΰ ∷ ῢ ∷ Ῠ ∷ ῠ
  ∷ ω ∷ Ὠ ∷ ὠ ∷ Ὤ ∷ ὤ ∷ ᾤ ∷ ὢ ∷ Ὦ ∷ ὦ ∷ ᾦ ∷ ᾠ ∷ ὡ ∷ ὥ ∷ ὣ ∷ Ὧ ∷ ὧ ∷ ᾧ ∷ ώ ∷ ῴ ∷ ὼ ∷ ῶ ∷ ῷ ∷ ῳ
  ∷ [])
Apostrophe = _≡ ᾽
Digamma    = _≡ ϝ
HasDiaeresis = _∈
  ( ϊ ∷ ΐ ∷ ῒ ∷ ῗ
  ∷ ϋ ∷ ΰ ∷ ῢ
  ∷ [])
\end{code}
}

\newcommand\morphWords{%
\begin{code}
Syllable   = List⁺ Letter
Syllables  = Vec Syllable

data Word : ℕ {- syllables -} → Type where
  word : {_ : auto∶ n ≢ 0} → Syllables n → Word n

data Words : ℕ → Type where
  []   : Words 0
  _∷_  : Word n → Words n′ → Words (n + n′)
\end{code}
}

\begin{code}[hide]
Letters = List Letter
unword : Word n → Syllables n
unword (word sys) = sys
\end{code}
