\begin{code}[hide]
module Synizesis where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Dec.Core

FirstVowel LastVowel : Pred₀ Syllable
FirstVowel = Vowel ∘ head
LastVowel  = Vowel ∘ last
\end{code}

\newcommand\synizesisCoalescing{%
\begin{code}
record Merge (sy sy′ : Syllable) : Type where
  field
    vowels       : LastVowel sy × FirstVowel sy′
    .¬diaeresis  : ¬ HasDiaeresis (head sy′)

_⁀_ : Syllable → Syllable → Syllable
_⁀_ = L.NE._⁺++⁺_
\end{code}
}

\newcommand\synizesis{%
\begin{AgdaMultiCode}
\begin{code}
-- when all else fails, merge two adjacent vowel syllables and rescan (586)
data _-synizizes*-_ : Syllables n → Syllables n′ → Type
\end{code}
\begin{code}[hide]
private _~_ = _-synizizes*-_
data _-synizizes*-_
\end{code}
\begin{code}
 where
 []   : [] ~ []
 _∷_  : ∀ sy → sys ~ sys′ → (sy ∷ sys) ~ (sy ∷ sys′)
 _∺_  : Merge sy sy′ → sys ~ sys′ → (sy ∷ sy′ ∷ sys) ~ (sy ⁀ sy′ ∷ sys′)
\end{code}
\end{AgdaMultiCode}
}
