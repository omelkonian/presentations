\begin{code}[hide]
module LevelThree where

open import Iliagda.Init hiding (∅)
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Prosody.Rules.Level3
  hiding ( Context; ∅; inner; outer; ctx; ctx′; toLetters
         ; module QuantityRules; _⊢_~∗_; _⊢_≁∗_; _⊢_~?_
         ; Complies-Sy-MQ )
\end{code}

\newcommand\levelThreeCtx{%
\begin{code}
data Context : Type where
  ∅      : Context
  inner  : Syllable → Context
  outer  : ∃ Word → Context
\end{code}
}

\begin{code}[hide]
toLetters : Context → Letters
toLetters = λ where
  ∅ → []
  (inner sy) → toList sy
  (outer (_ , w)) → unsyllables (unword w)
\end{code}

\newcommand\levelThree{%
\begin{AgdaMultiCode}
\begin{code}
module _ (ctx : Flat Quantity × Context) (let mq , next = ctx) where
\end{code}
\vdots
\begin{code}[hide]
  FollowedBy FollowedByOuter : (Q : Letters → Type) {P : Letter → Type} {ls : Letters} →
    Any P ls → Type
  FollowedBy Q = λ where
    (here {xs = sys} _) → Q (sys ++ toLetters next)
    (there p) → FollowedBy Q p
  FollowedByOuter Q = λ where
    (here {xs = []} _) → Q (toLetters next)
    (here {xs = _ ∷ _} _) → ⊥
    (there p) → FollowedByOuter Q p
\end{code}
\begin{code}
  data _~∗_ : Syllable → Quantity → Type where
\end{code}
\medskip
\begin{minipage}[t]{.62\textwidth}
\begin{code}
    -- long by position
    [522] :
      (v∈ : Any Vowel sy) →
      ∙ FollowedBy (  StartsWithDoubleConsonant
                   ∪¹ StartsWithTwoConsonants ) v∈
        ─────────────────────────────────────────
        sy ~∗ ─

    -- (572) long vowels may be shortened
    -- before another vowel
    [1173] :
      (v∈ : Any Vowel sy) →
      ∙ mq ≡ single ─
      ∙ LastAny v∈
      ∙ FollowedBy StartsWithVowel v∈
        ─────────────────────────────
        sy ~∗ q

\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}[t]{.32\textwidth}
\vspace{1cm}
\begin{code}
    -- mutes followed by liquids make a *common* syllable
    [524] :
      (v∈ : Any Vowel sy) →
      ∙ mq ≡ single ·
      ∙ FollowedByInner MuteThenLiquid v∈
      ⊎ FollowedByOuter MuteThenLiquid v∈
        ─────────────────────────────────
        sy ~∗ q
\end{code}
\end{minipage}
\end{AgdaMultiCode}
\begin{code}[hide]
  _≁∗_ = λ x y → ¬ (x ~∗ y)
\end{code}
}

\newcommand\levelThreeQ{%
\begin{code}

  data _~?_ : Syllable → Flat Quantity → Type where

    ambiguous :
      (∀ q → sy ≁∗ q)
      ───────────────
      sy ~? none

    ambivalent :
      ∙ sy ~∗ ─
      ∙ sy ~∗ ·
        ─────────
        sy ~? all

    certain :
      ∙ sy ~∗ q
      ∙ sy ≁∗ (! q)
        ──────────────
        sy ~? single q
\end{code}
}
