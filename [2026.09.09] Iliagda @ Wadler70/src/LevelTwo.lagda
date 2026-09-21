\begin{code}[hide]
module LevelTwo where

open import Iliagda.Init
open import Prelude.Vectors

open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Lexicon
open import Iliagda.Prosody.Rules.Level2
  hiding (_⊨_~%′_; _⊨_~%_; _~ʷ_; Complies-W-MQs)

infix 1 _⊨_~%′_ _⊨_~%_
\end{code}

\newcommand\levelTwo{%
\begin{AgdaMultiCode}
\begin{code}
data _⊨_~%′_ : Quantities n → Syllables n → Op₁ (Quantities n) → Type where
\end{code}
\medskip
\begin{minipage}[t]{.48\textwidth}
\begin{code}

  -- The vowel of the ultima in every
  -- word having the circumflex on
  -- the penult is short (545).
  [1160] :
    InPenult (Any HasCircumflex) sys
    ────────────────────────────────
    mqs ⊨ sys ~%′ (_≔ₙ single ·)

  -- If a long penult has the acute
  -- accent, then the ultima must
  -- be long also.
  [1161] :
    ∙ InPenult (_≡ single ─)   mqs
    ∙ InPenult (Any HasAcute)  sys
      ───────────────────────────
      mqs ⊨ sys ~%′ (_≔ₙ single ─)

\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}[t]{.48\textwidth}
\begin{code}
  -- If the ultima is short and the
  -- penult has the acute accent, then
  -- the penult must be short also.
  [1162] :
    ∙ InUlt     (_≡ single ·)   mqs
    ∙ InPenult  (_≢ single ─)   mqs
    ∙ InPenult  (Any HasAcute)  sys
      ─────────────────────────────
      mqs ⊨ sys ~%′ (_≔ₙ₋₁ single ·)

  -- If the antepenult has the accent,
  -- the vowel of the ultima must be
  -- short (544).
  [1163] :
    InAntepenult (Any HasAccent) sys
    ────────────────────────────────
    mqs ⊨ sys ~%′ (_≔ₙ single ·)
\end{code}
\end{minipage}
\end{AgdaMultiCode}
}

\newcommand\levelTwoExc{%
\begin{AgdaMultiCode}
\begin{code}
data _⊨_~%_ : Quantities n → Syllables n → Op₁ (Quantities n) → Type where
\end{code}
\medskip
\begin{minipage}[t]{.42\textwidth}
\begin{code}

  [1164] :
    EndsInFinalDiphthong sys
    ────────────────────────
    mqs ⊨ sys ~% id

  [574] :
    ApparentException sys
    ─────────────────────
    mqs ⊨ sys ~% id

  -- (575/583) Elision
  -- has taken place.
  [575] :
    EndsInApostrophe sys
    ────────────────────
    mqs ⊨ sys ~% id

\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}[t]{.52\textwidth}
\begin{code}
  fromBelow : ∀ {f} →
    ∙ ¬ EndsInFinalDiphthong sys
    ∙ ¬ ApparentException sys
    ∙ ¬ EndsInApostrophe sys
    ∙ SingleAccents sys
    ∙ mqs ⊨ sys ~%′ f
      ───────────────────────────
      mqs ⊨ sys ~% f

  noop :
    ∙ (¬ SingleAccents sys)
    ⊎ (∀ {f} → ¬ (mqs ⊨ sys ~%′ f))
      ─────────────────────────────────
      mqs ⊨ sys ~% id
\end{code}
\end{minipage}
\end{AgdaMultiCode}
}

\newcommand\levelTwoWord{%
\begin{code}
data _~ʷ_ : Word n → Quantities n → Type where

  𝟙-then-L-then-𝟚 : ∀ {f g} → let sys = unword w in
    ∙ sys ~ mqs
    ∙ sys ~L f
    ∙ f mqs ⊨ sys ~% g
      ────────────────
      w ~ʷ g (f mqs)
\end{code}
}
