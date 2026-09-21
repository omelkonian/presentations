\begin{code}[hide]
module LevelFour where

open import Iliagda.Init; open import Prelude.Vectors
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Reading
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level2
open import Iliagda.Prosody.Rules.Level3

private variable x : X
\end{code}
\newcommand\levelFourMasks{%
\begin{code}
data _-masks-_ {X : Type} : Flat X → X → Type where
  none    : none      -masks- x
  all     : all       -masks- x
  single  : single x  -masks- x

_-masks*-_ : Vec (Flat X) n → Vec X n → Type
_-masks*-_ = VPointwise _-masks-_
\end{code}
\begin{code}[hide]
infix 2 _~ᵐ_
\end{code}
}

\newcommand\levelFourFeet{%
\begin{code}
data _~ᵐ_ : Words n × Vec Quantity n → Meter n m → Type where

  [] :
    ───────────────────
    [] , [] ~ᵐ mkPM []

  spondee :
    dropSys 2 ws , qs ~ᵐ pm
    ──────────────────────────────
    ws , ─  ∷ ─ ∷ qs ~ᵐ ── ∷ᵖᵐ pm

  dactyl :
    dropSys 3 ws , qs ~ᵐ pm
    ───────────────────────────────────
    ws , ─  ∷ · ∷ · ∷ qs ~ᵐ ─·· ∷ᵖᵐ pm
\end{code}
}

\newcommand\levelFourBend{%
\begin{code}
  -- lengthen by thesis
  [1168] : let sy′ = firstSy ws in
    ∙ EndsWith    [ Vowel ⨾ Consonant ]  (toList sy)
    ∙ BeginsWith  [ Vowel ]              (toList sy′)
    ∙ word [ sy ] ∷ ws , ─ ∷ qs ~ᵐ pm
      ──────────────────────────────────────────
      word [ sy ] ∷ ws , · ∷ qs ~ᵐ pm

  -- Whenever a word ends within a foot, it is called *caesura*. (1185)
  [1167/1a] :
    word [ sy ] ∷ ws , ─ ∷ qs ~ᵐ pm
    ────────────────────────────────
    word [ sy ] ∷ ws , · ∷ qs ~ᵐ pm

  -- Whenever the end of a word coincides with the end of a foot, it is called *diaeresis*. (1188)
  [1167/1b] :
    ∙ Split 2 ws
    ∙ dropSys 2 ws , qs ~ᵐ pm
      ───────────────────────────────
      ws , ─ ∷ · ∷ qs ~ᵐ (── ∷ᵖᵐ pm)
\end{code}
}

\newcommand\levelFourReify{%
\begin{code}[hide]
instance
  Complies-Qs-PM : (Words n × Vec Quantity n) -compliesWith- Meter n m
  Complies-Qs-PM ._~_ = _~ᵐ_

  Complies-MQs-HM : (Words n × Quantities n) -compliesWith- Hexameter n
  Complies-MQs-HM ._~_ = _~′_
    module ∣Complies-MQs-HM∣ where
\end{code}
\begin{code}
      -- (1180) There are six feet to the verse...
      data _~′_ : Words n × Quantities n → Hexameter n → Type where
        reify : {mqs : Quantities n} → let mkLastLong = _≔ₙ⟨ Hex>0 hm ⟩ single ─ in
          -- (1184) The last syllable of a verse is considered long (due to pause)
          ∙ mkLastLong mqs -masks*- qs
          ∙ ws , qs ~ᵐ hm
            ──────────────────────────
            (ws , mqs) ~′ hm
\end{code}
}
\begin{code}[hide]
private
  _~⁴_ : Words n × Quantities n → Hexameter n → Type
  _~⁴_ {n = n} = ∣Complies-MQs-HM∣._~′_ {n = n}
instance
\end{code}

\newcommand\pipeline{%
\begin{code}[hide]
  Complies-Ws-HM : Words n -compliesWith- Hexameter n′
  Complies-Ws-HM ._~_ = _~′_
    module ∣Complies-Ws-HM∣ where
\end{code}
\begin{code}
    data _~′_ : Words n → Hexameter n′ → Type where

      _▷_≫⟨_⟩≫_≫_ : ∀ {ws wsʳ : Words n} {sys′ : Syllables n′} {hm : Hexameter n′}
        → ws -reads- wsʳ
        → wsʳ ~² mqs₂
        -- [586] synizesis -----------------------
        → (syn : unwords wsʳ -synizizes*- sys′) →
        let
          ws′   = synizizeWords wsʳ syn
          mqs₂′ = synizize syn mqs₂
        in
        ------------------------------------------
        ∙ (ws′ , mqs₂′) ~³ mqs₃
        ∙ (ws′ , mqs₂′ ⊗ mqs₃) ~⁴ hm
          ────────────────────────────
          ws ~′ hm
\end{code}
}

\newcommand\derivation{%
\begin{code}
Derivation : Words n → Type
Derivation ws = ∃ λ n′ → ∃ λ (hm : Hexameter n′) → ws ~ hm

Derivations : Words n → Type
Derivations ws = List (Derivation ws)
\end{code}
}
