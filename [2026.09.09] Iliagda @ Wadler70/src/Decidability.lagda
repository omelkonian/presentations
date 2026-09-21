\begin{code}[hide]
module Decidability where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Rules.Core
  hiding (Enumeration; allBs; sound; complete)
open import Iliagda.Prosody.Rules.Level4
import Iliagda.Prosody.Rules.Level4.Dec as L4D
\end{code}

\newcommand\enumeration{%
\begin{code}
record Enumeration (_~_ : A → B → Type) : Type where
  field
    allBs     : A → List B
    sound     : ∀ {a b} → b ∈ allBs a → a ~ b
    complete  : ∀ {a b} → a ~ b → b ∈ allBs a
\end{code}
}

\newcommand\allHexameters{%
\begin{code}
allHexameters :
  (smqs : Words n × Quantities n) →
  ∃ λ (hms : List (Hexameter n)) →
      (∀ {hm} → hm ∈ hms → smqs ~ hm)
    × (∀ {hm} → smqs ~ hm → hm ∈ hms)
\end{code}
\begin{code}[hide]
allHexameters = L4D.allHexameters
\end{code}
}
