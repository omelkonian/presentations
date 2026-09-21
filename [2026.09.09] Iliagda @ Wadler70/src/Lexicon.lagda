\begin{code}[hide]
module Lexicon where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
\end{code}

\newcommand\lexiconEntry{%
\begin{code}
data Locus : Type where
  from-start from-end : ℕ → Locus

data Mode : Type where
  exact   : Locus → Mode
  prefix  : ℕ → Mode

record Entry : Type where
  constructor mkEntry
  field  key   : Letters
         mode  : Mode
         qty   : Quantity
\end{code}
}

\newcommand\lexicon{%
\begin{code}
lexicon : List Entry
lexicon
  = mkEntry [ ἀ ⨾ μ ⨾ φ ⨾ ι ]  (prefix 1)            ·
  ∷ mkEntry [ ὀ ⨾ ξ ⨾ ὺ ]      (exact $ from-end 0)  ·
  ∷ mkEntry [ ἔ ⨾ ρ ⨾ γ ⨾ α ]  (exact $ from-end 0)  ·
\end{code}
\begin{code}[hide]
  ∷ mkEntry [ Ἀ ⨾ φ ⨾ ρ ⨾ ο ⨾ δ ⨾ ί ⨾ τ ] (prefix 0) ·
  ∷ mkEntry [ ἀ ⨾ μ ⨾ φ ⨾ ὶ ] (prefix 1) ·
  ∷ mkEntry [ ἀ ⨾ ƛ ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ῥ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ ῥ ⨾ ά ] (exact (from-end 0)) ·
  ∷ mkEntry [ π ⨾ τ ⨾ ε ⨾ ρ ⨾ ό ⨾ ε ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ δ ⨾ ο ⨾ υ ⨾ ρ ⨾ ὶ ] (exact (from-end 0)) ·
  ∷ mkEntry [ π ⨾ ο ⨾ ƛ ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἄ ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ κ ⨾ α ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἐ ⨾ ƛ ⨾ ε ⨾ ε ⨾ ι ⨾ ν ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἐ ⨾ σ ⨾ σ ⨾ ι ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἐ ⨾ σ ⨾ τ ⨾ ὶ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ὅ ⨾ θ ⨾ ι ] (exact (from-end 0)) ·
  ∷ mkEntry [ ε ⨾ ἰ ⨾ ν ⨾ ὶ ] (exact (from-end 0)) ·
  ∷ mkEntry [ γ ⨾ υ ⨾ μ ⨾ ν ⨾ ω ⨾ θ ⨾ έ ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ τ ⨾ ε ⨾ ι ⨾ χ ⨾ ε ⨾ σ ⨾ ι ⨾ π ⨾ ƛ ⨾ ῆ ⨾ τ ⨾ α ] (exact (from-start 2)) ·
  ∷ mkEntry [ ἀ ⨾ β ⨾ ρ ⨾ ό ⨾ τ ⨾ η ] (exact (from-start 0)) ·
  ∷ mkEntry [ ἀ ⨾ β ⨾ ρ ⨾ ο ⨾ τ ⨾ ά ⨾ ξ ⨾ ο ⨾ μ ⨾ ε ⨾ ν ] (exact (from-start 0)) ·
  ∷ mkEntry [ ἀ ⨾ ν ⨾ δ ⨾ ρ ⨾ ο ⨾ τ ⨾ ῆ ⨾ τ ] (prefix 0) ·
  ∷ []
\end{code}
}

\newcommand\reading{%
\begin{code}[hide]
data Reading : Type where
  unwritten : Letters
            → Letter
            → ℕ  -- which syllable in the word
            → ℕ  -- which position in the syllable
            → Reading
\end{code}
\begin{code}
readings : List Reading
readings
  = unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ ε ⨾ ν ]              ϝ 1 1
  ∷ unwritten [ Β ⨾ ο ⨾ ρ ⨾ έ ⨾ ῃ ]                      ρ 0 2
  ∷ unwritten [ φ ⨾ ι ⨾ ƛ ⨾ ο ⨾ μ ⨾ ε ⨾ ι ⨾ δ ⨾ ὴ ⨾ ς ]  μ 1 2
\end{code}
\begin{code}[hide]
  ∷ unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ ε ] ϝ 1 1
  ∷ unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ α ⨾ ς ] ϝ 1 1
  ∷ unwritten [ ἐ ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ τ ⨾ ε ] ϝ 1 1
  ∷ unwritten [ ὑ ⨾ π ⨾ έ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ α ⨾ ν ] ϝ 2 1
  ∷ unwritten [ ὑ ⨾ π ⨾ ο ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ ν ⨾ τ ⨾ ε ⨾ ς ] ϝ 2 1
  ∷ unwritten [ ὑ ⨾ π ⨾ ο ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ ς ] ϝ 2 1
  ∷ unwritten [ Β ⨾ ο ⨾ ρ ⨾ έ ⨾ η ⨾ ς ] ρ 0 2
  ∷ unwritten [ φ ⨾ ι ⨾ ƛ ⨾ ο ⨾ μ ⨾ ε ⨾ ι ⨾ δ ⨾ ή ⨾ ς ] μ 1 2
  ∷ unwritten [ ἐ ⨾ ƛ ⨾ ί ⨾ σ ⨾ σ ⨾ ε ⨾ τ ⨾ ο ] ἰ 0 1
  ∷ []
\end{code}
}
