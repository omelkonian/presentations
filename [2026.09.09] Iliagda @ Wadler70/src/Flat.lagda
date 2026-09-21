\begin{code}[hide]
module Flat where

open import Iliagda.Init
open import Iliagda.Prosody.Core using (Quantity; ·; ─)

private variable x : X
\end{code}

\newcommand\flatQ{%
\begin{code}
data Flat (A : Type) : Type where
  single  : A → Flat A
  none    : Flat A
  all     : Flat A

Quantities : ℕ → Type
Quantities = Vec (Flat Quantity)
\end{code}
}

\newcommand\flatCombine{%
\begin{code}
_⊗₁_ : Op₂ $ Flat Quantity
_⊗₁_ = λ where
  (single _)  (single q)  → single q  -- RIGHT BIASED
  (single q)  none        → single q
  (single _)  all         → all
  none        mq          → mq
  all         mq          → mq

_⊗_ : Op₂ $ Quantities n
_⊗_ = V.zipWith _⊗₁_
\end{code}
}

\newcommand\masks{%
\begin{code}
data _-masks-_ {X : Type} : Flat X → X → Type where
  none    : none       -masks- x
  all     : all        -masks- x
  single  : single x   -masks- x
\end{code}
}
