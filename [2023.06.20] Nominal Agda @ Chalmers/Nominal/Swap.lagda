\documentclass[main]{subfiles}
\begin{document}
\section*{Nominal/Swap.agda}
\begin{code}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module Nominal.Swap (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap.Base         Atom public
open import Nominal.Swap.Derive       Atom public
open import Nominal.Swap.Equivariance Atom public
\end{code}
\end{document}
