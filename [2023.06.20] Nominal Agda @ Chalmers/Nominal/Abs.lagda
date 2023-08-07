\documentclass[main]{subfiles}
\begin{document}
\section*{Nominal/Abs.agda}
\begin{code}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module Nominal.Abs (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Abs.Base Atom public
open import Nominal.Abs.Lift Atom public
open import Nominal.Abs.Support Atom public
open import Nominal.Abs.Product Atom public
\end{code}
\end{document}
