\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Agda.Primitive renaming (Set to Type)

import Data.Maybe as Maybe
open import Data.Maybe.Properties
open import Interface.STS hiding (_⊢_⇀⟦_⟧*_)
open import Relation.Binary.PropositionalEquality

private variable
  C S Sig : Type
  Γ : C
  s s' s'' : S
  b sig : Sig
  sigs : List Sig
\end{code}

In order to deliver on our promise that the specification is also \emph{executable},
there is still some work to be done
given that all transitions have been formulated as relations.

This is precisely the reason we also manually prove that
each and every transition of the previous sections is indeed \emph{computational}:
\begin{code}
record Computational (_⊢_⇀⦇_,X⦈_ : C → S → Sig → S → Type) : Type where
  field  compute          : C → S → Sig → Maybe S
         compute-correct  : compute Γ s b ≡ just s' ⇔ Γ ⊢ s ⇀⦇ b ,X⦈ s'
\end{code}
The definition above captures what it means for a (small-step) relation
to be accurately computed by a function \AgdaField{compute},
which given as input an environment, source state, and signal, outputs
the resulting state or an error for invalid transitions.
%
Most importantly, such a function must be \emph{sound} and \emph{complete}:
it does not return output states that are not related,
and, \emph{vice versa}, all related states are successfully returned.
%
An alternative interpretation is that this rules out \emph{non-determinism}
across all ledger transitions,
\ie there cannot be two distinct states arising from the same inputs.

There is one last obstacle that hinders execution:
we have leveraged Agda's module system\footnote{\url{
https://agda.readthedocs.io/en/v2.6.4/language/module-system.html\#parameterised-modules
}} to parameterize our specification
over some abstract types and functions that we assume as given,
\eg the cryptographic primitives.
%
As a final step,
we instantiate these parameters with concrete definitions,
either by manually providing them within Agda,
or deferring to the Haskell \emph{foreign function interface}
to reuse existing Haskell ones that have no Agda counterpart.

Equipped with a fully concrete specification
and the \Computational proofs for each relation,
it is finally possible to generate executable Haskell code
using Agda's MAlonzo compilation backend.\footnote{\url{
https://agda.readthedocs.io/en/v2.6.4/tools/compilers.html\#ghc-backend
}}
%
The resulting Haskell library is then deployed as part of
the automated testing setup for the Cardano ledger in production,
so as to ensure the developers have faithfully implemented the specification.
%
This is made possible
by virtue of the implementation mirroring the specification's structure
to define transitions,
which one can then test by randomly generating environments/states/signals,
and executing both state machines on these same random inputs
to compare the final results for \emph{conformance}.

One small caveat remains though:
production code might use different data structures,
mainly for reasons of \emph{performance},
which are not isomorphic to those used in the specification
and might require non-trivial translation functions
and notions of equality to perform the aforementioned tests.
%
In the future, we plan to also formalize these more efficient representations
in Agda and prove that soundness is preserved regardless.
