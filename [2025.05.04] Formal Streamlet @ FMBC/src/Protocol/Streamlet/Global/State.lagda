\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Global.State (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.State ⋯
open import Protocol.Streamlet.Local.Chain ⋯

StateMap : Type
\end{code}

\newcommand\globalState{%
\begin{AgdaMultiCode}
\begin{code}
record GlobalState : Type where
\end{code}
\begin{code}[hide]
  constructor mkGlobalState
\end{code}

\vspace{-15pt}
\hspace{1em}
\begin{minipage}[t]{.35\textwidth}
\begin{code}
  field  e-now     : Epoch
         stateMap  : StateMap
\end{code}
\end{minipage}%
\begin{minipage}[t]{.35\textwidth}
\begin{code}
         networkBuffer  : List Envelope
         history        : List Message
\end{code}
\end{minipage}
\end{AgdaMultiCode}
\vfill\hrule\vfill
\begin{code}
StateMap = HonestVec LocalState
\end{code}
}

\begin{code}[hide]
open GlobalState public
variable s s′ s″ : GlobalState

initStateMap : StateMap
initStateMap = V.replicate _ initLocalState

initGlobalState : GlobalState
initGlobalState = mkGlobalState 1 initStateMap [] []

instance
  Def-StateMap     = Default _ ∋ λ where .def → initStateMap
  Def-GlobalState  = Default _ ∋ λ where .def → initGlobalState
  Init-GlobalState = HasInitial _ ∋ λ where .Initial → _≡ initGlobalState

_＠_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → LocalState
s ＠ p = pLookup (s .stateMap) (p ,· it)

_＠_≔_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → LocalState → GlobalState
s ＠ p ≔ ls = record s
  { stateMap = s .stateMap [ p ,· it ]≔ ls }

updateLocal : ∀ p ⦃ _ : Honest p ⦄ → LocalState → Op₁ GlobalState
updateLocal p ls s = s ＠ p ≔ ls
\end{code}
