\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Jolteon.Base
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Global.State (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon.Block ⋯
open import Protocol.Jolteon.Message ⋯
open import Protocol.Jolteon.Local.State ⋯

StateMap : Type
StateMap = HonestVec LocalState

TPMessage  = Time × Pid × Message
TPMessages = List TPMessage
\end{code}
\newcommand\globalState{%
\begin{code}
record GlobalState : Type where
  field  currentTime    : Time
         stateMap       : HonestVec LocalState
         networkBuffer  : List (Time × Pid × Message)
         history        : List Message
\end{code}
}
\begin{code}[hide]
open GlobalState public
variable s s′ s″ : GlobalState

initStateMap : StateMap
initStateMap = V.replicate _ initLocalState

initGlobalState : GlobalState
initGlobalState = record
  { currentTime = 0
  ; stateMap    = initStateMap
  ; networkBuffer = []
  ; history = []
  }

instance Def-StateMap     = Default _ ∋ λ where .def → initStateMap
         Def-GlobalState  = Default _ ∋ λ where .def → initGlobalState
         Init-GlobalState = HasInitial _ ∋ λ where .Initial → _≡ initGlobalState

-- Retrieve a replica's local state.
_＠ᵐ_ : StateMap → ∀ p ⦃ _ : Honest p ⦄ → LocalState
sm ＠ᵐ p = pLookup sm p

_＠ᵐᵖ_ : StateMap → HonestPid → LocalState
sm ＠ᵐᵖ hp = pLookup′ sm hp

_＠_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → LocalState
s ＠ p = s .stateMap ＠ᵐ p

_＠ʰ_ : GlobalState → ∀ {p} → Honest p → LocalState
s ＠ʰ hp = pLookup′ (s .stateMap) (_ ,· hp)

_＠ʰᵖ_ : GlobalState → HonestPid → LocalState
s ＠ʰᵖ hp = pLookup′ (s .stateMap) hp

-- Update a replica's local state.
_＠_%=_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → Op₁ LocalState → GlobalState
s ＠ p %= f = record s
  { stateMap = s .stateMap [ p ]%= f }

-- Set a replica's local state.
_＠_≔_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → LocalState → GlobalState
s ＠ p ≔ ls = record s
  { stateMap = s .stateMap [ p ]≔ ls }
\end{code}
