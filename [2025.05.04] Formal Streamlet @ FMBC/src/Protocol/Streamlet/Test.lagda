\begin{code}[hide]
module Protocol.Streamlet.Test where

open import Prelude
open import Hash
open import DummyHashing
open import Protocol.Streamlet.Assumptions

open import Protocol.Streamlet.Test.Core

_ =
\end{code}
\newcommand\exampleTraceA{%
\begin{code}
  begin
    initGlobalState
  ⟶⟨ Propose? 𝕃 [] [] ⟩                                      -- leader proposes b₁
    record  { e-now          = 1
            ; history        = [ p₁ ]
            ; networkBuffer  = [  [ 𝔸 ∣ p₁ ⟩ ⨾ [ 𝔹 ∣ p₁ ⟩ ]
            ; stateMap       = [  {- 𝕃 -} ⦅ Voted , [ p₁ ]  , [] , [] ⦆
                               ⨾  {- 𝔸 -} ⦅ Ready , []      , [] , [] ⦆
                               ⨾  {- 𝔹 -} ⦅ Ready , []      , [] , [] ⦆ ]}
  ⟶⟨ Deliver? [ 𝔹 ∣ p₁ ⟩ ⟩
    _
\end{code}
}
\newcommand\exampleTraceB{%
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
\begin{code}
  ⟶⟨ Vote? 𝔹 [] [] ⟩                                         -- b₁ becomes notarized
    record  { e-now          = 1
            ; history        = [ v₁ ⨾ p₁ ]
            ; networkBuffer  = [ [ 𝔸 ∣ p₁ ⟩ ⨾ [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ v₁ ⟩  ]
            ; stateMap       = [  ⦅ Voted , [ p₁ ]       , [] , [] ⦆
                               ⨾  ⦅ Ready , []           , [] , [] ⦆
                               ⨾  ⦅ Voted , [ v₁ ⨾ p₁ ]  , [] , [] ⦆ ]}
\end{code}
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
}
\begin{code}[hide]
  ⟶⟨ AdvanceEpoch ⟩
    record
    { e-now         = 2
    ; history       = [ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾ [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ v₁ ⟩  ]
    ; stateMap      = [ ⦅ Ready , [ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Propose? 𝕃 [] [] ⟩                                      -- leader proposes b₂
    record
    { e-now         = 2
    ; history       = [ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Deliver? [ 𝔸 ∣ p₂ ⟩ ⟩
    record
    { e-now         = 2
    ; history       = [ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ]  , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [ p₂ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Vote? 𝔸 [] [] ⟩                                         -- b₂ becomes notarized
    record
    { e-now         = 2
    ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆ ]}
  ⟶⟨ AdvanceEpoch ⟩
    record
    { e-now         = 3
    ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Deliver? [ 𝕃 ∣ v₁ ⟩ ⟩
   record
   { e-now         = 3
   ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
   ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ]
   ; stateMap      = [ ⦅ Ready , [ p₂ ⨾ p₁ ] , [ v₁ ] , [] ⦆
                     ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                     ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                     ]}
  ⟶⟨ Register? 𝕃 v₁ ⟩
   record
   { e-now         = 3
   ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
   ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ]
   ; stateMap      = [ ⦅ Ready , [ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                     ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                     ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                     ]}
  ⟶⟨ Propose? 𝕃 [ b₁ ] [] ⟩                                  -- leader proposes b₃
    record
    { e-now         = 3
    ; history       = [ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔹 ∣ p₃ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Deliver? [ 𝔹 ∣ p₃ ⟩ ⟩
    record
    { e-now         = 3
    ; history       = [ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [ p₃ ] , [] ⦆
                      ]}
  ⟶⟨ Vote? 𝔹 [ b₁ ] [] ⟩                                     -- b₃ becomes notarized
    record
    { e-now         = 3
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ AdvanceEpoch ⟩
    record
    { e-now         = 4
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ AdvanceEpoch ⟩
    record
    { e-now         = 5
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Deliver? [ 𝕃 ∣ v₂ ⟩ ⟩
    record
    { e-now         = 5
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₂ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Register? 𝕃 v₂ ⟩
    record
    { e-now         = 5
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Propose? 𝕃 [ b₂ ] [] ⟩                                  -- leader proposes b₅
    record
    { e-now         = 5
    ; history       = [ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Deliver? [ 𝔸 ∣ p₅ ⟩ ⟩
    record
    { e-now         = 5
    ; history       = [ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [ p₅ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Vote? 𝔸 [ b₂ ] [] ⟩                                     -- b₅ becomes notarized
    record
    { e-now         = 5
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝕃 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ AdvanceEpoch ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝕃 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Deliver? [ 𝕃 ∣ v₃ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝕃 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₃ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Deliver? [ 𝕃 ∣ v₅ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₃ ⨾ v₅ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Register? 𝕃 v₃ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₅ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Register? 𝕃 v₅ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  ⟶⟨ Propose? 𝕃 [ b₅ ⨾ b₂ ] [] ⟩                             -- leader proposes b₆
    record
    { e-now         = 6
    ; history       = [ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔸 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  ⟶⟨ Deliver? [ 𝔸 ∣ p₆ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [ p₆ ] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  ⟶⟨ Vote? 𝔸 [ b₅ ⨾ b₂ ] [] ⟩                                -- b₆ becomes notarized
    record
    { e-now         = 6
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝕃 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Voted , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  ⟶⟨ AdvanceEpoch ⟩
    record
    { e-now         = 7
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝕃 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Ready , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  ⟶⟨ Deliver? [ 𝕃 ∣ v₆ ⟩ ⟩
    record
    { e-now         = 7
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Ready , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₆ ] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  ⟶⟨ Register? 𝕃 v₆ ⟩
    record
    { e-now         = 7
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
\end{code}
\newcommand\exampleTraceC{%
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
\begin{code}
  ⟶⟨ Propose? 𝕃 [ b₆ ⨾ b₅ ⨾ b₂ ] [] ⟩                        -- leader proposes b₇
\end{code}
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
\begin{code}[hide]
    record
    { e-now         = 7
    ; history       = [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ⨾ [ 𝔸 ∣ p₇ ⟩ ⨾ [ 𝔹 ∣ p₇ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  ⟶⟨ Deliver? [ 𝔸 ∣ p₇ ⟩ ⟩
    record
    { e-now         = 7
    ; history       = [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ p₇ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [ p₇ ] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
\end{code}
\begin{code}
  ⟶⟨ Vote? 𝔸 [ b₆ ⨾ b₅ ⨾ b₂ ] [] ⟩                           -- b₇ becomes notarized
\end{code}
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
}
\newcommand\exampleTraceD{%
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
\begin{code}[hide]
    record
    { e-now         = 7
    ; history       = [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾  [ 𝔸 ∣ v₁ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ p₇ ⟩ ]
                   ++  [ [ 𝕃 ∣ v₇ ⟩ ⨾ [ 𝔹 ∣ v₇ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Voted , [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
\end{code}
\begin{code}
  ⟶⟨ Finalize? 𝔸 [ b₆ ⨾ b₅ ⨾ b₂ ] b₇ ⟩                       -- b₆ becomes finalized
    record  { e-now          =  7
            ; history        =  [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
            ; networkBuffer  =  _
            ; stateMap       =  [  ⦅ Voted , _ , [] ,  []                ⦆
                                ⨾  ⦅ Voted , _ , [] ,  [ b₆ ⨾ b₅ ⨾ b₂ ]  ⦆
                                ⨾  ⦅ Ready , _ , [] ,  []                ⦆ ]}
  ∎
\end{code}
}
