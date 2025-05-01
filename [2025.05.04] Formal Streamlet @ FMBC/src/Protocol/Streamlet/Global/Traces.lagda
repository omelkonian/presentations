\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions
module Protocol.Streamlet.Global.Traces (⋯ : _) (open Assumptions ⋯)
 where
open import Protocol.Streamlet.Block ⋯
open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.Chain ⋯
open import Protocol.Streamlet.Local.State ⋯
open import Protocol.Streamlet.Local.Step ⋯
open import Protocol.Streamlet.Global.State ⋯
open import Protocol.Streamlet.Global.Step ⋯
\end{code}

\begin{code}[hide]
module ALTERNATE:Closures where

  private
    variable x y z : GlobalState
    _⟵_ = flip _⟶_
\end{code}

\newcommand{\agdartc}{%
\begin{AgdaMultiCode}
\begin{code}
  data _↞_ : GlobalState → GlobalState → Type where
\end{code}

\vspace{-3mm}
\begin{minipage}[t]{0.35\textwidth}
 \begin{code}
    _∎ : ∀ x →
      ──────
      x ↞ x
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
    _⟨_⟩⟵_ : ∀ z →
\end{code}

\vspace{-3mm}
\begin{minipage}[t]{0.24\textwidth}
 \begin{code}
      ∙ z ⟵ y
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.24\textwidth}
\begin{code}
      ∙ y ↞ x
\end{code}
\end{minipage}
 \begin{code}
      ────────────────────
      z ↞ x
\end{code}
\end{minipage}
\end{AgdaMultiCode}
}

\begin{code}[hide]
open import Prelude.Closures _⟶_ initGlobalState public
  renaming
    ( _↞—_ to _↞_
    ; _—→⟨_⟩_ to _⟶⟨_⟩_
    ; _←—_ to _⟵_
    ; _⟨_⟩←—_ to _⟨_⟩⟵_
    ; _⟨_∣_⟩←—_ to _⟨_∣_⟩⟵_
    )
  using ( begin_; _∎
        ; StepPreserved; Step⇒Invariant
        ; _—↠_
        ; Trace; TraceProperty; TraceInvariant
        )
\end{code}

\begin{code}[hide]
module Alternate:GP where

  s₀ = initGlobalState
\end{code}

\newcommand{\agdaStateProperty}{%
\begin{code}
  StateProperty = GlobalState → Type
\end{code}
}

\newcommand{\agdaReachable}{%
\begin{code}
  Reachable : StateProperty
  Reachable s = s ↞ s₀
\end{code}
}

\newcommand{\agdaInvariant}{%
\begin{code}
  Invariant : StateProperty → Type
  Invariant P = ∀{s} → Reachable s → P s
\end{code}
}

\begin{code}[hide]
open import Prelude.Closures _⟶_ initGlobalState public
  using (Invariant)

StateProperty = GlobalState → Type

record Step : Type where
  constructor _⊢_
  field  stepArgs  : _ × _ × _ × _ × _
         step      :  let p , e , ls , mm , ls' = stepArgs in
                      p ▷ e ⊢ ls —[ mm ]→ ls'

LocalStepProperty = Step → Type

allLocalSteps : (s′ ↞ s) → List Step
allLocalSteps = λ where  (_ ∎) → []
                         (_ ⟨ LocalStep st  ⟩⟵ tr) → (_ ⊢ st) ∷ allLocalSteps tr
                         (_ ⟨ _             ⟩⟵ tr) → allLocalSteps tr

_∋⋯_ : Trace → LocalStepProperty → Type
(_ , tr) ∋⋯ P = Any P (allLocalSteps tr)
\end{code}
