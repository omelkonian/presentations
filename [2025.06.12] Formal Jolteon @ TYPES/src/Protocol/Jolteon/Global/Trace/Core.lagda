\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude

open import Protocol.Jolteon.Base
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Global.Trace.Core (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon.Block ⋯
open import Protocol.Jolteon.Message ⋯
open import Protocol.Jolteon.Local.Step ⋯
open import Protocol.Jolteon.Local.State ⋯
open import Protocol.Jolteon.Global.State ⋯
open import Protocol.Jolteon.Global.Step ⋯
\end{code}
\newcommand{\agdartc}{%
\begin{code}[hide]
module ALTERNATE:Closures where
  private variable x y z : GlobalState
\end{code}
\begin{AgdaMultiCode}
\begin{code}
  data _—↠_ : GlobalState → GlobalState → Type where
\end{code}

\vspace{-3mm}
\begin{minipage}[t]{0.35\textwidth}
 \begin{code}
    _∎ : ∀ x →
      ──────
      x —↠ x
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
    _—→⟨_⟩_ : ∀ x →
\end{code}

\vspace{-3mm}
\begin{minipage}[t]{0.24\textwidth}
 \begin{code}
      ∙ x —→ y
 \end{code}
 \hfill
\end{minipage}%
\begin{minipage}[t]{0.24\textwidth}
\begin{code}
      ∙ y —↠ z
\end{code}
\end{minipage}
 \begin{code}
      ────────────────────
      x —↠ z
\end{code}
\end{minipage}
\end{AgdaMultiCode}
}
\newcommand\reachable{%
\begin{code}[hide]
  private s₀ = initGlobalState
\end{code}
\begin{code}
  Reachable : GlobalState → Type
  Reachable s = s₀ —↠ s₀
\end{code}
}

\begin{code}[hide]
open import Prelude.Closures _—→_ public
  using ( begin_; _∎ ; _↞—_; _⟨_⟩←—_; _⟨_∣_⟩←—_ ; ↞—-trans; ↞—-trans-stop
        ; _—↠_; —↠-trans; _—→⟨_⟩_; _—→⟨_∣_⟩_; _`—→⟨_⟩_
        ; factor; factor⁺; Reachable-inj
        ; Reachable; Invariant; StepPreserved; Step⇒Invariant
        ; Trace; TraceProperty; TraceInvariant
        ; viewLeft; viewRight; viewLeft∘viewRight
        ; viewLeft∘—↠-trans
        ; states⁺; states; states⁺-↞—; states-↞—; states⁺∘viewLeft
        ; head≡; first∈
        ; steps; steps-trans; steps˘; steps˘-trans
        ; module EqReasoning; module LeqReasoning
        )
  renaming (_←—_ to _¹←—_; Step to GStep)

Rs₀ : Reachable initGlobalState
Rs₀ = _ , refl , (initGlobalState ∎)

StateProperty = GlobalState → Type

∃Step : Type
∃Step = ∃ λ s → ∃ λ s′ → s —→ s′

record Step : Type where
  constructor _⊢_
  field
    stepArgs : _ × _ × _ × _ × _
    theStep  : let p , t , ls , menv , ls′ = stepArgs in
               p ⦂ t ⊢ ls — menv —→ ls′
    ⦃ hp ⦄ : Honest (stepArgs .proj₁)
open Step public
  hiding (hp)

-- doStep : Step → Op₁ GlobalState
-- doStep st s = let p , _ , _ , menv , ls′ = st .stepArgs in
--   broadcast menv (s ＠ p ≔ ls′)

LocalStepProperty = Step → Type

allLocalSteps : (s′ ↞— s) → List Step
allLocalSteps = λ where
  (_ ∎) → []
  (_ ⟨ LocalStep st ⟩←— tr) → (_ ⊢ st) ∷ allLocalSteps tr
  (_ ⟨ _ ⟩←— tr) → allLocalSteps tr

_∋⋯_ : Reachable s → LocalStepProperty → Type
(_ , _ , tr) ∋⋯ P = Any P (allLocalSteps tr)

-- ** steps in non-well-rooted traces

_∋⋯′_ : (s′ ↞— s) → LocalStepProperty → Type
tr ∋⋯′ P = Any P (allLocalSteps tr)

{- [TODO] generalize with typeclass:

record HasLocalSteps (A : Type) : Type where
  allLocalSteps : A → List Step

_∋⋯_ : A → ⦃ _ : HasLocalSteps A ⦄ → LocalStepProperty → Type
tr ∋⋯ P = Any P (allLocalSteps tr)
-}

-- ** segments

record Segment (A B : Type) : Type where
  constructor from_to_
  field _∙start _∙end : B → A
open Segment ⦃...⦄ public

instance
  Segment-↞ : Segment GlobalState (s′ ↞— s)
  Segment-↞ {s′}{s} = from (const s) to (const s′)

  Segment-→ : Segment LocalState (p ⦂ t ⊢ ls — menv —→ ls′)
  Segment-→ {ls = ls} {ls′ = ls′} = from (const ls) to (const ls′)

  Segment-Step : Segment LocalState Step
  Segment-Step = from (_∙start ∘ theStep) to (_∙end ∘ theStep)
\end{code}
