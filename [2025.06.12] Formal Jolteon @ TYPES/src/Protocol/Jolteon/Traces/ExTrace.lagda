\begin{code}[hide]
module Protocol.Jolteon.Traces.ExTrace where

open import Prelude
open import Protocol.Jolteon.Traces.Core


private
  src =
      record
      { currentTime    = 10
      ; history        = [ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer  = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ]
      ; stateMap       =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Voting , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
  target =
      record
      { currentTime    = 13
      ; history        = h₂
      ; networkBuffer  = []
      ; stateMap       =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }

opaque
  unfolding blockPayload chainPayload

  _ : src —↠ target
  _ =
\end{code}
\newcommand\exA{%
\begin{code}
    begin
      record
      { currentTime  = 10; history = [ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ]
      ; stateMap     =
      [ {- 𝕃 -} ⦅ 2 , 2 , qc₁ , nothing , Receiving , _ , [] , [] , just 20 , false , false ⦆
      ⨾ {- 𝔸 -} ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , _ , [] , [] , nothing , false , true ⦆
      ⨾ {- 𝔹 -} ⦅ 0 , 1 , qc₀ , nothing , Voting , _ , _ , [] , just τ , false , false ⦆ ] }
    —→⟨ 𝔹 :VoteBlock? b₁ ⟩
      record
      { currentTime  = 10; history = v₁ 𝔹 ∷ _; networkBuffer = _
      ; stateMap     =
      [ ⦅ 2 , 2 , qc₁ , nothing , Receiving , _ , [] , [] , just 20 , false , false ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , _ , [] , [] , nothing , false , true ⦆
      ⨾ ⦅ 1 , 1 , qc₀ , nothing , Receiving , _ , _ , [] , just τ , false , false ⦆ ] }
    —→⟨ 𝔹 :RegisterProposal? ⟩
      record
      { currentTime  = 10; history = _ ; networkBuffer = _
      ; stateMap     =
      [ ⦅ 2 , 2 , qc₁ , nothing , Receiving , _ , [] , [] , just 20 , false , false ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , _ , [] , [] , nothing , false , true ⦆
      ⨾ ⦅ 1 , 1 , qc₀ , nothing , AdvancingRound , [ p₂ ⨾ p₁ ] , [] , [] , just τ , false , false ⦆ ] }
\end{code}
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
}
\begin{code}[hide]
    —→⟨ 𝔹 :AdvanceRoundQC? qc₁ ⟩
      record
      { currentTime   = 10
      ; history       = [ v₁ 𝔹 ⨾ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ⨾ 10 , 𝕃 , v₁ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 2 , qc₀ , nothing , AdvancingRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 10
      ; history       = [ v₁ 𝔹 ⨾ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ⨾ 10 , 𝕃 , v₁ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 2 , qc₀ , nothing , Locking , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
      record
      { currentTime   = 10
      ; history       = [ v₁ 𝔹 ⨾ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ⨾ 10 , 𝕃 , v₁ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 2 , qc₁ , nothing , Committing , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :CommitNoOp? ⟩
      _
    —→⟨ 𝔹 :VoteBlock? b₂ ⟩
      record
      { currentTime   = 10
      ; history       = h₂
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ⨾ 10 , 𝕃 , v₁ 𝔹 ⨾ 10 , 𝕃 , v₂ 𝔹 ]
      ; stateMap      =
      [ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just 20 , false , false ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆ ] }
    —→⟨ Deliver? (10 , 𝕃 , v₂ 𝔸) ⟩
      record
      { currentTime   = 10
      ; history       = h₂
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝕃 ⨾ 10 , 𝕃 , v₁ 𝔹 ⨾ 10 , 𝕃 , v₂ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₂ 𝔸 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ Deliver? (10 , 𝕃 , v₂ 𝕃) ⟩
      record
      { currentTime   = 10
      ; history       = h₂
      ; networkBuffer = [ 10 , 𝕃 , v₁ 𝔹 ⨾ 10 , 𝕃 , v₂ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₂ 𝔸 ⨾ v₂ 𝕃 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ Deliver? (10 , 𝕃 , v₁ 𝔹) ⟩
      record
      { currentTime   = 10
      ; history       = h₂
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₂ 𝔸 ⨾ v₂ 𝕃 ⨾ v₁ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ Deliver? (10 , 𝕃 , v₂ 𝔹) ⟩
      record
      { currentTime   = 10
      ; history       = h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₂ 𝔸 ⨾ v₂ 𝕃 ⨾ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ WaitUntil? 13 ⟩
      record
      { currentTime   = 13
      ; history       = [ v₂ 𝔹 ⨾ v₁ 𝔹 ⨾ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₂ 𝔸 ⨾ v₂ 𝕃 ⨾ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
\end{code}
\newcommand\exB{%
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
\begin{code}
    —→⟨ 𝕃 :RegisterVote? b₂ ⟩
      record
      { currentTime   = 13
      ; history       = _
      ; networkBuffer = []
      ; stateMap      =
      [ ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , v₂ 𝔸 ∷ _ , v₂ 𝕃 ∷ _ , [] , just 20 , false , false ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆ ] }
\end{code}
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
}
\begin{code}[hide]
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      _
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 13
      ; history       = h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Committing , [ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₂ 𝕃 ⨾ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      _
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      _
\end{code}
\newcommand\exC{%
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
\begin{code}
    —→⟨ 𝕃 :RegisterVote? b₂ ⟩
      record
      { currentTime   = 13
      ; history       = _
      ; networkBuffer = []
      ; stateMap      =
      [ ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , v₂ 𝕃 ∷ _ , _ , [] , just 20 , false , false ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , _ , [] , [] , nothing , false , true ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , _ , [] , [] , nothing , false , true ⦆ ] }
\end{code}
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
}
\begin{code}[hide]
    —→⟨ 𝕃 :AdvanceRoundQC? qc₂ ⟩
      record
      { currentTime   = 13
      ; history       = h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₁ , nothing , AdvancingRound , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 13
      ; history       = h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₁ , nothing , Locking , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 13
      ; history       = h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Committing , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
\end{code}
\newcommand\exD{%
\vspace{-.2em}
$\ \ \ \ \vdots$
\vspace{-.2em}
\begin{code}
    —→⟨ 𝕃 :Commit? [ b₂ ⨾ b₁ ] ⟩
      record
      { currentTime   = 13
      ; history       = _
      ; networkBuffer = []
      ; stateMap      =
      [ ⦅ 2 , 3 , qc₂ , nothing , Voting , _ , _ , [ b₁ ] , nothing , false , true ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , _ , [] , [] , nothing , false , true ⦆
      ⨾ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , _ , [] , [] , nothing , false , true ⦆ ] }
    ∎
\end{code}
}
