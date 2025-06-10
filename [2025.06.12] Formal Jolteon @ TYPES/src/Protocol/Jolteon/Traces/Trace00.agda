module Protocol.Jolteon.Traces.Trace00 where

open import Prelude
open import Protocol.Jolteon.Traces.Core

opaque
  unfolding blockPayload chainPayload

  trace00 : s₀ —↠ s₁
  trace00 =
    begin
      s₀
    —→⟨ 𝕃 :InitNoTC? ⟩
      record s₀
      { stateMap
      = record def {phase = Proposing; timer = just τ; roundAdvanced? = false}
      ∷ def
      ∷ def
      ∷ []
      }
    —→⟨ 𝕃 :ProposeBlock? [] ⟩
      record s₀
      { history = [ p₁ ]
      ; networkBuffer = [ 0 , 𝕃 , p₁ ⨾ 0 , 𝔸 , p₁ ⨾ 0 , 𝔹 , p₁ ]
      ; stateMap
      = record def {phase = Receiving; timer = just τ; roundAdvanced? = false}
      ∷ def
      ∷ def
      ∷ []
      }
    —→⟨ 𝔸 :InitNoTC? ⟩
      record
      { currentTime   = 0
      ; history       = [ p₁ ]
      ; networkBuffer = [ 0 , 𝕃 , p₁ ⨾ 0 , 𝔸 , p₁ ⨾ 0 , 𝔹 , p₁ ]
      ; stateMap      =
          ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ ⦅ 0 , 1 , qc₀ , nothing , Proposing , [] , [] , [] , just τ , false , false ⦆
        ∷ def
        ∷ []
      }
    —→⟨ 𝔸 :ProposeBlockNoOp? ⟩
      record
      { currentTime   = 0
      ; history       = [ p₁ ]
      ; networkBuffer = [ 0 , 𝕃 , p₁ ⨾ 0 , 𝔸 , p₁ ⨾ 0 , 𝔹 , p₁ ]
      ; stateMap      =
          ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ def
        ∷ []
      }
    —→⟨ 𝔹 :InitNoTC? ⟩
      record
      { currentTime   = 0
      ; history       = [ p₁ ]
      ; networkBuffer = [ 0 , 𝕃 , p₁ ⨾ 0 , 𝔸 , p₁ ⨾ 0 , 𝔹 , p₁ ]
      ; stateMap      =
          ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ ⦅ 0 , 1 , qc₀ , nothing , Proposing , [] , [] , [] , just τ , false , false ⦆
        ∷ []
      }
    —→⟨ 𝔹 :ProposeBlockNoOp? ⟩
      record
      { currentTime   = 0
      ; history       = [ p₁ ]
      ; networkBuffer = [ 0 , 𝕃 , p₁ ⨾ 0 , 𝔸 , p₁ ⨾ 0 , 𝔹 , p₁ ]
      ; stateMap      =
          ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just τ , false , false ⦆
        ∷ []
      }
    —→⟨ Deliver? (0 , 𝕃 , p₁) ⟩
      _
    —→⟨ Deliver? (0 , 𝔸 , p₁) ⟩
      _
    —→⟨ Deliver? (0 , 𝔹 , p₁) ⟩
      _
    —→⟨ WaitUntil? 3 ⟩
      record
      { currentTime   = 3
      ; history       = [ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [ p₁ ] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [ p₁ ] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [ p₁ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterProposal? ⟩
      record
      { currentTime   = 3
      ; history       = [ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , []  , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , []  , [ p₁ ] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , []  , [ p₁ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :RegisterProposal? ⟩
      record
      { currentTime   = 3
      ; history       = [ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , []  , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , []  , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Receiving , []  , [ p₁ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :RegisterProposal? ⟩
      record
      { currentTime   = 3
      ; history       = [ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 3
      ; history       = [ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 0 , 1 , qc₀ , nothing , Locking  , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 3
      ; history       = [ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 0 , 1 , qc₀ , nothing , Committing  , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      record
      { currentTime   = 3
      ; history       = [ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 0 , 1 , qc₀ , nothing , Voting   , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :VoteBlock? b₁ ⟩
      record
      { currentTime   = 3
      ; history       = [ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 3 , 𝕃 , v₁ 𝕃 ]
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 3
      ; history       = [ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 3 , 𝕃 , v₁ 𝕃 ]
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Locking , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :Lock? ⟩
      record
      { currentTime   = 3
      ; history       = [ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 3 , 𝕃 , v₁ 𝕃 ]
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Committing , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :CommitNoOp? ⟩
      record
      { currentTime   = 3
      ; history       = [ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 3 , 𝕃 , v₁ 𝕃 ]
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Voting , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :VoteBlock? b₁ ⟩
      record
      { currentTime   = 3
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 3 , 𝕃 , v₁ 𝕃 ⨾  3 , 𝕃 , v₁ 𝔸 ]
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (3 , 𝕃 , v₁ 𝕃) ⟩
      _
    —→⟨ Deliver? (3 , 𝕃 , v₁ 𝔸) ⟩
      _
    —→⟨ WaitUntil? 8 ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [ v₁ 𝕃 ⨾ v₁ 𝔸 ] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterVote? b₁ ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , AdvancingRound , [ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔸 ] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Locking , [ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔸 ] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Committing , [ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔸 ] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Voting , [ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔸 ] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔸 ] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterVote? b₁ ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 1 , qc₀ , nothing , AdvancingRound , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundQC? qc₁ ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₀ , nothing , AdvancingRound , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₀ , nothing , Locking , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Committing , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Voting , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , EnteringRound , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :InitNoTC? ⟩
      record
      { currentTime   = 8
      ; history       = [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Proposing , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :ProposeBlock? [] ⟩
      record
      { currentTime   = 8
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 8 , 𝕃 , p₂ ⨾ 8 , 𝔸 , p₂ ⨾ 8 , 𝔹 , p₂ ]
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Receiving , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (8 , 𝕃 , p₂ ) ⟩
      _
    —→⟨ Deliver? (8 , 𝔸 , p₂ ) ⟩
      _
    —→⟨ Deliver? (8 , 𝔹 , p₂ ) ⟩
      _
    —→⟨ WaitUntil? 10 ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Receiving , [ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ p₂ ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterProposal? ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , AdvancingRound , p₂ ∷ _ , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :RegisterProposal? ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , AdvancingRound , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , AdvancingRound , p₂ ∷ _ , []  , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Locking , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , AdvancingRound , p₂ ∷ _ , []  , [] , just τ , false , false ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :AdvanceRoundQC? qc₁ ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Locking , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 2 , qc₀ , nothing , AdvancingRound , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Locking  , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 2 , qc₀ , nothing , Locking  , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :Lock? ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Locking  , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 2 , qc₁ , nothing , Committing  , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :CommitNoOp? ⟩
      record
      { currentTime   = 10
      ; history       = [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Locking  , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 1 , 2 , qc₁ , nothing , Voting   , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :VoteBlock? b₂ ⟩
      record
      { currentTime   = 10
      ; history       = [ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ]
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Locking  , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 10
      ; history       = [ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ]
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Committing  , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      record
      { currentTime   = 10
      ; history       = [ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ]
      ; stateMap      =
        ⦅ 1 , 2 , qc₁ , nothing , Voting   , p₂ ∷ _ , []  , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :VoteBlock? b₂ ⟩
      s₁
    ∎
