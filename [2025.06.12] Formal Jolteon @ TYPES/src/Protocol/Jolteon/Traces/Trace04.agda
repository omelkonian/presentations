module Protocol.Jolteon.Traces.Trace04 where

open import Prelude
open import Protocol.Jolteon.Traces.Core

s₄′ s₄″ : GlobalState
s₄′ = record s₄
  { history       = t₄ ∷ h₄
  ; networkBuffer = [ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , t₄ ⨾ 46 , 𝔸 , t₄ ⨾ 46 , 𝔹 , t₄ ]
  ; stateMap      =
    ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound  , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Locking , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , []  , [ b₁ ] , just 58 , false , false ⦆
  ∷ []
  }

s₄″ = record s₄
  { currentTime   = 50
  ; history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 4 , 4 , qc₂ , just tc₁ , AdvancingRound , tcf₁ ∷ ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ t₄ ⨾ tcf₁ ⨾ p₄ ] , [ b₁ ] , just 58 , false , false ⦆
  ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Locking , p₄ ∷ t₂ ∷ db₃ , [ t₃ ⨾ t₄ ]  , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [ t₄ ⨾ p₄ ]  , [ b₁ ] , just 58 , false , false ⦆
  ∷ []
  }

opaque
  unfolding blockPayload chainPayload

  trace04 : s₄ —↠ s₄′
  trace04 =
      s₄
    —→⟨ 𝔸 :TimerExpired? ⟩
      record s₄
      { history       = t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , t₄ ⨾ 46 , 𝔸 , t₄ ⨾ 46 , 𝔹 , t₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound  , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , []  , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :RegisterTimeout? tm₃ ⟩
      _
  -- ** TODO: set up example with 4 replicas to exercise `EnoughTimeouts`
  {-
    —→⟨ 𝔸 :EnoughTimeouts? 3 ⟩
  -}
    —→⟨ 𝔸 :AdvanceRoundTC? tc₁ ⟩
      record s₄
      { history       = t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , t₄ ⨾ 46 , 𝔸 , t₄ ⨾ 46 , 𝔹 , t₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound  , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , AdvancingRound , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , []  , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :AdvanceRoundNoOp? ⟩
    s₄′
    ∎

  _ : s₄ —↠ s₄″
  _ =
      s₄
    —→⟨ 𝔸 :TimerExpired? ⟩
      record s₄
      { history       = t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , t₄ ⨾ 46 , 𝔸 , t₄ ⨾ 46 , 𝔹 , t₄ ]
      ; stateMap      =
        _
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝕃 :InitTC? ⟩
      record s₄
      { history       = tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , t₄ ⨾ 46 , 𝔸 , t₄ ⨾ 46 , 𝔹 , t₄ ⨾ 46 , 𝕃 , tcf₁ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Proposing , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ _
      ∷ _
      ∷ []
      }
    —→⟨ 𝕃 :ProposeBlock? [] ⟩
      record s₄
      { history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , t₄ ⨾ 46 , 𝔸 , t₄ ⨾ 46 , 𝔹 , t₄
                        ⨾ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , p₄ ⨾ 46 , 𝔸 , p₄ ⨾ 46 , 𝔹 , p₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ _
      ∷ _
      ∷ []
      }
    —→⟨ Deliver? (46 , 𝕃 , tcf₁) ⟩
      record s₄
      { history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , t₄   ⨾ 46 , 𝔸 , t₄ ⨾ 46 , 𝔹 , t₄
                        ⨾ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , p₄ ⨾ 46 , 𝔸 , p₄ ⨾ 46 , 𝔹 , p₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ tcf₁ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃  , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (46 , 𝕃 , t₄) ⟩
      record s₄
      { history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝔸 , t₄   ⨾ 46 , 𝔹 , t₄
                        ⨾ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , p₄ ⨾ 46 , 𝔸 , p₄ ⨾ 46 , 𝔹 , p₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ tcf₁ ⨾ t₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃  , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (46 , 𝔸 , t₄) ⟩
      record s₄
      { history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝔹 , t₄ ⨾ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , p₄ ⨾ 46 , 𝔸 , p₄ ⨾ 46 , 𝔹 , p₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ tcf₁ ⨾ t₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃  , [ t₃ ⨾ t₄ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (46 , 𝔹 , t₄) ⟩
      record s₄
      { history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , tcf₁ ⨾ 46 , 𝕃 , p₄ ⨾ 46 , 𝔸 , p₄ ⨾ 46 , 𝔹 , p₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ tcf₁ ⨾ t₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃  , [ t₃ ⨾ t₄ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [ t₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (46 , 𝕃 , tcf₁) ⟩
      record s₄
      { history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = [ 46 , 𝕃 , p₄ ⨾ 46 , 𝔸 , p₄ ⨾ 46 , 𝔹 , p₄ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ tcf₁ ⨾ t₄ ⨾ tcf₁ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃  , [ t₃ ⨾ t₄ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [ t₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (46 , 𝕃 , p₄) ⟩
      _
    —→⟨ Deliver? (46 , 𝔸 , p₄) ⟩
      _
    —→⟨ Deliver? (46 , 𝔹 , p₄) ⟩
      _
    —→⟨ WaitUntil? 50 ⟩
      record s₄
      { currentTime   = 50
      ; history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ tcf₁ ⨾ t₄ ⨾ tcf₁ ⨾ p₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃  , [ t₃ ⨾ t₄ ⨾ p₄ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [ t₄ ⨾ p₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterTC? ⟩
      _
    —→⟨ 𝔸 :RegisterProposal? ⟩
      _
    —→⟨ 𝔸 :AdvanceRoundTC? tc₁ ⟩
      record s₄
      { currentTime   = 50
      ; history       = p₄ ∷ tcf₁ ∷ t₄ ∷ h₄
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , AdvancingRound , tcf₁ ∷ ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ t₄ ⨾ tcf₁ ⨾ p₄ ] , [ b₁ ] , just 58 , false , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , AdvancingRound , p₄ ∷ t₂ ∷ db₃ , [ t₃ ⨾ t₄ ]  , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , [ t₄ ⨾ p₄ ]  , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :AdvanceRoundNoOp? ⟩
    s₄″
    ∎
