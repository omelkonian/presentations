module Protocol.Jolteon.Traces.Trace00b where

open import Prelude
open import Protocol.Jolteon.Traces.Core

opaque

  private
    tm₀₀b : Message
    tm₀₀b = Timeout (signData 𝔸 (1 , qc₀) , nothing)

    s₀₀b : GlobalState
    s₀₀b = record
        { currentTime = 15
        ; history = tm₀₀b ∷ []
        ; networkBuffer = (15 , 𝕃 , tm₀₀b)
                        ∷ (15 , 𝔸 , tm₀₀b)
                        ∷ (15 , 𝔹 , tm₀₀b)
                        ∷ []
        ; stateMap =
          [ initLocalState
          ⨾ recordTimeout
            ⦅ 0 , 1 , qc₀ , nothing , Receiving , [] , [] , [] , just 12 , false , false ⦆
          ⨾ initLocalState
          ]
      }

  trace00b : s₀ —↠ s₀₀b
  trace00b =
    begin
      s₀
    —→⟨ 𝔸 :InitNoTC? ⟩
      _
    —→⟨ 𝔸 :ProposeBlockNoOp? ⟩
      _
    —→⟨ WaitUntil? 15 ⟩
      _
    —→⟨ 𝔸 :TimerExpired? ⟩
      _
    ∎
