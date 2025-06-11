\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Jolteon.Base
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Global.Step2 (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Jolteon.Block ⋯
open import Protocol.Jolteon.Message ⋯
open import Protocol.Jolteon.Local.State ⋯
open import Protocol.Jolteon.Local.Step ⋯
open import Protocol.Jolteon.Global.State ⋯
open import Protocol.Jolteon.Global.NoForging ⋯ using (NoSignatureForging)

honestTPMessage : TPMessage → Maybe (HonestPid × Message)
honestTPMessage (_ , p , m) = case honest? p of λ where
    (yes hp) → just ((p ,· hp) , m)
    (no _)   → nothing

-- Delivers a message to replicas' inboxes.
receiveMsg : StateMap → Maybe (HonestPid × Message) → StateMap
receiveMsg sm = M.maybe′ (λ (p , m) → sm [ p ]%=′ receiveMessage m) sm

-- Deliver a message which is in transit:
--   · adds it to the corresponding inbox in a local state
--   · removes it from the network buffer
deliverMsg : ∀ s {tpm} → tpm ∈ s .networkBuffer → GlobalState
deliverMsg s {tpm} tpm∈ = record s
  { stateMap      = receiveMsg (s .stateMap) (honestTPMessage tpm)
  ; networkBuffer = s .networkBuffer L.Mem.─ tpm∈
  }

-- Takes a time and envelope and expand the broadcasted messages to n unicast messages.
-- This function broadcasts messages even to the sender (otherwise we would filter).
expandBroadcasts : Time → Envelope → TPMessages
expandBroadcasts t = expandEnv
  module _ where
  expandEnv : Envelope → TPMessages
  expandEnv = λ where
    [ m ⟩     → L.map (λ p → (t , p , m)) allPids
    [ p ∣ m ⟩ → [ (t , p , m) ]

  expandEnv-content≡ : ∀ env → All (λ (_ , _ , m) → m ≡ env .content) (expandEnv env)
  expandEnv-content≡ = λ where
    [ m ⟩     → L.All.tabulate λ x∈ → let _ , _ , eq = L.Mem.∈-map⁻ (λ p → (t , p , m)) x∈ in
                cong (proj₂ ∘ proj₂) eq
    [ p ∣ m ⟩ → refl ∷ []

broadcast : Maybe Envelope → Op₁ GlobalState
broadcast me s = let t = s .currentTime in record s
  { networkBuffer = maybe (λ e → s .networkBuffer ++ expandBroadcasts t e) (s .networkBuffer) me
  ; history       = L.fromMaybe (M.map _∙message me) ++ s .history
  }
\end{code}
\newcommand\globalStep{%
\begin{AgdaMultiCode}
\begin{code}
data _—→_ (s : GlobalState) : GlobalState → Type where
\end{code}

\noindent
\begin{minipage}[t]{0.5\textwidth}
\noindent
\begin{code}
  Deliver : ∀ {tpm}
    (tpm∈ : tpm ∈ s .networkBuffer) →
    ───────────────────────────────
    s —→ deliverMsg s tpm∈

  WaitUntil : ∀ t →
    ∙ All  (λ (t′ , _ , _) → t ≤ t′ + Δ)
           (s .networkBuffer)
    ∙ s .currentTime < t
      ──────────────────────────────
      s —→ record s { currentTime = t }
\end{code}
\hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
  LocalStep : ∀ {m} ⦃ _ : Honest p ⦄ →
    (p ⦂ s .currentTime ⊢ s ＠ p — m —→ ls′)
    ─────────────────────────────────────
    s —→ broadcast m (s ＠ p ≔ ls′)

  DishonestLocalStep : ∀ {m} →
    ∙ ¬ Honest p
    ∙ NoSignatureForging (m .content) s
      ─────────────────────────────────
      s —→ broadcast (just m) s
\end{code}
\end{minipage}%
\end{AgdaMultiCode}
}
