\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Jolteon.Base
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon.Local.Step2 (⋯ : _) (open Assumptions ⋯ hiding (sign)) where

open import Protocol.Jolteon.Block ⋯
open import Protocol.Jolteon.Message ⋯
open import Protocol.Jolteon.Local.State ⋯

enterRound : Time → Op₁ LocalState
enterRound currentTime ls = record ls
  { timer          = just (currentTime + τ)
  ; phase          = Proposing
  ; roundAdvanced? = false
  }

propose : Op₁ LocalState
propose ls = record ls
  { phase = Receiving }

recordTimeout : Op₁ LocalState
recordTimeout ls = record ls
  { timer     = nothing -- don't fire again.
  ; timedOut? = true
  ; r-vote    = 1 + ls .r-cur
  }

registerMessage : (ls : LocalState) → m ∈ ls .inbox → LocalState
registerMessage {m} ls m∈ = record ls
  { phase = AdvancingRound
  ; db    = m ∷ ls .db
  ; inbox = L.removeAt (ls .inbox) (L.Any.index m∈)
  }

registerTimeout  = registerMessage
registerVote     = registerMessage
registerProposal = registerMessage

advanceRound : QC ⊎ TC → Op₁ LocalState
advanceRound qtc ls = record ls
  { phase          = AdvancingRound
  ; r-cur          = 1 + qtc ∙round
  ; tc-last        = Sum.isInj₂ qtc
  ; timer          = nothing
  ; timedOut?      = false
  ; roundAdvanced? = true
  }

lock : QC → Op₁ LocalState
lock qc ls = record ls
  { qc-high = qc  -- ⊔qc ls .qc-high
  ; phase   = Committing
  }

commit : Chain → Op₁ LocalState
commit ch ls =  record ls
  { phase      = Voting
  ; final = ch
  }

shouldEnterRound : Op₁ LocalState
shouldEnterRound ls = record ls
  { phase = if ls .roundAdvanced? then EnteringRound else Receiving }

voteProposal : Op₁ LocalState
voteProposal ls = record (shouldEnterRound ls)
  { r-vote = ls .r-cur }

private vote = voteProposal

receiveMessage : Message → Op₁ LocalState
receiveMessage m ls = record ls
  { inbox = ls .inbox L.∷ʳ m }
\end{code}
\newcommand\localStep{%
\begin{AgdaMultiCode}
\begin{code}[hide]
private
  sign = signData
mutual
  -- special case of step sending one message to one recipient
  _⦂_⊢_—[_∣_⟩—→_ : Pid → Time → LocalState → Pid → Message → LocalState → Type
  p ⦂ t ⊢ ls —[ p′ ∣ m ⟩—→ ls′ = p ⦂ t ⊢ ls — just [ p′ ∣ m ⟩ —→ ls′

  -- special case of step multicasting one message
  _⦂_⊢_—[_]—→_ : Pid → Time → LocalState → Message → LocalState → Type
  p ⦂ t ⊢ ls —[ m ]—→ ls′ = p ⦂ t ⊢ ls — just [ m ⟩ —→ ls′

  -- special case of step sending no message
  _⦂_⊢_——→_ : Pid → Time → LocalState → LocalState → Type
  p ⦂ t ⊢ ls ——→ ls′ = p ⦂ t ⊢ ls — nothing —→ ls′
\end{code}
\begin{code}
  data _⦂_⊢_—_—→_ (p : Pid) (t : Time) (ls : LocalState) : Maybe Envelope → LocalState → Type where
\end{code}

\only<+>{
\noindent
\begin{minipage}[t]{.45\textwidth}
\begin{code}
    ProposeBlock : ∀ {txs} →
      let  L  = roundLeader (ls .r-cur)
           b  = mkBlockForState ls txs
           m  = Propose (sign L b)
      in
      ∙ p ≡ L
        ────────────────────────────
        p ⦂ t ⊢ ls —[ m ]—→ ls
\end{code}
\end{minipage}%
\begin{minipage}[t]{.54\textwidth}
\begin{code}
    RegisterProposal : ∀ {sb} →
      let  m  = Propose sb
           b  = sb .datum
      in
      ∀ (m∈ : m ∈ ls .inbox) →
      ∙ ¬ timedOut ls t
      ∙ sb .node ≡ roundLeader (b ∙round)
      ∙ ValidProposal (ls .db) b
        ──────────────────────────────────
        p ⦂ t ⊢ ls ——→ registerProposal ls m∈
\end{code}
\end{minipage}%
\raisebox{-10ex}{
\begin{minipage}{.05\textwidth}
$\dots$
\end{minipage}%
}
}

\only<+>{
\begin{minipage}[t]{.45\textwidth}
\begin{code}
    VoteBlock : ∀ {b} →
      let  br  = (b ∙blockId , b ∙round)
           m   = Vote $ sign p br
           L′  = nextLeader ls
      in
      ∙ b ∙∈ ls .db
      ∙ ShouldVote ls b
        ─────────────────────────────
        p ⦂ t ⊢ ls —[ L′ ∣ m ⟩—→ vote ls
\end{code}
\end{minipage}%
\begin{minipage}[t]{.54\textwidth}
\begin{code}
    Commit : ∀ {b b′ ch} →
      ∙ b   -certified-∈-  ls .db
      ∙ b′  -certified-∈-  ls .db
      ∙ (b′ ∷ b ∷ ch) ∙∈   ls .db
      ∙ length ch  >  length (ls .final)
      ∙ b′ .round  ≡  1 + b .round
        ─────────────────────────────────────
        p ⦂ t ⊢ ls ——→ record ls {final = b ∷ ch}
\end{code}
\end{minipage}%
\raisebox{-10ex}{
\begin{minipage}{.05\textwidth}
$\dots$
\end{minipage}%
}
}
\begin{code}[hide]
    --------------------------
    -- * EnteringRound
    --------------------------

    -- Initialisation: replica enters round either with a TC or without one
    InitTC : let L = currentLeader ls; m = TCFormed tc in
      ∙ ls .phase ≡ EnteringRound
      ∙ ls .tc-last ≡ just tc
        ───────────────────────────────────────
        p ⦂ t ⊢ ls —[ L ∣ m ⟩—→ enterRound t ls

    InitNoTC :
      ∙ ls .phase ≡ EnteringRound
      ∙ ls .tc-last ≡ nothing
        ──────────────────────────────
        p ⦂ t ⊢ ls ——→ enterRound t ls

    --------------------------
    -- * Proposing
    --------------------------

    -- Leader proposes a new block.

    -- Non-leader skips proposing.
    ProposeBlockNoOp : let L = currentLeader ls in
      ∙ ls .phase ≡ Proposing
      ∙ p ≢ L
        ─────────────────────────
        p ⦂ t ⊢ ls ——→ propose ls

    --------------------------
    -- * Receiving
    --------------------------

    RegisterVote :
      let
        L′ = roundLeader (1 + r)
        m  = Vote $ signData p′ (b ∙blockId , r)
      in
      ∀ (m∈ : m ∈ ls .inbox) →
      ∙ ls .phase ≡ Receiving
      ∙ ¬ timedOut ls t
      ∙ b ∙∈ ls .db
      ∙ m ∉ ls .db
      ∙ L′ ≡ p
        ─────────────────────────────────
        p ⦂ t ⊢ ls ——→ registerVote ls m∈

    RegisterTimeout : let m = Timeout tm in
      ∀ (m∈ : m ∈ ls .inbox) →
      ∙ ls .phase ≡ Receiving
      ∙ ¬ timedOut ls t
      ∙ m ∉ ls .db
        ────────────────────────────────────
        p ⦂ t ⊢ ls ——→ registerTimeout ls m∈

    RegisterTC : let m = TCFormed tc in
      ∀ (m∈ : m ∈ ls .inbox) →
      ∙ ls .phase ≡ Receiving
      ∙ ¬ timedOut ls t
      ∙ m ∉ ls .db
        ────────────────────────────────────
        p ⦂ t ⊢ ls ——→ registerTimeout ls m∈

    EnoughTimeouts :
      let
        m   = Timeout $ signData p (ls .r-cur , ls .qc-high) , ls .tc-last
        tms = filter (IsTimeoutForRound? r) (ls .db)
      in
      ∙ ls .phase ≡ Receiving
      ∙ ¬ timedOut ls t
      ∙ IncludesHonest tms
      ∙ r ≥ ls .r-cur
        ────────────────────────────────────
        p ⦂ t ⊢ ls —[ m ]—→ recordTimeout ls

    TimerExpired :
      let m = Timeout $ signData p (ls .r-cur , ls .qc-high) , ls .tc-last in
      ∙ ls .phase ≡ Receiving
      ∙ timedOut ls t
        ────────────────────────────────────
        p ⦂ t ⊢ ls —[ m ]—→ recordTimeout ls

    --------------------------
    -- * AdvancingRound
    --------------------------

    AdvanceRoundQC :
      ∙ ls .phase ≡ AdvancingRound
      ∙ qc ∙∈ ls .db
      ∙ qc ∙round ≥ ls .r-cur
        ──────────────────────────────────────────
        p ⦂ t ⊢ ls ——→ advanceRound (inj₁ qc) ls

    AdvanceRoundTC :
      ∙ ls .phase ≡ AdvancingRound
      ∙ tc ∙∈ ls .db
      ∙ tc ∙round ≥ ls .r-cur
        ──────────────────────────────────────────
        p ⦂ t ⊢ ls ——→ advanceRound (inj₂ tc) ls

    AdvanceRoundNoOp : --when no new QC or TC has formed yet.
      ∙ ls .phase ≡ AdvancingRound
      ∙ AllQC (λ qc → qc ∙round < ls .r-cur) (ls .db)
      ∙ AllTC (λ tc → tc ∙round < ls .r-cur) (ls .db)
        ─────────────────────────────────────────────
        p ⦂ t ⊢ ls ——→ record ls { phase = Locking }

    --------------------------
    -- * Locking
    --------------------------

    Lock :
      ∙ ls .phase ≡ Locking
      ∙ qc -highest-qc-∈- ls .db
        ─────────────────────────
        p ⦂ t ⊢ ls ——→ lock qc ls

    --------------------------
    -- * Committing
    --------------------------

    CommitNoOp :
      ∙ ls .phase ≡ Committing
      ∙ NoBlock (_longer-final-∈ ls) (ls .db)
        ─────────────────────────────────────────
        p ⦂ t ⊢ ls ——→ record ls {phase = Voting}

    --------------------------
    -- * Voting
    --------------------------

    VoteBlockNoOp :
      ∙ ls .phase ≡ Voting
      ∙ NoBlock (ShouldVote ls) (ls .db)
        ──────────────────────────────────
        p ⦂ t ⊢ ls ——→ shouldEnterRound ls
\end{code}
\end{AgdaMultiCode}
}
