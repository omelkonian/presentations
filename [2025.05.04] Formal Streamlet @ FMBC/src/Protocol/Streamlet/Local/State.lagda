\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Local.State (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯
open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.Chain ⋯

data Phase : Type where
  Ready Voted : Phase

instance
  DecEq-Phase : DecEq Phase
  DecEq-Phase ._≟_ = λ where
    Ready Ready → yes refl
    Ready Voted → no λ ()
    Voted Ready → no λ ()
    Voted Voted → yes refl
\end{code}

\newcommand\localState{%
\begin{minipage}{\textwidth}
\AgdaNoSpaceAroundCode{}
\begin{AgdaMultiCode}
\begin{code}
record LocalState : Type where
\end{code}
\begin{code}[hide]
  constructor ⦅_,_,_,_⦆
\end{code}

\vspace{-3mm}
\hspace{1em}
\begin{minipage}[t]{.3\textwidth}
\begin{code}
  field  phase  : Phase
         db     : List Message
\end{code}
\hfill
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}
\begin{code}
         inbox  : List Message
         final  : Chain
\end{code}
\end{minipage}
\end{AgdaMultiCode}
\AgdaSpaceAroundCode{}
\end{minipage}
}

\begin{code}[hide]
open LocalState public

variable ls ls′ ls″ : LocalState

initLocalState : LocalState
initLocalState = ⦅ Ready , [] , [] , genesisChain ⦆

instance
  Def-LocalState  = Default _ ∋ λ where .def → initLocalState
  Init-LocalState = HasInitial _ ∋ λ where .Initial → _≡ initLocalState
\end{code}

\newcommand\chainIn{%
\begin{AgdaMultiCode}
\begin{code}
data _chain-∈_ : Chain → List Message → Type where
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{0.35\textwidth}
\begin{code}
  [] :
       ─────────────
       [] chain-∈ ms
\end{code}
\AgdaNoSpaceAroundCode{}
\hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
  _∷_⊣_ :
    ∙ Any (λ m → b ≡ m ∙block) ms
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{.38\textwidth}
\begin{code}
    ∙ ch chain-∈ ms
\end{code}
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}
\begin{code}
    ∙ b -connects-to- ch
\end{code}
\end{minipage}%
\begin{code}
    ─────────────────────────────────────
    (b ∷ ch) chain-∈ ms
\end{code}
\end{minipage}
\end{AgdaMultiCode}
\AgdaSpaceAroundCode{}
}
\begin{code}[hide]
chain-∈⇒Valid : ch chain-∈ ms → ValidChain ch
chain-∈⇒Valid [] = []
chain-∈⇒Valid (_ ∷ ch∈ ⊣ b→ch) = _ ∷ chain-∈⇒Valid ch∈ ⊣ b→ch

uncons-ch∈ : (b ∷ ch) chain-∈ ms → ch chain-∈ ms
uncons-ch∈ (_ ∷ ch∈ ⊣ _) = ch∈

⊆-ch∈ :
  ∙ ms ⊆ˢ ms′
  ∙ ch chain-∈ ms
    ──────────────
    ch chain-∈ ms′
⊆-ch∈ ms⊆ = λ where
  [] → []
  (m∈ ∷ ch∈ ⊣ p) → L.SubS.Any-resp-⊆ ms⊆ m∈ ∷ ⊆-ch∈ ms⊆ ch∈ ⊣ p

chain-∈-∷ :
  ch chain-∈ ms
  ───────────────────
  ch chain-∈ (m ∷ ms)
chain-∈-∷ = λ where
  [] → []
  (m∈ ∷ ch∈ ⊣ x) → there m∈ ∷ chain-∈-∷ ch∈ ⊣ x

Suffix-ch∈ :
  ∙ Suffix≡ ch′ ch
  ∙ ch  chain-∈ ms
    ──────────────
    ch′ chain-∈ ms
Suffix-ch∈ (here eq) p rewrite L.PW.Pointwise-≡⇒≡ eq = p
Suffix-ch∈ (there suf) (m∈ ∷ p ⊣ x) = Suffix-ch∈ suf p
\end{code}

\newcommand\notarization{%
\begin{code}[hide]
module ALTERNATIVE:NotarizedBlock where
  private variable b₁ b₂ b₃ : Block
\end{code}
\begin{code}
  votes : List Message → Block → List Message
  votes ms b = filter (λ m → b ≟ m ∙block) ms
\end{code}
\vfill\hrule\vfill
\begin{code}
  NotarizedBlock : List Message → Block → Type
  NotarizedBlock ms b = IsMajority (votes ms b)
\end{code}
\vfill\hrule\vfill
\begin{code}
  NotarizedChain : List Message → Chain → Type
  NotarizedChain ms ch = All (NotarizedBlock ms) ch
\end{code}
}

\newcommand\finalization{%
\vspace{-3mm}
\begin{code}
  data FinalizedChain (ms : List Message) : Chain → Block → Type where
    Finalize :
      ∙ NotarizedChain ms (b₃ ∷ b₂ ∷ b₁ ∷ ch)
      ∙ b₃ .epoch ≡ suc (b₂ .epoch)
      ∙ b₂ .epoch ≡ suc (b₁ .epoch)
      ───────────────────────────────────────
      FinalizedChain ms (b₂ ∷ b₁ ∷ ch) b₃
\end{code}
}
\begin{code}[hide]
module _ (ms : List Message) where
  module _ (b : Block) where
    votes : List Message
    votes = filter ((b ≟_) ∘ _∙block) ms

    voteIds : List Pid
    voteIds = map _∙pid votes

    voteRightBlock : All ((b ≡_) ∘ _∙block) votes
    voteRightBlock = L.All.all-filter ((b ≟_) ∘ _∙block) ms

    seenVotes : votes ⊆ˢ ms
    seenVotes = L.SubS.filter-⊆ ((b ≟_) ∘ _∙block) ms

    record NotarizedBlock : Type where
      field enoughVotes : IsMajority votes

      enoughVoteIds : IsMajority voteIds
      enoughVoteIds rewrite L.length-map _∙pid votes = enoughVotes
      votesNonempty : length votes > 0
      votesNonempty with votes in eq
      ... | [] = ⊥-elim (majority⁺ (subst IsMajority eq enoughVotes))
      ... | x ∷ xs = Nat.s≤s Nat.z≤n

    open NotarizedBlock public
      -- NB: Proposals count as votes

  NotarizedChain : Chain → Type
  NotarizedChain = All NotarizedBlock

  data FinalizedChain : Chain → Block → Type where
    Finalize : ∀ {ch b₁ b₂ b₃} →
      ∙ NotarizedChain (b₃ ∷ b₂ ∷ b₁ ∷ ch)
      ∙ b₃ .epoch ≡ suc (b₂ .epoch)
      ∙ b₂ .epoch ≡ suc (b₁ .epoch)
        ───────────────────────────────────
        FinalizedChain (b₂ ∷ b₁ ∷ ch) b₃
\end{code}

\newcommand\longestNotarized{%
\begin{AgdaMultiCode}
\begin{code}[hide]
module ALTERNATIVE:notarized∈ where
\end{code}
\begin{code}
  _notarized-chain-∈_ _longest-notarized-chain-∈_ : Chain → List Message → Type
  ch notarized-chain-∈ ms =
    ch chain-∈ ms × NotarizedChain ms ch
  ch longest-notarized-chain-∈ ms =
    ch notarized-chain-∈ ms ×
    (∀ {ch′} → ch′ notarized-chain-∈ ms → length ch′ ≤ length ch)
\end{code}
\end{AgdaMultiCode}
}

\begin{code}[hide]
_notarized-chain-∈_ : Chain → List Message → Type
ch notarized-chain-∈ ms
  = (ch chain-∈ ms)
  × NotarizedChain ms ch

_notarized-block-∈_ : Block × Chain → List Message → Type
(b , ch) notarized-block-∈ ms
  = b -connects-to- ch
  × NotarizedBlock ms b

notarized-chain-∈⇒Valid : ch notarized-chain-∈ ms → ValidChain ch
notarized-chain-∈⇒Valid = chain-∈⇒Valid ∘ proj₁

NotarizedBlock-⊆ :
  ∙ ms ⊆ ms′
  ∙ NotarizedBlock ms b
    ────────────────────
    NotarizedBlock ms′ b
NotarizedBlock-⊆ {b = b} ms⊆ nb .enoughVotes =
  majority-⊆ (L.SubL.filter⁺ _ dec¹ (λ where refl refl → refl) ms⊆) (nb .enoughVotes)

NotarizedChain-⊆ :
  ∙ ms ⊆ ms′
  ∙ NotarizedChain ms ch
    ─────────────────────
    NotarizedChain ms′ ch
NotarizedChain-⊆ ms⊆ = L.All.map (NotarizedBlock-⊆ ms⊆)

⊆-nch∈ :
  ∙ ms ⊆ ms′
  ∙ ch notarized-chain-∈ ms
    ────────────────────────
    ch notarized-chain-∈ ms′
⊆-nch∈ ms⊆ (ch∈ , nch) = ⊆-ch∈ (⊆⇒⊆ˢ ms⊆) ch∈ , NotarizedChain-⊆ ms⊆ nch

Suffix-nch∈ :
  ∙ Suffix≡ ch′ ch
  ∙ ch notarized-chain-∈ ms
    ────────────────────────
    ch′ notarized-chain-∈ ms
Suffix-nch∈ suf (ch∈ , nch)
  = Suffix-ch∈ suf ch∈
  , Suffix⇒All suf nch

_≤ᶜʰ_ _≼_ : Chain → Chain → Type
_≤ᶜʰ_ = _≤_ on length
_≼_   = Suffix≡

data Longest∈ (ch : Chain) (ms : List Message) : Type where
  mkLongest∈ :
    (∀ {ch′} → ch′ notarized-chain-∈ ms → length ch′ ≤ length ch)
    ─────────────────────────────────────────────────
    Longest∈ ch ms

_longest-notarized-chain-∈_ : Chain → List Message → Type
ch longest-notarized-chain-∈ ms
  = ch notarized-chain-∈ ms
  × Longest∈ ch ms

-- ** Utilities related to votes/notarization

open L.All using (¬Any⇒All¬)

-- votes
votes-accept : ∀ m ms → m ∙block ≡ b → votes (m ∷ ms) b ≡ m ∷ votes ms b
votes-accept _ _ = L.filter-accept ((_ ≟_) ∘ _∙block) ∘ sym

votes-reject : ∀ m ms → m ∙block ≢ b → votes (m ∷ ms) b ≡ votes ms b
votes-reject {b} _ _ = L.filter-reject ((b ≟_) ∘ _∙block) ∘ Eq.≢-sym

-- voteIds
voteIds-∷˘ : m ∙pid ≢ p → p ∈ voteIds (m ∷ ms) b → p ∈ voteIds ms b
voteIds-∷˘ {m = m} {b = b} p≢ p∈ with b ≟ m ∙block | p∈
... | yes _ | here ≡p = ⊥-elim $ p≢ $ sym ≡p
... | yes _ | there p = p
... | no  _ | p       = p

voteIds-∷˘′ : m ∙block ≢ b → p ∈ voteIds (m ∷ ms) b → p ∈ voteIds ms b
voteIds-∷˘′ = subst ((_ ∈_) ∘ map _) ∘ votes-reject _ _

voteIds-head : ∀ b → p ∉ voteIds ms b → p ∈ voteIds (m ∷ ms) b
             → m ∙block ≡ b × m ∙pid ≡ p
voteIds-head {p = p} {m = m} b p∉ p∈ =
  case (m ∙block ≟ b) ,′ (m ∙pid ≟ p) of λ where
    (yes b≡ , yes p≡) → b≡ , p≡
    (yes _  , no  p≢) → ⊥-elim $ p∉ (voteIds-∷˘  {b = b} p≢ p∈)
    (no  b≢ , _)      → ⊥-elim $ p∉ (voteIds-∷˘′ {b = b} b≢ p∈)

voteIds⁻ : p ∈ voteIds ms b → ∃ (λ m → m ∈ ms × m ∙signedBlock ≡ b signed-by p)
voteIds⁻ {p}{m ∷ ms}{b} p∈
  with m ∙block ≟ b
... | no m≢ =
  let m' , m'∈ , eq = voteIds⁻ $ voteIds-∷˘′ m≢ p∈
  in  m' , there m'∈ , eq
... | yes refl
  with m ∙pid ≟ p
... | yes refl = m , here refl , refl
... | no p≢ =
  let m' , m'∈ , eq = voteIds⁻ $ voteIds-∷˘ {b = b} p≢ p∈
  in  m' , there m'∈ , eq

voteIds-here : b ≡ m ∙block → p ≡ m ∙pid → p ∈ voteIds (m ∷ ms) b
voteIds-here {m = m} {ms = ms} refl refl
  rewrite votes-accept m ms refl
  = here refl

voteIds-there : ∀ b → p ∈ voteIds ms b → p ∈ voteIds (m ∷ ms) b
voteIds-there {ms = ms} {m = m} b p∈
  with m ∙block ≟ b
... | yes b≡ rewrite votes-accept m ms b≡ = there p∈
... | no  b≢ rewrite votes-reject m ms b≢ = p∈

voteIds-accept∈ : ∀ {m ms b p} →
  ∙ m ∈ ms
  ∙ b ≡ m ∙block
  ∙ p ≡ m ∙pid
  ──────────────────
    p ∈ voteIds ms b
voteIds-accept∈ {b = b} = λ where
  (here refl) → voteIds-here
  (there m∈)  → voteIds-there b ∘₂ voteIds-accept∈ m∈

-- NotarizedBlock
NotarizedBlock-∷ : NotarizedBlock ms b → NotarizedBlock (m ∷ ms) b
NotarizedBlock-∷ {b = b} {m = m} (record {enoughVotes = IH}) .enoughVotes
  with b ≟ m ∙block
... | no  _ = IH
... | yes _ = majority-∷ IH

NotarizedBlock-∷˘ : m ∙block ≢ b → NotarizedBlock (m ∷ ms) b → NotarizedBlock ms b
NotarizedBlock-∷˘ {m}{b}{ms} b≢ nb .enoughVotes =
  subst IsMajority (votes-reject _ _ b≢) (nb .enoughVotes)


-- NotarizedChain
NotarizedChain-∷ : NotarizedChain ms ch → NotarizedChain (m ∷ ms) ch
NotarizedChain-∷ = λ where
  [] → []
  (px ∷ p) → NotarizedBlock-∷ px ∷ NotarizedChain-∷ p

NotarizedChain-∷˘ :
  ∙ All (m ∙block ≢_) ch
  ∙ NotarizedChain (m ∷ ms) ch
    ──────────────────────────
    NotarizedChain ms ch
NotarizedChain-∷˘ = λ where
  [] [] → []
  (b≢ ∷ ms≢) (px ∷ p) → NotarizedBlock-∷˘ b≢ px ∷ NotarizedChain-∷˘ ms≢ p

NotarizedChain-∉ :
  ∙ m ∙block ∉ ch
  ∙ NotarizedChain (m ∷ ms) ch
    ──────────────────────────
    NotarizedChain ms ch
NotarizedChain-∉ = NotarizedChain-∷˘ ∘ ¬Any⇒All¬ _

-- chain-∈
chain-∈-∷˘ :
  ∙ All (m ∙block ≢_) ch
  ∙ ch chain-∈ (m ∷ ms)
    ────────────────────
    ch chain-∈ ms
chain-∈-∷˘ = λ where
  [] [] → []
  (b≢ ∷ ch≢) (here b≡ ∷ ch∈ ⊣ x) → ⊥-elim $ b≢ $ sym b≡
  (b≢ ∷ ch≢) (there m∈ ∷ ch∈ ⊣ x) → m∈ ∷ chain-∈-∷˘ ch≢ ch∈ ⊣ x

chain-∉ :
  ∙ m ∙block ∉ ch
  ∙ ch chain-∈ (m ∷ ms)
    ────────────────────
    ch chain-∈ ms
chain-∉ = chain-∈-∷˘ ∘ ¬Any⇒All¬ _

-- notarized-chain-∈
notarized-chain-∈-∷ : ch notarized-chain-∈ ms → ch notarized-chain-∈ (m ∷ ms)
notarized-chain-∈-∷ (ch∈ , nch) = chain-∈-∷ ch∈ , NotarizedChain-∷ nch

notarized-chain-∈-∷˘ :
  ∙ All (m ∙block ≢_) ch
  ∙ ch notarized-chain-∈ (m ∷ ms)
    ─────────────────────────────
    ch notarized-chain-∈ ms
notarized-chain-∈-∷˘ ms≢ (ch∈ , nch) = chain-∈-∷˘ ms≢ ch∈ , NotarizedChain-∷˘ ms≢ nch

notarized-chain-∉ :
  ∙ m ∙block ∉ ch
  ∙ ch notarized-chain-∈ (m ∷ ms)
    ─────────────────────────────
    ch notarized-chain-∈ ms
notarized-chain-∉ = notarized-chain-∈-∷˘ ∘ ¬Any⇒All¬ _

notarized-chain-∈-tail : (b ∷ ch) notarized-chain-∈ ms → ch notarized-chain-∈ ms
notarized-chain-∈-tail (_ ∷ ch∈ ⊣ _ , _ ∷ nc) = ch∈ , nc
\end{code}
