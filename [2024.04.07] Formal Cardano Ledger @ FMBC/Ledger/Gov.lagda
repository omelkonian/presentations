\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
open import Ledger.Prelude
open import Ledger.Types.GovStructure

module Ledger.Gov (gs : _) (open GovStructure gs hiding (epoch)) where

open import Ledger.GovernanceActions gs
\end{code}

The order of proposals is maintained by keeping governance actions in
a list---this acts as a tie breaker when multiple competing actions
might be able to be ratified at the same time.

\begin{minipage}{.6\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record GovActionState : Type where
\end{code}
\begin{code}[hide]
  field
\end{code}
\begin{code}
    votes       : (GovRole × Credential) ⇀ Vote
    returnAddr  : RwdAddr
    expiresIn   : Epoch
    action      : GovAction; prevAction : NeedsHash action

GovState = List (GovActionID × GovActionState)
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\hfill\vrule \hfill
\begin{minipage}{.3\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   GovEnv : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⊗_⟧ᵍ
  field
\end{code}
\begin{code}
    txid        : TxId
    epoch       : Epoch
    pparams     : PParams
    enactState  : EnactState
\end{code}
\end{AgdaMultiCode}
\end{minipage}

\begin{code}[hide]
open GovActionState

private variable
  Γ : GovEnv
  s s' : GovState
  aid : GovActionID
  role : GovRole
  cred : Credential
  v : Vote
  c d : Coin
  addr : RwdAddr
  a : GovAction
  prev : NeedsHash a
  k : ℕ
\end{code}

%% \emph{Functions used in the GOV rules}
\newcommand\govAddVote{%
The two functions adjusting the state in GOV are \addVote and \addAction.

\begin{itemize}
\item \addVote inserts (and potentially overrides) a vote made for a
  particular governance action by a credential in a role.

\item \addAction adds a new proposed action at the end of a given
  \GovState, properly initializing all the requiered fields.
\end{itemize}

\begin{code}
addVote : GovState → GovActionID → GovRole → Credential → Vote → GovState
addVote s aid r kh v = map modifyVotes s
  where modifyVotes = λ (gid , s') → gid , record s'
          { votes = if gid ≡ aid then insert (votes s') (r , kh) v else votes s'}

addAction : GovState
          → Epoch → GovActionID → RwdAddr → (a : GovAction) → NeedsHash a
          → GovState
addAction s e aid addr a prev = s ∷ʳ (aid , record
  { votes = ∅ ; returnAddr = addr ; expiresIn = e ; action = a ; prevAction = prev })
\end{code}
\begin{code}[hide]
validHFAction : GovProposal → GovState → EnactState → Type
validHFAction (record { action = TriggerHF v ; prevAction = prev }) s e =
  (let (v' , aid) = EnactState.pv e in aid ≡ prev × pvCanFollow v' v)
  ⊎ ∃₂[ x , v' ] (prev , x) ∈ fromList s × x .action ≡ TriggerHF v' × pvCanFollow v' v
validHFAction _ _ _ = ⊤
\end{code}
}

\hrule
\begin{AgdaMultiCode}
\begin{code}[hide]
data  _⊢_⇀⦇_,GOV⦈_ : GovEnv × ℕ → GovState → GovVote ⊎ GovProposal → GovState → Type where
\end{code}
\begin{code}
  GOV-Vote :
\end{code}
\begin{code}[hide]
    ∀ {x ast} →
    let  open GovEnv Γ
         sig = inj₁ record  { gid = aid ; role = role
                            ; credential = cred
                            ; vote = v ; anchor = x }
    in
\end{code}
\begin{code}
      ∙  (aid , ast) ∈ fromList s ∙  canVote pparams (action ast) role
         ───────────────────────────────────────
         (Γ , k) ⊢ s ⇀⦇ sig ,GOV⦈ addVote s aid role cred v

  GOV-Propose :
\end{code}
\begin{code}[hide]
   ∀ {x} →
    let  open GovEnv Γ
         open PParams pparams hiding (a)
         prop = record  { returnAddr = addr ; action = a
                        ; anchor = x ; deposit = d
                        ; prevAction = prev }
    in
      ∙  (∀ {new rem q} → a ≡ NewCommittee new rem q → ∀[ e ∈ range new ]  epoch < e  ×  dom new ∩ rem ≡ᵉ ∅)
      ∙  validHFAction prop s enactState
\end{code}
\begin{code}
      ∙  actionWellFormed a ≡ true ∙  d ≡ govActionDeposit
         ───────────────────────────────────────
         (Γ , k) ⊢ s ⇀⦇ inj₂ prop ,GOV⦈ addAction s (govActionLifetime +ᵉ epoch) (txid , k) addr a prev
\end{code}
\end{AgdaMultiCode}
\begin{code}[hide]
_⊢_⇀⦇_,GOV∗⦈_ : GovEnv → GovState → List (GovVote ⊎ GovProposal) → GovState → Type
_⊢_⇀⦇_,GOV∗⦈_ = ReflexiveTransitiveClosureᵢ _⊢_⇀⦇_,GOV⦈_
\end{code}
