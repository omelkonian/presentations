\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Agda.Primitive renaming (Set to Type)
import Data.List as L

open import Ledger.Prelude
open import Ledger.Abstract
open import Ledger.Transaction using (TransactionStructure)

open import Tactic.MkRecord

module Ledger.Ledger
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where

open import Ledger.Gov govStructure
open import Ledger.PPUp txs
open import Ledger.Utxo txs abs
open import Ledger.Utxow txs abs

open Tx
\end{code}

\newcommand\ledger{%
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   LEnv : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⊗_⟧ˡ
  field
\end{code}
\begin{code}
    slot        : Slot
    ppolicy     : Maybe ScriptHash
    pparams     : PParams
    enactState  : EnactState
\end{code}
\end{AgdaMultiCode}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}{.4\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record   LState : Type where
\end{code}
\begin{code}[hide]
  constructor ⟦_⊗_⊗_⟧ˡ
  field
\end{code}
\begin{code}
    utxoSt     : UTxOState
    govSt      : GovState
    certState  : CertState
\end{code}
\end{AgdaMultiCode}
\end{minipage}

\begin{code}[hide]
txgov : TxBody → List (GovVote ⊎ GovProposal)
txgov txb = map inj₁ txvote ++ map inj₂ txprop
  where open TxBody txb

mkUTxOEnv : LEnv → UTxOEnv
mkUTxOEnv Γ = record { LEnv Γ }

private variable
  Γ : LEnv
  s s' s'' : LState
  utxoSt' : UTxOState
  govSt' : GovState
  certState' : CertState
  tx : Tx

open RwdAddr
open DState
open CertState
\end{code}
\hrule
\begin{AgdaMultiCode}
\begin{code}[hide]
data  _⊢_⇀⦇_,LEDGER⦈_ : LEnv → LState → Tx → LState → Type where
\end{code}
\begin{code}
  LEDGER :
\end{code}
\begin{code}[hide]
    let open LState s; txb = tx .body; open TxBody txb; open LEnv Γ in
\end{code}
\begin{code}
      ∙  mkUTxOEnv Γ ⊢ utxoSt ⇀⦇ tx ,UTXOW⦈ utxoSt'
      ∙  ⟦ epoch slot ⊗ pparams ⊗ txvote ⊗ txwdrls ⟧ᶜ ⊢ certState ⇀⦇ txcerts ,CERT∗⦈ certState'
      ∙  ⟦ txid ⊗ epoch slot ⊗ pparams ⊗ enactState ⟧ᵍ ⊢ govSt ⇀⦇ txgov txb ,GOV∗⦈ govSt'
         ───────────────────────────────────────
         Γ ⊢ s ⇀⦇ tx ,LEDGER⦈ ⟦ utxoSt' ⊗ govSt' ⊗ certState' ⟧
\end{code}
\end{AgdaMultiCode}
\begin{code}[hide]
_⊢_⇀⦇_,LEDGER∗⦈_ = ReflexiveTransitiveClosure _⊢_⇀⦇_,LEDGER⦈_
pattern LEDGER⋯ x y z w = LEDGER (x , y , z , w)
\end{code}
}
