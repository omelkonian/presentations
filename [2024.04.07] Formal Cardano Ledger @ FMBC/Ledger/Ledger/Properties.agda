open import Ledger.Prelude
open import Ledger.Transaction
open import Ledger.Abstract

module Ledger.Ledger.Properties
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where

open import Ledger.Deleg.Properties govStructure
open import Ledger.Gov govStructure
open import Ledger.Gov.Properties govStructure
open import Ledger.Ledger txs abs
open import Ledger.Utxo txs abs
open import Ledger.Utxo.Properties txs abs
open import Ledger.Utxow txs abs
open import Ledger.Utxow.Properties txs abs

-- ** Proof that LEDGER is computational.

postulate instance
  Computational-LEDGER : Computational _⊢_⇀⦇_,LEDGER⦈_

Computational-LEDGER∗ : Computational _⊢_⇀⦇_,LEDGER∗⦈_
Computational-LEDGER∗ = it

instance
  HasCoin-LState : HasCoin LState
  HasCoin-LState .getCoin s = getCoin (LState.utxoSt s)

-- ** Proof that LEDGER preserves values.

private variable
  tx : Tx
  Γ : LEnv
  s s' : LState
  l : List Tx

FreshTx : Tx → LState → Set
FreshTx tx ls = tx .body .txid ∉ mapˢ proj₁ (dom (ls .utxoSt .utxo))
  where open Tx; open TxBody; open UTxOState; open LState

postulate
  LEDGER-pov : FreshTx tx s → Γ ⊢ s ⇀⦇ tx ,LEDGER⦈ s' → getCoin s ≡ getCoin s'

data FreshTxs : LEnv → LState → List Tx → Set where
  []-Fresh : FreshTxs Γ s []
  ∷-Fresh  : FreshTx tx s → Γ ⊢ s ⇀⦇ tx ,LEDGER⦈ s' → FreshTxs Γ s' l
            → FreshTxs Γ s (tx ∷ l)

LEDGER∗-pov : FreshTxs Γ s l → Γ ⊢ s ⇀⦇ l ,LEDGER∗⦈ s' → getCoin s ≡ getCoin s'
LEDGER∗-pov _ (BS-base Id-nop) = refl
LEDGER∗-pov {Γ} {_} {_ ∷ l} (∷-Fresh h h₁ h₂) (BS-ind x st) =
  trans (LEDGER-pov h x) $
    LEDGER∗-pov (subst (λ s → FreshTxs Γ s l)
                        (sym $ computational⇒rightUnique Computational-LEDGER x h₁)
                        h₂) st
