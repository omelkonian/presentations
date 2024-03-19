open import Ledger.Prelude
open import Ledger.Transaction
open import Ledger.Abstract

module Ledger.Chain.Properties
  (txs : _) (open TransactionStructure txs)
  (abs : AbstractFunctions txs) (open AbstractFunctions abs)
  where

open import Ledger.Ratify txs
open import Ledger.Ledger.Properties txs abs
open import Ledger.Ratify.Properties txs
open import Ledger.Chain txs abs
open import Ledger.Ledger txs abs

open Computational ⦃...⦄

postulate instance
  Computational-NEWEPOCH : Computational _⊢_⇀⦇_,NEWEPOCH⦈_
  Computational-CHAIN : Computational _⊢_⇀⦇_,CHAIN⦈_
