open import Ledger.Prelude
open import Ledger.GovStructure

open import Data.Maybe.Properties
open import Relation.Nullary.Decidable

open import Tactic.ReduceDec

module Ledger.Deleg.Properties (gs : _) (open GovStructure gs) where

open import Ledger.GovernanceActions gs hiding (yes; no)
open import Ledger.Deleg gs

open Computational ⦃...⦄

postulate instance
  Computational-DELEG : Computational _⊢_⇀⦇_,DELEG⦈_
  Computational-POOL : Computational _⊢_⇀⦇_,POOL⦈_
  Computational-GOVCERT : Computational _⊢_⇀⦇_,GOVCERT⦈_
  Computational-CERT : Computational _⊢_⇀⦇_,CERT⦈_
  Computational-CERTBASE : Computational _⊢_⇀⦇_,CERTBASE⦈_

Computational-CERTS : Computational _⊢_⇀⦇_,CERTS⦈_
Computational-CERTS = it
