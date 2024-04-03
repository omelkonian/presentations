import Data.List.Membership.Propositional as P
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any

open import Ledger.Prelude hiding (Any; any?)
open import Ledger.Types.GovStructure

module Ledger.Gov.Properties (gs : _) (open GovStructure gs hiding (epoch)) where

open import Ledger.Gov gs
open import Ledger.GovernanceActions gs hiding (yes; no)

open Computational ⦃...⦄
open Equivalence
open GovActionState
open Inverse

postulate instance
  Computational-GOV : Computational _⊢_⇀⦇_,GOV⦈_

Computational-GOV∗ : Computational _⊢_⇀⦇_,GOV∗⦈_
Computational-GOV∗ = it
