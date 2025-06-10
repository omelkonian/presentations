# Decidability of logical propositions

All the logical propositional appearing in the formulation
of the Jolteon protocol (c.f. `Protocol.Jolteon`) are in fact **decidable**,
meaning that we can utilize *proof-by-computation* to automatically discharge
proofs on closed terms. (c.f. `Protocol.Jolteon.Test`).

Many of these are **already** decidable, by virtue of the decidability of their
building blocks.

The rest of these files provide manual proofs that this is indeed the case
for all other propositions where this is not automatically derived.

```agda
{-# OPTIONS --safe #-}
open import Protocol.Jolteon.Assumptions

module Protocol.Jolteon (⋯ : Assumptions) where

open import Protocol.Jolteon.Base public
open import Protocol.Jolteon.Assumptions public

open import Protocol.Jolteon.Block ⋯ public
open import Protocol.Jolteon.Message ⋯ public
open import Protocol.Jolteon.Local.State ⋯ public
open import Protocol.Jolteon.Local.Step ⋯ public
open import Protocol.Jolteon.Global.State ⋯ public
open import Protocol.Jolteon.Global.NoForging ⋯ public
  using (NoSignatureForging)
open import Protocol.Jolteon.Global.Step ⋯ public
open import Protocol.Jolteon.Global.Trace ⋯ public
```
