# Examples that require (unsafe) dummy hashing.
```agda
-- {-# OPTIONS --safe #-}

-- ** example traces
open import Protocol.Jolteon.Traces {- unsafe due to dummy hashing -}

-- postulate proofs for quicker LaTeX generation
open import Protocol.Jolteon.Local.Slice.TraceVerifier
```
