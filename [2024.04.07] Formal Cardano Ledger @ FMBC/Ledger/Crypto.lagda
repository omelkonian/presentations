\begin{code}[hide]
{-# OPTIONS --safe #-}
module Ledger.Crypto where

open import Ledger.Prelude hiding (T)
open import Agda.Primitive renaming (Set to Type)

record isHashableSet (T : Type) : Type₁ where
  constructor mkIsHashableSet
  field THash : Type
        ⦃ DecEq-THash ⦄ : DecEq      THash
        ⦃ DecEq-T     ⦄ : DecEq    T
        ⦃ T-Hashable  ⦄ : Hashable T THash
open isHashableSet

record HashableSet : Type₁ where
  constructor mkHashableSet
  field T : Type; ⦃ T-isHashable ⦄ : isHashableSet T
  open isHashableSet T-isHashable public

record PKKScheme : Type₁ where
  field
\end{code}

There are two types of credentials that can be used on Cardano: VKey
and script credentials. VKey credentials use a public key signing
scheme (Ed25519) for verification. Some serialized (\Ser) data can be
signed, and \isSigned is the property that a public \VKey signed some
data with a given signature. There are also other cryptographic
primitives in the Cardano ledger, for example KES and VRF used in the
consensus layer, but we omit those here.

Script credentials correspond to a hash of a script that has to be
executed by the ledger as part of transaction validation. There are
two different types of scripts, native and Plutus, but the details of
this are not relevant for the rest of this paper.

\begin{minipage}{.25\textwidth}
\begin{code}
        VKey Sig Ser : Type
\end{code}
\begin{code}[hide]
        SKey : Type
        sign : SKey → Ser → Sig
\end{code}
\end{minipage}
\hfill
\begin{minipage}{.45\textwidth}
\begin{code}
        isSigned   : VKey → Ser → Sig → Type
\end{code}
\begin{code}[hide]
        isKeyPair  : SKey → VKey → Type
  KeyPair = Σ[ sk ∈ SKey ] Σ[ vk ∈ VKey ] isKeyPair sk vk
\end{code}
\end{minipage}

\begin{code}[hide]
  field ⦃ Dec-isSigned ⦄ : isSigned ⁇³
        isSigned-correct :
\end{code}
\begin{code}[hide]
          ∀ sk vk d σ → sign sk d ≡ σ → isSigned vk d σ
\end{code}
\begin{code}[hide]
        ⦃ DecEq-Sig  ⦄ : DecEq Sig
        ⦃ DecEq-Ser  ⦄ : DecEq Ser

record Crypto : Type₁ where
  field pkk : PKKScheme

  open PKKScheme pkk public

  field ⦃ khs ⦄    : isHashableSet VKey
        ScriptHash : Type; ⦃ DecEq-ScriptHash ⦄ : DecEq ScriptHash

  open isHashableSet khs renaming (THash to KeyHash) hiding (DecEq-T) public

-- TODO: KES and VRF
\end{code}

In the specification, all definitions that require these primitives
must accept these as additional arguments. To streamline this process,
these definitions are bundled into a record and, using Agda's module
system, are quantified only once per file. We are using this pattern
many times, either to introduce additional abstraction barriers or to
effectively provide foreign functions within a safe
environment. Additionally, particularly fundamental interfaces like
the one presented above are sometimes re-bundled transitively into
larger records, which further streamlines the interface. This is in
stark contrast to the Haskell implementation, which often needs to
repeat tens of type class constraints on many functions in a module.
