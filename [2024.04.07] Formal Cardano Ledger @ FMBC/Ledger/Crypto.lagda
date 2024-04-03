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

\newcommand\crypto{%
\begin{code}
        VKey Sig Ser : Type
\end{code}
\begin{code}[hide]
        SKey : Type
        sign : SKey → Ser → Sig
\end{code}
\begin{code}
        isSigned   : VKey → Ser → Sig → Type
\end{code}
\begin{code}[hide]
        isKeyPair  : SKey → VKey → Type
  KeyPair = Σ[ sk ∈ SKey ] Σ[ vk ∈ VKey ] isKeyPair sk vk
\end{code}
}

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
