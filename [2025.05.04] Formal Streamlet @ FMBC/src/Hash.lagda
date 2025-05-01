\begin{code}[hide]
{-# OPTIONS --safe #-}
module Hash where

open import Prelude

private variable A B : Type
\end{code}
\newcommand\hash{%
\begin{code}
Hash : Type
\end{code}
\vfill\hrule\vfill
\begin{code}
record Hashable (A : Type) : Type where
  field  _♯     : A → Hash
         ♯-inj  : Injective≡ _♯
\end{code}
}
\begin{code}[hide]

  infix 100 _♯

Hash = Bitstring

variable H H′ : Hash

Hashable¹ : ∀ {A} → (A → Type) → Type
Hashable¹ P = ∀ {x} → Hashable (P x)
\end{code}
\newcommand\hashAssumptions{%
\begin{code}
record HashAssumptions : Type₁ where
  field instance
    -- type formers
    Hashable-×      : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A × B)
    Hashable-⊎      : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A ⊎ B)
    Hashable-List   : ⦃ Hashable A ⦄ → Hashable (List A)
    Hashable-Maybe  : ⦃ Hashable A ⦄ → Hashable (Maybe A)

    -- base types
    Hashable-⊤       : Hashable ⊤
    Hashable-ℕ       : Hashable ℕ
    Hashable-String  : Hashable String
\end{code}
\begin{code}[hide]
    Hashable-Bitstring  : Hashable Bitstring
    Hashable-Int        : Hashable ℤ
    Hashable-Float      : Hashable Float
    Hashable-Fin        : ∀{n} → Hashable (Fin n)

open Hashable ⦃...⦄ public
\end{code}
}

\newcommand\signatures{%
\begin{code}
PrivateKey PublicKey Signature : Type
\end{code}
\vfill\hrule\vfill
\begin{code}
record SignatureAssumptions : Type₁ where
  field
    verify-signature  : PublicKey → Signature → Hash → Bool
    sign'             : ⦃ Hashable A ⦄ → PrivateKey → A → Signature
\end{code}
\begin{code}[hide]
Key : Type
Key        = Bitstring
Signature  = Bitstring
PublicKey  = Key
PrivateKey = Key
\end{code}
\begin{code}[hide]
record KeyPair : Type where
  constructor mk-keyPair
  field publicKey  : PublicKey
        privateKey : PrivateKey
open KeyPair public
\end{code}
}
