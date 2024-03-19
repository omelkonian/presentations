\begin{AgdaAlign}
\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Prelude hiding (Rel)
open import Agda.Primitive renaming (Set to Type)

open import Algebra as Alg       using (IsCommutativeMonoid; CommutativeMonoid)
open import Algebra.Morphism     using (module MonoidMorphisms )
open import Data.Nat.Properties  using (+-0-monoid)
open import Relation.Binary      using (Rel)
open import Relation.Unary       using (Pred)

module Ledger.TokenAlgebra (PolicyId : Type) where
\end{code}

The Cardano ledger natively supports multiple currencies
\cite{eutxoma}. This is implemented via the notion of a \TokenAlgebra,
which is an ordered commutative monoid togother with some additional
structure that is not relevant here. Both the \Coin type and the Value
type described in \cite{eutxoma} can be given the structure of a
\TokenAlgebra.

\AgdaTarget{TokenAlgebra}
\begin{AgdaSuppressSpace}
\begin{code}[hide]
record CommMonoid (A : Type) (_≈_ : Rel A 0ℓ) : Type where
  field ⦃ semigroup ⦄ : Semigroup A
        ⦃ monoid ⦄    : Monoid A
        isCommMonoid  : IsCommutativeMonoid {A = A} _≈_ _◇_ ε

  commMonoid : CommutativeMonoid 0ℓ 0ℓ
  commMonoid = record
    { Carrier             = A
    ; _≈_                 = _≈_
    ; _∙_                 = _◇_
    ; ε                   = ε
    ; isCommutativeMonoid = isCommMonoid }
open CommMonoid ⦃...⦄ public hiding (semigroup; monoid)

module _ {A : Type} {_≈_ : Rel A 0ℓ} ⦃ _ : CommMonoid A _≈_ ⦄ where
  rawMonoid : Alg.RawMonoid 0ℓ _
  rawMonoid = record { Carrier = A ; _≈_ = _≈_ ; _∙_ = _◇_ ; ε = ε }

  _≈ᶜᵐ_ = _≈_
\end{code}
\begin{code}[hide]
record TokenAlgebra : Type₁ where
\end{code}
\begin{code}[hide]
  MemoryEstimate = ℕ
  field
\end{code}
\begin{code}[hide]
    Value AssetName  : Type
\end{code}
\begin{code}[hide,inline]
    _≈ᵛ_ : Rel Value 0ℓ
    ⦃ CM-Value ⦄     : CommMonoid Value _≈ᵛ_
\end{code}
\begin{code}[hide]
    specialAsset     : AssetName
\end{code}
\begin{code}[hide]
    policies         : Value → ℙ PolicyId
    size             : Value → MemoryEstimate
\end{code}
\begin{code}[hide]
    coin         : Value → Coin
    inject       : Coin → Value
    coin∘inject  : coin ∘ inject ≗ id
\end{code}
\begin{code}[hide,inline]
  open MonoidMorphisms rawMonoid (Alg.Monoid.rawMonoid +-0-monoid) public
  open Semigroup {A = Value} it renaming (_◇_ to _+ᵛ_) public
  field
\end{code}
\begin{code}[hide]
    coinHomo     : IsMonoidHomomorphism coin
\end{code}
\end{AgdaSuppressSpace}
\begin{code}[hide]
    _≤ᵗ_ : Value → Value → Type
    ⦃ DecEq-Value ⦄ : DecEq Value
    ⦃ Dec-≤ᵗ ⦄      : _≤ᵗ_ ⁇²

  instance
    addValue : HasAdd Value
    addValue = record { _+_ = _+ᵛ_ }
\end{code}
\end{AgdaAlign}
