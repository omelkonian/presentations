\documentclass[main]{subfiles}
\begin{document}
\begin{frame}[fragile]{The notion of \alert{finite support}}
\begin{code}[hide]
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.InfEnumerable
open import Prelude.InferenceRules

\end{code}
\begin{code}[inline]
module
\end{code}
\begin{code}[hide,inline]
  Nominal.Support (Atom : Type) ⦃ _ : DecEq Atom ⦄
\end{code}$\ \dots$
\begin{code}[inline]
  ⦃ _ : Enumerable∞ Atom ⦄ where
\end{code}
\begin{code}[hide]

open import Nominal.New  Atom
open import Nominal.Swap Atom

freshAtom : Atoms → Atom
freshAtom = proj₁ ∘ minFresh

freshAtom∉ : ∀ {xs : Atoms} → freshAtom xs ∉ xs
freshAtom∉ {xs} = minFresh xs .proj₂

private variable A : Type ℓ; B : Type ℓ′

module _ ⦃ _ : ISetoid A ⦄ ⦃ _ : Swap A ⦄ where
\end{code}
\begin{code}
  FinSupp : Pred A _
  FinSupp x = И² λ 𝕒 𝕓 → swap 𝕓 𝕒 x ≈ x

  Equivariant′ : Pred A _
  Equivariant′  x = ∃ λ (fin-x : FinSupp x)  → fin-x .proj₁ ≡ []

\end{code}
\begin{code}[hide]
module _  (A : Type ℓ)
          ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
          ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄ where
\end{code}
\begin{code}
  record FinitelySupported : Typeω where
    field ∀fin : Unary.Universal FinSupp

    supp : A → Atoms
    supp = proj₁ ∘ ∀fin

    fresh∉ : (a : A) → ∃ (_∉ supp a)
    fresh∉ = minFresh ∘ supp

\end{code}
\begin{code}[hide]
    fresh-var : A → Atom
    fresh-var = proj₁ ∘ fresh∉

    swap-fresh : ∀ {𝕒 𝕓} (x : A) →
      ∙ 𝕒 ∉ supp x
      ∙ 𝕓 ∉ supp x
        ────────────────
        ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ x
    swap-fresh x = flip (∀fin x .proj₂ _ _)

open FinitelySupported ⦃...⦄ public

\end{code}
\end{frame}
\begin{frame}{Finitely supported \alert{atoms}}
\begin{code}
instance
  FinSupp-Atom : FinitelySupported Atom
  FinSupp-Atom .∀fin 𝕒 = [ 𝕒 ] , λ _ _ y∉ z∉ →
    swap-noop _ _ _ λ where 𝟘 → z∉ 𝟘; 𝟙 → y∉ 𝟘
\end{code}
\begin{code}[hide]
-- T0D0: generalize this to more complex types than Atom (c.f. supp-swap above)
supp-swap-atom : ∀ {𝕒 𝕓} (t : Atom) → supp (swap 𝕒 𝕓 t) ⊆ 𝕒 ∷ 𝕓 ∷ t ∷ []
-- supp (swap 𝕒 𝕓 t) ≡ swap 𝕒 𝕓 (supp t)
supp-swap-atom {a}{b} t
  with t ≟ a
... | yes refl = λ where 𝟘 → 𝟙
... | no _
  with t ≟ b
... | yes refl = λ where 𝟘 → 𝟘
... | no _     = λ where 𝟘 → 𝟚
\end{code}
\end{frame}
\end{document}
