\begin{code}[hide]
{-# OPTIONS --safe #-}
module Dec where

open import Prelude.Init
  hiding (Dec; yes; no; True)
open import Prelude.Decidable using (contradict)

private variable P : Type
\end{code}
\newcommand\dec{
\begin{minipage}[t]{.3\textwidth}
\begin{code}
data Dec (P : Type) : Type where
  yes  : P    → Dec P
  no   : ¬ P  → Dec P
\end{code}
\end{minipage}
\hfill\vrule\hfill
\begin{minipage}[t]{.5\textwidth}
\begin{AgdaMultiCode}
\begin{code}
record _⁇ (P : Type) : Type where
  field dec : Dec P
\end{code}
\begin{code}[hide]
open _⁇ ⦃...⦄
\end{code}
\smallskip
\begin{code}
¿_¿ : ∀ P → ⦃ P ⁇ ⦄ → Dec P
¿ _ ¿ = dec
\end{code}
\end{AgdaMultiCode}
\end{minipage}
}
\begin{code}[hide]
infix -100 auto∶_
\end{code}
\newcommand\auto{
\begin{code}
auto∶_ : (P : Type) → ⦃ P ⁇ ⦄ → Type
auto∶ P with ¿ P ¿
... | yes  _ = ⊤
... | no   _ = ⊥
\end{code}
}
\newcommand\decInstances{
\noindent
\hspace{-.8em}
\begin{code}[hide]
auto : ⦃ _ : P ⁇ ⦄ → ⦃ auto∶ P ⦄ → P
auto {P = P} with yes p ← ¿ P ¿ = p

private variable A : Type ℓ; B : Type ℓ′
\end{code}
\begin{minipage}[t]{.25\textwidth}
\begin{code}
instance
  Dec-⊥ : ⊥ ⁇
  Dec-⊥ .dec = no λ()

  Dec-⊤ : ⊤ ⁇
  Dec-⊤ .dec = yes tt
\end{code}
\end{minipage}
\hspace{.8em}\vrule\hspace{.8em}
\begin{minipage}[t]{.67\textwidth}
\begin{code}
module _ ⦃ _ : A ⁇ ⦄ ⦃ _ : B ⁇ ⦄ where instance
  Dec-→ : (A → B) ⁇
  Dec-→ .dec with ¿ A ¿ | ¿ B ¿
  ... | no ¬a  | _      = yes λ a → contradict (¬a a)
  ... | yes a  | yes b  = yes λ _ → b
  ... | yes a  | no ¬b  = no λ f → ¬b (f a)

  Dec-× : (A × B) ⁇
  Dec-× .dec with ¿ A ¿ | ¿ B ¿
  ... | yes a  | yes b  = yes (a , b)
  ... | no ¬a  | _      = no λ (a , _) → ¬a a
  ... | _      | no ¬b  = no λ (_ , b) → ¬b b

  Dec-⊎ : (A ⊎ B) ⁇
  Dec-⊎ .dec   with ¿ A ¿ | ¿ B ¿
  ... | yes a  | _      = yes (inj₁ a)
  ... | _      | yes b  = yes (inj₂ b)
  ... | no ¬a  | no ¬b  = no λ where (inj₁ a) → ¬a a; (inj₂ b) → ¬b b
\end{code}
\end{minipage}
}
