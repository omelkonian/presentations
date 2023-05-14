\documentclass[main]{subfiles}
\begin{document}
\begin{code}[hide]
module _ where
open import Prelude.Init; open SetAsType
open L.Mem
open Unary using (_∩_)
open import Prelude.Lists.Membership
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Functor
open import Prelude.FromList; open import Prelude.ToList
open import Prelude.DecEq
open import Prelude.Monad
open import Prelude.Maybes
open import Prelude.Membership using (_∉?_)

import Prelude.Bags as B
import Prelude.Maps as M

open import Common

module ℂ where
  open import UTxOErr.UTxO public
  open import UTxOErr.Ledger public
    renaming (VL to ValidLedger)
  open import UTxOErr.HoareLogic public

open ℂ using ([]; _⊣_∷_)
module 𝔸 where
  open import ValueSepUTxO.UTxO public
  open import ValueSepUTxO.Ledger public
    renaming (VL to ValidLedger)
  open import ValueSepUTxO.UTxO public
  open import ValueSepUTxO.HoareLogic public
open 𝔸 using ([]; _⊣_∷_)

-- ** abstracting away implementation details
private variable
  s s′ : ℂ.S
  l : ℂ.L
  t : ℂ.Tx
  P Q : Pred₀ 𝔸.S
\end{code}
\begin{frame}{Sound Abstraction: States and Validity}
\begin{code}
absS : ℂ.S → 𝔸.S
\end{code}
\begin{code}[hide]
absS = ℂ.valuesˢ
open ≡-Reasoning
\end{code}
\begin{code}

absVT : ℂ.IsValidTx t s → ∃ λ t̂ → 𝔸.IsValidTx t̂ (absS s)
\end{code}
\begin{code}[hide]
absVT {t}{s} vt = t̂ , record
  { validOutputRefs     = vor′
  ; preservesValues     = pv′
  ; allInputsValidate   = L.All.tabulate aiv′
  ; validateValidHashes = L.All.tabulate vvh′ }
  module ∣absVT∣ where
    is = t .ℂ.inputs; os = t .ℂ.outputs; frg = t .ℂ.forge
    vor = vt .ℂ.validOutputRefs

    goI : ℂ.TxInput × ℂ.TxOutput → 𝔸.TxInput
    goI (record {outputRef = _; validator = f; redeemer = r} , o)
       = record {outputRef = o; validator = f; redeemer = r}

    ris = ℂ.resolvedInputs vt
    is′ = map goI ris

    t̂ = record {inputs = is′; outputs = os; forge = frg}
    ŝ = absS s

    stxo≡ : 𝔸.stxoTx t̂ ≡ ℂ.values⊑ˢ s (-, vor)
    stxo≡ rewrite
      begin
        𝔸.outputRefs t̂
      ≡˘⟨ L.map-compose ris ⟩
        (𝔸.outputRef ∘ goI) <$> ris
      ≡⟨ map∘mapWith∈ (𝔸.outputRef ∘ goI) is _ ⟩
        mapWith∈ is _
      ≡⟨ mapWith∈-cong is _ _ (λ _ → refl) ⟩
        mapWith∈ is (ℂ.resolved vt ∘ ∈-map⁺ ℂ.outputRef)
      ≡˘⟨ mapWith∈∘map ℂ.outputRef is (ℂ.resolved vt) ⟩
        mapWith∈ (ℂ.outputRef <$> is) (ℂ.resolved vt)
      ≡⟨⟩
        ℂ.values⊑ s (-, vor)
      ∎ = refl

    vor′ : 𝔸.stxoTx t̂ B.⊆ˢ ŝ
    vor′ = subst (B._⊆ˢ ℂ.valuesˢ s) (sym stxo≡) (ℂ.values⊆⇒⊆ˢ s (-, vor))

    pv′ =
      begin
        t̂ .𝔸.forge + ∑ (t̂ .𝔸.inputs) (value ∘ 𝔸.outputRef)
      ≡⟨⟩
        frg + ∑ (map goI ris) (value ∘ 𝔸.outputRef)
      ≡⟨ cong (λ ◆ → frg + ◆) $ cong sum $ sym $ L.map-compose ris ⟩
        frg + ∑ ris (value ∘ proj₂)
      ≡⟨ vt .ℂ.preservesValues ⟩
        ∑ os value
      ≡⟨⟩
        ∑ (t̂ .𝔸.outputs) value
      ∎

    inputInfo≡ =
      begin
        (𝔸.mkInputInfo <$> 𝔸.resolveInputs t̂ (𝔸.resolved t̂))
      ≡⟨ map∘mapWith∈ 𝔸.mkInputInfo is′ _ ⟩
        mapWith∈ (goI <$> ris) _
      ≡⟨ mapWith∈∘map goI ris _ ⟩
        mapWith∈ ris _
      ≡⟨ mapWith∈-cong ris _ _ (λ _ → refl) ⟩
        mapWith∈ ris _
      ≡⟨ mapWith∈≗map _ ris ⟩
        (ℂ.mkInputInfo <$> ris)
      ∎

    aiv′ : ∀ {i} → i ∈ is′ →
      T $ i .𝔸.validator (𝔸.mkTxInfo t̂ $ 𝔸.resolved t̂) (i .𝔸.redeemer)
    aiv′ i∈
      with _ , i∈ , refl ← ∈-map⁻ goI i∈
      rewrite
        begin
          𝔸.mkTxInfo t̂ (𝔸.resolved t̂)
        ≡⟨ cong (λ ◆ → record {inputs = ◆; outputs = os; forge = frg}) inputInfo≡ ⟩
          ℂ.mkTxInfo t (ℂ.resolved vt)
        ∎
      with _ , i∈ , refl ← ∈-mapWith∈⁻ i∈
      = L.All.lookup (vt .ℂ.allInputsValidate) i∈

    vvh′ : ∀ {i} → i ∈ is′ → i .𝔸.outputRef .address ≡ i .𝔸.validator ♯
    vvh′ i∈
      with _ , i∈ , refl ← ∈-map⁻ goI i∈
      = L.All.lookup (vt .ℂ.validateValidHashes) i∈

absT : ℂ.IsValidTx t s → 𝔸.Tx
absT = proj₁ ∘ absVT

absS-utxo : ∀ (vt : ℂ.IsValidTx t s) → absS (ℂ.utxoTx t) ≡ 𝔸.utxoTx (absT vt)
absS-utxo {t}{s} vt =
  begin
    absS (fromList $ mapWith∈ (t .ℂ.outputs) (ℂ.mkUtxo t))
  ≡⟨⟩
    ℂ.valuesˢ (fromList $ mapWith∈ (t .ℂ.outputs) (ℂ.mkUtxo t))
  ≡⟨ ℂ.valuesˢ∘fromList $ ℂ.Unique-mkUtxo t ⟩
    fromList (proj₂ <$> mapWith∈ (t .ℂ.outputs) (ℂ.mkUtxo t))
  ≡⟨ cong fromList
   $ begin
        proj₂ <$> mapWith∈ (t .ℂ.outputs) (ℂ.mkUtxo t)
      ≡⟨ map∘mapWith∈ proj₂ _ _ ⟩
        mapWith∈ (t .ℂ.outputs) (proj₂ ∘ ℂ.mkUtxo t)
      ≡⟨ mapWith∈-cong _ _ _ (λ _ → refl) ⟩
        mapWith∈ (t .ℂ.outputs) (λ {o} _ → o)
      ≡⟨ mapWith∈≗map id _ ⟩
        map id (t .ℂ.outputs)
      ≡⟨ L.map-id _ ⟩
        t .ℂ.outputs
      ∎
   ⟩
    fromList (t .ℂ.outputs)
  ≡⟨⟩
    fromList (absT vt .𝔸.outputs)
  ∎

absS-stxo : ∀ (vt : ℂ.IsValidTx t s) →
  absS (s ℂ.─ᵏˢ ℂ.outputRefs t) ≡ absS s B.─ 𝔸.stxoTx (absT vt)
absS-stxo {t@record{outputs = os}}{s} vt@record{validOutputRefs = vor} =
  let t̂ = absT vt in
  begin
    absS (s ℂ.─ᵏˢ ℂ.outputRefs t)
  ≡⟨⟩
    ℂ.valuesˢ (s ℂ.─ᵏˢ ℂ.outputRefs t)
  ≡⟨ ℂ.valuesˢ-─ s (-, vor) ⟩
    ℂ.valuesˢ s B.─ ℂ.values⊑ˢ s (-, vor)
  ≡˘⟨ cong (ℂ.valuesˢ s B.─_) $ ∣absVT∣.stxo≡ vt ⟩
    ℂ.valuesˢ s B.─ 𝔸.stxoTx t̂
  ≡⟨⟩
    absS s B.─ 𝔸.stxoTx t̂
  ∎
denot-abs-t₀ : ∀ (vt : ℂ.IsValidTx t s) →
  𝔸.⟦ absT vt ⟧₀ (absS s) ≡ absS (ℂ.⟦ t ⟧₀ s)
denot-abs-t₀ {t}{s} vt = let t̂ = absT vt in
  sym $ begin
    absS (s ℂ.─ᵏˢ ℂ.outputRefs t M.∪ ℂ.utxoTx t)
  ≡⟨ ℂ.valuesˢ-∪ (s ℂ.─ᵏˢ ℂ.outputRefs t) (ℂ.utxoTx t) (ℂ.s♯t vt) ⟩
    absS (s ℂ.─ᵏˢ ℂ.outputRefs t) B.∪ absS (ℂ.utxoTx t)
  ≡⟨ cong (B._∪ _) (absS-stxo vt) ⟩
    absS s B.─ 𝔸.stxoTx t̂ B.∪ absS (ℂ.utxoTx t)
  ≡⟨ cong (absS s B.─ 𝔸.stxoTx t̂ B.∪_) (absS-utxo vt) ⟩
    absS s B.─ 𝔸.stxoTx t̂ B.∪ 𝔸.utxoTx t̂
  ∎

denot-t : ∀ {t : ℂ.Tx} {s : ℂ.S} (vt : ℂ.IsValidTx t s) →
  ℂ.⟦ t ⟧ s ≡ just (ℂ.⟦ t ⟧₀ s)
denot-t {t}{s} vt rewrite dec-yes (ℂ.isValidTx? t s) vt .proj₂ = refl

denot-t̂ : ∀ {t : 𝔸.Tx} {s : 𝔸.S} (vt : 𝔸.IsValidTx t s) →
  𝔸.⟦ t ⟧ s ≡ just (𝔸.⟦ t ⟧₀ s)
denot-t̂ {t}{s} vt rewrite dec-yes (𝔸.isValidTx? t s) vt .proj₂ = refl
\end{code}
\begin{code}

absVL : ℂ.ValidLedger s l → ∃ λ l̂ → 𝔸.ValidLedger (absS s) l̂
\end{code}
\end{frame}
\begin{frame}{Sound Abstraction: Denotations Coincide}
\begin{code}
denot-abs-t : ∀ (vt : ℂ.IsValidTx t s) →
  𝔸.⟦ absT vt ⟧ (absS s) ≡ (absS <$> ℂ.⟦ t ⟧ s)
\end{code}

\begin{code}[hide]
denot-abs-t {t}{s} vt =
  begin
    𝔸.⟦ absT vt ⟧ (absS s)
  ≡⟨ denot-t̂ (absVT vt .proj₂) ⟩
    just (𝔸.⟦ absT vt ⟧₀ $ absS s)
  ≡⟨ cong just $ denot-abs-t₀ vt ⟩
    just (absS $ ℂ.⟦ t ⟧₀ s)
  ≡˘⟨ M.map-just $ denot-t vt ⟩
    (absS <$> ℂ.⟦ t ⟧ s)
  ∎
\end{code}
\begin{code}[hide]
absVL [] = -, []
absVL {s}{.t ∷ l} (t ⊣ vt ∷ vl) =
  let
    t̂ , vt̂ = absVT {s = s} vt
    l̂  , vl̂ = absVL vl

    EQ : absS (ℂ.⟦ t ⟧₀ s) ≡ 𝔸.⟦ t̂ ⟧₀ (absS s)
    EQ = sym $ denot-abs-t₀ vt
  in
    t̂ ∷ l̂ , t̂ ⊣ vt̂ ∷ subst (λ ◆ → 𝔸.ValidLedger ◆ l̂) EQ vl̂

absL : ℂ.ValidLedger s l → 𝔸.L
absL = proj₁ ∘ absVL

denot-abs₀ : ∀ (vl : ℂ.ValidLedger s l) →
  𝔸.⟦ absL vl ⟧₀ (absS s) ≡ absS (ℂ.⟦ l ⟧₀ s)
denot-abs₀ [] = refl
denot-abs₀ {s} {t ∷ l} (t ⊣ vt ∷ vl) = let ŝ = absS s; t̂ = absT vt; l̂ = absL vl in
  begin
    𝔸.⟦ l̂ ⟧₀ (𝔸.⟦ t̂ ⟧₀ ŝ)
  ≡⟨ cong 𝔸.⟦ l̂ ⟧₀ $ denot-abs-t₀ vt ⟩
    𝔸.⟦ l̂ ⟧₀ (absS $ ℂ.⟦ t ⟧₀ s)
  ≡⟨ denot-abs₀ {s = ℂ.⟦ t ⟧₀ s} vl ⟩
    absS (ℂ.⟦ l ⟧₀ $ ℂ.⟦ t ⟧₀ s)
  ∎

denot-l : ∀ {l : ℂ.L} {s : ℂ.S} (vl : ℂ.ValidLedger s l) →
  ℂ.⟦ l ⟧ s ≡ just (ℂ.⟦ l ⟧₀ s)
denot-l [] = refl
denot-l (_ ⊣ vt ∷ vl) rewrite denot-t vt | denot-l vl = refl

denot-l̂ : ∀ {l : 𝔸.L} {s : 𝔸.S} (vl : 𝔸.ValidLedger s l) →
  𝔸.⟦ l ⟧ s ≡ just (𝔸.⟦ l ⟧₀ s)
denot-l̂ [] = refl
denot-l̂ (_ ⊣ vt ∷ vl) rewrite denot-t̂ vt | denot-l̂ vl = refl
\end{code}
\begin{code}
denot-abs : ∀ (vl : ℂ.ValidLedger s l) →
  𝔸.⟦ absL vl ⟧ (absS s) ≡ (absS <$> ℂ.⟦ l ⟧ s)
\end{code}
\begin{code}[hide]
denot-abs [] = refl
denot-abs {s} {t ∷ l} (.t ⊣ vt ∷ vl)
  rewrite denot-t vt | denot-t̂ (absVT vt .proj₂) =
  let ŝ = absS s; t̂ = absT vt; l̂ , vl̂ = absVL vl in
  begin
    𝔸.⟦ l̂ ⟧ (𝔸.⟦ t̂ ⟧₀ ŝ)
  ≡⟨ cong 𝔸.⟦ l̂ ⟧ $ denot-abs-t₀ vt ⟩
    𝔸.⟦ l̂ ⟧ (absS $ ℂ.⟦ t ⟧₀ s)
  ≡⟨ denot-l̂ vl̂ ⟩
    just (𝔸.⟦ l̂ ⟧₀ $ absS $ ℂ.⟦ t ⟧₀ s)
  ≡⟨ cong just $ denot-abs₀ vl ⟩
    just (absS $ ℂ.⟦ l ⟧₀ $ ℂ.⟦ t ⟧₀ s)
  ≡˘⟨ M.map-just $ denot-l vl ⟩
    (absS <$> ℂ.⟦ l ⟧ (ℂ.⟦ t ⟧₀ s))
  ∎

↑ = M.Any.Any

denot-sound : ∀ (vl : ℂ.ValidLedger s l) →
  (P (absS s) → ↑ Q (𝔸.⟦ absL vl ⟧ $ absS s))
  ───────────────────────────────────────────
  (P (absS s) → ↑ Q (absS <$> ℂ.⟦ l ⟧ s))
denot-sound vl PlQ Ps = subst (↑ _) (denot-abs vl) (PlQ Ps)

denot-sound′ : ∀ (vl : ℂ.ValidLedger s l) →
  ∙ P (absS s)
  ∙ ↑ Q (𝔸.⟦ absL vl ⟧ $ absS s)
    ─────────────────────────────
    ↑ Q (absS <$> ℂ.⟦ l ⟧ s)
denot-sound′ vl Ps = subst (↑ _) (denot-abs vl)
\end{code}
\begin{center}
\begin{tikzpicture}
  \matrix (m) [row sep = 2cm, column sep = 3cm]
    { $\AB{s}$ \& $\AB{s′}$ \\
      $\AB{ŝ}$ \& $\AB{ŝ′}$ \\
    };
  \path
    (m-1-1) edge [->] node [left] {$\AF{absS}$} (m-2-1)
    (m-1-2) edge [->] node [right] {$\AF{absS}$} (m-2-2)
    (m-1-1) edge [->] node [above] {$\AR{\mathbb{C}.\llbracket\_\rrbracket}$} (m-1-2)
    (m-2-1) edge [->] node [below] {$\AR{\mathbb{A}.\llbracket\_\rrbracket}\ \AF{\circ}\ \AF{abs}$} (m-2-2)
    ;
\end{tikzpicture}
\end{center}
\end{frame}
\begin{frame}{Sound Abstraction}
\begin{code}[hide]
{- ** cannot formulate soundness without relating to a specific state
soundness : ∀ {P Q : Pred₀ 𝔸.S} (vl : ℂ.ValidLedger {!!} l) →
  𝔸.⟨ P ⟩ absL vl ⟨ Q ⟩
  ─────────────────────────────
  ℂ.⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩
soundness = {!!}
-}

-- ** universally quantifying abstract ledgers
soundness-∀l̂ : ∀ {P Q : Pred₀ 𝔸.S} →
    (∀ l̂ → 𝔸.⟨ P ⟩ l̂ ⟨ Q ⟩)
    ─────────────────────────────────────────────
    ℂ.⟨ (P ∘ absS) ∩ flip ℂ.ValidLedger l ⟩ l ⟨ Q ∘ absS ⟩
soundness-∀l̂ {l}{P}{Q} PlQ {s} (Ps , vl) =
  MAny-map⁻ Qs
  where
    ŝ = absS s
    l̂ = absL vl

    Qŝ : M.Any.Any Q (𝔸.⟦ l̂ ⟧ ŝ)
    Qŝ = PlQ l̂ Ps

    Qs : M.Any.Any Q (absS <$> ℂ.⟦ l ⟧ s)
    Qs = subst (M.Any.Any Q) (denot-abs vl) Qŝ

-- ** universally quantifying proofs of validity
soundness-∀vl : ∀ {P Q : Pred₀ 𝔸.S} →
  (∀ {s} (vl : ℂ.ValidLedger s l) → 𝔸.⟨ P ⟩ absL vl ⟨ Q ⟩)
  ───────────────────────────────────────────────
  ℂ.⟨ (P ∘ absS) ∩ flip ℂ.ValidLedger l ⟩ l ⟨ Q ∘ absS ⟩
soundness-∀vl {l}{P}{Q} PlQ {s} (Ps , vl) =
  MAny-map⁻ Qs
  where
    ŝ = absS s
    l̂ = absL vl

    Qŝ : M.Any.Any Q (𝔸.⟦ l̂ ⟧ ŝ)
    Qŝ = PlQ vl Ps

    Qs : M.Any.Any Q (absS <$> ℂ.⟦ l ⟧ s)
    Qs = subst (M.Any.Any Q) (denot-abs vl) Qŝ

-- ** alternative formulation using "strong" abstract Hoare triples
𝔸⟨_⟩_⊣_⟨_⟩ : ∀ P l →
  (∀ s → P $ absS s → ℂ.ValidLedger s l) → Pred₀ 𝔸.S → Type
𝔸⟨ P ⟩ l ⊣ P⇒ ⟨ Q ⟩ =
  (∀ s (p : P $ absS s) → (Q 𝔸.↑∘ 𝔸.⟦ absL (P⇒ s p) ⟧) (absS s))

semi-soundness : ∀ {P Q : Pred₀ 𝔸.S} →
  ∀ (P⇒ : ∀ s → P $ absS s → ℂ.ValidLedger s l) →
  ∙ 𝔸⟨ P ⟩ l ⊣ P⇒ ⟨ Q ⟩
    ──────────────────────────────────
    ℂ.⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩
semi-soundness {l}{P}{Q} P⇒ PlQ {s} Ps
  = MAny-map⁻ $ subst (M.Any.Any Q) (denot-abs vl) Qs
  where
    vl = P⇒ _ Ps

    Qs : (Q 𝔸.↑∘ 𝔸.⟦ absL vl ⟧) (absS s)
    Qs = PlQ _ Ps

-- ** Reasoning on the abstract level is sound; proving an abstract Hoare triple
-- is enough to prove a concrete Hoare triple (with abstract pre-/post-conditions).
\end{code}
\begin{AgdaAlign}
\begin{code}
soundness :
  ∀ (vl : ℂ.ValidLedger s l) →
\end{code}
\begin{code}[hide]
  let 𝔸⟨_⟩_⟨_⟩ : _
      𝔸⟨ P ⟩ l ⟨ Q ⟩ = 𝔸.⟨ P ⟩ l ⟨ Q ⟩＠ absS s
      ℂ⟨_⟩_⟨_⟩ : _
      ℂ⟨ P ⟩ l ⟨ Q ⟩ = ℂ.⟨ P ⟩ l ⟨ Q ⟩＠ s
  in
\end{code}
\begin{code}
  𝔸⟨ P ⟩ absL vl ⟨ Q ⟩
  ────────────────────────────
  ℂ⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩
\end{code}
\end{AgdaAlign}
\begin{code}[hide]
soundness {s}{l}{P}{Q} vl PlQ Ps
  = MAny-map⁻ $ subst (M.Any.Any Q) (denot-abs vl) Qs
  where
    Qs : (Q 𝔸.↑∘ 𝔸.⟦ absL vl ⟧) (absS s)
    Qs = PlQ Ps
\end{code}
\end{frame}
\end{document}
