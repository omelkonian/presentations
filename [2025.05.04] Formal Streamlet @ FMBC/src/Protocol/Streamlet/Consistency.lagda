
\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Prelude hiding (ℓ)
open import Hash
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Consistency (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
  hiding (vch; vch′; ls; ms; ms′)

open import Protocol.Streamlet.Decidability ⋯
open import Protocol.Streamlet.Invariants ⋯
\end{code}

\newcommand{\agdaConsistency}{%
\begin{AgdaMultiCode}
\begin{code}
Consistency : StateProperty
Consistency s = ∀ {p p′ b ch ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let ms = (s ＠ p) .db ; ms′ = (s ＠ p′)  .db in
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{0.3\textwidth}
\begin{code}
  ∙ (b ∷ ch) chain-∈ ms
  ∙ FinalizedChain ms ch b
\end{code}
\hfill
\end{minipage}%
\begin{minipage}[t]{0.49\textwidth}
\begin{code}
  ∙ ch′ notarized-chain-∈ ms′
  ∙ length ch ≤ length ch′
\end{code}
\end{minipage}%
\begin{code}
  ──────────────────────────────────────────────────────
  ch ≼ ch′
\end{code}
\end{AgdaMultiCode}}

\newcommand{\agdahonestintersection}{%
\begin{code}
honest-intersection : ∀ {vs vs′ : List Pid} →
  ∙ Unique vs
  ∙ Unique vs′
  ∙ IsMajority vs
  ∙ IsMajority vs′
    ───────────────────────────────────────
    Σ Pid (λ p → Honest p × p ∈ vs × p ∈ vs′)
\end{code}}

\begin{code}[hide]
honest-intersection {vs}{vs′} u u′ maj maj′ =
  let
    vs∩ = vs ∩ vs′

    u∩ : Unique vs∩
    u∩ = Unique-∩ u

    len≥n/3 : 3 * length vs∩ ≥ nodes
    len≥n/3 = let open Nat; open ≤-Reasoning in
      ≤-Reasoning.begin
        nodes
      ≡˘⟨ *-identityˡ _ ⟩
        1 * nodes
      ≡⟨ *-distribʳ-∸ nodes 4 3 ⟩
        4 * nodes ∸ 3 * nodes
      ≡⟨ cong (_∸ 3 * nodes) $ *-distribʳ-+ nodes 2 2 ⟩
        (2 * nodes + 2 * nodes) ∸ 3 * nodes
      ≤⟨ ∸-monoˡ-≤ (3 * nodes)
       $ ≤-Reasoning.begin
           2 * nodes + 2 * nodes
         ≤⟨ +-monoʳ-≤ (2 * nodes) maj′  ⟩
           2 * nodes + 3 * length vs′
         ≤⟨ +-monoˡ-≤ _ maj ⟩
           3 * length vs + 3 * length vs′
         ≡˘⟨ *-distribˡ-+ 3 (length vs) _ ⟩
           3 * (length vs + length vs′)
         ≤-Reasoning.∎
       ⟩
        3 * (length vs + length vs′) ∸ 3 * nodes
      ≡˘⟨ *-distribˡ-∸ 3 _ nodes ⟩
        3 * (length vs + length vs′ ∸ nodes)
      ≤⟨ *-mono-≤ {x = 3} ≤-refl $ length-∩ u u′ ⟩
        3 * length vs∩
      ≤-Reasoning.∎

    ∃p : Any Honest vs∩
    ∃p = honestFromMajority u∩ len≥n/3

    p , p∈vs , hp = L.Mem.find ∃p
    p∈ , p∈′ = ∈-∩⁻ p vs vs′ p∈vs
  in
    p , hp , p∈ , p∈′
\end{code}

\newcommand{\agdaUniqueNotarization}{%
\begin{AgdaMultiCode}
\begin{code}
UniqueNotarization : StateProperty
UniqueNotarization s = ∀ {p p′ b b′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let ms = (s ＠ p) .db ; ms′ = (s ＠ p′) .db in
\end{code}

\vspace{-3mm}
\noindent
\begin{minipage}[t]{0.3\textwidth}
\begin{code}
  ∙ NotarizedBlock ms   b
\end{code}
\hfill
\end{minipage}%
\begin{minipage}[t]{0.3\textwidth}
\begin{code}
  ∙ NotarizedBlock ms′  b′
\end{code}
\hfill
\end{minipage}%
\begin{minipage}[t]{0.3\textwidth}
\begin{code}
  ∙ b .epoch ≡ b′ .epoch
\end{code}
\end{minipage}%
\begin{code}
  ───────────────────────────────────────────────────────────────────────
  b ≡ b′
\end{code}
\end{AgdaMultiCode}}

% ** Proof **
% Suppose that two blocks B and B′, both of epoch e, are notarized in honest view.
% It must be that at least 2n/3 nodes, denoted the set S, signed the block B, and
% at least 2n/3 nodes, denoted the set S′, signed the block B′.
% Since there are only n nodes in total, S ∩ S′ must have size at least n/3, and thus
% at least one honest node is in S ∩ S′. According to our protocol, every honest node
% votes for at most one block per epoch. This means that B = B′. ∎

\begin{code}[hide]
uniqueNotarization : Invariant UniqueNotarization
uniqueNotarization (_ ∎) {p} {b} {b′} nb nb′ e≡
  rewrite let open ∣Base∣ p in lookup✓
  = ⊥-elim $ Nat.1+n≰n (votesNonempty nb)
uniqueNotarization Rs′@(s′ ⟨ _ ⟩⟵ _) {p} {p′} {b} {b′} nb nb′ e≡
    with b ≟ b′
... | yes b≡ = b≡
... | no  b≢ =
        let
          ms  = (s′ ＠ p)  .db
          ms′ = (s′ ＠ p′) .db

          vs  = voteIds ms  b
          vs′ = voteIds ms′ b′

          uvs : ∀ {b} → Unique $ voteIds ms b
          uvs {b} = uniqueVoteIds Rs′

          uvs′ : ∀ {b} → Unique $ voteIds ms′ b
          uvs′ {b} = uniqueVoteIds Rs′

          mvs  : IsMajority vs
          mvs  = enoughVoteIds nb

          mvs′ : IsMajority vs′
          mvs′ = enoughVoteIds nb′

          p″ , hp″ , p∈ , p∈′ = honest-intersection uvs uvs′ mvs mvs′
          instance _ = hp″

          b≡ : b ≡ b′
          b≡ = votedOnlyOncePerEpoch Rs′ p∈ p∈′ e≡
        in
          ⊥-elim $ b≢ b≡
\end{code}

\newcommand{\agdaConsistencyLemma}{%
\begin{AgdaMultiCode}
\begin{code}
ConsistencyLemma : StateProperty
ConsistencyLemma s = ∀ {p p′ b₁ b₂ b ch ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let ms = (s ＠ p) .db ; ms′ = (s ＠ p′) .db in
\end{code}

\vspace{-4mm}
\noindent
\begin{minipage}[t]{0.5\textwidth}
\begin{code}
  ∙ (b₂ ∷ b₁ ∷ ch) chain-∈ ms
  ∙ FinalizedChain ms (b₁ ∷ ch) b₂
\end{code}
\hfill
\end{minipage}%
\begin{minipage}[t]{0.48\textwidth}
\begin{code}
  ∙ (b ∷ ch′) notarized-chain-∈ ms′
  ∙ length ch′ ≡ length ch
\end{code}
\end{minipage}%
\begin{code}
  ─────────────────────────────────────────────────────────────────────
  b₁ ≡ b
\end{code}
\end{AgdaMultiCode}}

\begin{code}[hide]
consistencyLemma : Invariant ConsistencyLemma
consistencyLemma (_ ∎) {p} (m∈ ∷ _ ⊣ _) _ _ _
  rewrite let open ∣Base∣ p in lookup✓
  = case m∈ of λ ()
consistencyLemma Rs@(s ⟨ _ ⟩⟵ _) {p} {p′} {B₁} {B₂} {B} {ch@(B₀ ∷ ch₀)} {ch′}
  ch∈@(_ ∷ ch₁∈@(_ ∷ (_ ∷ _ ⊣ B₀connects) ⊣ _) ⊣ B₂connects)
  fch@(Finalize nch@(nB₂ ∷ nB₁ ∷ nB₀ ∷ _) e₂≡ e₁≡)
  (ch∈′@(B∈ ∷ ch′∈ ⊣ Bconnects) , (nB ∷ _))
  len≡
  with B₁ ≟ B
... | yes B₁≡B = B₁≡B
... | no  B₁≢B = ⊥-elim QED
  where
  open Nat
  -- * messages
  ms  = (s ＠ p) .db
  ms′ = (s ＠ p′) .db

  -- * epochs
  eᴮ = B  .epoch
  e₀ = B₀ .epoch
  e₁ = B₁ .epoch
  e₂ = B₂ .epoch

  -- * lengths
  ch₁ = B₁ ∷ ch
  ch₂ = B₂ ∷ ch₁

  ℓ-1 = length ch₀
  ℓ   = length ch
  ℓ+1 = length ch₁
  ℓ+2 = length ch₂
  ℓᴮ  = length (B ∷ ch′)

  ℓᴮ≡ : ℓᴮ ≡ ℓ+1
  ℓᴮ≡ = cong suc len≡

  -- * validity
  vch₂ : ValidChain ch₂
  vch₂ = chain-∈⇒Valid ch∈

  vch : ValidChain ch
  vch = uncons-vc $ uncons-vc vch₂

  vch′ : ValidChain (B ∷ ch′)
  vch′ = chain-∈⇒Valid ch∈′

  ch∈₀ : ch chain-∈ ms
  ch∈₀ = uncons-ch∈ $ uncons-ch∈ ch∈

  nch∈₁ : ch₁ notarized-chain-∈ ms
  nch∈₁ = ch₁∈ , L.All.tail nch

  nch∈₀ : ch₀ notarized-chain-∈ ms
  nch∈₀ = notarized-chain-∈-tail $ notarized-chain-∈-tail nch∈₁

  -- B ∉ {B₀, B₁, B₂}
  B₀≢B : B₀ ≢ B
  B₀≢B = ∣ch∣≢→b≢ vch vch′ (subst (_ ≢_) (sym len≡) $ Eq.≢-sym $ 1+n≢n)
  B₂≢B : B₂ ≢ B
  B₂≢B = ∣ch∣≢→b≢ (chain-∈⇒Valid ch∈) vch′
       $ subst (_ ≢_) (sym len≡) 1+n≢n

  -- honest intersection
  vsᴮ vsᴮ⁰ vsᴮ² : List Pid
  vsᴮ  = voteIds ms′ B
  vsᴮ⁰ = voteIds ms B₀
  vsᴮ² = voteIds ms B₂

  vsᴮ′ vsᴮ⁰′ vsᴮ²′ : List Pid
  vsᴮ′  = voteIds ms′ B
  vsᴮ⁰′ = voteIds ms′ B₀
  vsᴮ²′ = voteIds ms′ B₂

  uvs : ∀ {b} → Unique $ voteIds ms b
  uvs {b} = uniqueVoteIds Rs

  uvs′ : ∀ {b} → Unique $ voteIds ms′ b
  uvs′ {b} = uniqueVoteIds Rs

  mvsᴮ  : IsMajority vsᴮ′
  mvsᴮ  = enoughVoteIds nB
  mvsᴮ⁰ : IsMajority vsᴮ⁰
  mvsᴮ⁰ = enoughVoteIds nB₀
  mvsᴮ² : IsMajority vsᴮ²
  mvsᴮ² = enoughVoteIds nB₂

  B∩B₀ : ∃ λ p′ → Honest p′ × p′ ∈ vsᴮ × p′ ∈ vsᴮ⁰
  B∩B₀ = honest-intersection uvs′ uvs mvsᴮ mvsᴮ⁰

  B∩B₂ : ∃ λ p′ → Honest p′ × p′ ∈ vsᴮ × p′ ∈ vsᴮ²
  B∩B₂ = honest-intersection uvs′ uvs mvsᴮ mvsᴮ²

  QED : ⊥
  QED
    with eᴮ ≤? e₂ | ⟫ e₂≡ | ⟫ e₁≡
  ... | no eᴮ≰e₂ | _ | _
    -- Case (2): eᴮ > e + 2
    = ≤⇒≯ e₂≤eᴮ e₂>eᴮ
    where
    e₂≤eᴮ : e₂ ≤ eᴮ
    e₂≤eᴮ = ≮⇒≥ (≰⇒≮ eᴮ≰e₂)

    e₂>eᴮ : e₂ > eᴮ
    e₂>eᴮ =
      let
        p″ , hp″ , p∈′ , p∈ = B∩B₂
        instance _ = hp″

        len< : length ch′ < length ch₁
        len< = subst (_< _) (sym len≡)  (n<1+n ℓ)
      in
        increasingEpochs Rs p∈′ Bconnects p∈ B₂connects len<
  ... | yes e> | ⟫ e₂≡ | ⟫ e₁≡
    with ≤⇒≤′ e>
  ... | ≤′-refl
    = B₂≢B $ uniqueNotarization Rs nB₂ nB refl
  ... | ≤′-step ≤′-refl
    with e≡ ← suc-injective e₂≡
    = B₁≢B $ uniqueNotarization Rs nB₁ nB (sym e≡)
  ... | ≤′-step (≤′-step ≤′-refl)
    with e≡ ← suc-injective e₂≡
    = B₀≢B $ uniqueNotarization Rs nB₀ nB e≡′
    where e≡′ : e₀ ≡ eᴮ
          e≡′ = sym $ suc-injective $ trans e≡ e₁≡
  ... | ≤′-step (≤′-step eᴮ≤′)
    -- Case (1): eᴮ < e
    = ≤⇒≯ eᴮ≤e₀ eᴮ>e₀
    where
    eᴮ≤e₀ : eᴮ ≤ e₀
    eᴮ≤e₀ = subst (_ ≤_)
                  (suc-injective $ subst (_ ≡_) e₁≡ $ suc-injective e₂≡)
                  (≤′⇒≤ eᴮ≤′)

    eᴮ>e₀ : eᴮ > e₀
    eᴮ>e₀ =
      let
        p″ , hp″ , p∈′ , p∈ = B∩B₀
        instance _ = hp″

        len< : length ch₀ < length ch′
        len< = subst (_ <_) (sym len≡) (n<1+n ℓ-1)
      in
        increasingEpochs Rs p∈ B₀connects p∈′ Bconnects len<
\end{code}

\newcommand{\agdaConsistencyEqualLen}{%
\begin{code}
ConsistencyEqualLen : StateProperty
ConsistencyEqualLen s = ∀ {p p′ b ch ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let ms = (s ＠ p)   .db ; ms′  = (s ＠ p′)  .db in
  ∙ (b ∷ ch) chain-∈ ms
  ∙ ch′ notarized-chain-∈ ms′
  ∙ FinalizedChain ms ch b
  ∙ length ch ≡ length ch′
    ─────────────────────────
    ch ≡ ch′
\end{code}}

\begin{code}[hide]
consistencyEqualLen : Invariant ConsistencyEqualLen
consistencyEqualLen (_ ∎) {p} (b∈ ∷ _ ⊣ _) _ _ _
  rewrite let open ∣Base∣ p in lookup✓
  = case b∈ of λ ()
consistencyEqualLen
  Rs@(_ ⟨ x ⟩⟵ tr) {p}{ch = ch} {ch′}
  b∷ch∈@(_ ∷ ch∈ ⊣ _) nch∈′@(ch∈′ , nch′) fch len≡
  = ch≡
  where
  ch≡ : ch ≡ ch′
  ch≡ with ch ≟ ch′
  ... | yes ch≡ = ch≡
  ... | no  ch≢
    with ⟫ B  ∷ _ ← ⟫ ch
    with ⟫ ch′    | ⟫ nch′
  ... | ⟫ B′  ∷ _ | ⟫ nB′ ∷ _
    = ⊥-elim (b≢ b≡)
    where
    vch : ValidChain ch
    vch = chain-∈⇒Valid ch∈

    vch′ : ValidChain ch′
    vch′ = chain-∈⇒Valid ch∈′

    b≢ : B ≢ B′
    b≢ b≡@refl = ch≢ $ cong (_ ∷_) (b≡→ch≡ vch vch′ b≡)

    b≡ : B ≡ B′
    b≡ = consistencyLemma Rs b∷ch∈ fch nch∈′ (sym $ Nat.suc-injective len≡)
\end{code}

\begin{code}[hide]
consistency : Invariant Consistency
consistency (_ ∎) {p} (b∈ ∷ _ ⊣ _) fch nch∈′ len≤
  rewrite let open ∣Base∣ p in lookup✓
  = case b∈ of λ ()
consistency Rs@(_ ⟨ x ⟩⟵ tr) {p} {ch = ch} {ch′} ch∈ fch nch∈′ len≤
  = QED
  where
  n   = length ch′ ∸ length ch
  ch″ = L.drop n ch′

  len≡ : length ch ≡ length ch″
  len≡ = sym $ ≡-Reasoning.begin
    length ch″     ≡⟨ L.length-drop n ch′ ⟩
    length ch′ ∸ n ≡⟨ Nat.m∸[m∸n]≡n len≤ ⟩
    length ch      ≡-Reasoning.∎ where open ≡-Reasoning

  nch∈″ : ch″ notarized-chain-∈ _
  nch∈″ = Suffix-nch∈ (Suffix-drop n) nch∈′

  QED′ : ch ≼ ch″
  QED′ = ≡⇒Suffix $ consistencyEqualLen Rs ch∈ nch∈″ fch len≡

  QED : ch ≼ ch′
  QED = L.Suf.trans trans QED′ (Suffix-drop n)
\end{code}
