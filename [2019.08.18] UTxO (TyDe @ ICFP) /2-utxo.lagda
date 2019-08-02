\section{Extended UTxO}
\subsection{Transactions/Ledgers}
\begin{frame}{Basic Types}
\begin{agda}\begin{code}
module UTxO.Types (Value : Set) (Hash : Set) where

record State : Set where
  field  height : ℕ
         VDOTS

record HashFunction (A : Set) : Set where
  field  _ ♯        : A → Hash
         injective  : ∀ {x y} → x ♯ ≡ y ♯ → x ≡ y

postulate
  _ ♯ : ∀ {A : Set} → HashFunction A
\end{code}\end{agda}
\end{frame}

\begin{frame}{Inputs and Output References}
\begin{agda}\begin{code}
record TxOutputRef : Set where
  constructor _ at _
  field  id     : Hash
         index  : ℕ

record TxInput : Set where
  field  outputRef  : TxOutputRef

         R  D       : 𝕌
         redeemer   : State → el R
         validator  : State → Value → PendingTx → el R → el D → Bool
\end{code}\end{agda}

\begin{itemize}
\item |𝕌| is a simple type universe for first-order data.
\end{itemize}

\end{frame}

\begin{frame}{Transactions}
\begin{agda}\begin{code}
module UTxO  (Address : Set) (_ ♯ ^^ SUBA : HashFunction Address)
             (_ ≟ SUBA _ : Decidable {A = Address} _ ≡ _) where

record TxOutput : Set where
  field  value       : Value
         address     : Address

         Data        : 𝕌
         dataScript  : State → el Data

record Tx : Set where
  field  inputs   : List TxInput
         outputs  : List TxOutput
         forge    : Value
         fee      : Value

Ledger : Set
Ledger = List Tx
\end{code}\end{agda}
\end{frame}

\begin{frame}{Validation}
\begin{agda}\begin{code}
validate  :  PendingTx
          →  (i : TxInput)
          →  (o : TxOutput)
          →  D i ≡ Data o
          →  State
          →  Bool
validate ptx i o refl st =
  validator i st (value o) ptx (redeemer i st) (dataScript o st)
\end{code}\end{agda}
\end{frame}

\begin{frame}{Unspent Outputs}
\begin{agda}\begin{code}
unspentOutputs : Ledger → Set⟨ TxOutputRef ⟩
unspentOutputs []          = ∅
unspentOutputs (tx ∷ txs)  = (unspentOutputs txs ─ spentOutputsTx tx)
                           ∪ unspentOutputsTx tx
  where
    spentOutputsTx, unspentOutputsTx : Tx → Set⟨ TxOutputRef ⟩
    spentOutputsTx       = (outputRef ⟨$⟩ UR) ∘ inputs
    unspentOutputsTx tx  = (tx ♯ ^^ at UR) ⟨$⟩ indices (outputs tx)
\end{code}\end{agda}
\end{frame}

\subsection{Validity}
\begin{frame}{Validity I}
\begin{agda}\begin{code}
record IsValidTx (tx : Tx) (l : Ledger) : Set where
field
  validTxRefs : ∀ i → i ∈ inputs tx ->
    Any (λ t → t ♯ ≡ id (outputRef i)) l

  validOutputIndices : ∀ i → (iin : i ∈ inputs tx) ->
    index (outputRef i) <
      length (outputs (lookupTx l (outputRef i) (validTxRefs i iin)))

  validOutputRefs : ∀ i → i ∈ inputs tx ->
    outputRef i ∈ unspentOutputs l

  validDataScriptTypes : ∀ i → (iin : i ∈ inputs tx) ->
    D i ≡ D (lookupOutput l (outputRef i) DOTS)
\end{code}\end{agda}
\end{frame}

\begin{frame}{Validity II}
\begin{agda}\begin{code}
preservesValues :
  forge tx + sum (lookupValue l DOTS ⟨$⟩ inputs tx)
    ≡
  fee tx + sum (value ⟨$⟩ outputs tx)

noDoubleSpending :
  noDuplicates (outputRef ⟨$⟩ inputs tx)

allInputsValidate : ∀ i → (iin : i ∈ inputs tx) ->
  let  out = lookupOutput l (outputRef i) DOTS
       ptx = mkPendingTx l tx validTxRefs validOutputIndices
  in   T (validate ptx i out (validDataScriptTypes i iin) (getState l))

validateValidHashes : ∀ i → (iin : i ∈ inputs tx) ->
  let  out = lookupOutput l (outputRef i) DOTS
  in   (address out) ♯ ≡ validator i ♯
\end{code}\end{agda}
\end{frame}

\begin{frame}{Valid Ledgers}
We do not want a ledger to be any list of transactions,
but a ``snoc''-list that carries proofs of validity:
\begin{agda}\begin{code}
data ValidLedger : Ledger → Set where

  ∙           :  ValidLedger []

  _ ⊕ _ ∶- _  :  ValidLedger l
              →  (tx : Tx)
              →  IsValidTx tx l
              →  ValidLedger (tx ∷ l)
\end{code}\end{agda}
\end{frame}

\begin{frame}{Decision Procedures}
\begin{agda}\begin{code}
VDOTS
validOutputRefs? : ∀ (tx : Tx) (l : Ledger)
  → Dec (∀ i → i ∈ inputs tx → outputRef i ∈ unspentOutputs l)
validOutputRefs? tx l =
  ∀? (inputs tx) λ i _ → outputRef i ∈? unspentOutputs l
  VDOTS
  where
    ∀?  :  (xs : List A)
        →  {P : (x : A) (xin : x ∈ xs) → Set}
        →  (∀ x → (xin : x ∈ xs) → Dec (P x xin))
        →  Dec (∀ x xin → P x xin)
\end{code}\end{agda}
\end{frame}


\subsection{Extensions}

\begin{frame}{Extension: Multi-currency}
\begin{enumerate}
\item Generalize values from integers to maps: |Value = List (Hash × ℕ)|
\item Implement additive group operators (on top of AVL trees):
\begin{agda}\begin{code}
open import Data.AVL ℕ-strictTotalOrder

_ + SC _ : Value → Value → Value
c + SC c′ = toList (foldl go (fromList c) c′)
  where
    go : Tree Hash ℕ → (Hash × ℕ) → Tree Hash ℕ
    go m (k , v) = insertWith k ((UL + v) ∘ fromMaybe 0) m

sum SC : Values → Value
sum SC = foldl UL + SC UR []
\end{code}\end{agda}
\end{enumerate}
\end{frame}

\begin{frame}{Multi-currency: Forging condition}
We now need to enforce monetary policies on forging transactions:
\begin{agda}\begin{code}
record IsValidTx (tx : Tx) (l : Ledger) : Set where
  VDOTS
  forging :
    ∀ c → c ∈ keys (forge tx) →
      ∃[ i ] ^^ ∃ λ (iin : i ∈ inputs tx) →
        let out = lookupOutput l (outputRef i) DOTS
        in (address out) ♯ ≡ c
\end{code}\end{agda}
\end{frame}

\subsection{Example}
\newcommand\forge[1]{forge: \bitcoin ~#1}
\newcommand\fee[1]{fee:\hspace{7pt} \bitcoin ~#1}
\begin{frame}{Example: Transaction Graph}
\begin{figure}\begin{tikzpicture}
  [transform canvas={scale=0.8},
   basic box/.style = {
     draw,
     shape = rectangle,
     align = left,
     minimum width=2cm,
     minimum height=1.2cm,
     rounded corners},
   upedge/.style = {
     },
   downedge/.style = {
     },
   to/.style = {
     ->,
     >=stealth',
     semithick
  },
  every matrix/.style={column sep=1.3cm, row sep=1cm, ampersand replacement=\&},
  font=\footnotesize
  ]
  \matrix{
    \node[basic box, label = |t SUBONE|] (t)
      {\forge{1000}\\ \fee{0}};
    \& \node[basic box, label = |t SUBTWO|] (tt)
      {\forge{0}\\ \fee{0}};
    \& \node[basic box, label = |t SUBFIVE|] (tfive)
      {\forge{0}\\ \fee{7}};
    \& \node[basic box, label = |t SUBSIX|] (tsix)
      {\forge{0}\\ \fee{1}};
    \& \node (end) {}; \\

    \node {};
    \& \node[basic box, label = |t SUBTHREE|] (ttt)
      {\forge{0}\\ \fee{1}};
    \& \node {};
    \& \node {}; \\

    \node {};
    \& \node[basic box, label = |t SUBFOUR|] (tfour)
      {\forge{10}\\ \fee{2}};
    \& \node {};
    \& \node {}; \\
  };

  \path
  (t) edge[to]
    node[above]{\bitcoin ~1000}
    node[below]{@@|ONEB|}
  (tt)
  (tt) edge[to, bend right = 30]
    node[left]{\bitcoin ~200}
    node[right]{@@|ONEB|}
  (ttt)
  (tt) edge[to]
    node[above]{\bitcoin ~800}
    node[below]{@@|TWOB|}
  (tfive)
  (ttt) edge[to, bend right = 30]
    node[left]{\bitcoin ~199}
    node[right]{@@|THREEB|}
  (tfour)
  (tfour) edge[to, bend right = 45]
    node[left]{\bitcoin ~207}
    node[right]{@@|TWOB|}
  (tfive)
  (tfive) edge[to, transform canvas={yshift=13pt}]
    node[above]{\bitcoin ~500}
    node[below]{@@|TWOB|}
  (tsix)
  (tfive) edge[to, transform canvas={yshift=-13pt}]
    node[above]{\bitcoin ~500}
    node[below]{@@|THREEB|}
  (tsix)
  (tsix) edge[to, red]
    node[above,black]{\bitcoin ~999}
    node[below,black]{@@|THREEB|}
  (end)
  ;
\end{tikzpicture}\end{figure}
\end{frame}

\begin{frame}{Example: Transaction Graph \alert{+ monetary policy}}
\begin{figure}\begin{tikzpicture}
  [transform canvas={scale=0.8},
   basic box/.style = {
     draw,
     shape = rectangle,
     align = left,
     minimum width=2cm,
     minimum height=1.2cm,
     rounded corners},
   upedge/.style = {
     },
   downedge/.style = {
     },
   to/.style = {
     ->,
     >=stealth',
     semithick
  },
  every matrix/.style={column sep=1.3cm, row sep=1cm, ampersand replacement=\&},
  font=\footnotesize
  ]
  \matrix{
    \node[basic box, label = |t SUBONE|] (t)
      {\forge{1000}\\ \fee{0}};
    \& \node[basic box, label = |t SUBTWO|] (tt)
      {\forge{0}\\ \fee{0}};
    \& \node[basic box, label = |t SUBFIVE|] (tfive)
      {\forge{0}\\ \fee{7}};
    \& \node[basic box, label = |t SUBSIX|] (tsix)
      {\forge{0}\\ \fee{1}};
    \& \node (end) {}; \\

    \node[basic box, label = |c SUBZERO|] (c)
      {\forge{0}\\ \fee{0}};
    \& \node[basic box, label = |t SUBTHREE|] (ttt)
      {\forge{0}\\ \fee{1}};
    \& \node {};
    \& \node {}; \\

    \node {};
    \& \node[basic box, label = |t SUBFOUR|] (tfour)
      {\forge{10}\\ \fee{2}};
    \& \node {};
    \& \node {}; \\
  };

  \path
  (t) edge[to]
    node[above]{\bitcoin ~1000}
    node[below]{@@|ONEB|}
  (tt)
  (tt) edge[to, bend right = 30]
    node[left]{\bitcoin ~200}
    node[right]{@@|ONEB|}
  (ttt)
  (tt) edge[to]
    node[above]{\bitcoin ~800}
    node[below]{@@|TWOB|}
  (tfive)
  (ttt) edge[to, bend right = 30]
    node[left]{\bitcoin ~199}
    node[right]{@@|THREEB|}
  (tfour)
  (tfour) edge[to, bend right = 45]
    node[left]{\bitcoin ~207}
    node[right]{@@|TWOB|}
  (tfive)
  (tfive) edge[to, transform canvas={yshift=13pt}]
    node[above]{\bitcoin ~500}
    node[below]{@@|TWOB|}
  (tsix)
  (tfive) edge[to, transform canvas={yshift=-13pt}]
    node[above]{\bitcoin ~500}
    node[below]{@@|THREEB|}
  (tsix)
  (tsix) edge[to, red]
    node[above,black]{\bitcoin ~999}
    node[below,black]{@@|THREEB|}
  (end)
  (c) edge[to, bend left = 30, green]
    node[left,black]{\bitcoin-policy}
    node[right,black]{@@|BIT|}
  (t)
  (c) edge[to, bend right = 40, green]
    node[left,black]{\bitcoin-policy}
    node[right,black]{@@|BIT|}
  (tfour)
  ;
\end{tikzpicture}\end{figure}
\end{frame}

\begin{frame}{Example: Setting Up}
\begin{agda}\begin{code}
Address = ℕ

ONEB , TWOB , THREEB : Address
ONEB    = 1 -- first address
TWOB    = 2 -- second address
THREEB  = 3 -- third address

open import UTxO Address (λ x → x) UL ≟ UR

BIT -validator : State → DOTS → Bool
BIT -validator (record {height = h}) DOTS = (h ≡ SB 1) ∨ (h ≡ SB 4)
\end{code}\end{agda}
\end{frame}

\begin{frame}{Example: Smart Constructors}
\begin{agda}\begin{code}
mkValidator : TxOutputRef → (DOTS → TxOutputRef → DOTS → Bool)
mkValidator o DOTS o′ DOTS = o ≡ SB o′

BIT _ : ℕ → Value
BIT v = [ (BIT -validator ♯ , v) ]

withScripts : TxOutputRef → TxInput
withScripts o = record  { outputRef  = o
                        ; redeemer   = λ _ → o
                        ; validator  = mkValidator tin }

withPolicy : TxOutputRef → TxInput
withPolicy tin = record  { outputRef = tin
                         ; redeemer  = λ _ → tt
                         ; validator = BIT -validator }

_ at _ : Value → Index addresses → TxOutput
v at addr = record { value = v ; address = addr ; dataScript  = λ _ → tt }
\end{code}\end{agda}
\end{frame}

\begin{frame}{Example: Definitions of Transactions}
\begin{agda}\begin{code}
c SUBZERO , t SUBONE , t SUBTWO , t SUBTHREE , t SUBFOUR , t SUBFIVE , t SUBSIX : Tx
c SUBZERO = record  { inputs   = []
                    ; outputs  = [ BIT 0 at (BIT -validator ♯) , BIT 0 at (BIT -validator ♯) ]
                    ; forge    = BIT 0
                    ; fee      = BIT 0 }
t SUBONE = record  { inputs   = [ withPolicy c SUBZERO SUBZERO ]
                   ; outputs  = [ BIT 1000 at ONEB ]
                   ; forge    = BIT 1000
                   ; fee      = BIT 0 }
VDOTS
t SUBSIX = record  { inputs   = [ withScripts t SUBFIVE SUBZERO , withScripts t SUBFIVE SUBONE ]
                   ; outputs  = [ BIT 999 at THREEB ]
                   ; forge    = BIT 0
                   ; fee      = BIT 1 }
\end{code}\end{agda}
\end{frame}

\begin{frame}{Example: Rewrite Rules}
Our hash function is a postulate, so our decision procedures will get stuck...
\begin{agda}\begin{code}
PRAGMAL OPTIONS {---rewriting-} PRAGMAR
postulate
  eq SUBONE SUBZERO   : (mkValidator t SUBONE SUBZERO)  ♯  ≡  ONEB
  VDOTS
  eq SUBSIX SUBZERO   : (mkValidator t SUBSIX SUBZERO)  ♯  ≡  THREEB
##
PRAGMAL BUILTIN REWRITE _ ≡ _ PRAGMAR
PRAGMAL REWRITE eq SUBZERO , eq SUBONE SUBZERO , DOTS , eq SUBSIX SUBZERO PRAGMAR
\end{code}\end{agda}
\end{frame}

\begin{frame}{Example: Correct-by-construction Ledger}
\begin{agda}\begin{code}
ex-ledger : ValidLedger [ t SUBSIX , t SUBFIVE , t SUBFOUR , t SUBTHREE , t SUBTWO , t SUBONE , c SUBZERO ]
ex-ledger =
  ∙  c SUBZERO  ∶- record  { DOTS }
  ⊕  t SUBONE   ∶- record  {  validTxRefs  = toWitness {Q = validTxRefs? t SUBONE l SUBZERO} tt
                              VDOTS
                           ;  forging      = toWitness {Q = forging? DOTS} tt }
  VDOTS
  ⊕  t SUBSIX   ∶- record { DOTS }
##
utxo : list (unspentOutputs ex-ledger) ≡ [ t SUBSIX SUBZERO ]
utxo = refl
\end{code}\end{agda}
\end{frame}


\section{Meta-theory}

\subsection{Weakening Lemma}
\begin{frame}{Weakening via Injections}
\begin{agda}\begin{code}
module Weakening
  (𝔸 : Set) (_♯ ^^ SA : HashFunction 𝔸) (_ ≟ SA _ : Decidable {A = 𝔸} _ ≡ _)
  (𝔹 : Set) (_♯ ^^ SB : HashFunction 𝔹) (_ ≟ SB _ : Decidable {A = 𝔹} _ ≡ _)
  (A↪B : 𝔸 , _♯ ^^ SA ↪ 𝔹 , _♯ ^^ SB)
  where
##
  import UTxO.Validity 𝔸 _♯ ^^ SA _ ≟ SA _ as A
  import UTxO.Validity 𝔹 _♯ ^^ SB _ ≟ SB _ as B
\end{code}\end{agda}
\end{frame}

\begin{frame}{Weakening Lemma}
After translating addresses, validity is preserved:
\begin{agda}\begin{code}
  weakening : ∀ {tx : A.Tx} {l : A.Ledger}

    →  A.IsValidTx tx l
       {-\inferLine{7cm}-}
    →  B.IsValidTx (weakenTx tx) (weakenLedger l)
  weakening = DOTS
\end{code}\end{agda}
\end{frame}

\subsection{Combining Ledgers}

\begin{frame}{Inspiration from Separation Logic}
\begin{itemize}
\item One wants to reason in a modular manner
  \begin{itemize}
  \item Conversely, one can study a ledger by studying its components, that is we can reason \textit{compositionally}
  \end{itemize}
\item In concurrency, |P ∗ Q| holds for disjoint parts of the memory heap
\item In blockchain, |P ∗ Q| holds for disjoint parts of the ledger
  \begin{itemize}
  \item But what does it mean for two ledgers to be disjoint?
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}{Disjoint Ledgers}
Two ledgers |l| and |l′| are disjoint, when
\begin{enumerate}
\item No common transactions: |Disjoint l l′ = ∀ t → ¬ (t ∈ l × v ∈ l′)|
\item Validation does not break:
\end{enumerate}
\vspace{-5pt}
\begin{agda}\begin{code}
PreserveValidations : Ledger → Ledger → Set
PreserveValidations l l″ =
  ∀ tx → tx ∈ l → tx ∈ l″ →
    ∀ {ptx i out vds}  →  validate ptx i out vds (getState (upTo tx l″))
                       ≡  validate ptx i out vds (getState (upTo tx l))
\end{code}\end{agda}
\end{frame}

\begin{frame}{Combining Ledgers}
\begin{agda}\begin{code}
_ LR _ ∶- _ : ∀ {l l′ l″ : Ledger}
  →  ValidLedger l
  →  ValidLedger l′
  →  Interleaving l l′ l″
  ×  Disjoint l l′
  ×  PreserveValidations l l″
  ×  PreserveValidations l′ l″
     {-\inferLine{6cm}-}
  →  ValidLedger l″
\end{code}\end{agda}
\end{frame}
