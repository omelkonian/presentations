\documentclass[final,hyperref={pdfpagelabels=false}]{beamer}
\usepackage[orientation=portrait,size=a0,scale=1.8]{beamerposter}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Theme
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\usetheme{Orestis}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Tikz
\usepackage{tikz}
\usetikzlibrary{chains,arrows,automata,fit,positioning,calc}

% Colors
\usepackage{xcolor}

% Images
\usepackage{graphics}
\graphicspath{{img/}}

% Math Symbols
\usepackage{amsmath,amsthm,amssymb,latexsym,stmaryrd}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand\alert[1]{\textcolor{mLightBrown}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%include polycode.fmt
%include stylish.fmt
\def\commentbegin{}
\def\commentend{}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Fonts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\usepackage{relsize}
\usepackage[tt=false]{libertine}
\usepackage[libertine]{newtxmath}

%----------------------------------------------------------------------------------------
% TITLE SECTION
%----------------------------------------------------------------------------------------

\title{\LARGE \textsc{Formalizing BitML Calculus in Agda}}
\author{Orestis Melkonian}
\date{July 8, 2019}
\institute{Utrecht University, The Netherlands}

%----------------------------------------------------------------------------------------
% FOOTER TEXT
%----------------------------------------------------------------------------------------

\newcommand\footsize{10ex}
\newcommand\leftfoot{
  \begin{minipage}{.5\textwidth}
  \includegraphics[keepaspectratio=true,height=8ex]{uu}
  \hspace{1cm}
  \includegraphics[keepaspectratio=true,height=8ex]{iohk}
  \end{minipage}
} % Left footer text
\newcommand\rightfoot{
  \begin{minipage}{.5\textwidth}
  \hspace{2cm}
  \textbf{https://github.com/omelkonian/formal-bitml}
  \end{minipage}
} % Right footer text

%----------------------------------------------------------------------------------------
% SIZES ( 3*sepsize + 2*colsize == 1 )
%----------------------------------------------------------------------------------------
\newcommand\sepsize{.025\textwidth}
\newcommand\colsize{.4705\textwidth}

\begin{document}

\addtobeamertemplate{block end}{}{\vspace*{13ex}} % White space under blocks

\begin{frame}[t] % The whole poster is enclosed in one beamer frame

\begin{columns}[t] % The whole poster consists of two major columns, each of which can be subdivided further with another \begin{columns} block - the [t] argument aligns each column's content to the top

\begin{column}{\sepsize}\end{column} % Empty spacer column

\begin{column}{\colsize} % The first column

%----------------------------------------------------------------------------------------
% CONTENT
%----------------------------------------------------------------------------------------

\begin{block}{Motivation}
\begin{itemize}

\item Blockchain technology has opened a whole array of interesting new applications,
mainly due to the sophisticated transaction schemes enabled by \textbf{smart contracts}
-- programs that run on the blockchain.

\item Reasoning about their behaviour is:
  \begin{itemize}
  \item \textit{necessary}, significant funds are involved
  \item \textit{difficult}, due to concurrency
  \end{itemize}

\item Provide rigid foundations via a language-based, type-driven approach, alongside a mechanized meta-theory.

\item Formalization of the \textit{Bitcoin Modelling Language} (BitML).

\end{itemize}
\end{block}

\begin{block}{BitML Contracts}
\begin{itemize}

\item The type of a contract is indexed by the total monetary value it carries and a set of deposits that guarantee
it will not get stuck. A contract can have multiple branches using the binary operator |_ ⊕ _|.
\begin{agda}\begin{code}
data Contract : Value → Values → Set where
  -- collect deposits and secrets
  put _ reveal _ ⇒ _ ∶- _ :
       (vs : Values) → Secrets → Contract (v + sum vs) vs PRIME
    →  Contract v (vs PRIME ++ vs)

  -- transfer the remaining balance to a participant
  withdraw : ∀ {v vs} → Participant → Contract v vs

  -- split the balance across different branches
  split :  ∀ {vs} → (cs : List (∃[ v ] Contract v vs))
        →  Contract (sum (proj SUBONE ⟨$⟩ cs)) vs

  -- wait for participant's authorization
  _ ∶ _ : Participant → Contract v vs → Contract v vs

  -- wait until some time passes
  after _ : _ : Time → Contract v vs → Contract v vs
\end{code}\end{agda}
\vspace{-1cm}

\item A contract is initially made public through an |Advertisement|, denoted |⟨ G ⟩ C|,
where |G| are the preconditions that have to be met in order for |C| to be stipulated.

\end{itemize}
\end{block}

\begin{block}{Small-step Semantics}
\begin{itemize}

\item BitML's semantics describes transitions between \textit{configurations},
which hold advertisements, deposits, contracts, secrets and action authorizations.
For the sake of semantic bug discovery, configurations are indexed by assets of type |(List A , List A)|,
where the first element is produced and the second required:
\begin{agda}\begin{code}
data Configuration′  :  Asset ^^ ∃Advertisement  -- advertised contracts
                     →  Asset ^^ ∃Contract       -- stipulated contracts
                     →  Asset Deposit            -- deposits
                     →  Set
\end{code}\end{agda}
\vspace{-1cm}

\item The small-step relation is a collection of permitted transitions between our intrinsically-typed states:
\begin{agda}\begin{code}
data _ —→ _  :  Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where

  D-AuthJoin :

    {-\inferLine{28cm}-}
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | Γ —→ ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | A [ 0 ↔ 1 ] | Γ
##
  D-Join :
    {-\inferLine{26cm}-}
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | A [ 0 ↔ 1 ] | Γ —→ ⟨ A , v + v′ ⟩ SDD | Γ
##
  C-Advertise :
    Any (UL ∈ Hon) (participants (G ad))
    {-\inferLine{15cm}-}
    Γ —→ ad | Γ
##
  C-AuthCommit :
    (secrets A (G ad) ≡ a₀ DOTS aₙ) × (A ∈ Hon → All (U ≢ ^^ nothing) a SUBI)
    {-\inferLine{30cm}-}
    ` ad | Γ —→ ` ad | Γ | DOTS ⟨ A : a SUBI ♯♯ N SUBI ⟩ DOTS ^^ BAR ^^ A [ ♯▷ ^^ ad ]

  VDOTS
\end{code}\end{agda}
\vspace{-1cm}

\end{itemize}
\end{block}


%----------------------------------------------------------------------------------------

\end{column} % End of the first column

\begin{column}{\sepsize}\end{column} % Empty spacer column

\begin{column}{\colsize} % The second column
\addtobeamertemplate{block end}{}{\vspace*{-7ex}} % White space under blocks

%----------------------------------------------------------------------------------------

\begin{block}{Equational Reasoning}
\begin{itemize}

\item Rules are always presented with the interesting parts of the state as the left operand,
implicitly relying on |(Configuration, _ BAR _)| being a \textit{commutative monoid}.

\vspace{.5cm}
\noindent
\textbf{\textsc{Solution}} Factor out reordering in the \textit{reflective transitive closure} of |_ —→ _|:
\begin{agda}\begin{code}
data _ —↠ _  :  Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where
  _ ∎ : (M : Configuration ads cs ds) → M —↠ M
  _ —→ ⟨ _ ⟩ _  :  (L : Configuration ads cs ds) {_ : L ≈ L′ × M ≈ M′}
                →  (L′ —→ M′) → (M —↠ N) → (L —↠ N)
\end{code}\end{agda}
\vspace{-1cm}

\end{itemize}
\end{block}

\begin{block}{Example Derivation}
\begin{itemize}

\item \textbf{Timed-commitment protocol}

|A| promises to reveal a secret to |B|, otherwise loses a deposit of |BIT 1|.
\begin{agda}\begin{code}
tc : Advertisement 1 [] [] [ 1 , 0 ])
tc =  ⟨ A ! 1 ∧ A ♯♯ a ∧ B ! 0  ⟩  reveal [ a ] ⇒ withdraw A ∶- DOTS ⊕ after t ∶ withdraw B
\end{code}\end{agda}
\vspace{-1cm}

\item The following proof exhibits a possible execution, where |A| reveals the secret:
\begin{agda}\begin{code}
tc-derivation : ⟨ A , 1 ⟩ SDD —↠ ⟨ A , 1 ⟩ SDD | A ∶ a ♯♯ 6
tc-derivation =         ⟨ A , 1 ⟩ SDD
—→⟨ C-Advertise ⟩       ` tc | ⟨ A , 1 ⟩ SDD
—→⟨ C-AuthInit ⟩        ` tc | ⟨ A , 1 ⟩ SDD         ^^ |  ^^ ⟨A ∶ a ♯♯ 6⟩ | A [ HTRI tc ]
—→⟨ C-Init ⟩            ⟨ tc , 1 ⟩ SCC               ^^ |  ^^ ⟨A ∶ a ♯♯ 6⟩
—→⟨ C-AuthRev ⟩         ⟨ tc , 1 ⟩ SCC               ^^ |  ^^ A ∶ a ♯♯ 6
—→⟨ C-Control ⟩         ⟨ [ reveal DOTS ] , 1 ⟩ SCC  ^^ |  ^^ A ∶ a ♯♯ 6
—→⟨ C-PutRev ⟩          ⟨ [ withdraw A ] , 1 ⟩ SCC   ^^ |  ^^ A ∶ a ♯♯ 6
—→⟨ C-Withdraw ⟩ ^^ ^^  ⟨ A , 1 ⟩ SDD                ^^ |  ^^ A ∶ a ♯♯ 6
∎
\end{code}\end{agda}
\vspace{-1cm}

\end{itemize}
\end{block}


\begin{block}{Symbolic Model}
\begin{itemize}

\item What we eventually want is to reason about the behaviour of participants.
By observing that our small-step derivations correspond to possible execution \textit{traces},
we can develop a game-theoretic view of our semantics by considering \textit{strategies},
in which participants make moves depending on the current trace.

\item \textbf{Honest participants} can pick a set of possible next moves, which have to adhere to certain validity conditions
(e.g. the move has to be permitted by the semantics).
\begin{agda}\begin{code}
record HonestStrategy (A : Participant) where
  field  strategy  :  Trace → Labels
         valid     :  (A ∈ Hon)
                   ×  (∀ R α → α ∈ strategy ^^ R ∗ → ∃[ R′ ] (R ——→⟦ α ⟧ R′))
                   ×  (∀ R α → α ∈ strategy R ∗ → authorizers α ⊆ [ A ])
                   VDOTS
\end{code}\end{agda}
\vspace{-1cm}

\item An \textbf{adversary} will choose the final move, out of the honest ones:
\begin{agda}\begin{code}
record AdversaryStrategy (Adv : Participant) where
  field  strategy  :  Trace → (∀ (A : Participant) → HonestStrategy A) → Label
         valid     :  (Adv ∉ Hon)
                   ×  ∀ {R : Trace} {honestMoves} →
                        let α = strategy R∗ honestMoves in
                        (  ∃[ A ] (A ∈ Hon × α ∈ honestMoves A)
                        ⊎  DOTS ^^ )
\end{code}\end{agda}
\vspace{-1cm}

\item We can now demonstrate a possible \textbf{attack} by proving that a given trace \textit{conforms} to a specific set of strategies,
i.e. we can arrive there from an initial configuration using the moves emitted by the strategies.

\end{itemize}
\end{block}


\begin{block}{Towards Certified Compilation}
\begin{itemize}

\item
Originally, the BitML proposal involved a compilation scheme from BitML contracts to Bitcoin transactions,
accompanied by a proof that attacks in the compiled contracts can always be observed in the symbolic model.

However, we aim to give a compiler to a more abstract accounting model for ledgers based on \textit{unspent output transactions} (UTxO)
and mechanize a similar \textit{compilation correctness} proof.

\item
We already have an Agda formalization for dependently-typed UTxO ledgers,
which statically enforces the validity of their transactions (e.g. all referenced addresses exist)
at \textbf{https://github.com/omelkonian/formal-utxo}.

\end{itemize}
\end{block}

%----------------------------------------------------------------------------------------

\end{column} % End of the second column

\begin{column}{\sepsize}\end{column} % Empty spacer column

\end{columns} % End of all the columns in the poster

\end{frame} % End of the enclosing frame

\end{document}
