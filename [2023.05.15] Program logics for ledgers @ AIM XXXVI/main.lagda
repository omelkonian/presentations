%% \documentclass[aspectratio=43]{beamer}
\documentclass[aspectratio=169]{beamer}
\usetheme[
  block=fill,
  background=light,
  titleformat=smallcaps,
  progressbar=frametitle,
  numbering=none,
]{metropolis}
%% \setbeamersize{text margin left=.5cm,text margin right=.5cm}
\usepackage{appendixnumberbeamer}
\input{preamble}
%----------------------------------------------------------------------------

\title{Program logics for ledgers}
%% \subtitle{Modular reasoning of UTxO-based blockchains}

\author{\alert{Orestis Melkonian}, Wouter Swierstra, James Chapman}
\date{May 15th 2023, AIM XXXVI @ Delft}

\begin{document}

% ** Agda setup
\AgdaNoSpaceAroundCode{}
\setbeamerfont{title}{size=\LARGE}
\setbeamerfont{subtitle}{size=\Large}

%% \titlegraphic{}

\begin{center}
\maketitle
\end{center}

\begin{frame}{Motivation}

\begin{itemize}
\item Local \& modular reasoning for UTxO blockchain ledgers
\item Entertain the following analogy with concurrency/PL:
\begin{tabular}{ccc}
\textbf{Blockchain} & & \textbf{Concurrency Theory} \\
\hline
ledgers &$\leftrightarrow$& computer memory \\
memory locations &$\leftrightarrow$& accounts \\
data values &$\leftrightarrow$& account balances \\
smart contracts &$\leftrightarrow$& programs accessing memory \\
\end{tabular}
\end{frame}
\begin{frame}{Approach}
Investigate multiple semantics in different systems of increasing complexity
\tikzset{
  %% font=\small,
  txt/.style =
  { align=center },
  % edges
  to/.style = {->, thick}
}
\begin{tikzpicture}
  \matrix (mat)
    [ column sep = .1cm,
      row sep = 1.5cm,
      every node/.style = txt
    ] {
    \node (oper) {\textbf{Operational}\\[4pt]
    \infer{Q(s')}{P(s) & (l , s) \rightsquigarrow^* s'}
    };
    \& \node {};
    \& \node {};
    \& \node {};
    \& \node {};
    \& \node (denot) {\textbf{Denotational}\\
    $P \vdash Q \circ \llbracket l \rrbracket$}; \\
    \node {};
    \& \node (axiom) {\textbf{Axiomatic}\\
    $\{ P \} l \{ Q \}$
    };
    \& \node {};
    \& \node {};
    \& \node {};
    \& \node {}; \\
  };
  \path
  (oper) edge[loosely dotted]
    node[above] {\Huge $\simeq$}
  (denot)
  (oper) edge[loosely dotted]
    node[left] {\Huge $\simeq$}
  (axiom)
  (denot) edge[loosely dotted]
    node[right] {\Huge $\simeq$}
  (axiom)
  ;
\end{tikzpicture}
\end{frame}

\subfile{simple}
\subfile{simple-example}
\subfile{partial}
\subfile{partial-example}
\subfile{utxo}
\subfile{utxo-example}
\subfile{autxo}
\subfile{autxo-example}
\subfile{sound-abstraction}

\begin{frame}{Future Work}
\begin{itemize}
\item Deeper compositionality (i.e. monoidally exploit the values in the bag)
  \begin{itemize}
  \item[$\rightarrow$] will require further abstraction of split/merge transactions
  \end{itemize}
\item Go beyond the monetary values (states, transaction data)
  \begin{itemize}
  \item[$\rightarrow$] leads to more practical verification of smart contracts
  \end{itemize}
\item Generalise to multiple separation views, aka zooming levels
\item Generically grow such separation logics, i.e. ``Separation Logics à la carte''
\end{itemize}
\end{frame}

\begin{frame}{Conclusion}
Agda as a design guide, rather than merely a verification tool of existing systems.
\includegraphics[keepaspectratio=true,height=1.0cm]{conor}
\end{frame}

\begin{frame}[standout]{}
Questions? Suggestions?
\end{frame}

\end{document}
