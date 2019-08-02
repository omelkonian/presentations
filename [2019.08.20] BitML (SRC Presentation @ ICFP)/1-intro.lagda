\section{Introduction}

\begin{frame}{Motivation}
\begin{itemize}
\item A lot of blockchain applications recently
\item Sophisticated transactional schemes via \alert{smart contracts}
\item Reasoning about their execution is:
  \begin{enumerate}
  \item \textit{necessary}, significant funds are involved
  \item \textit{difficult}, due to concurrency
  \end{enumerate}
\item Hence the need for automatic tools that verify no bugs exist
  \begin{itemize}
  \item This has to be done \alert{statically}!
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}{Background}

\begin{alertblock}{Bitcoin}
\begin{itemize}
\item Based on \textit{unspent transaction outputs} (UTxO)
\item Smart contracts in the simple language \textsc{script}
\end{itemize}
\end{alertblock}

\begin{alertblock}{Ethereum}
\begin{itemize}
\item Based on the notion of accounts
\item Smart contracts in (almost) Turing-complete Solidity/EVM
\end{itemize}
\end{alertblock}

\begin{alertblock}{Cardano (IOHK)}
\begin{itemize}
\item UTxO-based, with several extensions
\item Due to the extensions, smart contracts become more expressive
\end{itemize}
\end{alertblock}

\end{frame}

\begin{frame}{Methodology}
\begin{itemize}
\item Keep things on an abstract level
  \begin{itemize}
  \item Setup long-term foundations
  \end{itemize}
\item Fully mechanized approach, utilizing Agda's rich type system
\item Fits well with IOHK's research-oriented approach
\end{itemize}

\begin{tikzpicture}
  [basic box/.style = {
     draw,
     shape = rectangle,
     align = center,
     minimum width=2cm,
     minimum height=1.2cm,
     rounded corners},
   to/.style = {
     ->,
     >=stealth',
     semithick
  },
  every matrix/.style={column sep=.8cm, ampersand replacement=\&},
  font=\small
  ]
  \matrix{
     \node[basic box] (a) {pure\\ research};
  \& \node[basic box] (b) {mechanized\\ models};
  \& \node[basic box] (c) {reference\\ implementations};
  \& \node[basic box] (d) {production\\ code}; \\
  };

  \path
  (a) edge[to, mLightBrown] (b)
  (b) edge[to] (c)
  (c) edge[to] (d)
  ;
\end{tikzpicture}
\end{frame}
