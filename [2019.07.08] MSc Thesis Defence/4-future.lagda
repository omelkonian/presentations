\section{Future Work}

\begin{frame}{Next Steps: UTxO}
\begin{enumerate}
\item Multi-currency: \alert{non-fungible tokens}
  \begin{itemize}
  \item 2-level maps that introduce intermediate layer with tokens
  \end{itemize}
\item Integrate James Chapman's work on \alert{plutus-metatheory}
  \begin{itemize}
  \item Plutus terms instead of their denotations (i.e. Agda functions)
  \end{itemize}
\item Support for \alert{multi-signature} schemes
\end{enumerate}
\end{frame}

\begin{frame}{Next Steps: BitML}
\begin{enumerate}
\item A lot of proof obligations associated with most datatypes
  \begin{itemize}
  \item Implement \alert{decision procedures} for them, just like we did for UTxO
  \end{itemize}
\item Computational model
  \begin{itemize}
  \item Formulation very similar to the symbolic model we already have,
     but a lot of additional details to handle
  \end{itemize}
\item Compilation correctness: \textit{Symbolic Model} $\approx$ \textit{Computational Model}
  \begin{itemize}
  \item Compile to \alert{abstract UTxO model} instead of concrete Bitcoin transactions?
  \item Already successfully employed by \alert{Marlowe}
  \item \alert{Data scripts} stateful capabilities fit well for state transition systems!
  \end{itemize}
\end{enumerate}
\end{frame}

\begin{frame}{Next Steps: Others}
\begin{enumerate}
\item Proof automation via domain-specific tactics
   \begin{itemize}
   \item Accommodate future formalization efforts
   \end{itemize}
\item Featherweight Solidity
  \begin{itemize}
  \item Provide proof-of-concept model in Agda
  \item Perform some initial comparison with UTxO
  \end{itemize}
\item Investigate Chad Nester's work on \alert{monoidal ledgers}
  \begin{itemize}
  \item This leads to another reasoning device: \alert{string diagrams}
  \end{itemize}
\end{enumerate}
\end{frame}

\section{Conclusion}
\begin{frame}{Conclusion}
\begin{itemize}
\item Formal methods are a promising direction for blockchain
  \begin{itemize}
  \item Especially language-oriented, type-driven approaches
  \end{itemize}
\item Although formalization is tedious and time-consuming
  \begin{itemize}
  \item Strong results and deep understanding of models
  \item Certified compilation is here to stay! (c.f. \textit{CompCert, seL4})
  \end{itemize}
\item However, tooling is badly needed....
  \begin{itemize}
  \item We need better, more sophisticated programming technology
    for dependently-typed languages
  \end{itemize}
\end{itemize}
\end{frame}
