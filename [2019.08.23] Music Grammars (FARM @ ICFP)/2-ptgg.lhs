\section{PTGG Extensions}

\begin{frame}{Grammars}
\begin{itemize}
\item A grammars consists of an initial symbol and several rewrite rules:
\begin{hs}\begin{code}
data Grammar meta a
  = a :|: [Rule meta a]
\end{code}\end{hs}
\item A rule replaces an atomic symbol with a grammar term:
\begin{hs}\begin{code}
data Rule meta a
  = (a, Double, Dur -> Bool) :-> (Dur -> Term meta a)
\end{code}\end{hs}
\end{itemize}
\end{frame}

\begin{frame}{Terms}
\begin{itemize}
\item Terms are (sequences of) atomic symbols, possibly wrapped with metadata or repeated with |Let|:
\begin{hs}\begin{code}
data Term meta a
  =  a :#: Dur
  |  Term meta a :-: Term meta a
  |  meta :$: Term meta a
  |  Let (Term meta a) (Term meta a -> Term meta a)
\end{code}\end{hs}
\end{itemize}
\end{frame}

\begin{frame}{Expansion}
\begin{itemize}
\item The user has to provide a way to expand metadata:
\begin{hs}\begin{code}
class Expand input a meta b where
  expand :: input -> Term meta a -> IO (Term () b)
\end{code}\end{hs}
\end{itemize}
\end{frame}

\begin{frame}{Interpretation}
\begin{itemize}
\item The user has to provide a way to interpret abstract musical structures:
\begin{hs}\begin{code}
class ToMusic1 c => Interpret input b c where
  interpret :: input -> Music b -> IO (Music c)
\end{code}\end{hs}
\end{itemize}
\end{frame}

\begin{frame}{User Constraints}
\begin{itemize}
\item All in all, the user makes sure the following constraints are satisfied:
\begin{hs}\begin{code}
type Grammarly input meta a b c =
  ( Eq a, Eq meta, ToMusic1 c
  , Expand input a meta b
  , Interpret input b c )
\end{code}\end{hs}
\end{itemize}
\end{frame}

\begin{frame}{Rewriting}
\begin{itemize}
\item Given a desired total duration, a well-formed grammar and the
required input for expansion and interpretation, rewrite up to fixpoint:
\begin{hs}\begin{code}
runGrammar  ::   Grammarly input meta a b c
            =>   Grammar meta a -> Dur -> input
            ->   IO (Music b,  Music1)
runGrammar (init :|: rs) t0 input = do
  rewritten     <- fixpointM rewrite (init :%: t0)
  expanded      <- expand input (unlet rewritten)
  let abstract  = toMusic expanded
  concrete      <- toMusic1 <$> interpret input abstract
  return (abstract, concrete)
\end{code}\end{hs}
\end{itemize}
\end{frame}

