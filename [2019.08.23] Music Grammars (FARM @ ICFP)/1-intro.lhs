\section{Introduction}

\begin{frame}{Motivation}
\begin{itemize}
\item The aim is not to generate a complete music piece
  \begin{itemize}
  \item Rather an aid in the compositional process
  \end{itemize}
\item Do this in a concise way, which is also expressive enough
  \begin{itemize}
  \item To that end, we use formal grammars
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}{Probabilistic Temporal Graph Grammars [2013]}
\centering
\includegraphics[keepaspectratio=true,height=.5\paperheight]{source-ptgg.png}
\end{frame}

\begin{frame}{Probabilistic Temporal Graph Grammars}
\begin{itemize}
\item \textbf{Probabilistic:} Rules are assigned prob. weights
\item \textbf{Temporal:} Rules are time-parametric
\item \textbf{Graph:} |Let| construct allows sharing/repetition
\end{itemize}
\end{frame}

\begin{frame}{Euterpea}
\begin{itemize}
\item Euterpea will be our music development vehicle
\item Define some extra things that are not in the library
  \begin{enumerate}
  \item intervals, chords, scales
  \item transposition on several music elements
  \item random actions in |MonadRandom|
  \end{enumerate}
\end{itemize}
\end{frame}

\begin{frame}{Intervals, Chords/Scales}
\begin{hs}\begin{code}
data Interval
  =     P1   | Mi2  | M2   | Mi3  | M3  | P4    | A4    | P5
  ^^ |  Mi6  | M6   | Mi7  | M7   | P8  | Mi9   | dots  | P15
  deriving (Eq, Enum)
##
type ChordType  =  [Interval]    -- $\equiv$ ScaleType
type SemiChord  =  [PitchClass]  -- $\equiv$ SemiScale
type Chord      =  [Pitch]       -- $\equiv$ Scale

(.=) :: PitchClass -> ChordType -> SemiChord
(.=) = dots
\end{code}\end{hs}
\end{frame}

\begin{frame}{A fairly extensive set of scales/chords}
\begin{hs}\begin{code}
-- Chord types.
maj   =  [P1, M3, P5]
m7b5  =  [P1, Mi3, A4, Mi7]
vdots
allChords = [maj, dots ] :: [ChordType]
##
-- Scale types.
ionian  = [P1, M2, M3, P4, P5, M6, M7]
major   = ionian
lydian  =  mode 4 ionian
vdots
allScales = [ionian, dots ] :: [ScaleType]
\end{code}\end{hs}
\end{frame}

\begin{frame}{Transposition}
\begin{hs}\begin{code}
class Transposable a where
  (~>), (<~) :: a -> Interval -> a
##
instance Transposable PitchClass where dots
instance Transposable Chord where dots
\end{code}\end{hs}
\end{frame}

\begin{frame}{Random actions}
\begin{hs}\begin{code}
equally :: [a] -> [(Double, a)]
equally = zip (repeat 1.0)
##
choose :: MonadRandom m => [(Double, a)] -> m a
choose xs = do
  i <- getIndex <$> getRandomR (0, sum (fst <$> xs))
  return (xs !! i)
##
chooseBy :: MonadRandom m => (a -> Double) -> [a] -> m a
chooseBy = choose . fmap (\a -> (f a , a))
\end{code}\end{hs}
\end{frame}
