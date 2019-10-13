\section{Harmony}


\begin{frame}{Musicology Source: [Rohrmeier, 2011]}
\centering
\includegraphics[keepaspectratio=true,height=.5\paperheight]{source-h.png}
\end{frame}

\begin{frame}{Grammar Symbols: Harmonic Degrees}
\begin{hs}\begin{code}
data Degree
  =    I  | II  | III  | IV  | V  | VI  | VII  -- terminals
  MID  P  | TR  | DR   | SR  | T  | D   | S    -- non-terminals
  deriving (Eq, Enum)
\end{code}\end{hs}
\end{frame}

\begin{frame}{Grammar for Western Tonal Harmony}
\savecolumns
\begin{hs}\begin{code}
harmony :: Grammar Interval Degree
harmony = P :|:
   [  -- Phrase level
      (P,  1, always)  :-> \t -> fillBars (t, 4 * wn) TR
      -- Functional level: Expansion
   ,  (TR, 1, (> wn))  :-> \t -> TR  :%: t/2  :-:  DR  :%: t/2
   ,  (TR, 1, always)  :-> \t -> DR  :%: t/2  :-:  T   :%: t/2
   ,  (DR, 1, always)  :-> \t -> SR  :%: t/2  :-:  D   :%: t/2 ^^ ] ++
   [  (x, 1, (> wn)) :-> \t -> Let (x :%: t/2) (\y -> y :-: y)
   |  x <- [TR, SR, DR] ^^ ] ++
   [  (TR, 1, always)  :-> (T  %:)
   ,  (DR, 1, always)  :-> (D  %:)
   ,  (SR, 1, always)  :-> (S  %:)
\end{code}\end{hs}
\end{frame}

\begin{frame}{Grammar for Western Tonal Harmony}
\restorecolumns
\begin{hs}\begin{code}
      -- Functional level: Modulation
   ,  (D, 1, (>= qn))  :-> \t -> P5 :$: D  :%: t
   ,  (S, 1, (>= qn))  :-> \t -> P4 :$: S  :%: t ^^ ] ++
      -- Scale-degree level: Secondary dominants
   [  (x, 1, (>= hn)) :-> \t -> Let  (x :%: t/2) (\y -> (P5 :$: y) :-: y)
   |  x <- [T, D, S] ^^ ] ++
   [  -- Scale-degree level: Functional-Scale interface
      (T, 1, (>= wn))  :-> \t -> I :%: t/2 :-: IV :%: t/4 :-: I :%: t/4
   ,  (T, 1, always)   :-> (I   %:)
   ,  (S, 1, always)   :-> (IV  %:)
   ,  (D, 1, always)   :-> (V   %:)
   ,  (D, 1, always)   :-> (VI  %:) ^^ ]
\end{code}\end{hs}
\end{frame}

\begin{frame}{Expansion: Key Modulation}
\begin{hs}\begin{code}
data HarmonyConfig = HarmonyConfig
  {  basePc     ::  PitchClass
  ,  baseScale  ::  ScaleType
  ,  chords     ::  [(Double, ChordType)] ^^ }
##
instance Expand HarmonyConfig  Degree Interval SemiChord where
  expand  ::  HarmonyConfig -> Term Interval Degree
          ->  IO (Term () SemiChord)
  expand cfg  (i :$: e)       = expand (cfg {basePc = basePc cfg ~> i}) e
  dots
  expand cfg  (degree :%: t)  = (:%: t) <$> choose (filterChords cfg degree)
\end{code}\end{hs}
\end{frame}

\begin{frame}{Interpretation: From Abstract to Semi Chords}
\begin{hs}\begin{code}
instance Interpret HarmonyConfig SemiChord Chord where
  interpret :: HarmonyConfig -> Music SemiChord -> IO (Music Chord)
  interpret cfg = fold1 f
    where f m (sc, d) = do
      ch <- chooseBy (chordDistance m) (inversions sc)
      return (m :-: ch)
\end{code}\end{hs}
\end{frame}

\begin{frame}{Rewrite Example}
\centering

|P :%: 8 * wn|

\pause

|<~|

|TR :%: 4 * wn :-: TR :%: 4 * wn|

\pause

|<~|

|TR :%: 2 * wn :-: DR :%: 2 * wn :-: TR :%: 2 * wn|

\pause

|vdots|

|<~|

|I :%: wn :-: IV :%: hn I :%: hn :-: (P5 :$: VI :%: wn) :-: V :%: wn :-: I :%: 2 * wn|
\end{frame}
