\section{Melody}

\begin{frame}{Musicology Source: [Keller, 2007]}
\centering
\includegraphics[keepaspectratio=true,height=.5\paperheight]{source-m.png}
\end{frame}

\begin{frame}{Grammar Symbols: Tones}
\begin{hs}\begin{code}
data M
  =  HT  | CT  | L  | AT | ST | R  -- terminals
  |  P   | Q   | V  | N            -- non-terminals
  deriving Eq
##
(|->) :: (a, Double, Dur -> Bool) -> Term meta a -> Rule meta a
a |-> b = a :-> const b
\end{code}\end{hs}
\end{frame}

\begin{frame}{Grammar for Melodic Jazz Improvisation}
\savecolumns
\begin{hs}\begin{code}
melody :: Grammar () M
melody = P :|:
  [  -- Rhythmic Structure: Expand P to Q
     (P,  1,  (== qn))   :->  (Q %:)
  ,  (P,  1,  (== hn))   :->  (Q %:)
  ,  (P,  1,  (== hnD))  |->  Q :%: hn :-: Q :%: qn
  ,  (P, 25,  (> hnD))   :->  \t -> Q :%: hn  :-: P :%: (t - hn)
  ,  (P, 75,  (> wn))    :->  \t -> Q :%: wn  :-: P :%: (t - wn)
\end{code}\end{hs}
\end{frame}

\begin{frame}{Grammar for Melodic Jazz Improvisation}
\restorecolumns
\begin{hs}\begin{code}
     -- Melodic Structure: Expand Q to V, V to N
  ,  (Q,  52,  (== wn))  |->  Q:%:hn :-: V:%:qn :-: V:%:qn
  ,  (Q,  47,  (== wn))  |->  V:%:qn :-: Q:%:hn :-: V:%:qn
  ,  (Q,   1,  (== wn))  |->  V:%:en  :-: N:%:qn :-: N:%:qn :-: N:%:qn :-: V:%:en
  ,  (Q,  60,  (== hn))  |->  Let (V:%:qn) (\x -> x :-: x)
  ,  (Q,  16,  (== hn))  |->  HT:%:qnD :-: N:%:en
  ,  (Q,  12,  (== hn))  |->  V:%:en :-: N:%:qn :-: V:%:en
  ,  (Q,   6,  (== hn))  |->  N:%:hn
  ,  (Q,   6,  (== hn))  |->  HT:%:qnT :-: HT:%:qnT :-: HT:%:qnT
  ,  (Q,   1,  (== qn))  |->  CT:%:qn
  ,  (V,   1,  (== wn))  |->  Let  (V:%:qn) (\x -> x :-: x :-: x :-: x)
  ,  (V,  72,  (== qn))  |->  Let  (V:%:en) (\x -> x :-: x)
  ,  (V,  22,  (== qn))  |->  N:%:qn
  ,  (V,   5,  (== qn))  |->  Let  (HT:%:enT) (\x -> x :-: x :-: x)
  ,  (V,   1,  (== qn))  |->  Let  (HT:%:enT) (\x -> x :-: x :-: AT:%:enT)
  ,  (V,  99,  (== en))  |->  N:%:en
  ,  (V,   1,  (== en))  |->  HT:%:sn :-: AT:%:sn
\end{code}\end{hs}
\end{frame}

\begin{frame}{Grammar for Melodic Jazz Improvisation}
\restorecolumns
\begin{hs}\begin{code}
     -- Melodic Structure: Expand N to terminals
  ,  (N,   1,  (== hn))  |->  CT  :%:  hn
  ,  (N,  50,  (== qn))  |->  CT  :%:  qn
  ,  (N,  50,  (== qn))  |->  ST  :%:  qn
  ,  (N,  45,  (== qn))  |->  R   :%:  qn
  ,  (N,  20,  (== qn))  |->  L   :%:  qn
  ,  (N,   1,  (== qn))  |->  AT  :%:  qn
  ,  (N,  40,  (== en))  |->  CT  :%:  en
  ,  (N,  40,  (== en))  |->  ST  :%:  en
  ,  (N,  20,  (== en))  |->  L   :%:  en
  ,  (N,  20,  (== en))  |->  R   :%:  en
  ,  (N,   1,  (== en))  |->  AT  :%:  en ^^ ]
\end{code}\end{hs}
\end{frame}

\begin{frame}{Interpretation: From Abstract to Actual Notes}
\begin{hs}\begin{code}
data MelodyConfig = MelodyConfig
  { scales   :: [(Double, ScaleType)]
  , octaves  :: [(Double, Octave)] ^^ }
##
instance Interpret (MelodyConfig, Music SemiChord) M Pitch where
  interpret (cfg, chs) symbols = mapM interpretSymbol . synchronize chs
    where
      synchronize :: Music a -> Music b -> Music (a, b)

      interpretSymbol :: (SemiChord, M) -> IO Pitch
      interpretSymbol (ch, s) = case s of
        CT  -> choose ch
        AT  -> choose $ (ch <~ Mi2) ++ (ch ~> Mi2)
        ST  -> choose $ filter (match chord) (scales cfg)
        dots
\end{code}\end{hs}
\end{frame}
