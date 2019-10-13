\section{Generated Results}

\begin{frame}{Songs as Configurations}
\begin{itemize}
\item Given a total duration and the required configurations, generate a "music piece":
\begin{hs}\begin{code}
generate  ::  FilePath -> Dur
          ->  HarmonyConfig -> MelodyConfig
          ->  IO ()
generate f t hCfg mCfg = do
  (absHarm, harm) <- runGrammar harmony t hCfg
  (_,       mel)  <- runGrammar melody t (mCfg, absHarm)
  (_,       rhy)  <- runGrammar rhythm t ()
  writeToMidiFile f (harm :=: mel :=: rhy)
\end{code}\end{hs}
\end{itemize}
\end{frame}

\begin{frame}{Sonata in E Minor}
\begin{hs}\begin{code}
sonata
 =  generate "sonata" (12 * wn)
    HarmonyConfig
      { basePc     = E
      , baseOct    = 4
      , baseScale  = minor
      , chords     = equally [mi, maj, dim] }
    MelodyConfig
      { scales   = equally [ionian, harmonicMinor]
      , octaves  = [(5, 4), (20, 5), (10, 6)] }
\end{code}\end{hs}
\end{frame}

\begin{frame}{Oriental Algebras}
\begin{hs}\begin{code}
orientalAlgebras
 =  generate "oriental" (12 * wn)
    HarmonyConfig
      { basePc     = A
      , baseOct    = 3
      , baseScale  = arabian -- $\equiv$ [P1, M2, Mi3, P4, A4, Mi6, M7]
      , chords     = equally allChords }
    MelodyConfig
      { scales   = equally allScales
      , octaves  = [(20, 4), (15, 5), (5, 6)] }
\end{code}\end{hs}
\end{frame}

