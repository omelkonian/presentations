\section{Rhythm}

\begin{frame}{Musicology Source: [Bel, 1992]}
\centering
\includegraphics[keepaspectratio=true,height=.5\paperheight]{source-r.png}
\end{frame}

\begin{frame}{Grammar Symbols: Rhythmic Syllables}
\begin{hs}\begin{code}
data Syllable
  =  -- terminals
     Tr  | Kt  | Dhee  | Tee  | Dha  | Ta
  |  Ti  | Ge  | Ke    | Na   | Ra   | Noop
     -- non-terminals
  |  S    | XI   | XD   | XJ   | XA   | XB   | XG   | XH | XC
  |  XE   | XF   | TA7  | TC2  | TE1  | TF1  | TF4  | TD1
  |  TB2  | TE4  | TC1  | TB3  | TA8  | TA3  | TB1  | TA1
  deriving Eq
##
(|-->) :: a -> [a] -> Rule meta a
x |--> xs = (x, 1, always) |-> fold1 :-: ((:% en) <$> xs)
\end{code}\end{hs}
\end{frame}

\begin{frame}{Grammar for Tabla Improvisation}
\savecolumns
\begin{hs}\begin{code}
rhythm :: Grammar () Syllable
rhythm = S :|:
  [ S    |-->  [TE1, XI]
  , XI   |-->  [TA7, XD]  , XD   |-->  [TA8]
  , XI   |-->  [TF1, XJ]  , XJ   |-->  [TC2, XA]
  , XA   |-->  [TA1, XB]  , XB   |-->  [TB3, XD]
  , XI   |-->  [TF1, XG]  , XG   |-->  [TB2, XA]
  , S    |-->  [TA1, XH]
  , XH   |-->  [TF4, XB]  , XH   |-->  [TA3, XC]
  , XC   |-->  [TE4, XD]  , XC   |-->  [TA3, XE]
  , XE   |-->  [TA1, XD]  , XE   |-->  [TC1, XD]
  , XC   |-->  [TB1, XB]
  , S    |-->  [TB1, XF]
  , XF   |-->  [TA1, XJ]  , XF   |-->  [TD1, XG]
\end{code}\end{hs}
\end{frame}

\begin{frame}{Grammar for Tabla Improvisation}
\restorecolumns
\begin{hs}\begin{code}
  , TA7  |-->  [Kt, Dha, Tr, Kt, Dha, Ge, Na]
  , TC2  |-->  [Tr, Kt] , ^^ TE1 |--> [Tr] , ^^ TF1 |--> [Kt]
  , TF4  |-->  [Ti, Dha, Tr, Kt]
  , TE4  |-->  [Ti, Noop, Dha, Ti]
  , TD1  |-->  [Noop] , ^^ TB2 |--> [Dha, Ti] , ^^ TC1 |--> [Ge]
  , TB3  |-->  [Dha, Tr, Kt]
  , TA8  |-->  [Dha, Ti, Dha, Ge, Dhee, Na, Ge, Na]
  , TA3  |-->  [Tr, Kt, Dha] , TB1 |--> [Ti] , TA1 |--> [Dha] ^^ ]
\end{code}\end{hs}
\end{frame}

\begin{frame}{Interpretation: From Syllables to MIDI}
\begin{hs}\begin{code}
instance ToMusic1 Syllable where
  toMusic1 = toMusic . pitch . percussionMap
    where
      percussionMap :: Syllable -> Int
      percussionMap s = case s of  Tr -> 38
                                   Kt -> 45
                                   dots
\end{code}\end{hs}
\end{frame}
