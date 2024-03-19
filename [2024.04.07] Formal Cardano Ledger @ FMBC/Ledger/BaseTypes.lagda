The basic units of currency and time are \Coin, \Slot and \Epoch,
which we treat as natural numbers, while an implementation might use
isomorphic but more complicated types (for example to represent the
beginning of time in a special way). A \Coin is the smallest unit of
currency, a \Slot is the smallest unit of time (corresponding to 1s
in the main chain), and an \Epoch is a fixed number of slots
(corresponding to 5 days in the main chain). Every slot, a stake pool has
a random chance to be able to mint a block, and one block every five
slots is expected. See \cite{ouroboros_praos}.

\begin{code}[hide]
{-# OPTIONS --safe #-}

module Ledger.BaseTypes where

open import Prelude using (ℕ)

private
\end{code}
\begin{code}[inline]
  Coin =
\end{code}$\ $
\begin{code}[hide,inline]
    ℕ
\end{code}
\begin{code}[inline]
  Slot =
\end{code}$\ $
\begin{code}[hide,inline]
    ℕ
\end{code}
\begin{code}[inline]
  Epoch = ℕ
\end{code}
