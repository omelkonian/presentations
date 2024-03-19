\input{preamble}

\begin{code}[hide]
module Ledger.PDF where

open import Ledger.Introduction

open import Ledger.BaseTypes
open import Ledger.Crypto
open import Ledger.Epoch

open import Ledger.Address
open import Ledger.Script
open import Ledger.ScriptValidation
-- protocol parameters
open import Ledger.PParams
-- ENACT + GOV
open import Ledger.GovStructure
open import Ledger.GovernanceActions
open import Ledger.Gov
-- delegation (DELEG + POOL + GOVCERT)
open import Ledger.Deleg
-- multi-currency
open import Ledger.TokenAlgebra
open import Ledger.TokenAlgebra.ValueSet
-- transactions
open import Ledger.Transaction
-- UTXO
open import Ledger.Utxo
open import Ledger.Utxo.Properties
-- UTXOW
open import Ledger.Utxow
open import Ledger.Utxow.Properties
-- LEDGER
open import Ledger.Ledger
open import Ledger.Ledger.Properties
-- RATIFY
open import Ledger.Ratify
open import Ledger.Ratify.Properties
-- CHAIN
open import Ledger.Chain
open import Ledger.Chain.Properties

open import Haskell
\end{code}

\begin{document}

% Main body: up to 12 pages

\maketitle

\begin{abstract}
\input{abstract}
\end{abstract}

% page 1: title / abstract / intro
% page 2: essentials (sets / maps / transitions / closures)
\section{Introduction}
\label{sec:intro}
\input{Ledger/Introduction}

% page 3: basic types / crypto / token maps
\section{Fundamental entities}
\label{sec:basics}
\subsection{Cryptographic primitives}
\label{sec:crypto}
\input{Ledger/Crypto}
\subsection{Addresses}
\label{sec:addresses}
\input{Ledger/Address}
\subsection{Base types}
\label{sec:base-types}
\input{Ledger/BaseTypes}
%\subsection{Token algebras}
% might want to defer to EUTXO_ma
%\label{sec:token-algebra}
%\input{Ledger/TokenAlgebra}

% page 4-5: protocol parameters + chain transitions + ledger transitions
\section{Advancing the blockchain}
\label{sec:blockchain}
\subsection{Protocol parameters}
\label{sec:protocol-parameters}
\input{Ledger/PParams}
\subsection{Extending the blockchain block-by-block}
\label{sec:chain}
\input{Ledger/Chain} % transitioning the whole blockchain block-by-block
\subsection{Extending the ledger transaction-by-transaction}
\label{sec:ledger}
\input{Ledger/Ledger} % transition the ledger state transaction-by-transaction

% page 6-7: utxo / scripts / witnessing
\section{UTxO}
\label{sec:utxo}
\subsection{Witnessing}
\label{sec:witnessing}
\input{Ledger/Utxow}
\subsection{Accounting}
\label{sec:accounting}
\input{Ledger/Utxo}
\input{Ledger/Utxo/Properties}
%\subsection{Scripts}
%\label{sec:scripts}
%\input{Ledger/Script}

% page 8-9: decentralised governance
% TODO: move after tx?
\section{Decentralized Governance}
\label{sec:governance}

\subsection{Entities and actions}
\label{sec:entities-and-actions}
\input{Ledger/GovernanceActions}

\subsection{Voting and Proposing}
\label{sec:voting}
\input{Ledger/Gov}

\subsection{Ratification}
\label{sec:ratification}
\input{Ledger/Ratify}

% page 10: transactions
\section{Transactions}
\label{sec:transactions}
\input{Ledger/Transaction}

% page 11: Haskell / conformance
\section{
Compiling to a Haskell implementation \&
Conformance testing
}
\label{sec:hs-gen}
\input{Haskell}

% page 12: related work / outro
\section{Related Work}
\label{sec:related-work}
\input{related}

\section{Conclusion}
\input{outro}

% Bibliography: not counting towards page limit
\clearpage
\bibliographystyle{plainurl}
\bibliography{references}

% Appendix: up to 5 pages
\clearpage
\appendix
\input{appendix}

\end{document}
