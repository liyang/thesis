%include local.fmt

\chapter{A Model of STM}

%\begin{itemize}
%\item expand TFP paper
%\item why not full STM Haskell a là Beauty in the Beast?
%\item something that I could be reasonably expected to produce a proof for
%\item also contrast with Wouter's stop-the-world approach in his thesis
%\end{itemize}

In this chapter, we identify a simplified subset of STM Haskell and
a stop-the-world semantics for this language, suitable for exploring design
issues. We then specify a low-level virtual machine for this language, in
which the transactions are executed concurrently. Finally we give a compiler
correctness statement for the combination. Since the model is implemented as
a Haskell program, we can test its correctness using QuickCheck and HPC.

\section{A Simple Transactional Language}%{{{%

% provide a consistent snapshot of the current state of the shared heap

In chapter \S\ref{ch:stm}, we introduced STM Haskell, which provides a small
set of primitives for working with transactional variables (|TVar|s) in the
|STM| monad, along with |atomically| primitive for running transactions, and
|forkIO| for explicit concurrency in the |IO| monad. The essential parts of
the interface is summarised below:
\begin{spec}
newTVar     :: alpha -> STM (TVar alpha)
readTVar    :: TVar alpha -> STM alpha
writeTVar   :: TVar alpha -> alpha -> STM ()

atomically  :: STM alpha -> IO alpha
forkIO      :: IO () -> IO ()
\end{spec}

\noindent As a first step towards a verified implementation of STM, let us
consider a simplified language, without concerning ourselves with orthogonal
issues. It has a two-level syntax, which can be represented as the following
|Tran| and |Proc| data types in Haskell:
\begin{code}
data Tran  = ValT Integer  | Tran `AddT` Tran  | Read Var     | Write Var
data Proc  = ValP Integer  | Proc `AddP` Proc  | Atomic Tran  | Fork Proc
\end{code}
The two syntactic classes correspond to actions in the |STM| and |IO| monads
respectively. As name binding is a largely orthogonal to our goal of
verifying STM implementations, we replace the \emph{bind} and |return| of
both monads with the monoid of addition and integers, as motivated in
section \S\ref{sec:degenerate} of the previous chapter: by enforcing
a left-to-right reduction semantics for addition, we nevertheless retain the
fundamental monadic idea of sequencing computations and combining their
results~\cite{p1-11?}.

Let us examine the two levels in turn:

%}}}%

% wager

% vim: ft=tex:

