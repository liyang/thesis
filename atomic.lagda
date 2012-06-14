%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Language.lagda
%include Atomic/Heap.lagda
\end{comment}
%endif

%Implementing STM Correctly
\chapter{Transaction Correctness}

The previous chapter scaled our proof technique to a language with explicit
concurrency. In this chapter, we take a detour to show that we can reconcile
the stop-the-world and interleaved semantics for a simple transactional
language.

% * The Atomic Language
%   * Syntax (describe but explain why 'fork' was dropped)
%   * Heaps and Logs
%   * Choice of Actions
%   * Stop-the-world semantics
%   * Interleaved semantics (Y NO COMPILER?)
% * Reasoning Transactionally --various lemmas
% * Combined Semantics and Bisimilarity --definitions
% * Completeness and Soundness of transactions
% * Bisimilarity of Semantics (correctness, eval-left/right &c.)
% * Conclusion
% Fix up ch.1 & 10. Check for forward refs to ch.9


\input{Atomic/Language.lagda.tex}


\section{Combined Semantics and Bisimilarity}

\input{Atomic/Combined.lagda.tex}
\input{Atomic/Bisimilar.lagda.tex}

\subsection{Definition of Correctness}


\input{Atomic/Lemmas.lagda.tex}


\section{Transaction Correctness}

In this section, we will cover some useful lemmas concerning heaps and
transaction logs that are used to show that the stop-the-world and log-based
transaction semantics coincide.

\input{Atomic/Transaction.lagda.tex}
\input{Atomic/Complete.lagda.tex}
\input{Atomic/Sound.lagda.tex}


\input{Atomic/Correct.lagda.tex}


% vim: ft=tex fo-=m fo-=M:

