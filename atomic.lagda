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
% * Combined Semantics and Bisimilarity --definitions
% * Reasoning Transactionally --various lemmas
% * Completeness and Soundness of transactions
% * Bisimilarity of Semantics (correctness, eval-left/right &c.)
% * Conclusion
% Fix up ch.1 & 10. Check for forward refs to ch.9

\input{Atomic/Language.lagda.tex}

\input{Atomic/Transaction.lagda.tex}

% vim: ft=tex fo-=m fo-=M:

