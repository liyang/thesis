%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
%include Atomic/Combined.lagda
%include Atomic/Bisimilar.lagda
%include Atomic/Transaction.lagda
%include Atomic/Complete.lagda
%include Atomic/Sound.lagda
%include Atomic/Lemmas.lagda
\end{comment}
%endif

%Implementing STM Correctly
\chapter{Transaction Correctness}

The previous chapter scaled our proof technique to a language with explicit
concurrency. In this chapter, we now consider a language with transactions.
In order to reconcile the stop-the-world and log-based semantics, we make
two simplifications to our approach. First of all, we replace concurrency
with arbitrary interference by an external agent, and secondly we replace
the compiler and virtual machine with a direct log-based transactional
semantics for the source language.


\input{Atomic/Language.lagda.tex}


\section{Combined Semantics and Bisimilarity}

\input{Atomic/Combined.lagda.tex}
\input{Atomic/Bisimilar.lagda.tex}

\subsection{Definition of Correctness}

%format correct = "\func{correct}"
Having accumulated enough machinery, we can now give a definition of
correctness of the log-based semantics, which is simply the following:
\begin{spec}
correct : ∀ h e → h , e ⊢ ↦: ≈ ↣: ○
\end{spec}
That is for any heap |h| and expression |e|, the stop-the-world semantics
(as represented by |↦:|) and the log-based semantics with an empty
transaction state (proxied by |↣: ○|) are bisimilar up to visible
transitions.


%\input{Atomic/Lemmas.lagda.tex}


\section{Reasoning Transactionally}

In this section, we will cover some useful lemmas concerning heaps and
transaction logs that are used to show that the stop-the-world and log-based
transaction semantics coincide.

\input{Atomic/Transaction.lagda.tex}


\section{Transaction Correctness}

During a transaction, the high-level stop-the-world semantics manipulates
the heap directly, while the log-based semantics accumulates its reads and
writes in a transaction log, eventually committing it to the heap. In this
section we show that for any transaction sequence under one semantics, there
exists a matching sequence under the other semantics.

\input{Atomic/Complete.lagda.tex}

\input{Atomic/Sound.lagda.tex}


%\input{Atomic/Lemmas.lagda.tex} % trivial lemmas

\input{Atomic/Correct.lagda.tex}


\section{Conclusion}

In this chapter we considered a language with transactions, and a worst-case
`mutate' rule in place of explicitly modelling interference by concurrent
threads. We gave a fully formalised proof that our stop-the-world and
log-based semantics for transactions do indeed coincide, without resorting
to any postulated lemmas: the completeness part simply ran the log-based
transaction uninterrupted at the same time as the stop-the-world |↦-atomic|
rule. For soundness we used a key |↣′⋆-swap| lemma showing that regardless
of any heap interference during the log-based transaction, as long as the
pre-commit heap |h′| and logs |l′| were consistent, replaying the
transaction under |h′| gives the same results. This underlines the
importance of |Consistent h′ l′| as the correct criteria for a log-based
transaction to commit.

% vim: ft=tex fo-=m fo-=M:

