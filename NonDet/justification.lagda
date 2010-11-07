%if include /= True
\begin{comment}
%let include = True
%include NonDet/Language.lagda
%include NonDet/Machine.lagda
\end{comment}
%endif

\section{Non-Deterministic Compiler Correctness}\label{sec:nondet-justification}

%In the presence of non-determinism (such as concurrency) however, there may
%be more than one possible result, therefore we need to generalise this
%assertion to a pair of soundness and completeness properties: by the former,
%we mean that any behaviour of |c| must be permitted by the high-level
%semantics of |p|, while the latter states that |c| must be able to exhibit
%all possible behaviours permitted by |p|.

%To rephrase this in a more precise manner: the soundness property states
%that |p| must be a simulation of |c|, while the completeness property states
%the inverse: |c| must be a simulation of |p|. The generalise theorem is then
%a proposition that |c| and |p| are bisimilar. We will define these notions
%formally in a following section.

%format compile = "\func{compile}"
%format eval = "\func{eval}"
%format exec = "\func{exec}"
%format det-correct = "\func{det\text-correct}"
In general, a compiler correctness theorem asserts that for any source
program, the result of executing the corresponding compiled target code on
its virtual machine will coincide with that of evaluating the source using
its high-level semantics:
\[\xymatrix@@C=6ex@@R=6ex{
	\text{Source}
		\xyar[rr]^{|compile|}
		\xyar[dr]_{|eval|}
	&
	&\text{Target}
		\xyar[dl]^{|exec|}
\\
	&\text{Result}
}\]
With a deterministic language and virtual machine---such as our Zap language
without the two `zap' rules---it would be natural to use a high-level
denotational or big-step semantics for the expression language, which we can
realise as an interpreter
\begin{spec}
eval : Expression → ℕ
\end{spec}
In turn, the low-level operational or small-step semantics for the virtual
machine can be realised as a function
\begin{spec}
exec : List ℕ → List Instruction → List ℕ
\end{spec}
that takes an initial stack along with a list of instructions and returns
the final stack. Compiler correctness is then the statement that:
\begin{spec}
det-correct : ∀ c σ e → exec σ (compile e c) ≡ exec (eval e ∷ σ) c
\end{spec}
%\thmTag{Det}
Equivalently, we can visualise this as the following commuting diagram:
\[|det-correct : ∀ c σ →|
\xymatrix@@C=6ex@@R=8ex{
	\text{|Expression|}
		\xyar[rr]^{|compile _ c|}
		\xyar[dr]_{|exec (eval _ ∷ σ) c|~~}
	&&\text{|List Instruction|}
		\xyar[dl]^{~|exec σ _|}
\\
	&\text{|List ℕ / ≡|}
}\]
That is to say, compiling an expression |a| and then executing the resulting
code together with a code continuation |c| gives the same result---up to
definitional equality---as executing |c| with the value of |a| pushed onto
the original stack |σ|.

The presence of non-determinism requires a more refined approach, due to the
possibility that different runs of the same program may give different
results. One approach is to realise the interpreter and virtual machine as
set-valued functions~\cite{hutton07-interruptions}, restating the above
equality on final values in terms of \emph{sets} of final values. A more
natural approach however, is to define the high-level semantics as
a relation rather than a function, using a small-step operational semantics.
Moreover, the small-step approach also allows us to consider the
\emph{intensional} (or local) notion of what choices are made in the
reduction paths, in contrast to the \emph{extensional} (or global) notion of
comparing final results. In our Zap language, the available choices are
reflected in our selection of transition labels, and we weaken the above
definitional equality to a suitable notion of branching equivalence on
intermediate states. This is just the familiar notion of
bisimilarity~\cite{milner89-ccs}, which we shall make concrete in
\S\ref{sec:nondet-bisimilarity}. As we shall see, the local reasoning
afforded by this approach also leads to simpler and more natural proofs.

% vim: ft=tex fo-=m fo-=M:

