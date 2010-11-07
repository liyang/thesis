The standard approach~\cite{wand95-parallel} to proving compiler correctness
for concurrent languages requires the use of multiple translations into an
underlying process calculus. In this chapter, we present a simpler approach
that avoids the need for such an underlying language, using a new method
that allows us to directly establish a bisimulation between the source and
target languages. We illustrate this technique on a small non-deterministic
language, using the Agda system to present and formally verify our compiler
correctness proofs.

\section{Existing Approach}%{{{%

%format compile = "\func{compile}"
%format src (e) = "\func{s[\![}" e "\func{]\!]}"
%format tgt (e) = "\func{t[\![}" e "\func{]\!]}"
%format weakbisim = "\type{\approx}"
The standard approach~\cite{wand95-parallel} to proving compiler correctness
for concurrent languages requires the use of multiple translations into an
intermediate process calculus. This methodology is captured by the following
diagram:
\[\xymatrix@@C=2ex@@R=6ex{%{{{%
	\text{Source}
		\xyar[rr]^{|compile|}
		\xyar[dr]_{|src _|}
	&&\text{Target}
		\PATH `dr^dl,[] []
			*!(-2,2.125):(-1,.14)\dir{>}
		\xyar[dl]^{|tgt _|}
\\
	&\text{Process Calculus\;|/ weakbisim|}
		\PATH `dl^ul,[] []
			*!(-2.125,2):(.14,-1)\dir{>}
}\]%}}}%
That is, for some compiler from a source language to a target language, we
define separate denotational semantics |src _| and |tgt _| for both
languages in terms of an underlying process calculus with a suitable notion
of bisimulation, or observational equivalence. The compiler is said to be
correct when |src p| and |tgt (compile p)| are bisimilar for all programs |p|.
The advantage of using a traditional process calculus is that we may reuse
existing theories and techniques, and perform our reasoning in a single,
homogeneous framework.

However, there are two drawbacks to this method: firstly, the source
languages is defined by a map |src _| into an underlying process calculus,
which adds an extra level of indirection when reasoning about the
operational behaviour of source programs. Secondly, the target language and
process calculus are given separate \emph{operational} semantics ---
represented by the two circular arrows in the above diagram --- with
a semantic function |tgt _| mapping the former to the latter. Thus we need
to further show that the operational semantics of the target language is
\emph{adequate} with respect to that of the process calculus via the
translation |tgt _|.

%In this paper, we present a simpler approach that avoids the need for an
%intermediate process calculus. Our contributions include:
%\begin{itemize*}
%\item A \emph{combined semantics} which allows us to directly establish
%a bisimulation between the source and target languages.

%\item Illustration of our method on two small example languages, along with
%their respective virtual machines and compilers.

%\item A compiler correctness proof for both example languages, using the
%Agda system for our formal reasoning.
%\end{itemize*}
%After a brief overview of related work~(\S\ref{sec:related}), we begin by
%describing a small non-deterministic language with its associated virtual
%machine and compiler~(\S\ref{sec:zap}), before introducing and justifying
%our \emph{combined semantics}~(\S\ref{sec:justification}). We then state our
%compiler correctness theorem and outline its proof~(\S\ref{sec:zap-proof}).
%Sections \ref{sec:fork} and \ref{sec:fork-proof} scale the technique to
%a more general language with concurrency. Finally we conclude with some
%reflections on Agda and outline directions for future work.

%This paper is aimed at the reader with functional programming background and
%an interest in the semantics or implementation of concurrency. We make use
%of Agda~\cite{norell07-thesis,theagdateam09-wiki} --- a dependently-typed
%programming language and interactive proof assistant --- as a vehicle for
%expressing many of the ideas in this paper, as well as a formal means of
%checking our proofs. Knowledge of Agda is not a requirement and we will
%introduce any concepts when necessary. We use standard Agda colouring
%convention throughout to aid readability, so please download the colour
%version of our paper from \url{http://liyang.hu/#pub-cccctc} if later code
%fragments appear in black and white. The full Agda proofs may be found at
%the same location.

%}}}%

\section{Related Work}%{{{%

The formal notion of \emph{compiler correctness} dates back to 1967, when
McCarthy and Painter~\cite{mccarthy67-arith} proved the correctness of
a compiler from arithmetic expressions to a register machine. Their stated
goal was ``\emph{to make it possible to use a computer to check proofs that
compilers are correct}''; we aim to do precisely this for a concurrent
language.

In the four decades since, a large body of pen-and-paper correctness proofs
have been produced for various experimental languages. (See
\cite{dave03-bib} for a detailed bibliography.) However it is only
recently---by making essential use of a formal theorem prover---that it has
become possible to fully verify a realistic compiler. In particular,
Leroy~\cite{leroy06-certification} has produced a certified compiler for
a C-like core language in the Coq~\cite{the-coq-development-team08-website}
framework, relating a series of intermediate languages, eventually targeting
PowerPC assembly code.

% TODO: Meijer -- ``Calculating Compilers'' -- where do I find a copy? D:

While compiler correctness for sequential languages has been well explored
by many researchers, the issue of concurrency has received relatively little
attention, with most of the progress being made by Wand and his
collaborators. In the early 1980s, Wand~\cite{wand95-denotational} initially
suggested a methodology for sequential languages: by giving the
\emph{denotational} semantics of both source and target languages in
a common domain, the correctness proofs relating the \emph{operational}
behaviour of the source and target languages may then be carried out within
the same domain. Wand then adapted this paradigm to the concurrent
setting~\cite{wand95-parallel} as summarised in our introduction, which is
further elaborated by
Gladstein~\cite{gladstein96-concurrent,gladstein94-thesis}.

Our work in this chapter follows on from Hutton and
Wright~\cite{hutton07-interruptions}, who recently considered the issue of
compiler correctness for a simple non-deterministic language, by relating
a denotational source semantics to an operational target semantics, based on
the extensional notion of comparing final results. As noted
in~\cite{hutton07-interruptions}, the addition of effects and concurrency
requires an intensional notion of comparing intermediate actions via
a suitable notion of bisimulation. The purpose of this chapter is to explore
this idea, while retaining the approach of directly relating the source and
target without the need for an intermediate language.

%}}}%

% vim: ft=tex fo-=m fo-=M:

