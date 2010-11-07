%if include /= True
\begin{comment}
%let include = True
%include Fork/Action.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import Fork.Action

module Fork.Language where
\end{code}
%endif

\section{The Fork Language}

%format LTS = "\func{LTS}"
%if False
\begin{code}
infixl 4 _⊕_
infix 5 #_
\end{code}
%endif

\subsection{Syntax and Virtual Machine}

%format #_ = "\cons{\texttt{\#}\anonymous}"
%format # = "\cons{\texttt{\#}}"
%format _⊕_ = "\cons{\anonymous{\oplus}\anonymous}"
%format ⊕ = "\infix{\cons{\oplus}}"
%format fork = "\cons{fork}"
%format Expression = "\type{Expression}"
As with the Zap language of the previous chapter, we base this Fork language
on that of natural numbers and addition. The inclusion of an extra |fork|
primitive introduces a simple and familiar approach to explicit concurrency:
\begin{code}
data Expression : Set where
  #_    : (m : ℕ) → Expression
  _⊕_   : (a b : Expression) → Expression
  fork  : (e : Expression) → Expression
\end{code}
%format forkIO = "\func{forkIO}"
%format Instruction = "\type{Instruction}"
%format PUSH = "\cons{PUSH}"
%format ADD = "\cons{ADD}"
%format FORK = "\cons{FORK}"
An expression |fork e| will begin evaluation of |e| in a new thread,
immediately returning |# 0|, in a manner reminiscent of Haskell's |forkIO|
primitive. The collection of concurrent threads in the system is modelled as
a `thread soup'~\cite{peyton-jones01-awkward}, defined later in
\S\ref{sec:fork-combined}. Similarly, we extend the virtual machine with
a |FORK| instruction, which spawns a given sequence of instructions in a new
thread:
\begin{code}
data Instruction : Set where
  PUSH  : (m : ℕ) → Instruction
  ADD   : Instruction
  FORK  : (c : List Instruction) → Instruction
\end{code}
The compiler includes an extra case for |fork|, but remains otherwise
unchanged from the definition in \S\ref{sec:nondet-machine}:
%format compile = "\func{compile}"
\begin{code}
compile : Expression → List Instruction → List Instruction
compile (# m)     c = PUSH m ∷ c
compile (a ⊕ b)   c = compile a (compile b (ADD ∷ c))
compile (fork e)  c = FORK (compile e []) ∷ c
\end{code}
As before, each virtual machine thread comprises a list of |Instruction|s
along with a stack of natural numbers:
%format Machine = "\type{Machine}"
%format ⟨_‚_⟩ = "\cons{\langle\anonymous,\!\anonymous\rangle}"
%format ‚ = "\infix{\cons{,}}"
%format ⟨ = "\prefix{\cons{\langle}}"
%format ⟩ = "\postfix{\cons{\rangle}}"
\begin{code}
data Machine : Set where
  ⟨_‚_⟩ : (c : List Instruction) (σ : List ℕ) → Machine
\end{code}

\input{Fork/Action.lagda}

\subsection{Semantics}\label{sec:fork-semantics}

%format _↦‹_›_ = "\type{\anonymous{\mapsto}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↦‹ = "\infix{\type{{\mapsto}\texttt{<}}}"
%format › = "\infix{\type{\texttt{>}}}"
%format ↦-⊞ = "\cons{{\mapsto}\text-\boxplus}"
%format ↦-R = "\cons{{\mapsto}\text-R}"
%format ↦-L = "\cons{{\mapsto}\text-L}"
%format ↦-fork = "\cons{{\mapsto}\text-fork}"
%format a↦a′ = "a{\mapsto}a\Prime{}"
%format b↦b′ = "b{\mapsto}b\Prime{}"
It remains for us to give the semantics for expressions and virtual
machines. As per \S\ref{sec:nondet-language}, expression follow
a left-biased reduction semantics given by the |↦-⊞|, |↦-R| and |↦-L|
rules:
%if False
\begin{code}
infix 3 _↦‹_›_ _↣‹_›_
\end{code}
%endif
\begin{code}
data _↦‹_›_ : LTS (Action Expression) Expression where
  ↦-⊞  : ∀ {m n} → # m ⊕ # n ↦‹ ⊞ › # (m + n)
  ↦-R  : ∀ {m b b′ α}  (b↦b′  : b ↦‹ α › b′) → #  m ⊕ b  ↦‹ α › # m ⊕ b′
  ↦-L  : ∀ {a a′ b α}  (a↦a′  : a ↦‹ α › a′) →    a ⊕ b  ↦‹ α › a′ ⊕ b
  ↦-fork : ∀ {e} → fork e ↦‹ ⁺ e › # 0
\end{code}
%{
%format :: = "\keyw{::}"
%format IO = "\type{IO}"
%format Unit = "\type{()}"
Spawning of new threads is handled by the |↦-fork| rule, which embeds the
expression in an |⁺ e| action. The expression |fork e| immediately reduces
to |# 0|, in a manner reminiscent of Haskell's |forkIO :: IO Unit → IO Unit|
primitive.
%}

%format _↣‹_›_ = "\type{\anonymous{\rightarrowtail}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↣‹ = "\infix{\type{{\rightarrowtail}\texttt{<}}}"
%format ↣-PUSH = "\cons{{\rightarrowtail}\text-PUSH}"
%format ↣-ADD = "\cons{{\rightarrowtail}\text-ADD}"
%format ↣-FORK = "\cons{{\rightarrowtail}\text-FORK}"
In turn, the virtual machine for our Fork language inherits the |↣-PUSH| and
|↣-ADD| rules from that of the Zap language, given in
\S\ref{sec:nondet-machine}:
\begin{code}
data _↣‹_›_ : LTS (Action Machine) Machine where
  ↣-PUSH : ∀ {c σ m} →
    ⟨ PUSH m ∷ c ‚ σ ⟩ ↣‹ τ › ⟨ c ‚ m ∷ σ ⟩
  ↣-ADD : ∀ {c σ m n} →
    ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ↣‹ ⊞ › ⟨ c ‚ m + n ∷ σ ⟩
  ↣-FORK : ∀ {c c′ σ} →
    ⟨ FORK c′ ∷ c ‚ σ ⟩ ↣‹ ⁺ ⟨ c′ ‚ [] ⟩ › ⟨ c ‚ 0 ∷ σ ⟩
\end{code}
In this instance, we have added a |↣-FORK| rule that handles the case of
a |FORK c′| instruction: given a sequence of instructions |c′|, we emit
a newly initialised virtual machine embedded in an |⁺ ⟨ c′ ‚ [] ⟩| action,
leaving |0| on top of the stack.

% vim: ft=tex fo-=m fo-=M:

