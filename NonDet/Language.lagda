%if False
\begin{code}
import Level
open import Common

module NonDet.Language where
\end{code}
%endif

\section{A Non-Deterministic Language}\label{sec:nondet-language}

In order to focus on the essence of this problem, we abstract from the
details of a real language and keep to a simple expression language
consisting of integers and addition~\cite{hutton04-exceptions,
hutton06-calculating, hutton07-interruptions} as we had done in previous
chapters. We give its operational semantics using a labelled transition
system, together with an extra `\emph{zap}' rule to introduce a form of
non-determinism. A virtual machine, and a compiler linking the two completes
the definition. We present and justify a novel technique for proving
compiler correctness in the presence of non-determinism.

We begin by recalling the syntax of our expression language---comprising
natural numbers and addition---from the previous chapter:
%if False
\begin{code}
infixl 4 _⊕_
infix 5 #_
\end{code}
%endif
%format #_ = "\cons{\texttt{\#}\anonymous}"
%format # = "\cons{\texttt{\#}}"
%format _⊕_ = "\cons{\anonymous{\oplus}\anonymous}"
%format ⊕ = "\infix{\cons{\oplus}}"
%format Expression = "\type{Expression}"
\begin{code}
data Expression : Set where
  #_   : (m : ℕ)             → Expression
  _⊕_  : (a b : Expression)  → Expression
\end{code}
As we had previously noted in \S\ref{sec:semantics-degenerate}, the monoid
$(|ℕ|, |0|, |⊕|)$ may be seen as a degenerate monad, allowing us to avoid
orthogonal issues such as binding and substitution. The sequencing aspect of
monads is retained by giving our language a left-to-right evaluation order.

%format LTS = "\func{LTS}"
Rather than defining a reduction relation between pairs of states as in
chapter \ref{ch:agda}, we generalise to a labelled transition system. For
this we define a shorthand |LTS|, parametrised on the type of labels and the
underlying state:
\begin{spec}
LTS : Set → Set → Set₁
LTS L X = X → L → X → Set
\end{spec}
%format Action = "\type{Action}"
%format ⊞ = "\cons{\boxplus}"
%format ↯ = "\cons{\lightning}"
%format ∎_ = "\cons{\square\anonymous}"
%format ∎ = "\cons{\square}"
%format Label = "\type{Label}"
%format τ = "\cons{\tau}"
%format !_ = "\cons{!\anonymous}"
%format ! = "\cons{!}"
We use |Label|s to indicate the nature of the transition:
\begin{code}
data Action : Set where
  ⊞   : Action
  ↯   : Action
  ∎_  : (m : ℕ) → Action

data Label : Set where
  τ   : Label
  !_  : (α : Action) → Label
\end{code}
Each transition either emits (denoted by `|!|') one of the |⊞|, |↯| or |∎|
actions (pronounced `add', `zap' and `result' respectively), or has the
silent label |τ|. We make a two-level distinction between |Label|s and
|Action|s in this language so that potentially silent and non-silent
transitions may be identified by their types in the Agda proofs.

%if False
\begin{code}
infix 3 _↦‹_›_
\end{code}
%endif
%format _↦‹_›_ = "\type{\anonymous{\mapsto}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↦‹ = "\infix{\type{{\mapsto}\texttt{<}}}"
%format › = "\infix{\type{\texttt{>}}}"
%format ↦-⊞ = "\cons{{\mapsto}\text-\boxplus}"
%format ↦-↯ = "\cons{{\mapsto}\text-\lightning}"
%format ↦-R = "\cons{{\mapsto}\text-R}"
%format ↦-L = "\cons{{\mapsto}\text-L}"
Transitions on expressions are defined as the following data type:
%format a↦a′ = "a{\mapsto}a\Prime{}"
%format b↦b′ = "b{\mapsto}b\Prime{}"
\begin{code}
data _↦‹_›_ : LTS Label Expression where
  ↦-⊞ : ∀ {m n} →  # m  ⊕ # n  ↦‹ ! ⊞ ›  # m + n
  ↦-↯ : ∀ {m n} →  # m  ⊕ # n  ↦‹ ! ↯ ›  # 0
  ↦-R : ∀ {m b b′ Λ}  (b↦b′  : b  ↦‹ Λ › b′) →
                   # m  ⊕ b    ↦‹ Λ ›    # m  ⊕ b′
  ↦-L : ∀ {a a′ b Λ}  (a↦a′  : a  ↦‹ Λ › a′) →
                   a    ⊕ b    ↦‹ Λ ›    a′   ⊕ b
\end{code}
By convention, we will use the letters |m| and |n| for natural numbers, |a|,
|b| and |e| for expressions, |α| for actions and |Λ| for labels. Using
Agda's facility for mixfix operators, the proposition that |e| reduces in
a single |Λ|-labelled step to |e′| is written quite naturally as follows: |e
↦‹ Λ › e′|.

Each constructor of the above definition corresponds to a transition rule.
Let us consider the two base rules, covering expression of the form |#
m ⊕ # n|. When reducing |# m ⊕ # n|, one of two things can happen: either
the two numbers are summed as usual by the |↦-⊞| rule, or they are `zapped'
to zero by |↦-↯|; the two possible transitions are labelled accordingly. The
inclusion of the |↦-↯| rule introduces a simple form of non-determinism, as
a first step towards moving from a sequential, deterministic language, to
a concurrent, non-deterministic one. The two remaining rules |↦-R| and |↦-L|
ensure a left-biased reduction order, as mentioned previously.

\subsection{Choice of Action Set}\label{sec:nondet-action}

How was the set of actions chosen? As we shall see later in
\S\ref{sec:nondet-justification}, we wish to distinguish between different
choices in the reduction path a given expression can take. In the instance
of this Zap language, we need to know which of the |↦-⊞| or |↦-↯| rules were
applied, hence the use of the distinct actions |⊞| and |↯| respectively.
Where there is only one unique transition from some given state, we label it
with a silent |τ|. Later in \S\ref{sec:nondet-combined} we also wish to
distinguish between different final results for an expression, which are
revealed using the |∎| action.

% vim: ft=tex fo-=m fo-=M:

