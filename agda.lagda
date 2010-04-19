%include local.fmt
%include agda.fmt

\chapter{Machine-Assisted Proofs in Agda}

Agda~\cite{norell07-agda} is a dependently-typed functional programming
language based on Martin-L\"of intuitionistic type
theory~\cite{per-martin-lof}. Via the Curry-Howard correspondence---that is,
viewing types as propositions and programs as proofs---it is also used as
a proof assistant for constructive mathematics. In this chapter, we shall
provide a gentle introduction to the language, and demonstrate how we can
formalise statements of compiler correctness into machine-checked proofs,
culminating in a verified formalisation of the proofs of chapter
\ref{ch:semantics}.

\section{Introduction to Agda}%{{{%

%{{{%
%if False
\begin{code}
module agda where

private
  module ignore where
\end{code}
%endif
%}}}%

%{{{%

The current incarnation of Agda has a syntax similar to that of Haskell, and
should look familiar to readers versed in the latter. As we have done in
previous chapters, we will adopt a colouring convention for ease of
readability:
\begin{longtable}{l||l}
Syntactic Class & Examples \\
\hline
Keywords & |data|, |where|, |with|\ldots \\
Types & |ℕ|, |List|, |Set|\ldots \\
Constructors & |zero|, |suc|, |tt|, |[]|\ldots \\
Functions & |id|, |_+_|, |gmap|\ldots
%\\
%Literals & |0|, |1|, |"hello world"|\ldots
\end{longtable}

\noindent Semantically, Agda is distinguished by its foundation on
\emph{dependent types}, and is closely related to systems such as
Epigram~\cite{conor-thesis-and-papers} and Coq~\cite{coq?}. Dependent types
systems are so-called because they allow for types depend on---or
\emph{indexed} by values---as well as other types. In an informal sense,
generalised abstract data types (GADTs)~\cite{gadts} in recent
implementations of Haskell allow data types to be indexed on their argument
types, in a similar fashion. This provides us with a rich vocabulary of
discourse for not only stating the properties of our programs, but also to
be able to prove such properties within the same system. We will begin to
explore how this is facilitated by dependent types from section
\ref{sec:curry-howard}.

%}}}%

\subsection{Data and Functions}%{{{%

We start our introduction to Agda with some simple data and function
definitions. The language itself does not specify any primitive data types,
and it serves as a good introduction to see how some of these may be defined
in its standard library~\cite{nad-stdlib}. For example, we may define the
Peano numbers as follows:
\begin{code}
    data ℕ : Set where
      zero  : ℕ
      suc   : ℕ → ℕ
\end{code}
This ought to be syntactically reminiscent of Haskell's GADT declarations,
but with a few minor differences. Firstly, arbitrary Unicode~\cite{unicode?}
characters may be used in identifiers, and we do not use upper and lower
case letters to distinguish between values and constructors\footnote{The
implication here is that the processes of syntax highlighting and
type-checking are inextricably linked, and that the colouring provides more
information to the reader.}. Secondly, we write |:| to mean
\emph{has-type-of}, and write |Set| for the \emph{type of
types}\footnote{Agda in fact has countably infinite levels of |Set|s, with
$|Set : Set1 : Set2 : |\ldots$. This stratification prevents the formation
of say, \emph{Russel's paradox}, that would lead to inconsistencies in the
system.}.

Thus, the above defines |ℕ| as a new data type inhabiting |Set|, with
a nullary constructor |zero| as the base case and an unary constructor |suc|
as the inductive case, corresponding to Peano's two axioms: |zero| is
a natural number, and every number |n| has a successor |suc n|.

We may define addition on the natural numbers as follows, by induction on
its first argument:
\begin{code}
    _+_ : ℕ → ℕ → ℕ
    zero   + n = n
    suc m  + n = suc (m + n)
\end{code}
Agda allows the use of arbitrary mixfix operators, where underscores
`$\func{\anonymous}$' denote the positions of arguments. Another difference
is that all functions in Agda must be total. For example, omitting the
|zero| case of |_+_| would lead to an error during the typechecking process,
rather than a warning as in Haskell. Additionally, only structural recursion
is permitted. In the definition of |_+_| above, we recurse on the definition
of |ℕ|: the first argument is strictly smaller on the right hand side,
i.e.~|m| rather than |suc m|. While more general forms of recursion are
possible, Agda requires us to give a proof of their totality.

%}}}%

\subsection{Programs as Proofs and Types as Predicates}\label{sec:curry-howard}%{{{%

The Curry-Howard correspondence refers to the initial observation by Curry
that types---in the sense familiar to functional programmers---correspond to
axiom-schemes for intuitionistic logic, while Howard later noted that proofs
in formal systems such as natural deduction can be directly interpreted as
terms in a model of computation such as the typed lambda calculus.

The intuitionistic approach to logic only relies on constructive methods,
disallowing notions from classical logic such as the law of excluded middle
or double-negation elimination. For example, intuitionist reject the former
statement of $P \vee \lnot P$, since there exists a statement $P$ in any
sufficiently powerful logic that can neither be proved nor disproved within
the system, by G\"odel's incompleteness theorems. In other words,
intuitionism equates the truth of a statement $P$ with the possibility of
constructing a proof object that satisfies $P$. A proof refuting the
non-existence of such an object---that is, proving $\lnot \lnot
P$---provides strictly less information than constructing a proof object
satisfying $P$ itself.

What does this mean for the proletarian programmer? Under the Curry-Howard
correspondence, the type |A -> B| is interpreted as the logical statement
`\emph{|A| implies |B|}' and vice-versa. Accordingly, a program |p : A -> B|
corresponds to the proof of `\emph{|A| implies |B|}', in that executing |p|
constructs a witness of |B|, given a witness of |A| as input. Thus in
a suitable type system, programming is the same as constructing proofs in
a very concrete sense.

In a traditional strictly typed programming language such as Haskell, the
type system exists to segregate values of different types. On the other
hand, distinct values of the same type all look the same to the
type-checker, which means we are unable to form types corresponding to
propositions about particular values. Haskell's GADTs break down this
barrier in a limited sense, by allowing the constructors of a parametric
type to target particular instantiations of the return type. While this
allows us to abuse a Haskell type checker that supports GADTs as
a proof-checker in some simple cases, it comes at the cost of requiring
`counterfeit type-level copies of data'.~\cite{mcbride02-faking}

%}}}%

\subsection{Dependent Types}%{{{%

Dependent type systems follow a more principled approach, being founded on
Martin-L\"of intuitionistic type theory~\cite{martin-lof-1971}. These have
been studied over several decades, eventually evolving to its current form
in the second incarnation of Agda~\cite{ulf}.

Coming from a Hindley-Milner background, the key distinction of dependent
types is that values can influence the types of other, subsequent values.
Let us introduce the notion by considering an example of a dependent type:
%format fz = "\cons{fz}"
%format fs = "\cons{fs}"
\begin{code}
    data Fin : ℕ → Set where
      fz  : {n : ℕ}          → Fin (suc n)
      fs  : {n : ℕ} → Fin n  → Fin (suc n)
\end{code}
This defines a data type |Fin|---similar to |ℕ| above---that is additionally
parametrised---or \emph{indexed}---by a natural number. Its two constructor
are analogues of the |zero| and |suc| of |ℕ|. The |fz| constructor takes an
parameter of type |ℕ| named |n|, that is referred to in its resultant type
of |Fin (suc n)|. The braces |{| and |}| indicate that |n| is an implicit
parameter, which we may omit at applications of |fz|, provided that the
value of |n| can be automatically inferred. We can see how this might be
possible in the case of the |fs| constructor: its explicit argument has type
|Fin n|, from which we may deduce |n|.

The above |Fin| represents a family of types, where each type |Fin n| has
exactly |n| distinct values. This is apparent in the resultant types of the
constructors, for example: neither |fz| and |fs| can inhabit |Fin zero|, as
they both target |Fin (suc n)| for some value of |n|. The only inhabitant of
|Fin (suc zero)| is |fz|, since |fs| requires an argument of type |Fin
zero|, which would correspond to a proof that |Fin zero| is inhabited.
Applications of the |Fin| family include for example, type-safe lookup of
vectors or arrays, where we wish to have a static guarantee on the size of
the index is required.

This is only an elementary demonstration of the power of dependent types.
Being able to form any proposition in intuitionistic logic as a type gives
us a powerful vocabulary with which to state and verify the properties of
our programs. Conversely, by interpreting a type as its correspond
proposition, we have mapped the activity of constructing mathematical proofs
to `just' programming, albeit in a more rigorous fashion than usual.

%}}}%

%2010/04/14: [01:30] <pigworker> They have names. "Martin-Löf equality"
%takes just the set as as the parameter; "Paulin-Mohring equality" takes the
%set and one of the elements as parameter.

\subsection{Equality and Its Properties}%{{{%

The previous section introduced dependent types from a programming and data
types point-of-view. We shall now take a look at how we can use dependent
types to state logical propositions and to construct their proofs.

A simple and commonplace construct is that of an equality type,
corresponding to the proposition that two elements of the same type are
definitionally equal. The following definition encodes the Martin-L\"of
equality relation:
%format _≡_ = "\type{\anonymous{\equiv}\anonymous}"
%format refl = "\cons{refl}"
\savecolumns
\begin{code}
    data _≡_ {X : Set} : X → X → Set where
      refl : {x : X} → x ≡ x
\end{code}
Agda does not share Haskell's Hindley-Milner polymorphism, although we can
simply take an additional parameter of the type we wish to be polymorphic
over. In the above definition of equality, the variable |X| corresponds to
the type of the underlying values, which can often be inferred from the
surrounding context. By marking this parameter as implicit, we effectively
achieve the same end result.

The above definition of |_≡_| is indexed by two explicit parameters of type
|X|. Its sole constructor is |refl|, that inhabits the type |x ≡ x| given an
argument of |x : X|. Logically, |refl| corresponds to the axiom of
reflexivity $\forall x.\ x \equiv x$. In cases where the type of the
argument---such as |x| here---can be inferred form the surrounding context,
the |∀| keyword allows us to write the type in a way that better resembles
the corresponding logical notation, for example:
\restorecolumns
\begin{spec}
      refl : ∀ {x} → x ≡ x
\end{spec}
In general, Agda syntax allows us to write `$\anonymous$' in place of
expressions---including types---that may be automatically inferred. The
above is in fact syntactic sugar for the following:
\restorecolumns
\begin{spec}
      refl : {x : _} → x ≡ x
\end{spec}
Agda includes an interactive user interface for the Emacs~\cite{stallman}
operating system, which supports incremental development by the placement of
`holes' where arbitrary expressions are expected. Incomplete programs with
holes can be passed to the type checker, which then informs the user of the
expected type. Thus, writing proofs in Agda is typically a two-way dialogue
between the user and the type checker.

%format sym = "\func{sym}"
%format x≡y = "x{\equiv}y"
Given the above definition of reflexivity as an axiom, we may go on to prove
that |≡| is also symmetric and transitive. The former is the proposition
that given any |x|, |y|, a proof of |x ≡ y| implies that |y ≡ x|. This is
implemented as the following |sym| function,
\def\symHole{|sym x y x≡y = ?|}
\begin{code}
    sym : {X : Set} (x y : X) → x ≡ y → y ≡ x
    {-"\symHole"-}
\end{code}
where the `|?|' mark indicates an as-yet unspecified expression. Multiple
arguments of the same type are simply separated with spaces, while arrows
between pairs of named arguments can be omitted, since there cannot be any
ambiguity.

Successfully type-checking the above turns the `|?|' into a \emph{hole}
$\hole{\{~\}}$, inside which we may further refine the proof. The expected
type of the hole is also displayed, and we can ask the type-checker to
enumerate any local names that are in scope. In this case, the hole is
expected to be of type |y ≡ x|, and the arguments |x y : X| and |x≡y
: x ≡ y| are in scope.

At this point, we can ask the system to perform case-analysis on |x≡y|.
Being an instance of |_≡_|, we expect this argument can only be |refl|
constructor. But something magical also happens during the case analysis:
\begin{spec}
    sym x .x refl = {-"\hole{\{~\}}"-}
\end{spec}
Since |refl| only inhabits the type |x ≡ x|, the type checker concludes that
the first two arguments |x| and |y| must be the same, and rewrites the
second as |.x| to reflect this fact. Whereas pattern matching in Haskell is
an isolated affair, in a dependently typed context the same can potentially
cause interactions with other arguments, revealing more information about
the arguments that can be checked and enforced by the system.

Accordingly, |y| is no longer in-scope, and the goal type becomes |x ≡ x|,
which is satisfied by |refl|:
\begin{code}
    sym x .x refl = refl
\end{code}
%format sym' = sym
As we do not explicitly refer to |x| on the right hand side, we could have
made the |x| and |y| arguments implicit too, leading to a more succinct
definition:
\begin{code}
    sym' : {X : Set} → {x y : X} → x ≡ y → y ≡ x
    sym' refl = refl
\end{code}
We prove transitivity in a similar fashion,
%format trans = "\func{trans}"
\begin{code}
    trans : ∀ {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
    trans refl refl = refl
\end{code}
where pattern-matching the first explicit argument with |refl| unifies |x|
and |y|, while repeating this with the second argument unifies |x| and |z|.
The resulting goal of |x ≡ x| is then met on the right hand side with
|refl|.

%}}}%

\subsection{Existentials and Dependent Pairs}%{{{%

In the previous section, we had already surreptitiously modelled the
universal quantifier $\forall$ as dependent functions---that is, functions
where values of earlier arguments may influence later types. Dually, we can
model the existential quantifier $\exists$ using \emph{dependent pairs}.
This is typically defined in terms of the |Σ| type:
\begin{code}
    data Σ (X : Set) (P : X → Set) : Set where
      _‚_ : (x : X) → (p : P x) → Σ X P
\end{code}
We can interpret the type |Σ X (λ x → P x)| as the existentially quantified
statement that $\exists x \in X.\ P(x)$. Correspondingly, a proof of this
comprises a pair |x| and |p|, where the latter is a proof of the proposition
|P x|. Unlike classical proofs of existence which may not necessarily be
constructive, a proof of the existence of some |x| satisfying |P|
necessarily requires us to supply such an |x|. Conversely, we can always
extract an |x| from such a proof.

As |X| can often be inferred from the type of the predicate |P|, we may
define a convenience function |∃| that accepts |X| as an implicit argument:
\begin{code}
    ∃ : {X : Set} (P : X → Set) → Set
    ∃ {X} = Σ X
\end{code}
The above definition of |∃| allows us to write |∃ λ x → P x|, which better
resembles the corresponding logical proposition of $\exists x.\ P(x)$.

Of course, the predicate |P| need not necessarily depend on the first
element of a pair. In such cases, the resulting type is a non-dependent
pair, which corresponds to a logical conjunction. This can be recovered as
a degenerate case of the above |Σ| type, in which we simply ignore the value
of the first type:
\begin{code}
    _×_ : Set → Set → Set
    X × Y = Σ X (λ _ → Y)
\end{code}

%\noindent Logical disjunction on the other hand corresponds to a sum type,
%sometimes called a tagged-union.
%\begin{code}
%    data _⊎_ (X Y : Set) : Set where
%      inj₁  : (x : X) → X ⊎ Y
%      inj₂  : (y : Y) → X ⊎ Y
%\end{code}

%}}}%

\subsection{Binary Relations and Reflexive Transitive Closures}%{{{%

% \cite{McBride/Norell/Jansson}

Before we conclude this very brief introduction to Agda, we shall introduce
the \emph{reflexive transitive closure} of McBride, Norell and
Jansson~\cite{fita-2007-nov}, which generalises the notion of sequences in
a dependently-typed context. This general construct will prove useful later
when working with sequences of small-step reductions.

We begin by defining binary relations parametrised on their underlying
types:
\begin{code}
    Rel : Set → Set1
    Rel X = X → X → Set
\end{code}
|Rel X| corresponds to the type of binary relations on |X|. In fact, our
earlier definition of propositional equality could equivalently have been
written as follows:
\begin{spec}
    data _≡_ {X : Set} : Rel X where
      refl : {x : X} → x ≡ x
\end{spec}

\noindent The definition of |Star| is parametrised on a set of indices |I|
and a binary relation |R| on |I|. The type |Star {I} R| is itself another
binary relation, indexed on the same |I|:
\begin{code}
    data Star {I : Set} (R : Rel I) : Rel I where
      ε    : {i : I} → Star R i i
      _◅_  : {i j k : I} → (x : R i j) → (xs : Star R j k) → Star R i k
\end{code}
Here, |ε| gives a trivial witness of reflexivity for any |i|. The |_◅_|
constructor provides a heterogeneous definition of transitivity, accepting
a proof of |R i j| and an |R|-chain relating |j| and |k| as its two
arguments. Thus |Star R| defines the type of the reflexive transitive
closure of |R|. Being data, we may take apart an element of |Star R i k| and
inspect each step of the |R|-chain.

Alternatively the constructors |ε| and |_◅_| could be thought of as
generalisations of the \emph{nil} and \emph{cons} constructors of the list
data type for proofs of the form |R i k|, with the constraint that two
adjacent elements |x : R i j| and |y : R j k| must share a common index |j|.

%if False
\begin{code}
    infixr 5 _◅_
    data ⊤ : Set where
      tt : ⊤
\end{code}
%endif

In the degenerate case of a constant relation |(λ _ _ → X) : Rel I| that
ignores its indices, we recover the usual definition of lists of |X|:
\begin{code}
    List : Set → Set
    List X = Star (λ _ _ → X) tt tt
\end{code}
Here |tt| is the unique constructor of the unit type |⊤|, with |ε| and |_◅_|
taking the r\^oles of \emph{nil} and \emph{cons} respectively. For example,
we could write the two-element list of 0 and 1 as follows:
\begin{code}
    two : List ℕ
    two = zero ◅ suc zero ◅ ε
\end{code}
Given its similarities to lists, |Star| admits many of the usual list-like
functions. For example, while the |_◅◅_| function below provides a proof of
transitivity for |Star R|, it could equally be considered the generalisation
of \emph{append} on lists, as suggested by the structure of its definition:
\begin{code}
    _◅◅_ :  {I : Set} {R : Rel I} {i j k : I} →
            Star R i j → Star R j k → Star R i k
    ε         ◅◅ ys = ys
    (x ◅ xs)  ◅◅ ys = x ◅ (xs ◅◅ ys)
\end{code}
Similarly, we can define an analogue of \emph{map} on lists:
%format I′ = "I\Prime{}"
\begin{code}
    gmap :  {I I′ : Set} {R : Rel I} {S : Rel I′} (f : I → I′) →
            (  {x y : I}  →       R x y  →       S (f x)  (f y)) →
               {i j : I}  → Star  R i j  → Star  S (f i)  (f j)
    gmap f g ε         = ε
    gmap f g (x ◅ xs)  = g x ◅ gmap f g xs
\end{code}
As well a function |g| that is mapped over the individual elements of the
sequence, |gmap| also takes a function |f| that allows for the indices to
change.

%format <₁ = "\infix{\type{<_1}}"
%format _<₁_ = "\type{\anonymous{<_1}\anonymous}"
%format lt₁ = "\cons{lt_1}"
To conclude, let us consider a simple use case for |Star|. Take the
\emph{predecessor} relation on natural numbers, defined as |_<₁_| below:
\begin{code}
    data _<₁_ : Rel ℕ where
      lt₁ : (n : ℕ) → n <₁ suc n
\end{code}
Here, |lt₁ n| witnesses |n| as the predecessor of |suc n|. We can then
conveniently define the reflexive transitive closure of |_<₁_| as follows:
%format ≤ = "\infix{\type{\le}}"
%format _≤_ = "\type{\anonymous{\le}\anonymous}"
\begin{code}
    _≤_ : Rel ℕ
    _≤_ = Star _<₁_
\end{code}
Of course, this is just the familiar \emph{less than or equal} relation, for
which we can easily prove some trivial properties:
%format 0≤n = "\func{0{\le}n}"
\begin{code}
    0≤n : (n : ℕ) → zero ≤ n
    0≤n zero     = ε
    0≤n (suc n)  = 0≤n n ◅◅ (lt₁ n ◅ ε)
\end{code}
Note that a proof of |zero ≤ n| as produced by the above |0≤n| function
actually consists of a \emph{sequence} of proofs in the style of ``\emph{0
is succeeded by 1, which is succeeded by 2, \ldots{} which is succeeded by
|n|}'' that can be taken apart and inspected one by one. We will be doing
exactly this when considering reduction sequences in our later proofs.

%}}}%

%}}}%

%{{{%
%if False
\begin{code}
open import Data.Sum
import Data.Product as Σ
open Σ renaming (_,_ to _&_)
import Data.Star as Star
open Star

open import Data.Nat
open import Data.List
open import Data.List.Properties

open import Function

open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≢_; _with-≡_)
\end{code}
%endif
%}}}%

\section{Integers and Addition}

The language in question:
%{{{%
%if False
\begin{code}
infixl 4 _⊕_
infix 5 #_
\end{code}
%endif
%format #_ = "\cons{\texttt{\#}\anonymous}"
%format # = "\prefix{\cons{\texttt{\#}}}"
%format _⊕_ = "\cons{\anonymous{\oplus}\anonymous}"
%format ⊕ = "\infix{\cons{\oplus}}"
%format Expression = "\type{Expression}"
\begin{code}
data Expression : Set where
  #_   : (m : ℕ)             → Expression
  _⊕_  : (a b : Expression)  → Expression
\end{code}
%}}}%

\section{Denotational}

%{{{%
%format ⟦_⟧ = "\func{[\![\anonymous]\!]}"
%format ⟦ = "\prefix{\func{[\![}}"
%format ⟧ = "\postfix{\func{]\!]}}"
\begin{code}
⟦_⟧ : Expression → ℕ
⟦ # m ⟧    = m
⟦ a ⊕ b ⟧  = ⟦ a ⟧ + ⟦ b ⟧
\end{code}
%}}}%

\section{Big-Step Semantics}

Functions are more straightforward, but does not generalise to non-deterministic semantics.

%{{{%
%if False
\begin{code}
infix 4 _⇓_
\end{code}
%endif
%format _⇓_ = "\type{\anonymous{\Downarrow}\anonymous}"
%format ⇓ = "\infix{\type{{\Downarrow}}}"
%format ⇓-ℕ = "\cons{{\Downarrow}\text-\mathbb{N}}"
%format ⇓-⊕ = "\cons{{\Downarrow}\text-\oplus}"
\begin{code}
data _⇓_ : Expression → ℕ → Set where
  ⇓-ℕ  : ∀ {m} → # m ⇓ m
  ⇓-⊕  : ∀ {a b m n} → a ⇓ m → b ⇓ n → a ⊕ b ⇓ m + n
\end{code}
%}}}%

\section{Small-Step Semantics}

As a function:
%{{{%
%if False
\begin{code}
-- ⊕≡e⇒∄m≡e : ∀ {a b e} → a ⊕ b ≡ e → ∄ λ m → # m ≡ e
-- ⊕≡e⇒∄m≡e ≡.refl (n & ())

-- step : (e : Expression) → {_ : ∄ λ m → # m ≡ e} → Expression
-- step (# m) {¬m} = ⊥-elim (¬m (m & ≡.refl))
-- step (a ⊕ b) with ≡.inspect a
-- step (a ⊕ b) | (_ ⊕ _) with-≡ ⊕≡a = step a {⊕≡e⇒∄m≡e ⊕≡a} ⊕ b
-- step (a ⊕ b) | (# m) with-≡ m≡a with ≡.inspect b
-- step (a ⊕ b) | (# m) with-≡ m≡a | (_ ⊕ _) with-≡ ⊕≡b = a ⊕ step b {⊕≡e⇒∄m≡e ⊕≡b}
-- step (a ⊕ b) | (# m) with-≡ m≡a | (# n) with-≡ n≡b = # m + n
\end{code}
%endif
%format step = "\func{step}"
%format a′ = "a\Prime{}"
%format b′ = "b\Prime{}"
\begin{code}
step : (e : Expression) → ℕ ⊎ Expression
step (# m) = inj₁ m
step (a ⊕ b)  with step a
step (a ⊕ b)  | inj₁ m  with step b
step (a ⊕ b)  | inj₁ m  | inj₁ n   = inj₂ (# (m + n))
step (a ⊕ b)  | inj₁ m  | inj₂ b′  = inj₂ (a ⊕ b′)
step (a ⊕ b)  | inj₂ a′ = inj₂ (a′ ⊕ b)
\end{code}
%}}}%

As a relation:
%{{{%
%if False
\begin{code}
infix 3 _↦_ _↦⋆_ _↦⋆#_
\end{code}
%endif
%format _↦_ = "\type{\anonymous{\mapsto}\anonymous}"
%format ↦ = "\type{{\mapsto}}"
%format _↦⋆_ = "\type{\anonymous{\mapsto}^\star\anonymous}"
%format ↦⋆ = "\type{{\mapsto}^\star}"
%format _↦⋆#_ = "\type{\anonymous{\mapsto}^\star\;" # "\anonymous}"
%format ↦⋆# = "\type{{\mapsto}^\star}\;" #
%format ↦-ℕ = "\cons{{\mapsto}\text-\mathbb{N}}"
%format ↦-L = "\cons{{\mapsto}\text-L}"
%format ↦-R = "\cons{{\mapsto}\text-R}"
\begin{code}
data _↦_ : Rel Expression _ where
  ↦-ℕ  : ∀ {m n}       →           #  m  ⊕ # n  ↦ # (m + n)
  ↦-L  : ∀ {a a′ b  }  → a ↦ a′ →     a  ⊕ b    ↦    a′  ⊕ b
  ↦-R  : ∀ {m b  b′ }  → b ↦ b′ →  #  m  ⊕ b    ↦ #  m   ⊕ b′

_↦⋆_ : Rel Expression _
_↦⋆_ = Star _↦_

_↦⋆#_ : REL Expression ℕ _
e ↦⋆# m = e ↦⋆ # m
\end{code}
%}}}%

\section{Equivalence Proof and Techniques}

%{{{%
%format denotation→big = "\func{denot{\rightarrow}big}"
\begin{code}
denotation→big : ∀ {e m} → ⟦ e ⟧ ≡ m → e ⇓ m
denotation→big {# m}    ≡.refl = ⇓-ℕ
denotation→big {a ⊕ b}  ≡.refl = ⇓-⊕ (denotation→big ≡.refl) (denotation→big ≡.refl)
\end{code}

%format big→denotation = "\func{big{\rightarrow}denot}"
%format a⇓m = "a{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"
\begin{code}
big→denotation : ∀ {e m} → e ⇓ m → ⟦ e ⟧ ≡ m
big→denotation ⇓-ℕ = ≡.refl
big→denotation (⇓-⊕ a⇓m b⇓n) rewrite big→denotation a⇓m | big→denotation b⇓n = ≡.refl
\end{code}

%format big→small = "\func{big{\rightarrow}small}"
%format a⇓m = "a{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"
\begin{code}
big→small : ∀ {e m} → e ⇓ m → e ↦⋆# m
big→small ⇓-ℕ = ε
big→small (⇓-⊕ {a} {b} {m} {n} a⇓m b⇓n) =
  gmap (λ a′ →    a′  ⊕ b)   ↦-L (big→small a⇓m) ◅◅
  gmap (λ b′ → #  m   ⊕ b′)  ↦-R (big→small b⇓n) ◅◅
  ↦-ℕ ◅ ε
\end{code}

%format small→big = "\func{small{\rightarrow}big}"
%format e′ = "e\Prime{}"
%format e↦e′ = "e{\mapsto}e\Prime{}"
%format e′↦⋆m = "e\Prime{}{\mapsto}^\star{}m"
%format sound = "\func{sound}"
%format a↦a′ = "a{\mapsto}a\Prime{}"
%format b↦b′ = "b{\mapsto}b\Prime{}"
%format a′⇓m = "a\Prime{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"
%format b′⇓n = "b\Prime{\Downarrow}n"
%format m⇓m = "m{\Downarrow}m"
\begin{code}
small→big : ∀ {e m} → e ↦⋆# m → e ⇓ m
small→big ε = ⇓-ℕ
small→big (e↦e′ ◅ e′↦⋆m) = sound e↦e′ (small→big e′↦⋆m) where
  sound : ∀ {e e′ m} → e ↦ e′ → e′ ⇓ m → e ⇓ m
  sound ↦-ℕ         ⇓-ℕ               = ⇓-⊕ ⇓-ℕ ⇓-ℕ
  sound (↦-L a↦a′)  (⇓-⊕ a′⇓m  b⇓n)   = ⇓-⊕ (sound a↦a′ a′⇓m) b⇓n
  sound (↦-R b↦b′)  (⇓-⊕ m⇓m   b′⇓n)  = ⇓-⊕ m⇓m (sound b↦b′ b′⇓n)
\end{code}
%}}}%

\section{Stack Machines and Their Semantics}

%{{{%
%format Instruction = "\type{Instruction}"
%format PUSH = "\cons{PUSH}"
%format ADD = "\cons{ADD}"
\begin{code}
data Instruction : Set where
  PUSH : ℕ → Instruction
  ADD : Instruction
\end{code}

%format compile = "\func{compile}"
\begin{code}
compile : Expression → List Instruction → List Instruction
compile (# m)    c = PUSH m ∷ c
compile (a ⊕ b)  c = compile a (compile b (ADD ∷ c))
\end{code}

%format Machine = "\type{Machine}"
%format ⟨_‚_⟩ = "\cons{\langle\anonymous{,}\anonymous\rangle}"
%format ⟨ = "\prefix{\cons{\langle}}"
%format ‚ = "\cons{,}"
%format ⟩ = "\postfix{\cons{\rangle}}"
\begin{code}
data Machine : Set where
  ⟨_‚_⟩ : List Instruction → List ℕ → Machine
\end{code}

%format _↣_ = "\type{\anonymous{\rightarrowtail}\anonymous}"
%format ↣ = "\type{{\rightarrowtail}}"
%format _↣⋆_ = "\type{\anonymous{\rightarrowtail}^\star\anonymous}"
%format ↣⋆ = "\type{{\rightarrowtail}^\star}"
%format _↣⋆#_ = "\type{\anonymous{\rightarrowtail}^\star\;" # "\anonymous}"
%format ↣⋆# = "\type{{\rightarrowtail}^\star}\;" #
%format σ = "\sigma"
%format ↣-PUSH = "\cons{{\rightarrowtail}\text-PUSH}"
%format ↣-ADD = "\cons{{\rightarrowtail}\text-ADD}"
\begin{code}
infix 3 _↣_
data _↣_ : Rel Machine _ where
  ↣-PUSH : ∀ {m c σ} → ⟨ PUSH m ∷ c ‚ σ ⟩ ↣ ⟨ c ‚ m ∷ σ ⟩
  ↣-ADD : ∀ {m n c σ} → ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ↣ ⟨ c ‚ m + n ∷ σ ⟩
\end{code}

%if False
\begin{code}
infix 3 _↣⋆_
_↣⋆_ : Rel Machine _
_↣⋆_ = Star _↣_

infix 3 _↣⋆#_
\end{code}
%endif

%}}}%

%{{{%
%format big→machine = "\func{big{\rightarrow}machine}"
\begin{code}
_↣⋆#_ : REL Expression ℕ _
e ↣⋆# m = ∀ {c σ} → ⟨ compile e c ‚ σ ⟩ ↣⋆ ⟨ c ‚ m ∷ σ ⟩

big→machine : ∀ {e m} → e ⇓ m → e ↣⋆# m
big→machine ⇓-ℕ = ↣-PUSH ◅ ε
big→machine (⇓-⊕ a⇓m b⇓n) =
  big→machine a⇓m ◅◅ big→machine b⇓n ◅◅ ↣-ADD ◅ ε
\end{code}

\begin{code}
small→machine : ∀ {e m} → e ↦⋆# m → e ↣⋆# m
small→machine ε = ↣-PUSH ◅ ε
small→machine (↦-ℕ ◅ ε) = ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ ε
small→machine (↦-ℕ ◅ () ◅ xs)
small→machine (↦-L a↦a′ ◅ a′⊕b↦m) = {!small→machine a′⊕b↦m!}
small→machine (↦-R b↦b′ ◅ na⊕b′↦m) = {!!}
\end{code}

%format exec = "\func{exec}"
%format na = "n_a"
%format a↣⋆#na = a "{\rightarrowtail^\star}" na
%format nb = "n_b"
%format b↣⋆#nb = b "{\rightarrowtail^\star}" nb
\begin{code}
exec : ∀ e → ∃ λ m → e ↣⋆# m
exec (# m) = m & λ {c} {σ} → ↣-PUSH ◅ ε
exec (a ⊕ b) with exec a | exec b
exec (a ⊕ b) | na & a↣⋆#na | nb & b↣⋆#nb = na + nb &
  λ {c} {σ} → a↣⋆#na ◅◅ b↣⋆#nb ◅◅ ↣-ADD ◅ ε
\end{code}

%format unique = "\func{unique}"
%format σ′ = σ "\Prime{}"
%format σ″ = σ "\PPrime{}"
%format σ₀ = σ "_0"
%format c′ = c "\Prime{}"
%format c′↣⋆σ″ = c′ "{\rightarrowtail^\star}" σ″
%format c′↣⋆σ′ = c′ "{\rightarrowtail^\star}" σ′
%format c↣⋆σ″ = c "{\rightarrowtail^\star}" σ″
\begin{code}
unique : ∀ {c σ σ′ σ″} →  ⟨ c ‚ σ ⟩ ↣⋆ ⟨ [] ‚ σ′ ⟩ →
                          ⟨ c ‚ σ ⟩ ↣⋆ ⟨ [] ‚ σ″ ⟩ → σ′ ≡ σ″
unique {[]} ε ε = ≡.refl
unique {[]} ε              (() ◅ c′↣⋆σ″)
unique {[]} (() ◅ c′↣⋆σ′)  c↣⋆σ″
unique {PUSH m ∷ c′} (↣-PUSH ◅ c′↣⋆σ′) (↣-PUSH ◅ c′↣⋆σ″) = unique c′↣⋆σ′ c′↣⋆σ″
unique {ADD ∷ c′} {          []  } (() ◅ c′↣⋆σ′) c↣⋆σ″
unique {ADD ∷ c′} {     m ∷  []  } (() ◅ c′↣⋆σ′) c′↣⋆σ″
unique {ADD ∷ c′} {n ∷  m ∷  σ   } (↣-ADD ◅ c′↣⋆σ′) (↣-ADD ◅ c′↣⋆σ″) = unique c′↣⋆σ′ c′↣⋆σ″
\end{code}

%format machine→big = "\func{machine{\rightarrow}big}"
%format m↣⋆#m = m "{\rightarrowtail^\star}" m
%format m′↣⋆#m = m "\Prime{}{\rightarrowtail^\star}" m
%format a⊕b↣⋆#m = a "{\oplus}" b "{\rightarrowtail^\star}" m
\begin{code}
machine→big : ∀ {e m} → e ↣⋆# m → e ⇓ m
machine→big {# m} m↣⋆#m with m↣⋆#m {[]} {[]}
machine→big {# m} m↣⋆#m | ↣-PUSH ◅ ε = ⇓-ℕ
machine→big {# m} m↣⋆#m | ↣-PUSH ◅ () ◅ m′↣⋆#m
machine→big {a ⊕ b} a⊕b↣⋆#m with exec a | exec b
machine→big {a ⊕ b} a⊕b↣⋆#m | na & a↣⋆#na | nb & b↣⋆#nb
  with unique {σ = []} a⊕b↣⋆#m a⊕b↣⋆#na+nb where
    a⊕b↣⋆#na+nb : a ⊕ b ↣⋆# na + nb
    a⊕b↣⋆#na+nb = a↣⋆#na ◅◅ b↣⋆#nb ◅◅ ↣-ADD ◅ ε
machine→big {a ⊕ b} a⊕b↣⋆#m | na & a↣⋆#na | nb & b↣⋆#nb
  | ≡.refl = ⇓-⊕ (machine→big a↣⋆#na) (machine→big b↣⋆#nb)
\end{code}
%}}}%

%{{{%
%if False
\begin{code}
-- comp : Expression → List Instruction
-- comp (# m) = PUSH m ∷ []
-- comp (a ⊕ b) = comp a ++ comp b ++ ADD ∷ []

-- import Level
-- infix 3 _Comp_
-- data _Comp_ : REL Expression (List Instruction) Level.zero where
--   Comp# : ∀ {m} → # m Comp [ PUSH m ]
--   Comp⊕ : ∀ {a ca b cb} → a Comp ca → b Comp cb → a ⊕ b Comp ca ++ cb ++ [ ADD ]

-- infix 3 _WithCont_CompilesTo_
-- data _WithCont_CompilesTo_ : Expression → List Instruction → List Instruction → Set where
--   Compile# : ∀ {m c} → # m WithCont c CompilesTo PUSH m ∷ c
--   Compile⊕ : ∀ {a b c ⊕B A⊕B} → a WithCont ⊕B CompilesTo A⊕B → b WithCont (ADD ∷ c) CompilesTo ⊕B → a ⊕ b WithCont c CompilesTo A⊕B

-- compile→Compile : ∀ {e c c′} → compile e c ≡ c′ → e WithCont c CompilesTo c′
-- compile→Compile {# m} ≡.refl = Compile#
-- compile→Compile {a ⊕ b} ≡.refl = Compile⊕ (compile→Compile ≡.refl) (compile→Compile ≡.refl)

-- Compile→compile : ∀ {e c c′} → e WithCont c CompilesTo c′ → compile e c ≡ c′
-- Compile→compile Compile# = ≡.refl
-- Compile→compile (Compile⊕ a b) with Compile→compile a | Compile→compile b
-- Compile→compile (Compile⊕ a b) | ≡.refl | ≡.refl = ≡.refl
\end{code}
%endif
%}}}%

%{{{%
%if False
\begin{code}
-- machine→small : ∀ {e m} → ⟨ compile e c , [] ⟩ ↣⋆ ⟨ c , m ∷ [] ⟩ → e ↦⋆# m
-- machine→small {# m} .{m} (↣-PUSH ◅ ε) = ε
-- machine→small {# m} (↣-PUSH ◅ () ◅ _)
-- machine→small {a ⊕ b} (a↣a′ ◅ a′↣⋆m) = {!!}

-- decompile : ∀ {a b c A⊕B} → a ⊕ b WithCont c CompilesTo A⊕B → ∃ λ ⊕B → compile a ⊕B ≡ A⊕B × compile b (ADD ∷ c) ≡ ⊕B
-- decompile (Compile⊕ {⊕B = ⊕B} aWith⊕BCompA⊕B bWithADDComp⊕B) = ⊕B & Compile→compile aWith⊕BCompA⊕B & Compile→compile bWithADDComp⊕B

-- decomp : ∀ e c σ → ∃ λ m → ⟨ compile e c , σ ⟩ ↣⋆ ⟨ c , m ∷ σ ⟩
-- decomp (# m) c σ = m & ↣-PUSH ◅ ε
-- decomp (a ⊕ b) c σ with decomp a (compile b (ADD ∷ c)) σ
-- decomp (a ⊕ b) c σ | m & a↣⋆m with decomp b (ADD ∷ c) (m ∷ σ)
-- decomp (a ⊕ b) c σ | m & a↣⋆m | n & b↣⋆n = m + n & a↣⋆m ◅◅ b↣⋆n ◅◅ ↣-ADD ◅ ε

--   split foo | na & a↣⋆#na | nb & b↣⋆#nb = na & nb & (λ {c} {σ} → a↣⋆#na) & (λ {c} {σ} → b↣⋆#nb) & {!boo moo poo!}
--     where
--     moo = a↣⋆#na {compile b [ ADD ]} {[]} ◅◅ b↣⋆#nb {[ ADD ]} {[ na ]} ◅◅ ↣-ADD ◅ ε
--     poo = a⊕b↣⋆#m {[]} {[]}

-- machine→big {a ⊕ b} {m} a⊕b↣⋆#m with split a⊕b↣⋆#m where
--   split : a ⊕ b ↣⋆# m → ∃ λ na → ∃ λ nb → a ↣⋆# na × b ↣⋆# nb × m ≡ na + nb
--   split foo with decomp a | decomp b
--   split foo | na & a↣⋆#na | nb & b↣⋆#nb = na & nb & (λ {c} {σ} → a↣⋆#na) & (λ {c} {σ} → b↣⋆#nb) & {!boo moo poo!}
--     where
--     moo = a↣⋆#na {compile b [ ADD ]} {[]} ◅◅ b↣⋆#nb {[ ADD ]} {[ na ]} ◅◅ ↣-ADD ◅ ε
--     poo = a⊕b↣⋆#m {[]} {[]}
-- machine→big {a ⊕ b} .{na + nb} a⊕b↣⋆#m | na & nb & a↣⋆#na & b↣⋆#nb & ≡.refl = ⇓-⊕ (machine→big a↣⋆#na) (machine→big b↣⋆#nb)

-- small→machine : ∀ {e m} → e ↦⋆# m → e ↣⋆# m
-- small→machine = big→machine ∘ small→big

-- eval : Expression → ℕ
-- eval = ⟦_⟧

-- exec : List Instruction → List ℕ → List ℕ
-- exec [] σ = σ
-- exec (PUSH m ∷ c) σ = exec c (m ∷ σ)
-- exec (ADD ∷ c) [] = {!unpossible!!}
-- exec (ADD ∷ c) (_ ∷ []) = {!unpossible!!}
-- exec (ADD ∷ c) (n ∷ m ∷ σ) = exec c (m + n ∷ σ)

-- machine→exec : ∀ {c σ σ′} → ⟨ c , σ ⟩ ↣⋆ ⟨ [] , σ′ ⟩ → exec c σ ≡ σ′
-- machine→exec {[]} ε = ≡.refl
-- machine→exec {[]} (() ◅ xs)
-- machine→exec {PUSH m ∷ c} (↣-PUSH ◅ xs) = machine→exec xs
-- machine→exec {ADD ∷ c} (↣-ADD ◅ xs) = machine→exec xs

-- exec→machine : ∀ {c σ σ′} → exec c σ ≡ σ′ → ⟨ c , σ ⟩ ↣⋆ ⟨ [] , σ′ ⟩
-- exec→machine {[]} ≡.refl = ε
-- exec→machine {PUSH _ ∷ c′} exec-c-σ≡σ′ = ↣-PUSH ◅ exec→machine exec-c-σ≡σ′
-- exec→machine {ADD ∷ c′} {[]} exec-c-σ≡σ′ = {!unpossible!!}
-- exec→machine {ADD ∷ c′} {_ ∷ []} exec-c-σ≡σ′ = {!unpossible!!}
-- exec→machine {ADD ∷ c′} {n ∷ m ∷ σ} exec-c-σ≡σ′ = ↣-ADD ◅ exec→machine exec-c-σ≡σ′

-- correctness : ∀ e {c σ} → exec (compile e c) σ ≡ exec c (eval e ∷ σ)
-- correctness (# m) = ≡.refl
-- correctness (a ⊕ b) {c} {σ} =
--   begin
--     exec (compile (a ⊕ b) c) σ
--   ≡⟨ ≡.refl ⟩
--     exec (compile a (compile b (ADD ∷ c))) σ
--   ≡⟨ correctness a ⟩
--     exec (compile b (ADD ∷ c)) (eval a ∷ σ)
--   ≡⟨ correctness b ⟩
--     exec (ADD ∷ c) (eval b ∷ eval a ∷ σ)
--   ≡⟨ ≡.refl ⟩
--     exec c (eval a + eval b ∷ σ)
--   ∎ where open ≡.≡-Reasoning

-- correctness′ : ∀ e {c σ m} → e ⇓ m → exec (compile e c) σ ≡ exec c (m ∷ σ)
-- correctness′ e e⇓m with big→denotation e⇓m
-- correctness′ e e⇓m | ≡.refl = correctness e

-- correctness″ : ∀ e {c σ m} → e ↦⋆# m → exec (compile e c) σ ≡ exec c (m ∷ σ)
-- correctness″ e = correctness′ e ∘ small→big

\end{code}
%endif
%}}}%

%{{{%
%if False
\begin{code}
-- machine≡small : ∀ e {m m′} → e ↣⋆# m → e ↦⋆# m′ → m ≡ m′
-- machine≡small (# m) ∀cσ∶e↣⋆m (() ◅ _)
-- machine≡small (# m) ∀cσ∶e↣⋆m ε with ∀cσ∶e↣⋆m {[]} {[]}
-- machine≡small (# m) ∀cσ∶e↣⋆m ε | ↣-PUSH ◅ ε = ≡.refl
-- machine≡small (# m) ∀cσ∶e↣⋆m ε | ↣-PUSH ◅ () ◅ _
-- machine≡small (a ⊕ b) ∀cσ∶e↣⋆m e↦⋆m′ = {!!}
\end{code}
%endif
%}}}%

%{{{%
%if False
%\begin{code}
-- ∀ {i c σ σ′} → 


import Data.List.Properties as ListProp

-- x≢x∷xs : ∀ {A : Set} {x : A} {xs : List A} → xs ≢ x ∷ xs
-- x≢x∷xs xs≡x∷xs with left-identity-unique [ _ ] xs≡x∷xs
-- x≢x∷xs xs≡x∷xs | ()

x∷xs≢xs : ∀ {A : Set} {x : A} {xs : List A} → x ∷ xs ≢ xs
x∷xs≢xs {xs = []} ()
x∷xs≢xs {xs = x′ ∷ xs′} x∷xs≡xs = x∷xs≢xs (proj₂ (ListProp.∷-injective x∷xs≡xs))

-- foo : ∀ {c σ c′ σ′} → ⟨ c , σ ⟩ ↣ ⟨ c′ , σ′ ⟩ → c′ ≢ c
-- foo ↣-PUSH = x≢x∷xs
-- foo ↣-ADD = x≢x∷xs

open import Data.Empty

-- boo : ∀ {A : Set} {i j k : A} {T : Rel A _} {x : T i j} {xs : Star T j k} →
--   x ◅ xs ≇ xs
-- boo {xs = ε} ()
-- boo {xs = x′ ◅ xs} foo = boo (proj₂ (◅-injective foo))

-- moo : ∀ {A : Set} {i j k : A} {T : Rel A _} {jTk : T j k} {xs : Star T i j} → xs ◅◅ jTk ◅ ε ≇ (_ : ε)
-- moo {xs = ε} ()
-- moo {xs = x ◅ xs} ()

-- moo : ∀ {xs tr} → xs ◅◅ tr ◅ ε ≇ ε
-- moo cow = {!!}

-- bar : ∀ {c σ} → (tr : ⟨ c , σ ⟩ ↣⋆ ⟨ c , σ ⟩) → tr ≡ ε
-- bar ε = ≡.refl
-- bar (x ◅ xs) = {!!}

-- bar ε = inj₁ ≡.refl
-- bar (↣-PUSH ◅ xs) = {!!}
-- bar (↣-ADD ◅ xs) with bar (xs ◅◅ ↣-ADD ◅ ε)
-- bar (↣-ADD ◅ xs) | inj₁ cow = {!!}
-- bar (↣-ADD ◅ xs) | inj₂ cow = inj₂ cow

◅-view : ∀ {A : Set} {T : Rel A _} {i k : A} → i ≢ k → (s : Star T i k) →
  ∃ λ j → Σ (T i j) λ iTj → Σ (Star T j k) λ jT⋆k → s ≡ iTj ◅ jT⋆k
◅-view i≢k ε = ⊥-elim (i≢k ≡.refl)
◅-view i≢k (x ◅ xs) = _ & x & xs & ≡.refl

↣-wf : ∀ {c σ u} → ⟨ c , σ ⟩ ↣ u →
  ∃ λ i → ∃ λ c′ → ∃ λ σ′ →
    c ≡ i ∷ c′ × u ≡ ⟨ c′ , σ′ ⟩
↣-wf ↣-PUSH = PUSH _ & _ & _ & ≡.refl & ≡.refl
↣-wf ↣-ADD = ADD & _ & _ & ≡.refl & ≡.refl

-- infix 3 _>∷_ _>∷⋆_
-- data _>∷_ {A : Set} : List A → List A → Set where
--   +∷ : ∀ {x xs} → x ∷ xs >∷ xs

-- _>∷⋆_ : ∀ {A : Set} → List A → List A → Set
-- _>∷⋆_ = Star _>∷_

-- >∷-injective : ∀ {A} {x y : A} {xs ys} → x ∷ xs >∷ y ∷ ys → xs ≡ y ∷ ys × xs >∷ ys
-- >∷-injective +∷ = ≡.refl & +∷

-- code : Machine → List Instruction
-- code ⟨ c , _ ⟩ = c

-- f : _↣_ =[ code ]⇒ _>∷_
-- f ↣-PUSH = +∷
-- f ↣-ADD = +∷

-- g : _↣⋆_ =[ code ]⇒ _>∷⋆_
-- g = gmap code f

-- cow : ∀ {A} {xs : List A} → xs >∷ xs → ⊥
-- cow {A} {[]} ()
-- cow {xs = x′ ∷ xs} foo = cow (proj₂ (>∷-injective foo))

-- elim : ∀ {A} {c c′ : List A} → c >∷⋆ c′ → c ≡ c′
-- elim ε = ≡.refl
-- elim (x ◅ xs) = {!!}

-- elim foo ε = cow foo
-- elim foo (x ◅ xs) = elim x (xs ◅◅ foo ◅ ε)

⟨,⟩-injective : ∀ {c σ c′ σ′} → ⟨ c , σ ⟩ ≡ ⟨ c′ , σ′ ⟩ → c ≡ c′ × σ ≡ σ′
⟨,⟩-injective ≡.refl = ≡.refl & ≡.refl


-- wat : ∀ {c i σ σ′} → ⟨ c , σ ⟩ ≢ ⟨ i ∷ c , σ′ ⟩
-- wat {[]} ()
-- wat {x ∷ xs} foo with proj₁ (⟨,⟩-injective foo)
-- wat {x ∷ xs} foo | c≡i∷c = x≢x∷xs c≡i∷c

-- -- no : ∀ {c σ c′ σ′} → ⟨ c , σ ⟩ ↣⋆ ⟨ c′ ++ c , σ′ ⟩ → ⊥
-- -- no foo = {!!}

-- absurd : ∀ {c σ i σ′} → ⟨ c , σ ⟩ ↣⋆ ⟨ i ∷ c , σ′ ⟩ → ⊥
-- absurd cow with ◅-view wat cow
-- absurd ._ | u & c↣u & u↣⋆ic & ≡.refl with ↣-wf c↣u
-- absurd ._ | ._ & c↣u & u↣⋆ic & ≡.refl | j & c′ & σ′ & ≡.refl & ≡.refl = {!!}

-- -- ↣⋆→≡ : ∀ {c σ σ″} → ⟨ c , σ ⟩ ↣⋆ ⟨ c , σ″ ⟩ → σ ≡ σ″
-- -- ↣⋆→≡ ε = ≡.refl
-- -- ↣⋆→≡ (↣-PUSH ◅ xs) = proj₂ (∷-injective (↣⋆→≡ (xs ◅◅ ↣-PUSH ◅ ε)))
-- -- ↣⋆→≡ (↣-ADD ◅ xs) = {!xs ◅◅ ↣-ADD ◅ ε!}

-- -- with ↣-wf x
-- -- ↣⋆→≡ (x ◅ xs) | i & c′ & σ′ & ≡.refl & ≡.refl = {!!}

-- -- ⊥-elim (absurd xs)


c↣⋆c→σ≡σ : ∀ {c σ σ′} → ⟨ c , σ ⟩ ↣⋆ ⟨ c , σ′ ⟩ → σ ≡ σ′
c↣⋆c→σ≡σ ε = ≡.refl
c↣⋆c→σ≡σ (x ◅ xs) with ↣-wf x
c↣⋆c→σ≡σ (x ◅ xs) | i & c′ & σ′ & ≡.refl & ≡.refl = {!!}

ys++xs≢xs : ∀ {A : Set} {xs} (ys : List A) → ys ≢ [] → ys ++ xs ≢ xs
ys++xs≢xs ys ¬ys = ¬ys ∘ ListProp.left-identity-unique ys ∘ ≡.sym

∷≢[] : ∀ {A : Set} {x : A} {xs} → x ∷ xs ≢ []
∷≢[] ()

-- x₀₁₂∷xs≢xs [] ()
-- x₀₁₂∷xs≢xs (x ∷ xs) eq = {!!}

recon : ∀ e {m} {c′ σ′} → ⟨ compile e c′ , σ′ ⟩ ↣⋆ ⟨ c′ , m ∷ σ′ ⟩ → e ↣⋆# m
recon (# n) e↣⋆m with ◅-view (ys++xs≢xs [ _ ] ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) e↣⋆m
recon (# n) ._ | ._ & ↣-PUSH & n↣⋆m & ≡.refl with c↣⋆c→σ≡σ n↣⋆m
recon (# n) ._ | ._ & ↣-PUSH & n↣⋆m & ≡.refl | ≡.refl = ↣-PUSH ◅ ε

recon (# m ⊕ # n) m⊕n↣⋆m+n with ◅-view (ys++xs≢xs (_ ∷ _ ∷ _ ∷ []) ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) m⊕n↣⋆m+n
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & foo & ≡.refl with ◅-view (ys++xs≢xs (_ ∷ _ ∷ []) ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) foo
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-PUSH & foo & ≡.refl with ◅-view (ys++xs≢xs (_ ∷ []) ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) foo
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-ADD & foo & ≡.refl with c↣⋆c→σ≡σ foo
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-ADD & foo & ≡.refl | ≡.refl = ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ ε

recon (# m ⊕ (b₀ ⊕ b₁)) cow = {!!}
recon ((a₀ ⊕ a₁) ⊕ b) cow = {!!}

-- -- foo : ∀ {m n e} → # m ⊕ e ↣⋆# m + n → e ↣⋆# n
-- -- foo cow {c} {σ} with cow {[]} {[]}
-- -- foo cow {c} {σ} | ↣-PUSH ◅ xs = {!!}

-- -- decomp-⊕ : ∀ a b m+n → a ⊕ b ↣⋆# m+n → ∃₂ λ m n → a ↣⋆# m × b ↣⋆# n × m + n ≡ m+n
-- -- decomp-⊕ (# m) (# n) m+n a⊕b↣⋆m+n with a⊕b↣⋆m+n {[]} {[]}
-- -- decomp-⊕ (# m) (# n) m+n a⊕b↣⋆m+n | ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ () ◅ _
-- -- decomp-⊕ (# m) (# n) .(m + n) a⊕b↣⋆m+n | ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ ε = m & n & (λ {c} {σ} → ↣-PUSH ◅ ε) & (λ {c} {σ} → ↣-PUSH ◅ ε) & ≡.refl
-- -- decomp-⊕ (# m) (b₀ ⊕ b₁) m+n a⊕b↣⋆m+n with a⊕b↣⋆m+n {[]} {[]}
-- -- decomp-⊕ (# m) (b₀ ⊕ b₁) m+n a⊕b↣⋆m+n | foo with decomp-⊕ b₀ b₁ {!!} {!!}
-- -- decomp-⊕ (# m) (b₀ ⊕ b₁) m+n a⊕b↣⋆m+n | ↣-PUSH ◅ xs | cow = {!!}
-- -- decomp-⊕ (a₀ ⊕ a₁) b m+n a⊕b↣⋆m+n = {!!}

-- -- ⟨ PUSH m ∷ compile (b₀ ⊕ b₁) (ADD ∷ c) , σ ⟩ ↣⋆ ⟨ c , m+n ∷ σ ⟩  →  ⟨ compile (b₀ ⊕ b₁) c , σ ⟩ ↣⋆ ⟨ c , m+n - m ∷ σ ⟩

-- -- decomp : ∀ e c σ → ∃ λ m → ⟨ compile e c , σ ⟩ ↣⋆ ⟨ c , m ∷ σ ⟩
-- -- decomp (# m) c σ = m & ↣-PUSH ◅ ε
-- -- decomp (a ⊕ b) c σ with decomp a (compile b (ADD ∷ c)) σ
-- -- decomp (a ⊕ b) c σ | m & a↣⋆m with decomp b (ADD ∷ c) (m ∷ σ)
-- -- decomp (a ⊕ b) c σ | m & a↣⋆m | n & b↣⋆n = m + n & a↣⋆m ◅◅ b↣⋆n ◅◅ ↣-ADD ◅ ε

machine→small : ∀ e {m} → e ↣⋆# m → e ↦⋆# m
machine→small e ∀cσ∶e↣⋆m with ∀cσ∶e↣⋆m {[]} {[]}
machine→small (# m) ∀cσ∶e↣⋆m | ↣-PUSH ◅ ε = ε
machine→small (# m) ∀cσ∶e↣⋆m | ↣-PUSH ◅ () ◅ _
machine→small (a ⊕ b) ∀cσ:a⊕b↣⋆m | a⊕b↣⋆m = {!!}


-- --   gmap (λ a′ → a′ ⊕ b) ↦-L (machine→small a {!cow!}) ◅◅
-- --   gmap (λ b′ → # _ ⊕ b′) ↦-R (machine→small b {!!}) ◅◅ ↦-ℕ ◅ ε where
-- --   cow : ∀ c σ → {!!}
-- --   cow c σ = ∀cσ:e↣⋆m {compile a (compile b (ADD ∷ c))} {σ}
-- --   cow : ∀ a m → a ↣⋆# m
-- --   cow a m {c} {σ} with decomp a (compile b c) σ
-- --   cow a m {c} {σ} | m′ & a↣⋆m = {!!}

-- -- foo : ∀ {a m b n} → a ⊕ b ↣⋆# m + n → a ↣⋆# m × b ↣⋆# n
-- -- foo abmn = {!!}

-- -- machine→big : ∀ e m → e ↣⋆# m → e ⇓ m
-- -- machine→big (# m′) m ∀cσ∶e↣⋆m with ∀cσ∶e↣⋆m {[]} {[]}
-- -- machine→big (# m′) m ∀cσ∶e↣⋆m | ↣-PUSH ◅ () ◅ _
-- -- machine→big (# m) .m ∀cσ∶e↣⋆m | ↣-PUSH ◅ ε = ⇓-ℕ
-- -- machine→big (a ⊕ b) m ∀cσ∶e↣⋆m = {!!}

-- -- with decomp a (compile ) | decomp b
-- -- machine→small (a ⊕ b) ∀cσ:e↣⋆m | x ◅ xs | foo | bar = {!!}

machine→small : ∀ {e m} → ⟨ compile e [] , [] ⟩ ↣⋆ ⟨ [] , m ∷ [] ⟩ → e ↦⋆# m
machine→small {# m} .{m} (↣-PUSH ◅ ε) = ε
machine→small {# m} (↣-PUSH ◅ () ◅ _)
machine→small {a ⊕ b} (a↣a′ ◅ a′↣⋆m) = {!!}
%\end{code}
%endif
%}}}%


% vim: ft=tex:

