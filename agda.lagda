\chapter{Machine-Assisted Proofs in Agda}\label{ch:agda}

To give a formal proof of the correctness property posited in the previous
chapter, we may make use of a mechanised proof assistant.
Agda~\cite{norell07-thesis,theagdateam10-wiki} is a dependently-typed
functional programming language based on Martin-L\"{o}f intuitionistic type
theory~\cite{martin-lof80-itt,nordstrom90-program}. Via the Curry-Howard
correspondence---that is, viewing types as propositions and programs as
proofs---it is also used as a proof assistant for constructive mathematics.
In this chapter, we shall provide a gentle introduction to the language, and
demonstrate how we can formalise statements of compiler correctness by means
of machine-checked proofs, culminating in a verified formalisation of the
proofs of chapter \ref{ch:semantics}.

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
should look familiar to readers versed in the latter. As in previous
chapters, we will adopt a colouring convention for ease of readability:
\begin{longtable}{l||l}
Syntactic Class & Examples \\
\hline
Keywords & |data|, |where|, |with|\ldots \\
Types & |ℕ|, |List|, |Set|\ldots \\
Constructors & |zero|, |suc|, |tt|, |[]|\ldots \\
Functions & |id|, |_+_|, |Star.gmap|\ldots
%\\
%Literals & |0|, |1|, |"hello world"|\ldots
\end{longtable}

\noindent Semantically, Agda is distinguished by its foundation on
\emph{dependent types}, and is closely related to systems such as
Epigram~\cite{mcbride08-epigram,mcbride05-epigram-notes} and
Coq~\cite{the-coq-development-team08-website}. Dependent types systems are
so-called because they allow for types to depend on values, in addition to
the usual parametrisation by other types as seen in languages such as
Haskell. This provides us with a much richer vocabulary of discourse for not
only stating the properties of our programs, but also to be able to prove
such properties within the same system. We will begin to explore how this is
facilitated by dependent types from section \ref{sec:agda-curryhoward}
onwards.

%In an informal sense, generalised abstract data types (GADTs)
%in recent implementations of Haskell allow data types to be indexed on their
%argument types, in a similar fashion.

%}}}%

\subsection{Data and Functions}%{{{%

We start our introduction to Agda with some simple data and function
definitions. The language itself does not specify any primitive data types,
and it serves as a good introduction to see how some of these may be defined
in its standard library~\cite{danielsson10-stdlib}. For example, we may
define the Peano numbers as follows:
\begin{code}
    data ℕ : Set where
      zero  : ℕ
      suc   : ℕ → ℕ
\end{code}
This is syntactically similar to Haskell's generalised abstract data type
(GADT) declarations~\cite{peyton-jones04-gadt} with a few minor differences.
Firstly, arbitrary Unicode characters may be used in identifiers, and we do
not use upper and lower case letters to distinguish between values and
constructors\footnote{The implication here is that the processes of syntax
highlighting and type-checking are inextricably linked, and that syntax
colours provides more information for the reader.}. Secondly, we write |:|
to mean \emph{has-type-of}, and write |Set| for the \emph{type of
types}\footnote{Agda in fact has countably infinite levels of |Set|s, with
$|Set : Set₁ : Set₂ : |\ldots$. This stratification prevents the formation
of paradoxes that would lead to inconsistencies in the system.}.
% FIXME: cite Russell?

Thus, the above defines |ℕ| as a new data type inhabiting |Set|, with
a nullary constructor |zero| as the base case and an unary constructor |suc|
as the inductive case. These correspond to two of the Peano axioms that
define the natural numbers: |zero| is a natural number, and every number |n|
has a successor |suc n|.

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
possible, Agda requires us to explicitly prove that the resulting
definitions are total.

%}}}%

\subsection{Programs as Proofs and Types as Predicates}\label{sec:agda-curryhoward}%{{{%

The Curry-Howard correspondence refers to the initial observation by Curry
that types---in the sense familiar to functional programmers---correspond to
axiom-schemes for intuitionistic logic, while Howard later noted that proofs
in formal systems such as natural deduction can be directly interpreted as
terms in a model of computation such as the typed lambda calculus.

%incompleteness theorems ~\cite{godel?}

The intuitionistic approach to logic only relies on constructive methods,
disallowing notions from classical logic such as the law of the excluded
middle ($P \vee \lnot P$) or double-negation elimination ($\lnot \lnot
P \rightarrow P$). For example, intuitionist reject $P \vee \lnot P$ because
there exists a statement $P$ in any sufficiently powerful logic that can
neither be proved nor disproved within the system, by G\"{o}del's
incompleteness theorems. In other words, intuitionism equates the truth of
a statement $P$ with the possibility of constructing a proof object that
satisfies $P$, therefore a proof of $\lnot \lnot P$, refuting the
non-existence of $P$, does not imply $P$ itself.

What does this mean for the proletarian programmer? Under the Curry-Howard
correspondence, the type |A -> B| is interpreted as the logical statement
`\emph{|A| implies |B|}', and vice-versa. Accordingly, a program |p : A ->
B| corresponds to a proof of `\emph{|A| implies |B|}', in that executing |p|
constructs a witness of |B| as output, given a witness of |A| as input. Thus
in a suitable type system, programming is the same as constructing proofs in
a very concrete sense.

In a traditional strongly typed programming language such as Haskell, the
type system exists to segregate values of different types. On the other
hand, distinct values of the same type all look the same to the
type-checker, which means we are unable to form types corresponding to
propositions about particular values. Haskell's GADTs break down this
barrier in a limited sense, by allowing the constructors of a parametric
type to target particular instantiations of the return type. While this
allows us to exploit a Haskell type checker that supports GADTs as
a proof-checker in some very simple cases, it comes at the cost of requiring
`counterfeit type-level copies of data'~\cite{mcbride02-faking}.

%}}}%

\subsection{Dependent Types}\label{sec:agda-dependent}%{{{%

%FIXME: martin-lof-1971
Dependent type systems follow a more principled approach, being founded on
Martin-L\"of intuitionistic type theory~\cite{nordstrom90-program}. These
have been studied over several decades, and the current incarnation of
Agda~\cite{norell07-thesis,theagdateam10-wiki} is one example of such
a system.

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
\emph{indexed} by a natural number. Its two constructor are analogues of the
|zero| and |suc| of |ℕ|. The |fz| constructor takes an argument of type |ℕ|
named |n|, that is referred to in its resultant type of |Fin (suc n)|. The
braces |{| and |}| indicate that |n| is an implicit parameter, which we may
omit at occurrences of |fz|, provided that the value of |n| can be
automatically inferred. We can see how this might be possible in the case of
the |fs| constructor: its explicit argument has type |Fin n|, from which we
may deduce |n|.

The above |Fin| represents a family of types, where each type |Fin n| has
exactly |n| distinct values. This is apparent in the resultant types of the
constructors, for example: neither |fz| and |fs| can inhabit |Fin zero|, as
they both target |Fin (suc n)| for some |n|. The only inhabitant of |Fin
(suc zero)| is |fz|, since |fs| requires an argument of type |Fin zero|,
which would correspond to a proof that |Fin zero| is inhabited.

A routine application of the |Fin| family is in the safe lookup of lists or
vectors, where a static guarantee on the bounds of the given position is
required. The following definition defines the type of vectors, indexed by
their length:
\begin{code}
    data Vec (X : Set) : ℕ → Set where
      []   :                          Vec X zero
      _∷_  : {n : ℕ} → X → Vec X n →  Vec X (suc n)
\end{code}
Unsurprisingly the empty list |[]| corresponds to a |Vec X| of length
|zero|, while the |_∷_| constructor prepends an element of |X| to an
existing |Vec X| of length |n|, to give a |Vec X| of length |suc n|.

%format lookup = "\func{lookup}"
%format n′ = "n\Prime{}"
A |lookup| function can then be defined as follows:
\savecolumns
\begin{code}
    lookup : {X : Set} {n : ℕ} → Fin n → Vec X n → X
    lookup fz      (x ∷ xs) = x
    lookup (fs i)  (x ∷ xs) = lookup i xs
\end{code}
The first argument gives the position in the vector where we wish to extract
an element, with the second argument being the vector itself.

Earlier we mentioned that all definitions in Agda must be total, yet the
|lookup| function seemingly does not consider the case of the empty vector
|[]|. This is because in a dependently-typed language, pattern matching on
one argument can potentially influence the types of other arguments:
matching on either |fz| or |fs i| forces |n| to |suc n′| for some |n′|, and
in both cases the type of the vector is refined to |Vec X (suc n′)|. As |[]|
can only inhabit |Vec X zero|, we needn't explicitly list this case. Had we
pattern matched the vector with |[]| first on the other hand, the type of
the position then becomes |Fin zero|, which is uninhabited. In this case, we
may use the `impossible' pattern |()| for the first argument, to indicate
that the case is unreachable:
\restorecolumns
\begin{code}
    lookup ()      []
\end{code}
In such cases, the right hand side of the definition is simply omitted.

This is only an elementary demonstration of the power of dependent types.
Being able to form any proposition in intuitionistic logic as a type gives
us a powerful vocabulary with which to state and verify the properties of
our programs. Conversely, by interpreting a type as its corresponding
proposition, we have mapped the activity of constructing mathematical proofs
to `just' programming, albeit in a more rigorous fashion than usual.

%}}}%

%2010/04/14: [01:30] <pigworker> They have names. "Martin-Löf equality"
%takes just the set as as the parameter; "Paulin-Mohring equality" takes the
%set and one of the elements as parameter.

\subsection{Equality and its Properties}%{{{%

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
Agda does not provide the kind of Hindley-Milner polymorphism as seen in
Haskell, although we can simply take an additional parameter of the type we
wish to be polymorphic over. In the above definition of equality, the
variable |X| corresponds to the type of the underlying values, which can
often be inferred from the surrounding context. By marking this parameter as
implicit, we effectively achieve the same end result in its usage.

The above definition of |_≡_| is indexed by two explicit parameters of type
|X|. Its sole constructor is |refl|, that inhabits the type |x ≡ x| given an
argument |x : X|. Logically, |refl| corresponds to the axiom of reflexivity
$\forall x.\ x \equiv x$. In cases where the type of the argument---such as
|x| here---can be inferred form the surrounding context, the |∀| keyword
allows us to write the type in a way that better resembles the corresponding
logical notation, for example:
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

Agda includes an interactive user interface for the
Emacs~\cite{stallman10-emacs} operating system that supports incremental
development by the placement of `holes' where arbitrary expressions are
expected. Incomplete programs with holes can be passed to the type checker,
which then informs the user of the expected type. Thus, writing proofs in
Agda typically involves a two-way dialogue between the user and the type
checker.

%format sym = "\func{sym}"
%format x≡y = "x{\equiv}y"
Given the above definition of reflexivity as an axiom, we may go on to prove
that |≡| is also symmetric and transitive. The former is the proposition
that given any |x| and |y|, a proof of |x ≡ y| implies that |y ≡ x|. This is
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
$\shed{\{~\}}$, inside which we may further refine the proof. The expected
type of the hole is displayed, and we can ask the type-checker to enumerate
any local names that are in scope. In this case, the hole is expected to be
of type |y ≡ x|, with the arguments |x y : X| and |x≡y : x ≡ y| in scope.

At this point, we can ask the system to perform case-analysis on |x≡y|.
Being an equality proof, this argument must be the |refl| constructor. But
something magical also happens during the case-split operation:
\begin{spec}
    sym x .x refl = {-"\shed{\{~\}}"-}
\end{spec}
Since |refl| only inhabits the type |x ≡ x|, the type checker concludes that
the first two arguments |x| and |y| must be the same, and rewrites the
second as |.x| to reflect this fact. Whereas pattern matching in Haskell is
an isolated affair, in a dependently typed context it can potentially cause
interactions with other arguments, revealing more information about the them
that can be checked and enforced by the system.

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
    sym' : {X : Set} {x y : X} → x ≡ y → y ≡ x
    sym' refl = refl
\end{code}
We prove transitivity in a similar fashion,
%format trans = "\func{trans}"
\begin{code}
    trans : ∀ {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
    trans refl refl = refl
\end{code}
where pattern-matching the first explicit argument with |refl| unifies |y|
with |x|, refining the type of the second argument to |x ≡ z|; in turn,
matching this with |refl| then unifies |z| with |x|. The resulting goal of
|x ≡ x| is met on the right hand side with simply |refl|.

%}}}%

\subsection{Existentials and Dependent Pairs}%{{{%

In the previous section, we had already surreptitiously modelled the
universal quantifier $\forall$ as dependent functions---that is, functions
where values of earlier arguments may influence later types. Dually, we can
model the existential quantifier $\exists$ using \emph{dependent pairs}.
This is typically defined in terms of the |Σ| type\footnote{In this thesis,
I deviate from the Agda standard library by writing |_∧_| instead of
$\cons{\anonymous{,}\anonymous}$, to avoid excessive visual overloading.}:
\begin{code}
    data Σ (X : Set) (P : X → Set) : Set where
      _∧_ : (x : X) → (p : P x) → Σ X P
\end{code}
We can interpret the type |Σ X (λ x → P x)| as the existentially quantified
statement that $\exists x \in X.\ P(x)$. Correspondingly, a proof of this
comprises a pair |x ∧ p|, where the latter is a proof of the proposition |P
x|. Unlike classical proofs of existence which may not necessarily be
constructive, a proof of the existence of some |x| satisfying |P|
necessarily requires us to supply such an |x|. Conversely, we can always
extract an |x| given such a proof.

As |X| can often be inferred from the type of the predicate |P|, we may
define a shorthand |∃| that accepts |X| as an implicit argument:
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

%format splitAt = "\func{splitAt}"
\noindent Putting the above into practice, we present below a definition of
|splitAt| that splits a vector of length |m + n| at position |m| into left
and right vectors of length |m| and |n| respectively. Unlike the eponymous
Haskell function, we can also witness that the contatenation of the
resulting vectors coincides with the input:
\begin{code}
    splitAt : (m : ℕ) {n : ℕ} {X : Set} (xs : Vec X (m + n)) →
      Σ (Vec A m) λ ys → Σ (Vec A n) λ zs → xs ≡ ys ++ zs
    splitAt zero     xs                 = [] ∧ xs ∧ ≡.refl
\end{code}
For the base case where the position is |zero|, we simply return the empty
list as the left part and the entirety of |xs| as the right. Since |[] ++
xs| reduces to just |xs|, a simple appeal to reflexivity completes this
clause.

In the inductive case of |suc m|, the input vector must contain at least one
element, followed by |xs|. We wish to split |xs| recursively at |m| and
prepend |x| to the left result. In Agda, we can pattern match on
intermediate results using the magic `|with|' keyword, which could be
thought of as the dependently-typed analogue to Haskell's $\keyw{case}$:
\begin{code}
    splitAt (suc m)  (x ∷ xs)           with splitAt m xs
    splitAt (suc m)  (x ∷ .(ys ++ zs))  | ys ∧ zs ∧ ≡.refl = x ∷ ys ∧ zs ∧ ≡.refl
\end{code}
When we case-split on the proof of |xs ≡ ys ++ zs|, Agda sees that |≡.refl|
is the only possible constructor, and correspondingly rewrites the tail of
the input vector to the dotted pattern |.(ys ++ zs)|. This is simply a more
sophisticated instance of what we saw when case-splitting |sym| in the
previous section.

%}}}%

\subsection{Reflexive Transitive Closure}%{{{%

% \cite{McBride/Norell/Jansson}

Before we conclude this brief introduction to Agda, we shall introduce the
\emph{reflexive transitive closure} of McBride, Norell and
Jansson~\cite{mcbride07-star}, which generalises the notion of sequences in
a dependently-typed context. This general construct will prove useful later
when working with sequences of small-step reductions.

We begin by defining binary relations parametrised on their underlying
types:
\begin{code}
    Rel : Set → Set₁
    Rel X = X → X → Set
\end{code}
|Rel| has |Set₁| as its codomain in order to avoid the |Set : Set|
inconsistency. We use the |Rel X| shorthand to denote the type of binary
relations on |X|. In fact, our earlier definition of propositional equality
could equivalently have been written as follows:
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

%format List′ = "\func{List}"
In the degenerate case of a constant relation |(λ _ _ → X) : Rel ⊤| whose
indices provide no extra information, we recover the usual definition of
lists of elements of type |X|:
\begin{code}
    List′ : Set → Set
    List′ X = Star (λ _ _ → X) tt tt
\end{code}
Here |tt| is the unique constructor of the unit type |⊤|, with |ε| and |_◅_|
taking the r\^oles of \emph{nil} and \emph{cons} respectively. For example,
we could write the two-element list of 0 and 1 as follows:
%format two = "\func{two}"
\begin{code}
    two : List′ ℕ
    two = zero ◅ suc zero ◅ ε
\end{code}
As it is a generalisation of lists, |Star| admits many of the usual
list-like functions. For example, while the |_◅◅_| function below provides
a proof of transitivity for |Star R|, it could equally be considered the
generalisation of \emph{append} on lists, as suggested by the structure of
its definition:
\begin{code}
    _◅◅_ :  {I : Set} {R : Rel I} {i j k : I} →
            Star R i j → Star R j k → Star R i k
    ε         ◅◅ ys = ys
    (x ◅ xs)  ◅◅ ys = x ◅ (xs ◅◅ ys)
\end{code}
Similarly, we can define an analogue of \emph{map} on lists:
%format I′ = "I\Prime{}"
%format gmap = "\func{gmap}"
\begin{code}
    gmap :  {I I′ : Set} {R : Rel I} {S : Rel I′} (f : I → I′) →
            (  {x y : I}  →       R x y  →       S (f x)  (f y)) →
               {i j : I}  → Star  R i j  → Star  S (f i)  (f j)
    gmap f g ε         = ε
    gmap f g (x ◅ xs)  = g x ◅ gmap f g xs
\end{code}
As well as a function |g| that is mapped over the individual elements of the
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
%format _≤_ = "\func{\anonymous{\le}\anonymous}"
%format ≤ = "\infix{\func{\le}}"
\begin{code}
    _≤_ : Rel ℕ
    _≤_ = Star _<₁_
\end{code}
Of course, this is just the familiar \emph{less than or equal} relation, for
which we can easily prove some familiar properties, such as the following:
%format z≤n = "\func{0{\le}n}"
\begin{code}
    z≤n : (n : ℕ) → zero ≤ n
    z≤n zero     = ε
    z≤n (suc n)  = z≤n n ◅◅ (lt₁ n ◅ ε)
\end{code}
Note that a proof of |zero ≤ n| as produced by the above |z≤n| function
actually consists of a \emph{sequence} of proofs in the style of ``\emph{0
is succeeded by 1, which is succeeded by 2, \ldots{} which is succeeded by
|n|}'' that can be taken apart and inspected one by one. We will be doing
exactly this when considering reduction sequences in our later proofs.

%}}}%

%}}}%

%{{{%
%if False
\begin{code}
import Level
open import Common
\end{code}
%endif
%}}}%

\section{Agda for Compiler Correctness}%{{{%

In this section, we shall revisit the language of numbers and addition from
chapter~\ref{ch:semantics}, and demonstrate how the previous compiler
correctness result can be formalised using Agda.

\subsection{Syntax and Semantics}%{{{%

As in chapter \ref{ch:model}, we can encode the syntax of our language as
a simple algebraic data type:
%if False
\begin{code}
infix l4 _⊕_
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
The two constructors |#_| and |_⊕_| correspond to the
\eqName{Exp-$\mathbb{N}$} and \eqName{Exp-$\oplus$} rules in our original
definition of the |Expression| language in chapter \ref{ch:semantics}.
%format ⟦_⟧ = "\func{[\![\anonymous]\!]}"
%format ⟦ = "\prefix{\func{[\![}}"
%format ⟧ = "\postfix{\func{]\!]}}"
Its denotational semantics---being a mapping from the syntax to the
underlying domain of $\mathbb{N}$---can be simply implemented as a function:
\begin{code}
⟦_⟧ : Expression → ℕ
⟦ # m ⟧    = m
⟦ a ⊕ b ⟧  = ⟦ a ⟧ + ⟦ b ⟧
\end{code}
The two cases in the definition of |⟦_⟧| correspond to \eqName{denote-val}
and \eqName{denote-plus} respectively. A numeric expression is interpreted
as just its value, while the |⊕| operator translates to the familiar |+| on
natural numbers.

%format _⇓_ = "\type{\anonymous{\Downarrow}\anonymous}"
%format ⇓ = "\infix{\type{{\Downarrow}}}"
%format ⇓-ℕ = "\cons{{\Downarrow}\text-\mathbb{N}}"
%format ⇓-⊕ = "\cons{{\Downarrow}\text-\oplus}"
We had previously modelled the big-step semantics of our language as
a binary relation $\Downarrow$ between expressions and numbers. In Agda,
such a relation can be implemented as a dependent data type, indexed on
|Expression| and |ℕ|:
%if False
\begin{code}
infix 4 _⇓_
\end{code}
%endif
\begin{code}
data _⇓_ : REL Expression ℕ Level.zero where
  ⇓-ℕ  : ∀ {m} → # m ⇓ m
  ⇓-⊕  : ∀ {a b m n} → a ⇓ m → b ⇓ n → a ⊕ b ⇓ m + n
\end{code}
The |⇓-ℕ| constructor corresponds to the \eqName{big-val} rule: an
expression |# m| evaluates to just the value |m|. The |⇓-⊕| constructor
takes two arguments of type |a ⇓ m| and |b ⇓ n|, corresponding to the two
premises of \eqName{big-plus}.

%%{{{%
%%if False
%\begin{code}
%-- ⊕≡e⇒∄m≡e : ∀ {a b e} → a ⊕ b ≡ e → ∄ λ m → # m ≡ e
%-- ⊕≡e⇒∄m≡e ≡.refl (n & ())

%-- step : (e : Expression) → {_ : ∄ λ m → # m ≡ e} → Expression
%-- step (# m) {¬m} = ⊥-elim (¬m (m & ≡.refl))
%-- step (a ⊕ b) with ≡.inspect a
%-- step (a ⊕ b) | (_ ⊕ _) with-≡ ⊕≡a = step a {⊕≡e⇒∄m≡e ⊕≡a} ⊕ b
%-- step (a ⊕ b) | (# m) with-≡ m≡a with ≡.inspect b
%-- step (a ⊕ b) | (# m) with-≡ m≡a | (_ ⊕ _) with-≡ ⊕≡b = a ⊕ step b {⊕≡e⇒∄m≡e ⊕≡b}
%-- step (a ⊕ b) | (# m) with-≡ m≡a | (# n) with-≡ n≡b = # m + n
%\end{code}
%%endif
%%format step = "\func{step}"
%%format a′ = "a\Prime{}"
%%format b′ = "b\Prime{}"
%\begin{code}
%step : (e : Expression) → ℕ ⊎ Expression
%step (# m) = inj₁ m
%step (a ⊕ b)  with step a
%step (a ⊕ b)  | inj₁ m  with step b
%step (a ⊕ b)  | inj₁ m  | inj₁ n   = inj₂ (# (m + n))
%step (a ⊕ b)  | inj₁ m  | inj₂ b′  = inj₂ (a ⊕ b′)
%step (a ⊕ b)  | inj₂ a′ = inj₂ (a′ ⊕ b)
%\end{code}
%%}}}%

%if False
\begin{code}
infix 3 _↦_ _↦⋆_ _↦⋆#_
\end{code}
%endif
The small-step semantics for |Expression|s is implemented in the same
fashion,
%format _↦_ = "\type{\anonymous{\mapsto}\anonymous}"
%format ↦ = "\type{{\mapsto}}"
%format _↦⋆_ = "\func{\anonymous{\mapsto}^\star\anonymous}"
%format ↦⋆ = "\func{{\mapsto}^\star}"
%format _↦⋆#_ = "\func{\anonymous{\mapsto}^\star\;" # "\anonymous}"
%format ↦⋆# = "\func{{\mapsto}^\star}\;" #
%format ↦-ℕ = "\cons{{\mapsto}\text-\mathbb{N}}"
%format ↦-L = "\cons{{\mapsto}\text-L}"
%format ↦-R = "\cons{{\mapsto}\text-R}"
\begin{code}
data _↦_ : Rel Expression Level.zero where
  ↦-ℕ  : ∀ {m n}       →           #  m  ⊕ # n  ↦ # (m + n)
  ↦-L  : ∀ {a a′ b  }  → a ↦ a′ →     a  ⊕ b    ↦    a′  ⊕ b
  ↦-R  : ∀ {m b  b′ }  → b ↦ b′ →  #  m  ⊕ b    ↦ #  m   ⊕ b′
\end{code}
with \eqName{small-val}, \eqName{small-left} and \eqName{small-right}
represented as the |↦-ℕ|, |↦-L| and |↦-R| constructors. Using |Star| defined
earlier in this chapter, we obtain the reflexive transitive closure of
|_↦_|, along with proofs of the usual properties, for free:
\begin{code}
_↦⋆_ : Rel Expression Level.zero
_↦⋆_ = Star _↦_
\end{code}

%if False
\begin{code}
_↦⋆#_ : REL Expression ℕ Level.zero
e ↦⋆# m = e ↦⋆ # m
\end{code}
%endif

%}}}%

\subsection{Semantic Equivalence}%{{{%

%format denote→big = "\func{denote{\rightarrow}big}"
%format big→denote = "\func{big{\rightarrow}denote}"
%format a⇓m = "a{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"

Let us move swiftly on to the semantic equivalence theorems of section
\ref{sec:semantic-equivalence}. Our previous technique of rule induction
essentially boils down to induction on the structure of inductively-defined
data types.

The proof for the forward direction of theorem \ref{thm:denote-big}---which
captures the equivalence of the denotational and big-step semantics---is
implemented as |denote→big|, proceeding by case analysis on its argument |e
: Expression|:
\begin{code}
denote→big : ∀ {e m} → ⟦ e ⟧ ≡ m → e ⇓ m
denote→big {# n}    ≡.refl = ⇓-ℕ
denote→big {a ⊕ b}  ≡.refl = ⇓-⊕ (denote→big ≡.refl) (denote→big ≡.refl)
\end{code}
For the |e ≡ # n| case, matching the proof of |⟦ # n ⟧ ≡ m| with |≡.refl|
convinces the typechecker that |m| and |n| are equal, so |e ⇓ n| is
witnessed by |⇓-ℕ|. Agda considers terms equal up to $\beta$-reduction, so
the |⟦ a ⊕ b ⟧ ≡ m| argument is equivalently a proof of |⟦ a ⟧ + ⟦ b ⟧ ≡ m|,
by the definition of |⟦_⟧|. The goal type of |a ⊕ b ⇓ ⟦ a ⟧ + ⟦ b ⟧| is
therefore met with |⇓-⊕|, whose premises of |a ⇓ ⟦ a ⟧| and |b ⇓ ⟦ b ⟧| are
obtained by recursively invoking |denote→big| with two trivial witnesses to
|⟦ a ⟧ ≡ ⟦ a ⟧| and |⟦ b ⟧ ≡ ⟦ b ⟧|.

The backwards direction of theorem \ref{thm:denote-big} is given by the
following |big→denote|, which uses structural induction on the definition of
|_⇓_|:
\begin{code}
big→denote : ∀ {e m} → e ⇓ m → ⟦ e ⟧ ≡ m
big→denote ⇓-ℕ = ≡.refl
big→denote (⇓-⊕ a⇓m b⇓n) with big→denote a⇓m | big→denote b⇓n
big→denote (⇓-⊕ a⇓m b⇓n) | ≡.refl | ≡.refl = ≡.refl
\end{code}
For the base case of |⇓-ℕ|, it must follow that |e ≡ # m|, so the goal type
after $\beta$-reduction of |⟦_⟧| becomes |m ≡ m|, which is satisfied
trivially. The |⇓-⊕| inductive case brings with it two proofs of |a ⇓ m| and
|b ⇓ n|, which can be used to obtain proofs of |⟦ a ⟧ ≡ m| and |⟦ b ⟧ ≡ n|
via the induction hypothesis. The goal of |⟦ a ⟧ + ⟦ b ⟧ ≡ m + n| after
$\beta$-reduction is then trivially satisfied, thus completing the proof of
theorem \ref{thm:denote-big}.

The |with| keyword provides an analogue of Haskell's
$\keyw{case}\;\ldots\;\keyw{of}$ construct that allows us to pattern match
on intermediate results. Agda requires us to repeat the left hand side of
the function definition when using a |with|-clause, since dependent pattern
matching may affect the other arguments, as noted earlier in this chapter.

We go on to prove theorem \ref{thm:big-small}---the equivalence between the
big-step and small-step semantics---in a similar manner:
%format big→small = "\func{big{\rightarrow}small}"
%format a⇓m = "a{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"
\begin{code}
big→small : ∀ {e m} → e ⇓ m → e ↦⋆# m
big→small ⇓-ℕ = ε
big→small (⇓-⊕ {a} {b} {m} {n} a⇓m b⇓n) =
  Star.gmap (λ a′ →    a′  ⊕ b)   ↦-L (big→small a⇓m) ◅◅
  Star.gmap (λ b′ → #  m   ⊕ b′)  ↦-R (big→small b⇓n) ◅◅
  ↦-ℕ ◅ ε
\end{code}
The goal in the case of |⇓-ℕ| is trivially satisfied by the empty reduction
sequence, since |e ≡ # m|. In the |⇓-⊕| case, recursively invoking
|big→small| with |a⇓m| and |b⇓n| gives reduction sequences for |a ↦⋆# m| and
|b ↦⋆# n| respectively. We can map over the former using |↦-L| over the
witnesses and |λ a′ → a′ ⊕ b| over the indices to obtain the reduction
sequence |a ⊕ b ↦⋆# m ⊕ b|, and likewise for the second to obtain |#
m ⊕ b ↦⋆ # m ⊕ # n|. By appending these two resulting sequences, followed by
a final application of the |↦-ℕ| rule---or equivalently invoking
transitivity---we obtain the desired goal of |a ⊕ b ↦⋆# m + n|.

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
The proof for the reverse direction of \ref{thm:big-small} proceeds by
`folding'\footnote{Unfortunately we cannot use |Star.gfold| from Agda's
standard library, as |_⇓_ : REL Expression ℕ| is not a homogeneous
relation.} lemma \ref{lem:small-sound}---implemented as the |sound| helper
function below---over the |e ↦⋆# m| reduction sequence:
\begin{code}
small→big : ∀ {e m} → e ↦⋆# m → e ⇓ m
small→big ε               = ⇓-ℕ
small→big (e↦e′ ◅ e′↦⋆m)  = sound e↦e′ (small→big e′↦⋆m) where
  sound : ∀ {e e′ m} → e ↦ e′ → e′ ⇓ m → e ⇓ m
  sound ↦-ℕ         ⇓-ℕ               = ⇓-⊕ ⇓-ℕ ⇓-ℕ
  sound (↦-L a↦a′)  (⇓-⊕ a′⇓m  b⇓n)   = ⇓-⊕ (sound a↦a′ a′⇓m) b⇓n
  sound (↦-R b↦b′)  (⇓-⊕ m⇓m   b′⇓n)  = ⇓-⊕ m⇓m (sound b↦b′ b′⇓n)
\end{code}
The |sound| helper performs case analysis on the structure of the |e ↦ e′|
small-step reduction. In the case of |↦-ℕ|, it must be the case that |e
≡ # m ⊕ # n| and |e′ ≡ # m + n| respectively, which in turn forces the |e′
⇓ m| argument to be |⇓-ℕ|. The goal type of |# m ⊕ # n ⇓ m + n| is
accordingly witnessed by |⇓-⊕ ⇓-ℕ ⇓-ℕ|.

For the two remaining |↦-L| and |↦-R| rules, it must necessarily be the case
that |e′ ≡ a′ ⊕ b| or |e′ ≡ # m ⊕ b′| respectively. Thus the |e′ ⇓ m|
argument contains a witness of either |a′ ⇓ m| or |b′ ⇓ n|, which we use to
recursively obtain a proof of |a ⇓ m| or |b ⇓ n|.

%}}}%

\subsection{Stack Machine, Compiler, and Correctness}%{{{%

%if False
\begin{code}
mutual
\end{code}
%endif

In section \ref{sec:stack-machine} we used a stack machine as our low-level
semantics, with the machine modelled as a pair of a list of instructions and
a stack of values. This translates to the following Agda data declaration:
%format Machine = "\type{Machine}"
%format ⟨_‚_⟩ = "\cons{\langle\anonymous{,}\anonymous\rangle}"
%format ⟨ = "\prefix{\cons{\langle}}"
%format ‚ = "\cons{,}"
%format ⟩ = "\postfix{\cons{\rangle}}"
%format σ = "\sigma"
%format σ′ = "\sigma\Prime{}"
%format Instruction = "\type{Instruction}"
%format PUSH = "\cons{PUSH}"
%format ADD = "\cons{ADD}"
\begin{code}
  data Machine : Set where
    ⟨_‚_⟩ : (c : List Instruction) → (σ : List ℕ) → Machine
\end{code}
The |List| type from in Agda's standard library implements the familiar
\emph{nil} and \emph{cons} lists as found in Haskell. In turn, the virtual
machine's instruction set comprises the standard |PUSH| and |ADD| for stack
machines:
\begin{code}
  data Instruction : Set where
    PUSH  : ℕ → Instruction
    ADD   : Instruction
\end{code}

%if False
\begin{code}
infix 3 _↣_
\end{code}
%endif

%format _↣_ = "\type{\anonymous{\rightarrowtail}\anonymous}"
%format ↣ = "\type{{\rightarrowtail}}"
%format _↣⋆_ = "\func{\anonymous{\rightarrowtail}^\star\anonymous}"
%format ↣⋆ = "\func{{\rightarrowtail}^\star}"
%format _↣⋆#_ = "\func{\anonymous{\rightarrowtail}^\star\texttt{\#}\anonymous}"
%format ↣⋆# = "\func{{\rightarrowtail}^\star\texttt{\#}}"
%format ↣-PUSH = "\cons{{\rightarrowtail}\text-PUSH}"
%format ↣-ADD = "\cons{{\rightarrowtail}\text-ADD}"
\noindent The two reduction rules \eqName{vm-push} \eqName{vm-add} for the
virtual machine are realised as the |↣-PUSH| and |↣-ADD| constructors of the
|_↣_| relation:
\begin{code}
data _↣_ : Rel Machine Level.zero where
  ↣-PUSH  : ∀ {m    c σ} → ⟨ PUSH m ∷ c ‚          σ ⟩ ↣ ⟨ c ‚ m      ∷ σ ⟩
  ↣-ADD   : ∀ {m n  c σ} → ⟨ ADD    ∷ c ‚ n ∷ m ∷  σ ⟩ ↣ ⟨ c ‚ m + n  ∷ σ ⟩

_↣⋆_ : Rel Machine Level.zero
_↣⋆_ = Star _↣_
\end{code}
Again, we define |_↣⋆_| as |Star _↣_|, and receive the usual properties of
a reflexive transitive closure absolutely free.

%if False
\begin{code}
infix 3 _↣⋆_ _↣⋆#_
\end{code}
%endif

The compiler is defined identically to that of section \ref{sec:compiler},
%format compile = "\func{compile}"
\begin{code}
compile : Expression → List Instruction → List Instruction
compile (# m)    c = PUSH m ∷ c
compile (a ⊕ b)  c = compile a (compile b (ADD ∷ c))
\end{code}
which compiles a number |# m| to |PUSH m|, and a sum |a ⊕ b| to the
concatenation of code that computes the value of |a| and |b|, followed by an
|ADD| instruction.

The following definition of |_↣⋆#_| provides a convenient synonym for what
it means when we say that executing the compiled code for an expression |e|
computes the result |m|:
\begin{code}
_↣⋆#_ : REL Expression ℕ Level.zero
e ↣⋆# m = ∀ {c σ} → ⟨ compile e c ‚ σ ⟩ ↣⋆ ⟨ c ‚ m ∷ σ ⟩
\end{code}
Note that the above proposition is quantified over any code continuation |c|
and initial stack |σ|, and a proof of compiler correctness (theorem
\ref{thm:compiler-correct}) amounts to functions in both directions between
|e ⇓ m| and |e ↣⋆# m|. In the forward direction---that is, from the
high-level/big-step semantics to the low-level/virtual machine
semantics---this is implemented by induction on the structure of |e ⇓ m|:
%format big→machine = "\func{big{\rightarrow}machine}"
\begin{code}
big→machine : ∀ {e m} → e ⇓ m → e ↣⋆# m
big→machine ⇓-ℕ = ↣-PUSH ◅ ε
big→machine (⇓-⊕ a⇓m b⇓n) =
  big→machine a⇓m ◅◅ big→machine b⇓n ◅◅ ↣-ADD ◅ ε
\end{code}
%format c_a
%format σ_a
%format c_b
%format σ_b
In the case of |⇓-ℕ| we have |e ≡ # m|, and so |↣-PUSH ◅ ε| witnesses the
reduction sequence |∀ {c σ} → ⟨ compile (# m) c ‚ σ ⟩ ↣⋆ ⟨ c ‚ m ∷ σ ⟩|. In
the second case, the recursive terms |big→machine a⇓m| and |big→machine b⇓n|
are of the following types:
\begin{spec}
big→machine a⇓m  : ∀ {c_a  σ_a} →  ⟨ compile a  c_a  ‚ σ_a  ⟩ ↣⋆ ⟨ c_a  ‚ m  ∷ σ_a  ⟩
big→machine b⇓n  : ∀ {c_b  σ_b} →  ⟨ compile b  c_b  ‚ σ_b  ⟩ ↣⋆ ⟨ c_b  ‚ n  ∷ σ_b  ⟩
\end{spec}
The right hand side requires a proof of:
\begin{gather*}
|∀ {c σ} → ⟨ compile (a ⊕ b) c ‚ σ ⟩ ↣⋆ ⟨ c ‚ m + n ∷ σ ⟩|
\end{gather*}
which can be obtained by instantiating |c_a = compile b (ADD ∷ c)|, |c_b
= ADD ∷ c|, |σ_a = σ|, |σ_b = m ∷ σ|, and concatenating the resulting
reduction sequences, followed by a final application of the |↣-ADD| rule. As
these values can be automatically inferred by Agda, we do not need to make
them explicit in the definition of |big→machine|.

%{{{%
%if False
\begin{spec}
small→machine : ∀ {e m} → e ↦⋆# m → e ↣⋆# m
small→machine ε = ↣-PUSH ◅ ε
small→machine (↦-ℕ ◅ ε) = ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ ε
small→machine (↦-ℕ ◅ () ◅ xs)
small→machine (↦-L a↦a′ ◅ a′⊕b↦m) = {!small→machine a′⊕b↦m!}
small→machine (↦-R b↦b′ ◅ na⊕b′↦m) = {!!}
\end{spec}
%endif
%}}}%

The backwards direction of the compiler correctness proof requires us to
compute a witness of |e ⇓ m| from one of |e ↣⋆# m|. We first need to
implement a pair of lemmas, however.
%format exec = "\func{exec}"
%format na = "n_a"
%format nb = "n_b"
%format a↣⋆#na = a "{\rightarrowtail^\star}\texttt{\#}" na
%format b↣⋆#nb = b "{\rightarrowtail^\star}\texttt{\#}" nb
The |exec| lemma simply states that that for any expression |e|, there
exists a number |m| for which executing |compile e| computes |m|:
\begin{code}
exec : ∀ e → ∃ λ m → e ↣⋆# m
exec (# m) = m ∧ λ {c} {σ} → ↣-PUSH ◅ ε
exec (a ⊕ b) with exec a | exec b
exec (a ⊕ b) | na ∧ a↣⋆#na | nb ∧ b↣⋆#nb = na + nb ∧
  λ {c} {σ} → a↣⋆#na ◅◅ b↣⋆#nb ◅◅ ↣-ADD ◅ ε
\end{code}
When |e ≡ # m|, this number clearly has to be |m|, with |↣-PUSH ◅ ε| serving
as the witness. Note that due to Agda's handling of implicit arguments, we
must explicitly generalise over |c| and |σ|. In the |e ≡ a ⊕ b| case, we
simply recurse on the |a| and |b| subexpressions and concatenate the
resulting reduction sequences with an |↣-ADD|.

%format unique = "\func{unique}"
%format σ′ = σ "\Prime{}"
%format σ″ = σ "\PPrime{}"
%format σ₀ = σ "_0"
%format c′ = c "\Prime{}"
%format c′↣⋆σ″ = c′ "{\rightarrowtail^\star}" σ″
%format c′↣⋆σ′ = c′ "{\rightarrowtail^\star}" σ′
%format c↣⋆σ″ = c "{\rightarrowtail^\star}" σ″
The |unique| lemma states that given two reduction sequences from the same
initial state, the resulting stacks must coincide:
\savecolumns
\begin{code}
unique : ∀ {c σ σ′ σ″} →  ⟨ c ‚ σ ⟩ ↣⋆ ⟨ [] ‚ σ′ ⟩ →
                          ⟨ c ‚ σ ⟩ ↣⋆ ⟨ [] ‚ σ″ ⟩ → σ′ ≡ σ″
unique {[]}                         (() ◅ c′↣⋆σ′)  c↣⋆σ″          {-""-}
unique {[]}                         ε              (() ◅ c′↣⋆σ″)  {-""-}
unique {[]}                         ε              ε              = ≡.refl
\end{code}
We proceed by recursion on the code |c|: the first group of cases above deal
with an empty |c|. Both sequences must be |ε|, since there no reduction is
possible from the machine state |⟨ [] ‚ σ ⟩|. In Agda, we identify such
cases with the `\emph{impossible}' pattern---written as |()|---and
accordingly the first two cases do not have a corresponding right hand side.
In the third case, the proof of |σ′ ≡ σ″| is trivial, since matching on the
two |ε| constructors for reflexivity has already unified the |σ|, |σ′| and
|σ″| variables.

The next two cases deal with the |PUSH| and |ADD| instructions. In the first
instance, we obtain the proof of |σ′ ≡ σ″| by recursion on |c′↣⋆σ′| and
|c′↣⋆σ″|, both starting from the machine state |⟨ c′ ‚ m ∷ σ ⟩|:
\restorecolumns
\begin{code}
unique {PUSH m ∷ c′}                (↣-PUSH  ◅ c′↣⋆σ′)
                                    (↣-PUSH  ◅ c′↣⋆σ″)  = unique c′↣⋆σ′ c′↣⋆σ″

unique {ADD ∷ c′} {          []  }  (()      ◅ c′↣⋆σ′)   c↣⋆σ″
unique {ADD ∷ c′} {     m ∷  []  }  (()      ◅ c′↣⋆σ′)   c′↣⋆σ″
unique {ADD ∷ c′} {n ∷  m ∷  σ   }  (↣-ADD   ◅ c′↣⋆σ′)
                                    (↣-ADD   ◅ c′↣⋆σ″)  = unique c′↣⋆σ′ c′↣⋆σ″
\end{code}
The reduction rule for |ADD| requires at least two numbers on top of the
stack, which is ruled out by the first two cases in the latter group. The
final case proceeds by recursion on the remainder of the reduction sequence,
both of which start from the same |⟨ c′ ‚ m + n ∷ σ ⟩| machine state.

%format machine→big = "\func{machine{\rightarrow}big}"
%format n↣⋆#m = "n{\rightarrowtail^\star}\texttt{\#}m"
%format n′↣⋆#m = "n\Prime{}{\rightarrowtail^\star}\texttt{\#}m"
Returning to the second half of our compiler correctness theorem, it remains
for us to show that |e ↣⋆# m| implies |e ⇓ m|. The following definition of
|machine→big| provides the proof, which proceeds by case analysis on the
expression |e|:
\savecolumns
\begin{code}
machine→big : ∀ {e m} → e ↣⋆# m → e ⇓ m
machine→big {# n} n↣⋆#m with n↣⋆#m {[]} {[]}
machine→big {# n} n↣⋆#m | ↣-PUSH ◅ ε = ⇓-ℕ
machine→big {# n} n↣⋆#m | ↣-PUSH ◅ () ◅ n′↣⋆#m
\end{code}
The |n↣⋆#m| argument is in fact a function that takes two implicit
arguments, having the type:
\begin{gather*}
	|∀ {c σ} → ⟨ compile (# n) c ‚ σ ⟩ ↣⋆ ⟨ c ‚ m ∷ σ ⟩|
\end{gather*}
To this we apply an empty code continuation and stack, then pattern match
the resulting reduction sequence against |↣-PUSH ◅ ε|. This unifies |n| and
the implicit argument |m|, allowing |⇓-ℕ| to witness the goal type of |#
m ⇓ m|. The second case handles the case of longer reduction sequences,
which is impossible, since |compile (# n)| outputs only a single |PUSH|
instruction.

For expressions of the form |e ≡ a ⊕ b|, we first use the |exec| helper to
obtain the two reduction sequences |a ↣⋆# na| and |b ↣⋆# nb|, making use of
a |with| clause:
%format a⊕b↣⋆#m = "a{\oplus}b{\rightarrowtail^\star}\texttt{\#}m"
% format a⊕b↣⋆#na+nb = "a{\oplus}b{\rightarrowtail^\star}\texttt{\#}" na "{+}" nb
\restorecolumns
\begin{code}
machine→big {a ⊕ b} a⊕b↣⋆#m with exec a    | exec b
machine→big {a ⊕ b} a⊕b↣⋆#m | na ∧ a↣⋆#na  | nb ∧ b↣⋆#nb
  with unique {σ = []} a⊕b↣⋆#m (a↣⋆#na ◅◅ b↣⋆#nb ◅◅ ↣-ADD ◅ ε)
machine→big {a ⊕ b} a⊕b↣⋆#m | na ∧ a↣⋆#na  | nb ∧ b↣⋆#nb
  | ≡.refl = ⇓-⊕ (machine→big a↣⋆#na) (machine→big b↣⋆#nb)
\end{code}
The concatenation |a↣⋆#na ◅◅ b↣⋆#nb ◅◅ ↣-ADD ◅ ε| produces a reduction
sequence of |a ⊕ b ↣⋆# na + nb|. Using the previously defined |unique|
lemma, we compare this with |a⊕b↣⋆#m| to yield a proof of |na + nb ≡ m|.
Examining this proof using a second |with| clause, the goal becomes |a
⊕ b ⇓ na + nb|. This calls for an instance of |⇓-⊕|, whose two premises of
|a ⇓ na| and |b ⇓ nb| are obtained by recursion.

%}}}%

%}}}%

%if False
\section{Coinductive Proofs and Data}\label{sec:agda-coinduction}%{{{%

* I CAN SEE FOREVER LOL

* Recent versions of Agda provides coinductive data. \cite{danielsson10-productivity}

* productive instead of terminating

* analysis necessarily conservative

* requires corecursive calls to be constructor guarded

\begin{code}
fib : Stream N
fib = 0 ∷ zipWith _+_ (1 ∷ fib)
\end{code}

%}}}%
%endif

\section{Conclusion}%{{{%

In this chapter we have given a tutorial of some basic Agda suitable for our
needs, and have produced a fully machine-verified version of the results of
chapter \ref{ch:semantics} as an example. Finally we concluded with a brief
to using coinductive data types in Agda.

On reflection, formalising such results in Agda has provided a number of
advantages: firstly, it clarifies thinking by forcing us to be very explicit
with regards to numerous low-level details that are often elided in
pen-and-paper proofs. Testing out new hypotheses also becomes easier, using
the type checker to guide proof development; in case of any invalid
assumptions, Agda helps to pinpoint precisely where these occur.

A final benefit of using a mechanised proof system such as Agda is that it
aids the incremental evolution of this work: often we would prove
a simplified form of a theorem to gain some insight. At this point, we may
then change, extend, or generalise some core definitions towards our target.
Strictly-speaking, all the proofs leading up to the final result would need
to be proved again, but in the majority of cases only minor tweaks to the
simplified proofs are required. Agda helps out by pointing out where these
changes need to be made. This process would not be as straightforward using
a script-based theorem prover, or even possible in a pen-and-paper-based
approach.

%}}}%

% ignore me from here on\ldots
%{{{%

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
-- correctness′ e e⇓m with big→denote e⇓m
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

%}}}%

% vim: ft=tex fo-=m fo-=M:

