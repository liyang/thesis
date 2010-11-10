%{{{%
%if False
\begin{code}
{-# LANGUAGE CPP #-}
#define NIL []

module Main where

import Prelude
import Control.Arrow
import Control.Applicative
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Test.QuickCheck
import Data.List
import Data.Function

type List = []
\end{code}
%endif
%}}}%

\def\TT#1{\texttt{#1}}
\def\NT#1{\textsf{#1}}
\def\Nat{\mathbb{N}}
\def\Expression{\NT{Expression}}
\def\Add{\oplus}
\def\PUSH{\TT{PUSH}\;}
\def\ADD{\TT{ADD}}
\def\nil{\TT{[]}}
%\def\Instruction{\NT{Instruction}}
%\def\Code{\NT{Code}}
%\def\Stack{\NT{Stack}}
%\def\Machine{\NT{Machine}}
\def\compile{\textit{compile}}

\def\Eval{\Downarrow}
\def\Step{\mapsto}
\def\Exec{\rightarrowtail}

\hyphenation{Qui-ck-Che-ck}

\chapter{Randomised Testing in Haskell}\label{ch:qc+hpc}

%{{{%

During the initial development of a language, it is useful to be able to
check that its behaviour agrees with our intuitive expectations. Formal
proofs require a significant investment of effort, and are not always
straightforward to revise in light of any underlying changes. Using Haskell,
we can implement our semantics as an executable program: its high-level
expressiveness leads to a much narrower semantic gap between the
mathematical definitions and the implementation, giving us much greater
confidence in the fidelity of the latter, in contrast to more traditional
programming languages.

In turn, if we state the expected properties as Boolean functions in
Haskell, these can then be subjected to randomly generated inputs using the
QuickCheck tool~\cite{claessen00-quickcheck}, which displays any
counterexamples found. While successful runs of hundreds and thousands of
such tests do not comprise a formal proof of the corresponding property,
they do however corroborate the existence of one. Additionally, the use of
the Haskell Program Coverage (HPC) toolkit offers confidence in the validity
of these tests by highlighting any unexercised fragments of the
implementation.

%}}}%

\section{Executable Semantics}%{{{%

%format Expression = "\type{Expression}"
%format Val = "\cons{Val}"
%format Add = "(\cons{\oplus})"
%format `Add` = "\mathbin{\cons{\oplus}}"
Let us begin by implementing the syntax of the expression language of the
previous chapter:
\begin{code}
data Expression = Val Integer | Expression `Add` Expression{-"\hide{"-}deriving (Eq, Ord, Show){-"}"-}
\end{code}
The |Expression| algebraic data type defined above has two constructors
|Val| and |Add|, corresponding to numerals and addition.

\subsection{Denotational Semantics}%{{{%

% semantic brackets
\def\sb[#1]{[\![#1]\!]}

The denotational semantics for our language given in the previous chapter
map expressions to its underlying domain of numbers:
\begin{align*}
	\sb[\anonymous] &: \Expression \rightarrow \Nat \\
	\sb[ m ] &= m \eqTag{denote-val} \\
	\sb[ a \Add b ] &= \sb[ a ] + \sb[ b ] \eqTag{denote-plus}
\end{align*}
%format denot = "\func{denot}"
This can be directly implemented as the following |denot| function, mapping
any given |Expression| to an |Integer|:
\begin{code}
denot :: Expression -> Integer
denot (Val m)      = m
denot (a `Add` b)  = denot a + denot b
\end{code}

%}}}%

\subsection{Big-Step Operational Semantics}%{{{%

While denotations can be implemented directly as functions, there is in
general no corresponding notion in Haskell for the transition relations
given for a definition of operational semantics, since transitions need not
necessarily be deterministic. Nevertheless, we can accommodate
non-deterministic transitions by implementing them as set-valued functions,
that return a set of possible reducts for each expression.

%format REL = "\type{REL}"
%format Rel = "\type{Rel}"
Let us first define two type synonyms |REL| and |Rel| corresponding to
heterogeneous and homogeneous relations respectively:
\begin{code}
type REL alpha beta = alpha -> Set beta
type Rel alpha = REL alpha alpha
\end{code}
That is, a heterogeneous relation between |alpha| and |beta| can be realised
as a function from |alpha| to a set of possible |beta|s.

%format joinSet = "\func{join_{Set}}"
For convenience, we also define some auxiliary functions not found in the
Haskell standard library. Firstly |joinSet| flattens nested sets,
\begin{code}
joinSet :: {-"\hide{"-}Ord alpha => {-"}"-}Set (Set alpha) -> Set alpha
joinSet = Set.fold Set.union Set.empty
\end{code}
by folding the binary set union operation |Set.union| over the outer set.
Note that we have typeset $\func{Set.union}$ and $\func{Set.empty}$ as their
usual mathematical notations.

%format productWith = "\func{productWith}"
The |productWith| function computes a generalised Cartesian product of two
sets, combining the elements from each set with the function |f|:
\begin{code}
productWith :: {-"\hide{"-}(Ord alpha, Ord beta, Ord gamma) => {-"}"-}(alpha -> beta -> gamma) -> Set alpha -> Set beta -> Set gamma
productWith f as bs = joinSet ((\ a -> f a `Set.map` bs) `Set.map` as)
\end{code}

\noindent Let us remind ourselves of the big-step $\Eval$ relation given in
the previous chapter:
\begin{gather*}
\inferrule*{ }
	{m \Eval m} \eqTag{big-val} \\[2ex]
\inferrule*{a \Eval m \quad b \Eval n}%
	{a \Add b \Eval m + n} \eqTag{big-plus}
\end{gather*}
%format bigStep = "\func{bigStep}"
Using our previously defined helpers, we can now implement the $\Eval$
relation as the following |bigStep| function, where
$\func{Set.singleton\;m}$ is rendered as |Set.singleton m|:
\begin{code}
bigStep :: REL Expression Integer
bigStep (Val m)      = Set.singleton m
bigStep (a `Add` b)  = productWith (+) (bigStep a) (bigStep b)
\end{code}
The first case corresponds to the \eqName{big-val} rule, with |Val m|
reducing to |m|. The second case of |a `Add` b| recursively computes the
possible reducts for |a| and |b|, then combines the two sets using
|productWith (+)| to obtain the possible values corresponding to |m + n|.

%}}}%

\subsection{Small-Step Operational Semantics}%{{{%

In the previous chapter, we had defined the small-step reduction relation
$\Step$ as follows:
\begin{gather*}
\inferrule*{ }%
	{m \Add n \Step m + n} \eqTag{small-plus} \\[2ex]
\inferrule*{b \Step b'}%
	{m \Add b \Step m \Add b'} \eqTag{small-right} \\[2ex]
\inferrule*{a \Step a'}%
	{a \Add b \Step a' \Add b} \eqTag{small-left}
\end{gather*}
%format smallStep = "\func{smallStep}"
The above rules are implemented as the three cases of the |smallStep|
function below, corresponding to \eqName{small-plus}, \eqName{small-right}
and \eqName{small-left} in that order:
\savecolumns
\begin{code}
smallStep :: Rel Expression
smallStep (Val m  `Add` Val n  )  = Set.singleton (Val (m + n))
smallStep (Val m  `Add` b      )  = (\ b'  -> Val m  `Add` b'  ) `Set.map` smallStep b
smallStep (a      `Add` b      )  = (\ a'  -> a'     `Add` b   ) `Set.map` smallStep a
\end{code}
The three patterns for |smallStep| above are not exhaustive, as we are
missing a case for |Val m|. Since such expressions cannot reduce any
further, we return an empty set to indicate the lack of such transitions:
\restorecolumns
\begin{code}
smallStep (Val m)                 = Set.empty
\end{code}

%format reduceUntil = "\func{reduceUntil}"
%format step = "\func{step}"
%format partition = "\func{partition}"
\noindent In a small-step semantics, the eventual result of a computation is
given by repeated application of the small-step reduction relation to the
initial expression. The following |reduceUntil|---parametrised on the
reduction relation---performs this task:
\def\stepSig{|step :: (Set alpha, Set beta) -> Set beta|}
\def\partitionSig{|partition :: alpha -> (Set alpha, Set beta) -> (Set alpha, Set beta)|}
\begin{code}
reduceUntil :: {-"\hide{"-}(Ord alpha, Ord beta) => {-"}"-}(alpha -> Maybe beta) -> Rel alpha -> REL alpha beta
reduceUntil p reduce init = step (Set.singleton init, Set.empty) where

	{-"\stepSig"-}
	step (running, finished) = case Set.null running of
		True   -> finished
		False  -> step (first (joinSet . Set.map reduce)
			(Set.fold partition (Set.empty, finished) running))

	{-"\partitionSig"-}
	partition e = case p e of
		Nothing  -> first (Set.insert e)
		Just n   -> second (Set.insert n)
\end{code}
The |step| helper takes a pair of |running| and |finished| sets of states,
accumulating those that satisfy |p| into the finished set for the next
iteration with the aid of |partition|, and repeatedly applies |reduce| to
the set of remaining running states until it becomes exhausted.

%format isVal = "\func{isVal}"
Together with the auxiliary |isVal| function,
\begin{code}
isVal :: Expression -> Maybe Integer
isVal (Val n)  = Just n
isVal _        = Nothing
\end{code}
we obtain an executable implementation of $\Step^\star$ as the following
Haskell function:
%format smallStepStar = "\func{smallStepStar}"
\begin{code}
smallStepStar :: REL Expression Integer
smallStepStar = reduceUntil isVal smallStep
\end{code}

%}}}%

\subsection{Virtual Machine}%{{{%

%format Machine = "\type{Machine}"
%format Code = "\type{Code}"
%format Stack = "\type{Stack}"
%format Instruction = "\type{Instruction}"
%format PUSH = "\cons{PUSH}"
%format ADD = "\cons{ADD}"
The virtual machine presented previously is implemented in a similarly
straightforward manner. We begin with a trio of type synonyms defining what
comprises a virtual machine:
\begin{code}
type Machine = (Code, Stack)
type Code = List Instruction
type Stack = List Integer
\end{code}
We make use of Haskell's built-in list type for |Code| and |Stack| rather
than giving our own definitions. Instructions are defined as the following
algebraic data type, with one constructor for each corresponding
instruction:
\begin{code}
data Instruction = PUSH Integer | ADD{-"\hide{"-}deriving (Eq, Ord){-"}"-}
\end{code}

\noindent Intuitively, a |PUSH m| instruction places the number |m| onto the
top of the stack, while the |ADD| instruction replaces the top two numbers
on the stack with their sum:
\def\MS<#1,#2>{\langle #1 ,\; #2 \rangle}
\begin{gather*}
	\MS<\PUSH m :: c , \sigma>
	\Exec
	\MS<c , m :: \sigma>
		\eqTag{vm-push} \\[2ex]
	\MS<\ADD :: c , n :: m :: \sigma>
	\Exec
	\MS<c , m + n :: \sigma>
		\eqTag{vm-add}
\end{gather*}
%format stepVM = "\func{stepVM}"
The \eqName{vm-push} and \eqName{vm-add} rules are directly implemented as
the first two rules of the following |stepVM| function:
\begin{code}
stepVM :: Rel Machine
stepVM (PUSH m  : c  ,          sigma) = Set.singleton ((c, m : sigma))
stepVM (ADD     : c  , n : m :  sigma) = Set.singleton ((c, m + n : sigma))
stepVM (c            ,          sigma) = Set.empty
\end{code}
Since no other transitions are possible for the virtual machine, we return
the empty set in the final catch-all case.

The virtual machine is considered halted when its sequence of instructions
is exhausted, and the stack consists of only a single number corresponding
to the result of the computation:
%format isHalted = "\func{isHalted}"
\begin{code}
isHalted :: Machine -> Maybe Integer
isHalted (NIL, n : NIL)  = Just n
isHalted _               = Nothing
\end{code}

In the same way as small-step semantics, we may make use of our earlier
|reduceUntil| function to repeatedly iterate |stepVM| until the virtual
machine halts:
%format stepVMStar = "\func{stepVMStar}"
\begin{code}
stepVMStar :: REL Machine Integer
stepVMStar = reduceUntil isHalted stepVM
\end{code}

%format compile = "\func{compile}"
Finally, the compiler is more-or-less a direct transliteration of our
previous definition:
\begin{code}
compile :: Expression -> Code -> Code
compile (Val n)      c = PUSH n : c
compile (a `Add` b)  c = compile a (compile b (ADD : c))
\end{code}

%}}}%

%}}}%

\section{Randomised Testing with QuickCheck and HPC}%{{{%

\TODO{slip in `\emph{assert}' a bit more liberally}

%{{{%

QuickCheck is a system for testing properties of Haskell programs with
randomly-generated inputs. Informally, properties are specified as Haskell
functions that return a boolean result. For example, to assert that |(2 * n)
/ 2 == n| holds in virtually all cases for floating-point numbers, we may
interactively invoke the following call to |quickCheck|:
\begin{spec}
hsPrompt quickCheck (\ n -> (2 * n) / 2 == n)
{-"\texttt{+++ OK, passed 100 tests.}"-}
\end{spec}
It is important to highlight the fact that unlike certain model-checking
tools, QuickCheck does not attempt to exhaustively generate all possible
inputs. Thus even given many successful repeated invocations of
|quickCheck|, some rare corner cases may remain unprobed. For example, even
discounting the possibility of \emph{NaN} and \emph{infinity}, the following
expression evaluates to |False| for 32-bit IEEE-754 floating-point numbers,
due to its limited range and finite precision:
%format ThreeE38 = "\ltrl{3e38}"
\begin{spec}
hsPrompt (\ n -> (2 * n) / 2 == n) (ThreeE38 :: Float)
False
\end{spec}

\noindent QuickCheck does not obviate the need for formal proofs. However,
it is nevertheless very helpful while the implementation is still in a state
of flux, allowing us to detect many flaws ahead of committing to more
rigorous and laborious analyses.

%}}}%

\subsection{Generating Arbitrary Expressions}%{{{%

While QuickCheck comes with existing generators for many built-in Haskell
data types, custom generators can also be seamlessly added for new data
types defined in our own programs. This is achieved using Haskell's
\emph{type class} mechanism---a form of ad-hoc polymorphism based on
type-directed dispatch that in essence allows us to overload function names
for more than one type.

The following code defines the generator for an arbitrary expression, by
instantiating the |Arbitrary| type class for |Expression|s:
\def\arbitrarySig{|arbitrary :: Gen Expression|}
\begin{spec}
instance Arbitrary Expression where
	{-"\arbitrarySig"-}
	arbitrary = oneof
		[  Val <$> arbitrary
		,  Add <$> arbitrary <*> arbitrary ]
\end{spec}
The |oneof :: List (Gen alpha) -> Gen alpha| combinator above picks one of
the listed generators with equal probability. In the first case, |Val| is
applied to an |Integer| generated by invoking a different instance of
|arbitrary|, while the latter recursively generate the two sub-expression
arguments to |Add|. We can test this with the following incantation:
\begin{spec}
hsPrompt sample (arbitrary :: Gen Expression)
Val 5 `Add` (Val 8 `Add` Val 4)
Val 1
{-"\ldots"-}
\end{spec}
However, we soon find that this generates some unacceptably large
expressions. Writing $\mathbb{E}[||e(n)||]$ for the \emph{expected size} of
the generated expression, we see why this is the case:
\[
	\mathbb{E}[||e(n)||] = \frac12 + \frac12(\mathbb{E}[||e(n)||] + \mathbb{E}[||e(n)||]) = \infty
\]
To bring the size of the generated expressions under control, we can use the
|sized| combinator as follows, to allow QuickCheck some influence over the
size of the resulting |Expression|:
\savecolumns
\begin{code}
instance Arbitrary Expression where
	{-"\arbitrarySig"-}
	arbitrary = sized (\ n -> frequency
		[  (n + 1,  Val <$> arbitrary)
		,  (n,      Add <$> arbitrary <*> arbitrary) ])
\end{code}
The |frequency| combinator behaves analogously to |oneof|, but chooses each
alternative with a probability proportional to the accompanying weight. That
is, the above definition of |arbitrary| produces a |Val| constructor with
probability $(n + 1) / (2n + 1)$, and an |Add| constructor with probability
$n / (2n + 1)$. Applying the same analysis as above, we expect the generated
expressions to be much more manageable:
\[
	\mathbb{E}[||e(n)||] = \frac{(n + 1) + 2 n \mathbb{E}[||e(n)||]}{2 n + 1} = n + 1
\]

\noindent When QuickCheck finds a counterexample to the proposition in
question, we often find that it is rarely the smallest such case, which
makes it difficult to understand exactly where and how the problem arises.
QuickCheck provides a mechanism to automate the search for smaller
counterexamples, via the |shrink| method of the |Arbitrary| type class:
\restorecolumns
\def\shrinkSig{|shrink :: Expression -> List Expression|}
\begin{code}
	{-"\shrinkSig"-}
	shrink e = case e of
		Val m      -> Val <$> shrinkIntegral m
		a `Add` b  -> [a, b]
\end{code}
QuickCheck expects our definition of |shrink| to return a list of similar
values that are `smaller' in some sense. This is implemented in
a straightforward manner for |Expression|s by simply returning a list of
direct sub-expressions for the |Add| constructor. For values, we use the
built-in |shrinkIntegral| to obtain a list of `smaller' candidates.

%}}}%

\subsection{Semantic Equivalence and Compiler Correctness}%{{{%

While we have already given a formal proof of the equivalence between
denotational, big-step and small-step semantics in the previous chapter, we
shall illustrate how we could have informally asserted our theorems using
QuickCheck with a much smaller investment of effort.

Let us recall theorem \ref{thm:denote-big}, which states that our
denotational and big-step semantics are equivalent:
\[
	\forall e \in \Expression,\ m \in \Nat.\quad
		\sb[e] \equiv m \leftrightarrow e \Eval m
\]
That is, for all expressions whose denotation is $m$, the same expression
also evaluates under our big-step semantics to $m$. Written literally, this
corresponds to the following Haskell predicate,
%if False
\begin{code}
mele :: Ord alpha => Set alpha -> alpha -> Bool
mele = flip Set.member
\end{code}
%endif
%format `mele` = "\mathrel{\func{\ni}}"
%format prop_DenotBig' = "\func{prop\anonymous{}DenotBig\Prime{}}"
\begin{code}
prop_DenotBig' :: Expression -> Integer -> Bool
prop_DenotBig' e m = (denot e == m) == (bigStep e `mele` m)
\end{code}
where |`mele`| is the flipped |Set| membership operator. This can be checked
as follows:
\begin{spec}
hsPrompt quickCheck prop_DenotBig'
{-"\texttt{+++ OK, passed 100 tests.}"-}
\end{spec}
There are some subtleties involved: in the above test, QuickCheck generates
a random |Integer| as well as an |Expression|, and checks that the
implication holds in both directions. However, given the unlikelihood of
some unrelated |m| coinciding with the value of |e| according to either
semantics, both sides of the outer |==| will be |False| a majority of the
time. This is clearly not a fruitful exploration of the test space.

We can write the same test much more efficiently by using only a single
random |Expression|, by rephrasing the property as below:
%format prop_DenotBig = "\func{prop\anonymous{}DenotBig}"
\begin{code}
prop_DenotBig :: Expression -> Bool
prop_DenotBig e = Set.singleton (denot e) == bigStep e
\end{code}
That is to say, |denot e| is the unique value that |e| can evaluate to
under the big-step semantics. When fed to QuickCheck, the response is as we
would expect:
\begin{spec}
hsPrompt quickCheck prop_DenotBig
{-"\texttt{+++ OK, passed 100 tests.}"-}
\end{spec}

Theorem \ref{thm:big-small}---that is, the correspondence between big-step
and small-step semantics---can be approached in the same way:
\[
	\forall e \in \Expression,\ m \in \Nat.\quad
		e \Eval m \leftrightarrow e \Step^\star m
\]
Transliterated as a QuickCheck property, this corresponds to the following
definition:
%format prop_BigSmall' = "\func{prop\anonymous{}BigSmall\Prime}"
\begin{code}
prop_BigSmall' :: Expression -> Integer -> Bool
prop_BigSmall' e m = bigStep e `mele` m == smallStepStar e `mele` m
\end{code}
However, the above is just an instance of what it means for two sets to be
equal. Thus we may elide the |m| argument and just use |Set|'s built-in
notion of equality:
%format prop_BigSmall = "\func{prop\anonymous{}BigSmall}"
\begin{code}
prop_BigSmall :: Expression -> Bool
prop_BigSmall e = bigStep e == smallStepStar e
\end{code}
Again, QuickCheck does not find any counterexamples:
\begin{spec}
hsPrompt quickCheck prop_BigSmall
{-"\texttt{+++ OK, passed 100 tests.}"-}
\end{spec}

\noindent Finally, we revisit our previous statement of compiler
correctness:
\[
	\forall e \in \Expression,\ m \in \Nat.\quad
	e \Eval m
	\quad\leftrightarrow\quad
	\MS<\compile\;e\;\nil, \nil>
		\Exec^\star \MS<\nil, m :: \nil>
\]
Taking into account what we discussed in the previous paragraphs, the above
can be defined as the following property:
%format prop_Correctness = "\func{prop\anonymous{}Correctness}"
\begin{code}
prop_Correctness :: Expression -> Bool
prop_Correctness e = smallStepStar e == stepVMStar (compile e NIL, NIL)
\end{code}
Feeding this to QuickCheck yields no surprises:
\begin{spec}
hsPrompt quickCheck prop_Correctness
{-"\texttt{+++ OK, passed 100 tests.}"-}
\end{spec}

%}}}%

\subsection{Coverage Checking with HPC}\label{sec:testing-hpc}%{{{%

With any testing process, it is important to ensure that all relevant parts
of the program has been exercised during testing. The Haskell Program
Coverage (HPC) toolkit~\cite{gill07-hpc} supports just this kind of
analysis. It instruments every (sub-)expression in the given Haskell source
file to record if it has been evaluated, and accumulates this information to
a \texttt{.tix} file each time the program is executed. Analysis of the
resulting \texttt{.tix} file enables us to quickly identify unevaluated
fragments of code.

%format main = "\func{main}"
Using HPC is a straightforward process, as it is included with all recent
releases of the Glasgow Haskell Compiler. We do however need to turn our
implementation so far into a fully-fledged program, namely by implementing
a |main| function:
\begin{code}
main :: IO ()
main = do
	quickCheck prop_DenotBig
	quickCheck prop_BigSmall
	quickCheck prop_Correctness
\end{code}
%if False
\begin{code}
	quickCheck prop_DenotBig'
	quickCheck prop_BigSmall'
\end{code}
%endif
This \emph{literate Haskell} source file is then compiled with HPC
instrumentation---then executed---as follows:
\begin{verbatim}
$ ghc -fhpc testing.lhs --make
[1 of 1] Compiling Main  ( testing.lhs, testing.o )
Linking testing ...
$ ./testing
+++ OK, passed 100 tests.
+++ OK, passed 100 tests.
+++ OK, passed 100 tests.
\end{verbatim}
Running the \texttt{hpc report} command on the resulting \texttt{testing.tix}
file displays the following report,
\begin{verbatim}
 94% expressions used (181/192)
 82% alternatives used (19/23)
 50% local declarations used (2/4)
 89% top-level declarations used (26/29)
\end{verbatim}
which is not quite the $100$\% coverage we might have expected. To see where,
we may use the \texttt{hpc draft} command to produce a set of missing `ticks',
corresponding to unevaluated expressions in our code. (Alternatively, we could
have visualised the results using the \texttt{hpc markup} command, which
generates a highlighted copy of the source code for our perusal.) The
salient\footnote{The omitted ticks correspond to compiler-generated helper
definitions, and are none of our concern.} ones are listed below:
\begin{verbatim}
module "Main" {
  inside "smallStep"  { tick "Set.empty" on line 201; }
  inside "stepVM"     { tick "Set.empty" on line 295; }
  tick function "shrink" on line 433;
}
\end{verbatim}
The first two missing ticks refer to the use of $\func{Set.empty}$---otherwise
typeset as |Set.empty|---in the cases where |smallStep| and |stepVM| are
invoked on expressions or virtual machine states that cannot reduce any
further, which would imply the existence of a `stuck' state. The third tick
refers to the |shrink| function, which QuickCheck only invokes when it finds
a counterexample for any of the properties under test. Thus incomplete
coverage in these cases is not unexpected.

%}}}%

%}}}%


\section{Conclusion}%{{{%

The combination of QuickCheck for randomised testing and HPC to confirm
complete code coverage was first pioneered in-the-large by the XMonad
project~\cite{stewart07-xmonad}, providing a high level of assurance of
implementation correctness with minimal effort. Leveraging these same tools and
techniques as a means of verifying semantic properties, we have conferred
similar levels of confidence that our implementation satisfies the compiler
correctness property. Given the small semantic gap between our implementation
and the mathematical definitions of the previous chapter, it would be
reasonable to interpret this as evidence towards the correctness of theorem
\ref{thm:compiler-correct} for our expression language.

%\TODO{this is just a demonstration\ldots actual usage of QC+HPC in next
%chapter.}

%}}}%

%\begin{itemize}
%\item executable semantics in Haskell
%\item denotational, operational, VM and also compiler
%\item introduction to QuickCheck (refer to source)
%\item apply to both proofs of previous section
%\item introduction to HPC (again)
%\item apply to proofs above
%\end{itemize}

% vim: ft=tex:

