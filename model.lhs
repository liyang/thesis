%{{{%
\def\Z{\mathbb Z}

%\def\finmap{\hookrightarrow}
%\def\finsert#1#2#3{#1{\left[ #2 \mapsto #3 \right]}}
\def\finsert#1#2#3{#1 \uplus \{ #2 \mapsto #3 \}}
\def\flookup#1#2{#1 \mathbin{?} #2}

\def\expr#1#2{#2\ensuremath{_\mathsf{\scriptscriptstyle#1}}}

\def\starred#1{\red #1^\star}
\def\red#1{\expr{#1}{\mapsto}}
\def\eval#1{\expr{#1}{\Downarrow}}

\def\AddLT{\expr T{AddL}}
\def\AddRT{\expr T{AddR}}
\def\AddZT{\expr T{Add$\Z$}}

\def\AddLP{\expr P{AddL}}
\def\AddRP{\expr P{AddR}}
\def\AddZP{\expr P{Add$\Z$}}

\def\WriteZ{Write$\Z$}

% HaX to fix the spacing in tuples
\def\Hp<#1,#2>{\left\langle#1,\;#2\right\rangle}
\def\Tr<#1,#2,#3>{\left\langle#1,\;#2,\;#3\right\rangle}
\def\Td(#1,#2,#3,#4,#5){(#1,\;#2,\;#3,\;#4,\;#5)}

\def\relcomp{\mathbin{\;;\;}}
%}}}%
%{{{%
%if False
\begin{code}
{-# LANGUAGE CPP, FlexibleInstances #-}
#define NIL []

module Main where

import Prelude hiding (sequence)
import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (ap)
import Data.Foldable
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Traversable
import Test.QuickCheck

type Var = Char
type List = []

mupdate :: Ord alpha => Map alpha beta -> Map alpha beta -> Map alpha beta
mupdate = flip Map.union
\end{code}
%endif
%}}}%
%format `mupdate` = "\mathbin{\func{\uplus}}"

\chapter{A Model of STM}\label{ch:model}

%\begin{itemize}
%\item expand TFP paper
%\item why not full STM Haskell a là Beauty in the Beast?
%\item something that I could be reasonably expected to produce a proof for
%\item also contrast with Wouter's stop-the-world approach in his thesis
%\end{itemize}

In this chapter, we identify a simplified subset of STM Haskell that is
suitable for exploring design and implementation issues, and define
a high-level stop-the-world semantics for this language. We then define
a low-level virtual machine for this language in which transactions are made
explicit, along with a semantics for this machine. Finally, we relate the
two semantics using a compiler correctness theorem, and test the validity of
this theorem using QuickCheck and HPC on an executable implementation this
language.

%In this chapter, we identify a simplified subset of STM Haskell and
%a stop-the-world semantics for this language, suitable for exploring design
%issues. We then specify a low-level virtual machine for this language, in
%which the transactions are executed concurrently. Finally we give a compiler
%correctness statement for the combination. Since the model is implemented as
%a Haskell program, we can test its correctness using QuickCheck and HPC.

%\TODO{this chapter is based on previous paper?}

%\TODO{need to say something about the executable model in the introduction}

\section{A Simple Transactional Language}\label{sec:model-language}%{{{%

% provide a consistent snapshot of the current state of the shared heap

In chapter \S\ref{ch:stm}, we introduced STM Haskell, which provides a small
set of primitives for working with transactional variables,
\begin{spec}
newTVar    ::                alpha ->  STM (TVar alpha)
readTVar   :: TVar alpha ->            STM alpha
writeTVar  :: TVar alpha ->  alpha ->  STM Unit
\end{spec}
along with a primitive for running transactions, and another for explicit
concurrency:
\begin{spec}
atomically  :: STM alpha ->  IO alpha
forkIO      :: IO Unit ->    IO Unit
\end{spec}
The |STM| and |IO| types are both monads (\S\ref{sec:stm-haskell}), so we
may use |>>=| and |return| on both levels for sequencing effectful
computations.

\subsection{Syntax}%{{{%

\def\sub#1{_{\scriptscriptstyle #1}}
%format Var = "\type{Var}"
%format Tran = "\type{Tran}"
%format ValT = "\cons{Val\sub T}"
%format `AddT` = "\mathbin{\cons{\oplus\sub T}}"
%format AddT = "(\cons{\oplus\sub T})"
%format Read = "\cons{Read}"
%format Write = "\cons{Write}"
%format Proc = "\type{Proc}"
%format ValP = "\cons{Val\sub P}"
%format `AddP` = "\mathbin{\cons{\oplus\sub P}}"
%format Atomic = "\cons{Atomic}"
%format Fork = "\cons{Fork}"
As a first step towards a verified implementation of STM, let us consider
a simplified model of the above, to allow us to focus on the key issues. The
language we consider has a two-level syntax---mirroring that of the STM
Haskell primitives---which can be represented as the following |Tran| and
|Proc| data types in Haskell:
\begin{code}
data Tran  = ValT Integer  | Tran `AddT` Tran  | Read Var     | Write Var Tran{-"\hide{"-}deriving (Eq, Ord, Show){-"}"-}
data Proc  = ValP Integer  | Proc `AddP` Proc  | Atomic Tran  | Fork Proc{-"\hide{"-}deriving (Eq, Ord, Show){-"}"-}
\end{code}
The two types correspond to actions in the |STM| and |IO| monads
respectively. The language is intentionally minimal, because issues such as
name binding and performing general-purpose computations are largely
orthogonal to our goal of verifying an implementation of STM. Thus, we
replace the |>>=| and |return| of both monads with the monoid of addition
and integers, as motivated in section \S\ref{sec:semantics-degenerate} of
the previous chapter. In our language, |ValT| and |ValP| correspond to
|return| for the |STM| and |IO| monads, while |`AddT`| and |`AddP`| combine
|Tran| and |Proc| computations in an analogous way to \emph{bind}. By
enforcing left-to-right reduction semantics for |`AddT`| and |`AddP`|, we
nevertheless retain the fundamental idea of using monads to sequence
computations and combine their results.

The remaining constructs emulate the |STM| and |IO| primitives provided by
STM Haskell: |Read| and |Write| correspond to |readTVar| and |writeTVar|,
where |Var| represents a finite collection of transactional variables. Due
to the lack of name binding, we omit an analogue of |newTVar| from our
language, and assume all variables are initialised to zero. |Atomic| runs
a transaction to completion, delivering a value, while |Fork| spawns off its
argument as a concurrent process in the style of |forkIO|.

For simplicity, we do not consider |orElse| or |retry|, as they are not
required to illustrate the basic implementation of a log-based transactional
memory system.

\subsection*{Example}%{{{%

Let us revisit the transactional counter example from section
\ref{sec:stm-intro}:
%format Counter_TVar = "\type{Counter_{TVar}}"
%format increment_TVar = "\func{increment_{TVar}}"
\begin{spec}
type Counter_TVar = TVar Integer

increment_TVar :: Counter_TVar -> STM ()
increment_TVar c = do
	n <- readTVar c
	writeTVar c (n + 1)
\end{spec}
%format increment = "\func{increment}"
%format decrement = "\func{decrement}"
In our STM model, the corresponding |increment| function would be written as
follows:
\begin{code}
increment :: Var -> Tran
increment c = Write c (Read c `AddT` ValT 1)
\end{code}
To increment the same counter twice using concurrent threads, we would
write:
%format incTwice = "\func{incTwice}"
\begin{code}
incTwice :: Var -> Proc
incTwice c = Fork (Atomic (increment c)) `AddP` Fork (Atomic (increment c))
\end{code}

%}}}%

%}}}%

\subsection{Transaction Semantics}%{{{%

We specify the meaning of transactions in this language using a small-step
operational semantics, following the approach of \cite{harris05-composable}.
Formally, we give a reduction relation $\red T$ on pairs $\Hp<h, e>$
consisting of a heap |h :: Heap| and a transaction |e :: Tran|. In this
section we explain each of the rules defining $\red T$, and simultaneously
describe its implementation in order to highlight their similarity.

First, we model the heap as a map from variable names to their
values---initialised to zero---and write $\flookup h v$ to denote the value
of variable $v$ in the heap $h$. This may be implemented in Haskell using
the standard |Map| datatype:
%format Heap = "\type{Heap}"
%format lookup (h) (v) = "\flookup{" h "}{" v "}"
%format ? = "\mathbin{\func{?}}"
\begin{code}
type Heap = Map Var Integer

(?) :: Heap -> Var -> Integer
h ? v = Map.findWithDefault 0 v h
\end{code}

\noindent While the $\red T$ relation cannot be implemented directly, we may
nevertheless model it as a set-valued function where each state reduces to
a \emph{set of possible results}:
%format Rel = "\type{Rel}"
%format REL = "\type{REL}"
%format redT = "\func{reduce_{Tran}}"
\savecolumns
\begin{code}
type REL alpha beta = alpha -> Set beta  -- Heterogeneous binary relations
type Rel alpha = REL alpha alpha         -- Homogeneous binary relations

redT :: Rel (Heap, Tran)
\end{code}

\noindent Reading a variable |v| looks up its value in the heap,
\begin{gather*}
	\Hp<h, |Read v|> \red T \Hp<h, |ValT (lookup h v)|> \eqTag{Read}
\end{gather*}
which is implemented by the following code, where we have written
$\func{Set.singleton}\;x$ as |Set.singleton x| for clarity of presentation:
\restorecolumns
\begin{code}
redT (h, Read v) = Set.singleton (h, ValT (h ? v))
\end{code}

\noindent Writing to a variable is taken care of by two rules:
\eqName{\WriteZ} updates the heap with the new value for a variable in the
same manner as the published semantics of STM
Haskell~\cite{harris05-composable}, while \eqName{WriteT} allows its
argument expression to be repeatedly reduced until it becomes a value,
\begin{gather*}
	\Hp<h, |Write v (ValT n)|> \red T \Hp<\finsert h v n, |ValT n|>
	\eqTag{\WriteZ} \\[1ex]
	\inferrule%
		{\Hp<h, e> \red T \Hp<h', e'>}%
		{\Hp<h, |Write v e|> \red T \Hp<h', |Write v e'|>}
	\eqTag{WriteT}
\end{gather*}
writing $\finsert h v n$ to denote the heap $h$ with the variable $v$
updated to $n$.

We implement these two rules by inspecting the subexpression |e| whose value
we wish to update the heap with. In the the former case, |e| is just a plain
number---corresponding to \eqName{\WriteZ}---and we update the heap with the
new value of |v| accordingly. The latter case implements \eqName{WriteT} by
recursively reducing the subexpression |e|, then reconstructing |Write v e'|
by mapping |second (Write v)| over the resulting set of |(h', e')|:
\restorecolumns
\begin{code}
redT (h, Write v e) = case e of
	ValT n  -> Set.singleton (Map.insert v n h, ValT n)
	_       -> second (Write v) `Set.map` redT (h, e)
\end{code}

\noindent As we replace the act of sequencing computations with addition in our
language, it is therefore important to enforce a sequential evaluation
order. The final group of three rules define reduction for |`AddT`|, and
ensure the left argument is evaluated to completion, before starting on the
right hand side:
\begin{gather*}
	\Hp<h, |ValT m `AddT` ValT n|> \red T \Hp<h, |ValT (m + n)|>
		\eqTag{\AddZT} \\
	\inferrule%
		{\Hp<h, b> \red T \Hp<h', b'>}%
		{\Hp<h, |ValT m `AddT` b|> \red T \Hp<h', |ValT m `AddT` b'|>}
		\eqTag{\AddRT} \\
	\inferrule%
		{\Hp<h, a> \red T \Hp<h', a'>}%
		{\Hp<h, |a `AddT` b|> \red T \Hp<h', |a' `AddT` b|>}
		\eqTag{\AddLT}
\end{gather*}
Our implementation of |`AddT`| mirrors the above rules, as below:
\restorecolumns
\begin{code}
redT (h, a `AddT` b) = case (a, b) of
	(ValT m  , ValT n  ) -> Set.singleton (h, ValT (m + n))
	(ValT m  , _       ) -> second (ValT m      `AddT` {-"{}\!"-}  ) `Set.map` redT (h, b)
	(_       , _       ) -> second ({-"\!{}"-}  `AddT` b           ) `Set.map` redT (h, a)
\end{code}


\noindent To complete the definition of |redT|, we require a further case,
\restorecolumns
\begin{code}
redT (h, ValT m) = Set.empty
\end{code}
where we return the empty set for |ValT m|, as it has no associated
reduction rules.

%format joinSet = "\func{join_{Set}}"
Because $\red T$ only describes a single reduction step, we also need to
implement a helper function to run a given initial expression to completion
for our executable model. Let us first define |joinSet|, which flattens
nested |Set|s:
\begin{code}
joinSet :: {-"\hide{"-}Ord alpha => {-"}"-}Set (Set alpha) -> Set alpha
joinSet = Set.fold Set.union Set.empty
\end{code}
Here, $\func{Set.union}$ and $\func{Set.empty}$ are written as |Set.union|
and |Set.empty| respectively.

%format reduceUntil = "\func{reduceUntil}"
%format step = "\func{step}"
%format partition = "\func{partition}"
\def\stepSig{|step :: (Set alpha, Set beta) -> Set beta|}
\def\partitionSig{|partition :: alpha -> (Set alpha, Set beta) -> (Set alpha, Set beta)|}
The following definition of |reduceUntil|---parameterised over a relation
|reduce|---reduces the given |init| state to completion, according to the
predicate |p|:
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

%format isValT = "\func{isVal_T}"
Finally, given the following |isValT| predicate,
\begin{code}
isValT :: (Heap, Tran) -> Maybe (Heap, Integer)
isValT (h, ValT n  ) = Just (h, n)
isValT (h, _       ) = Nothing
\end{code}
the expression |reduceUntil isValT redT| then corresponds to an
implementation of $\starred T$, which produces a set of |(Heap, Integer)|
pairs from an initial |(Heap, Tran)|.

%}}}%

\subsection{Process Soup Semantics}%{{{%

The reduction relation $\red P$ for processes acts on pairs $\Hp<h, s>$
consisting of a heap |h| as before, and a `soup' |s| of running
processes~\cite{peyton-jones01-awkward}. While the soup itself is to be
regarded as a multi-set, here we use a more concrete representation, namely
a list of |Proc|s.

The reduction rules for process are in general defined by matching on the
first process in the soup. However, we begin by giving the \eqName{Preempt}
rule, which allows the rest of the soup to make progress, giving rise to
non-determinism in the language:
\[
	\inferrule%
		{\Hp<h, s> \red P \Hp<h', s'>}%
		{\Hp<h, p : s> \red P \Hp<h', p : s'>}
	\eqTag{Preempt}
\]

%format redP = "\func{reduce_{P}}"
%format redS = "\func{reduce_{S}}"
\noindent Our implementation of $\red P$ comprise a pair of
mutually-recursive definitions,
\begin{code}
redP  :: Proc ->  Rel (Heap, [Proc])
redS  ::          Rel (Heap, [Proc])
\end{code}
where |redP| performs a single-step reduction of a particular |Proc| in the
context of the given heap and soup, and |redS| corresponds to the general
case. We begin with the definition of |redS|:
\begin{code}
redS (h, NIL    ) = Set.empty
redS (h, p : s  ) = (second (p : {-"{}"-}) `Set.map` redS (h, s))
	`Set.union` redP p (h, s)
\end{code}
That is, when the soup is empty, no reduction is possible, so we return
a empty set.

When the soup is not empty, we can either apply \eqName{Preempt} to reduce
the rest rest of the soup |s|, or reduce only the first process |p| using
|redP|. These two sets of reducts are combined using |Set.union|.

In turn, for the definition of |redP|, it is not possible for values to
reduce any further in our semantics, so we return an empty set when |p| is
a |ValP|.
\savecolumns
\begin{code}
redP (ValP n)      (h, s) = Set.empty
\end{code}

\noindent Executing |Fork p| adds |p| to the process soup, and evaluates to
|ValP 0| (which corresponds to |return ()| in Haskell) as the result of this
action:
\[
	\Hp<h, |Fork p : s|> \red P \Hp<h, |ValP 0 : p : s|>
	\eqTag{Fork}
\]
This is handled by the following case in the definition of |redP|:
\restorecolumns
\begin{code}
redP (Fork p)      (h, s) = Set.singleton (h, ValP 0 : p : s)
\end{code}

\noindent Next, the \eqName{Atomic} rule has a premise which evaluates the
given expression until it reaches a value (where $\starred T$ denotes the
reflexive, transitive closure of $\red T$), and a conclusion which
encapsulates this as a single transition on the process level:
\begin{gather*}
	\inferrule%
		{\Hp<h, e> \starred T \Hp<h', |ValT n|>}%
		{\Hp<h, |Atomic e : s|> \red P \Hp<h', |ValP n : s|>}
	\eqTag{Atomic}
\end{gather*}
In this manner we obtain a \emph{stop-the-world} semantics for atomic
transactions, preventing interference from other concurrently executing
processes. Note that while the use of $\starred T$ may seem odd in
a small-step semantics, it expresses the intended meaning in a clear and
concise way~\cite{harris05-composable}, namely that the transaction
executes as if it were a single atomic step.

Our model of the \eqName{Atomic} rule implements the same stop-the-world
semantics using |reduceUntil| defined in the previous section. The values
resulting from the execution of |t| are then placed back into the soup:
\restorecolumns
\begin{code}
redP (Atomic t)    (h, s) = second (\ n -> ValP n : s)
	`Set.map` reduceUntil isValT redT (h, t)
\end{code}

\noindent Finally, it is straightforward to handle |`AddP`| on the process
level using three rules, in an analogous manner to |`AddT`| on the
transaction level:
\begin{gather*}
	\Hp<h, |ValP m `AddP` ValP n : s|> \red P \Hp<h, |ValP (m + n) : s|>
	\eqTag{\AddZP}
	\\[1ex]
	\inferrule%
		{\Hp<h, |b : s|> \red P \Hp<h', |b' : s'|>}%
		{\Hp<h, |ValP m `AddP` b : s|> \red P \Hp<h', |ValP m `AddP` b' : s'|>}
	\eqTag{\AddRP}
	\\[1ex]
	\inferrule%
		{\Hp<h, |a : s|> \red P \Hp<h', |a' : s'|>}%
		{\Hp<h, |a `AddP` b : s|> \red P \Hp<h', |a' `AddP` b : s'|>}
	\eqTag{\AddLP}
\end{gather*}
The corresponding implementation mirrors that of |`AddT`|, evaluating
expressions in a left-to-right order:
%	(ValP m  `AddP` b)  -> second (\ (b' : s') -> ValP m `AddP` b' : s') `Set.map` redS (h, b : s)
%	(a       `AddP` b)  -> second (\ (a' : s') -> a' `AddP` b : s') `Set.map` redS (h, a : s)
%format mapHead = "\func{mapHead}"
\begin{code}
redP (a `AddP` b)  (h, s) = case (a, b) of
	(ValP m,  ValP n) -> Set.singleton (h, ValP (m + n) : s)
	(ValP m,  b)  -> second (mapHead (ValP m  `AddP`    )) `Set.map` redS (h, b : s)
	(a     ,  b)  -> second (mapHead (        `AddP` b  )) `Set.map` redS (h, a : s)
	where mapHead f (p : s) = f p : s
\end{code}
%format isValP = "\func{isVal_P}"
%format isValS = "\func{isVal_S}"
In a similar way to our earlier definition for |isValT|, we define an
|isValS| predicate to determine when an entire soup has finished reducing.
\begin{code}
isValS :: (Heap, [Proc]) -> Maybe (Heap, [Integer])
isValS (h, s) = case traverse isValP s of
	Nothing   -> Nothing
	Just ns   -> Just (h, ns)
	where
	isValP :: Proc -> Maybe Integer
	isValP (ValP n)  = Just n
	isValP _         = Nothing
\end{code}
This completes our executable model of the high-level semantics: in
particular, the term |reduceUntil isValS redS| then corresponds to an
implementation of $\red P$, which produces a set of |(Heap, [Integer])|
pairs from an initial |(Heap, [Proc])|.

In summary, the above semantics for transactions and processes mirror those
for STM Haskell, but for a simplified language. Moreover, while the original
semantics uses evaluation contexts to identify the point at which transition
rules such as \eqName{\AddZP} can be applied, our language is sufficiently
simple to allow the use of explicit structural rules such as \eqName{\AddLP}
and \eqName{\AddRP}, which for our purposes have the advantage of being
directly implementable.

%}}}%

%}}}%

\section{A Simple Transactional Machine}\label{sec:model-machine}%{{{%

The \eqName{Atomic} rule of the previous section simply states that the
evaluation sequence for a transaction may be seen as a single indivisible
transition with respect to other concurrent processes. However, to better
exploit the available multi-core hardware, an actual implementation of this
rule would have to allow multiple transactions to run concurrently, while
still maintaining the illusion of atomicity. In this section we consider how
this notion of concurrent transactions can be implemented, and present
a compiler and virtual machine for our language.

\subsection{Instruction Set}%{{{%

%format Code = "\type{Code}"
%format Instruction = "\type{Instruction}"
%format PUSH = "\cons{PUSH}"
%format ADD = "\cons{ADD}"
%format READ = "\cons{READ}"
%format WRITE = "\cons{WRITE}"
%format BEGIN = "\cons{BEGIN}"
%format COMMIT = "\cons{COMMIT}"
%format FORK = "\cons{FORK}"
Let us consider compiling expressions into code for execution on a stack
machine, in which |Code| comprises a sequence of |Instruction|s:
\begin{code}
type Code         =  List Instruction
data Instruction  =  PUSH Integer | ADD | READ Var | WRITE Var
                  |  BEGIN | COMMIT | FORK Code{-"\hide{"-}deriving (Eq, Ord){-"}"-}
\end{code}
The |PUSH| instruction leaves its argument on top of the stack, while |ADD|
replaces the top two numbers with their sum. The behaviour of the remaining
instructions is more complex in order to maintain atomicity, but
conceptually, |READ| pushes the value of the named variable onto the stack,
while |WRITE| updates the variable with the topmost value. In turn, |BEGIN|
and |COMMIT| mark the start and finish of a transaction, and |FORK| executes
the given code concurrently.

%}}}%

\subsection{Compiler}%{{{%

%format compileT = "\func{\expr T{compile}}"
%format compileP = "\func{\expr P{compile}}"
We define the |compileT| and |compileP| functions to provide translations
from |Tran| and |Proc| to |Code|, both functions taking an additional |Code|
argument to be appended to the instructions produced by the compilation
process, as in chapter \ref{ch:semantics}. In both cases, integers and
addition are compiled into |PUSH| and |ADD| instructions, while the
remaining language constructs map directly to their analogous machine
instructions. The intention is that executing a compiled transaction or
process always leaves a single result value on top of the stack.
\begin{code}
compileT :: Tran -> Code -> Code
compileT e c = case e of
	ValT i      -> PUSH i : c
	x `AddT` y  -> compileT x (compileT y (ADD : c))
	Read v      -> READ v : c
	Write v e'  -> compileT e' (WRITE v : c)

compileP :: Proc -> Code -> Code
compileP e c = case e of
	ValP i      -> PUSH i : c
	x `AddP` y  -> compileP x (compileP y (ADD : c))
	Atomic e'   -> BEGIN : compileT e' (COMMIT : c)
	Fork x      -> FORK (compileP x NIL) : c
\end{code}
For example, invoking |compileP (incTwice counter) NIL| delivers the
following code:
\begin{spec}
[  FORK [ BEGIN, READ counter, PUSH 1, ADD, WRITE counter, COMMIT ]
,  FORK [ BEGIN, READ counter, PUSH 1, ADD, WRITE counter, COMMIT ]
,  ADD ]
\end{spec}

%}}}%

\subsection{Implementing Transactions}%{{{%

The simplest method of implementing transactions would be to suspend
execution of all other concurrent processes on encountering a |BEGIN|, and
carry on with the current process until we reach the following |COMMIT|. In
essence, this is the approach used in the high-level semantics presented in
the previous section. Unfortunately, this does not allow transactions to
execute concurrently, one of the key aspects of transactional memory. This
section introduces the log-based approach to implementing transactions, and
discusses a number of design issues.


\subsubsection*{Transaction Logs}

In order to allow transactions to execute concurrently, we utilise the
notion of a \emph{transaction log}. Informally such a log behaves as a cache
for read and write operations on transactional variables. Only the first
read from any given variable accesses the heap, and only the last value
written can potentially modify the heap; all intermediate reads and writes
operate solely on the log. Upon reaching the end of the transaction, and
provided that that no other concurrent process has `interfered' with the
current transaction, the modified variables in the log can then be committed
to the heap. Otherwise, the log is discarded and the transaction is
restarted afresh.

Note that restarting a transaction relies on the fact that it executes in
complete isolation, in the sense that all its side-effects are encapsulated
within the log, and hence can be revoked by simply discarding the log. For
example, it would not be appropriate to `launch
missiles'~\cite{harris05-composable} during a transaction.


\subsubsection{Interference}

But what constitutes \emph{interference}? When a transaction succeeds and
commits its log to the heap, all of its side-effects are then made visible
in a single atomic step, as if it had been executed in its entirety at that
point with a stop-the-world semantics. Thus when a variable is read for the
first time and its value logged, the transaction is essentially
making the following bet: at the end of the transaction, the value of the
variable in the heap will still be the same as that in the log.

In this manner, interference arises when any such bet fails, as the result
of other concurrent processes changing the heap in a way that invalidates
the assumptions about the values of variables made in the log. In this case,
the transaction fails and is restarted. Conversely, the transaction succeeds
if the logged values of all the variables read are `equal' to their values
in the heap at the end of the transaction.


\subsubsection{Equality}\label{sec:model-equality}

But what constitutes \emph{equality}? To see why this is an important
question, and what the design choices are, let us return to our earlier
example of a transaction that increments a given counter.
%\nopagebreak
%\begin{spec}
%[BEGIN, READ account, PUSH 10, ADD, WRITE account, COMMIT]
%\end{spec}
Consider the following timeline:
{\footnotesize
\begin{longtable}{@@{}l@@{\hspace{1ex}}llclclclc}
\hspace{10ex}% shift boxes right a bit, towards the centre
& \multicolumn{8}{l}{|increment|} \\
\cline{2-9}
1 & \multicolumn{1}{||l||}{|BEGIN|} & \multicolumn{1}{l||}{|READ counter|}
	& \multicolumn{5}{c}{\ldots} & \multicolumn{1}{||l||}{|COMMIT|} & \\
\cline{2-9}
&&&& \rule{0pt}{3ex}|increment| \\
\cline{5-5}
2 &&&& \multicolumn{1}{||c||}{\ldots} \\
\cline{5-5}
&&&&&& \rule{0pt}{3ex}|decrement| & \\
\cline{7-7}
3 &&&&&& \multicolumn{1}{||c||}{\ldots} \\
\cline{7-7}
\multicolumn{10}{@@{}c@@{}}{\rule[0.5ex]{\textwidth}{0.5pt}\makebox[1pt][r]{$\rightarrow$}}\\
% \hline
\multicolumn{10}{c}{Time}
\end{longtable}}\vspace{-1ex}%
\noindent Suppose the |counter| starts at zero, which is read by the first
transaction and logged. Prior to its final |COMMIT|, a second concurrent
transaction successfully increments the |counter|, which is subsequently
decremented by a third transaction. When the first finally attempts to
commit, the count is back to zero as originally logged, even though it has
changed in the interim. Is this acceptable? That is, are the two zeros
`equal'? We can consider a hierarchy of notions of equality, in increasing
order of permissiveness:
\begin{itemize}

\item The most conservative choice is to increment a global counter every
time the heap is updated. Under this scheme, a transaction fails if the heap
is modified at any point during its execution, reflected by a change in the
counter, even if this does not actually interfere with the transaction
itself.

\item A more refined approach is provided by the notion of \emph{version
equality}, where a separate counter is associated with each variable, and is
incremented each time the variable is updated. In this case, our example
transaction would still fail to commit, since the two zeros would be have
different version numbers, and hence considered different.

\item For a pure language such as Haskell, in which values are represented
as pointers to immutable structures, \emph{pointer equality} can be used as
an efficient but weaker form of version equality. In this case, whether the
two zeros are considered equal or not depends on whether the implementation
created a new instance of zero, or reused the old zero by sharing.

\item We can also consider \emph{value equality}, in which two values are
considered the same if they have the same representation. In this case, the
two zeros are equal and the transaction succeeds.

\item The most permissive choice would be a \emph{user-defined equality},
beyond that built-in to the programming language itself, in order to handle
abstract data structures in which a single value may have several
representations, e.g.~sets encoded as lists. Haskell provides this
capability via the |Eq| typeclass.

\end{itemize}
Which of the above is the appropriate notion of equality when committing
transactions? Recall that under a stop-the-world semantics, a transaction
can be considered to be executed in its entirely at the point when it
successfully commits, and any prior reads are effectively bets on the state
of the heap at the commit point. Any intermediate writes that may have been
committed by other transactions do not matter, as long as the final heap is
consistent with the bets made in the log. Hence in our instance, there is no
need at commit time to distinguish between the two zeroes in our example, as
they are equal in the high-level expression language.

From a semantics point of view, therefore, value or user-defined equality
are the best choices. Practical implementations may wish to adopt a more
efficient notion of equality (e.g.~STM Haskell utilises pointer equality),
but for the purposes of this thesis, we will use value equality.

%}}}%

\subsection{Virtual Machine}%{{{%

%format Thread = "\type{Thread}"
%format Stack = "\type{Stack}"
%format Log = "\type{Log}"
The state of the virtual machine is given by a pair $\Hp<h, s>$, comprising
a heap $h$ mapping variables to integers, and a soup $s$ of concurrent
\emph{threads}. A |Thread| is represented as a tuple of the form |(c, sigma,
f, r, w)|, where |c| is the code to be executed, |sigma| is the thread-local
stack, |f| gives the code to be rerun if a transaction fails to commit, and
finally, |r| and |w| are two logs (partial maps from variables to integers)
acting as read and write caches between a transaction and the heap.
\begin{code}
type Thread  =  (Code, Stack, Code, Log, Log)
type Stack   =  [Integer]
type Log     =  Map Var Integer
\end{code}

\noindent We specify the behaviour of the machine using a transition
relation $\red M$ between machine states, defined via a collection of
transition rules that proceed by case analysis on the first thread in the
soup. As with the previous semantics, we begin by defining
a \eqName{PREEMPT} rule to allow the rest of the soup to make progress,
giving rise to non-determinism in the machine:
\[
	\inferrule%
		{\Hp<h, s> \red M \Hp<h', s'>}%
		{\Hp<h, |t : s|> \red M \Hp<h', |t : s'|>}
	\eqTag{PREEMPT}
\]
This rule corresponds to an idealised scheduler that permits context
switching at every instruction, as our focus is on the implementation of
transactions rather than scheduling policies. We return to this issue when
we consider the correctness of our compiler later on in this chapter.

%format stepM = "\func{step_M}"
%format stepT = "\func{step_T}"
We implement $\red M$ using a pair of mutually recursive functions |stepM|
and |stepT| in a similar fashion to that of $\red P$ earlier. The former
implements reduction between arbitrary soups of threads:
\begin{code}
stepM :: Rel (Heap, [Thread])
stepM (h, NIL    ) = Set.empty
stepM (h, t : s  ) = (second (t : {-"{}"-}) `Set.map` stepM (h, s)) `Set.union` stepT t (h, s)
\end{code}
The first case handles empty soups, returning an empty set of resulting
states. The second case takes the first thread |t| in the soup, and
implements the \eqName{PREEMPT} rule by reducing the rest of the soup |s|
before placing |t| back at the head. These are then combined with the states
resulting from a single step of |t|, implemeted by |stepT|:
%format sigma'
%format sigma_1 = sigma "_1"
%format sigma_2 = sigma "_2"
%format stepI = "\func{step_I}"
\savecolumns
\begin{code}
stepT :: Thread -> Rel (Heap, [Thread])
stepT (NIL  ,  sigma, f, r, w) (h, s) = Set.empty
stepT (i : c,  sigma, f, r, w) (h, s) = stepI i where
	~(n : sigma_1@ ~(m : sigma_2)) = sigma
	stepI :: Instruction -> Set (Heap, [Thread])
	{-"\ldots\textit{ defined below}"-}
\end{code}
A thread with an empty list of instructions cannot make any transitions, so
we return an empty set. When there is at least one instruction remaining, we
use the |stepI| helper function to handle each particular instruction. The
above code also brings into scope the names |c|, |sigma|, |f|, |r| and |w|
as detailed previously, as well as |sigma_1| and |sigma_2| for the current
stack with one or two values popped.

Let us detail the semantics of each instruction in turn. Firstly, executing
|FORK| adds a new thread |t| to the soup, comprising the given code |c'|
with an initially empty stack, restart code and read and write logs:
\begin{align*}
	&
		\Hp<h, \Td(|FORK c' : c|,     |sigma|, f, r, w) : s> \red M
		\Hp<h, \Td(          |c|, 0 |: sigma|, f, r, w) : t : s>
	\eqTag{FORK} \\[1ex]
	&	\text{where }t = \Td(c', |NIL|, |NIL|, \emptyset, \emptyset)
\end{align*}
The above transition may be implemented directly, as follows:
\restorecolumns
%format cc = c'
\begin{code}
	stepI (FORK cc)  = Set.singleton (h,   (c,      0  :  sigma,    f,        r,          w) : t      : s)
		where t = (cc, NIL, NIL, Map.empty, Map.empty)
\end{code}

\noindent The |PUSH| instruction places its argument |n| on top of the
stack, while |ADD| takes the top two integer from the stack and replaces
them with their sum:
\begin{align*}
	\langle|h, (PUSH n, c, sigma, f, r, w) : s|\rangle &\red M \langle|h, (c, n : sigma, f, r, w)  : s|\rangle
	\eqTag{PUSH} \\
	\langle|h, (ADD, c, n : m : sigma, f, r, w) : s|\rangle &\red M \langle|h, (c, m |+| n : sigma, f, r, w)  : s|\rangle
	\eqTag{ADD}
\end{align*}
%\[
%	\begin{array}{l@@{$\,:\,$}l@@{\:}r@@{\;}c@@{\;}l@@{\,}r}
%	%	 11111111111 | 22 | 3333333333333333333333333  | 44444 |  5555555 | 666666666666666666666666666
%		\langle|h, (PUSH n|&|c,|&|        sigma, f, r, w) : s|\rangle & \red M & \langle|h, (c,|&|     n : sigma, f, r, w)  : s|\rangle
%		\eqTag{PUSH} \\[1ex]
%		\langle|h, (ADD   |&|c,|&|n : m : sigma, f, r, w) : s|\rangle & \red M & \langle|h, (c,|&| m + n : sigma, f, r, w)  : s|\rangle
%		\eqTag{ADD}
%	\end{array}
%% HaX: My eyes. They bleed.
%	%\eqTag{\parbox{8ex}{\makebox[8ex][r]{PUSH}\\\makebox[8ex][r]{ADD}}}
%\]
The corresponding cases in the definition of |stepI| are almost identical:
\restorecolumns
\begin{code}
	stepI (PUSH n)   = Set.singleton (h,   (c,      n  :  sigma,    f,        r,          w)          : s)
	stepI ADD        = Set.singleton (h,   (c, m +  n  :  sigma_2,  f,        r,          w)          : s)
\end{code}

\noindent Executing |BEGIN| starts a transaction, which involves clearing
the read and write logs, while making a note of the code to be executed if
the transaction fails:
\[
	\Hp<h, \Td(|BEGIN : c|, \sigma,          |f|,       |r|,       |w|) : s> \red M
	\Hp<h, \Td(        |c|, \sigma,  |BEGIN : c|, \emptyset, \emptyset) : s> \\
	\eqTag{BEGIN}
\]
Accordingly, |stepI| sets up the retry code and initialises both read and
write logs:
\restorecolumns
\begin{code}
	stepI BEGIN      = Set.singleton (h,   (c,            sigma, BEGIN : c,   Map.empty,  Map.empty)  : s)
\end{code}

\noindent Next, |READ| places the appropriate value for the variable |v| on
top of the stack. The instruction first consults the write log. If the
variable has not been written to, the read log is then consulted. Otherwise,
if the variable has not been read from either, its value is looked up from
the heap and the read log updated accordingly:
\begin{align*}
	&
	\Hp<h, \Td(|READ v : c|,     \sigma, f, r,  w) : s> \red M
	\Hp<h, \Td(         |c|, n : \sigma, f, r', w) : s>
	\eqTag{READ} \\
	&\text{where }\Hp<n, r'> = \begin{cases}
		\Hp<w(v), r> & \text{if }v \in \text{dom}(w) \\
		\Hp<r(v), r> & \text{if }v \in \text{dom}(r) \\
		\Hp<h(v), \finsert r v {\flookup h v}> & \text{otherwise}
	\end{cases}
\end{align*}
The transliteration of the \eqName{READ} rule to our implementation is as
follows:
\restorecolumns
\begin{code}
	stepI (READ v)   = Set.singleton (h,   (c,      n  :  sigma,    f,        r',         w)          : s)
		where (n, r') = case (Map.lookup v w, Map.lookup v r, h ? v) of
			(Just n',  _,        _   ) -> (n', r)
			(Nothing,  Just n',  _   ) -> (n', r)
			(Nothing,  Nothing,  n'  ) -> (n', Map.insert v n' r)
\end{code}

\noindent In turn, |WRITE| simply updates the write log for the variable |v|
with the value on the top of the stack, without changing the heap or the
stack:
\begin{align*}
	&
	\Hp<h, \Td(|WRITE v : c|, |n : sigma|, f, r, w ) : s> \red M
	\Hp<h, \Td(          |c|, |n : sigma|, f, r, w') : s>
	\eqTag{WRITE} \\
	&\text{where }w' = \finsert w v n
\end{align*}
The \eqName{WRITE} rule has a similarly straightforward implementation:
\restorecolumns
\begin{code}
	stepI (WRITE v)  = Set.singleton (h,   (c,      n :  sigma_1,   f,        r,          w')         : s) where
		w' = Map.insert v n w
\end{code}

\noindent Finally, |COMMIT| checks the read log |r| for consistency with the
current heap |h|, namely that the logged value for each variable read is
equal to its value in the heap. According to the above definitions of
\eqName{READ} and \eqName{WRITE}, variables written to before being read
from during the same transaction will not result in a read log entry, since
the corresponding value in the global heap cannot influence the results of
the transaction. Therefore, we do not need to perform consistency checks for
variables that occur only in the write log.

Using our representation of logs and heaps, the consistency condition can be
concisely stated as $r \subseteq h$. That is, if they are consistent, then
the transaction has succeeded, so we may commit its write log $w$ to the
heap. This update is expressed in terms of the overriding operator on maps
as $h \uplus w$. Otherwise the transaction has failed, in which case the
heap is not changed, the result on the top of the stack is discarded, and
the transaction is restarted at |f|:
\begin{align*}
	&\Hp<h,  \Td(|COMMIT  : c|,  |n : sigma|,  f, r, w) : s> \red M
		\Hp<h', \Td(          |c'|,     |sigma'|, f, r, w) : s> \\
	&\text{where }\Tr<h', c', \sigma'> = \begin{cases}
		\Tr<h \uplus w, c, n : \sigma>
			&\text{if }r \subseteq h \\
		\Tr<h, f, \sigma>
			&\text{otherwise}
	\end{cases}
	\eqTag{COMMIT}
\end{align*}
There is no need to explicitly clear the logs in the above rule, since this
is already taken care of by the fact that the first instruction of |f| is
always a |BEGIN|.
\restorecolumns
\begin{code}
	stepI COMMIT     = Set.singleton (h',  (c',          sigma',    f,        r,          w)          : s)
		where (h', c', sigma') = case (r `Map.intersection` h) `Map.isSubmapOf` h of
			True   -> (h `mupdate` w,  c, n :   sigma_1)
			False  -> (h,              f,       sigma)
\end{code}

%format haltedT = "\func{halted_T}"
%format haltedM = "\func{halted_M}"
\noindent Finally we define a |haltedM| function on virtual machines to
discriminate between completed and running threads.
\begin{code}
haltedM :: (Heap, [Thread]) -> Maybe (Heap, [Integer])
haltedM (h, s) = case traverse haltedT s of
	Just ns -> Just (h, ns)
	Nothing -> Nothing
	where
	haltedT :: Thread -> Maybe Integer
	haltedT (NIL, n : NIL, _, _, _)  = Just n
	haltedT _                      = Nothing
\end{code}

%}}}%

%}}}%

% 2 pages / 1 page
\section{Correctness of the Implementation}%{{{%

As we have seen, the high-level semantics of atomicity is both clear and
concise, comprising a single inference rule \eqName{Atomic} that wraps up
a complete evaluation sequence as a single transition. On the other hand,
the low-level implementation of atomicity using transactions is rather more
complex and subtle, involving the management of read and write logs, and
careful consideration of the conditions that are necessary in order for
a transaction to commit. How can we be sure that these two different views
of atomicity are consistent? Our approach to establishing the correctness of
the low-level implementation is to formally relate it to the high-level
semantics via a compiler correctness theorem.


\subsection{Statement of Correctness}\label{sec:model-correctness}%{{{%

In order to formulate our correctness result, we utilise a number of
auxiliary definitions. First of all, because our semantics is
non-deterministic, we define a relation $\eval P$ that encapsulates the idea
of completely evaluating a process using our high-level semantics:
\[
	\Hp<h, ps> \eval P \Hp<h', ps'> \quad\leftrightarrow\quad \Hp<h, ps> \starred P \Hp<h', ps'> \not\red P
\]
%format eval = "\func{eval}"
That is, a process soup |ps :: [Proc]| with the initial heap |h| can
evaluate to any heap |h'| and soup |ps'| that results from completely
reducing |ps| using our high-level semantics, where $\not\red P$ expresses
that no further transitions are possible. We may implement the
$\eval P$ relation as the following |eval| function:
\begin{code}
eval :: REL (Heap, [Proc]) (Heap, [Integer])
eval = reduceUntil isValS redS
\end{code}

\noindent Similarly, we define a relation $\eval M$ that encapsulates
complete execution of a thread soup |ts :: [Thread]| with the initial heap
|h| using our virtual machine, resulting in a heap |h'| and a thread soup
|ts'|:
\[
	\Hp<h, ts> \eval M \Hp<h', ts'> \quad\leftrightarrow\quad \Hp<h, ts> \starred M \Hp<h', ts'> \not\red M
\]
%format exec = "\func{exec}"
Likewise, we may implement $\eval M$ as the following |exec| function:
\begin{code}
exec :: REL (Heap, [Thread]) (Heap, [Integer])
exec = reduceUntil haltedM stepM
\end{code}

%format load = "\func{load}"
\noindent Next, we define a function |load| that converts a process into
a corresponding thread for execution, which comprises the compiled code for
the process, together with an empty stack, restart code and read and write
logs:
\begin{code}
load :: [Proc] -> [Thread]
load = map (\ p -> (compileP p NIL, NIL, NIL, Map.empty, Map.empty))
\end{code}

%Dually, we define a partial function |unload :: Map Thread Proc| that
%extracts the resulting integer from a completely executed thread into
%our process language:
%\[
%	|unload (NIL, [n], f, r, w) = ValP n|
%\]

\noindent Using these definitions, the correctness of our compiler can now
be expressed by the following property:
\begin{align*}
	\forall p \in |Proc|&, h \in |Heap|, s \in |[Integer]|.\\
		&\Hp<|Map.empty|, |p : NIL|> \eval P \Hp<h, s>
		\leftrightarrow
		\Hp<|Map.empty|, |load (p : NIL)|> \eval M \Hp<h, s>
\end{align*}
\noindent That is, evaluating a process |p| starting with an initial heap
using our high-level stop-the-world process semantics is equivalent to
compiling and loading the process, and executing the resulting thread using
the interleaved virtual machine semantics. For the purposes of proving the
result, we generalise the above over a process soup rather than a single
process, as well as an arbitrary initial heap:
\begin{theorem}[Compiler Correctness]\label{thm:model-correct}%
\begin{align*}
	\forall ps \in |[Proc]|&, h, h' \in |Heap|, s \in |[Integer]|.\\
	& \Hp<h, ps> \eval P \Hp<h', s>
		\leftrightarrow
	\Hp<h, |load ps|> \eval M \Hp<h', s>
	%|eval| \;=\; |load| \relcomp |exec| \relcomp (|id| \times |map unload|)
\end{align*}
\end{theorem}
\noindent The above $\leftrightarrow$ equivalence can also be considered
separately, where the $\rightarrow$ direction corresponds to soundness, and
states that the compiled code will always produce a result that is permitted
by the semantics. Dually, the $\leftarrow$ direction corresponds to
completeness, and states that the compiled code can indeed produce every
result permitted by the semantics.

In practice, some language implementations are not complete with respect to
the semantics for the language by design, because implementing every
behaviour that is permitted by the semantics may not be practical or
efficient. For example, a real implementation may utilise a scheduler that
only permits a context switch between threads at fixed intervals, rather
than after every transition as in our semantics, because doing so would be
prohibitively expensive.

%}}}%

%if False
%{{{%
\begin{code}
arb :: Arbitrary a => Int -> Gen a
arb s = resize (max 0 s) arbitrary

vars :: [Var]
vars = [ 'a', 'b', 'c' ]

var :: Gen Var
var = elements vars

instance Arbitrary Tran where
	arbitrary = sized $ \ size -> frequency
		[ (8, ValT `fmap` elements [ 0, 1 ])
		, (4, AddT `fmap` arb (size - 1) `ap` arb (size - 1))
		, (4, Read `fmap` var)
		, (4, Write `fmap` var `ap` (resize (size - 1 `max` 0) arbitrary))
		]
	shrink t = case t of
		ValT _ -> []
		a `AddT` b -> [a, b]
		Read _ -> []
		Write _ u -> [u]

instance Arbitrary Proc where
	arbitrary = sized $ \ size -> frequency
		[ (8, ValP `fmap` elements [ 0, 1 ])
		, (4, AddP `fmap` arb (size - 1) `ap` arb (size - 1))
		, (4, Atomic `fmap` arb (size `div` 2))
		, (size, Fork `fmap` resize (size `div` 2) arbitrary)
		]
	shrink p = case p of
		ValP _ -> []
		a `AddP` b -> [a, b]
		Fork q -> [q]
		Atomic t -> Atomic `fmap` shrink t

instance Arbitrary (Map Var Integer) where
	arbitrary = do
		let fromPositive (Positive n) = n
		let pair = (,) <$> var <*> (fromPositive <$> arbitrary)
		n <- choose (0, length vars)
		Map.fromList <$> sequence (replicate n pair)
\end{code}
%}}}%
%endif

\subsection{Validation of Correctness}%{{{%

%\TODO{this section needs a rewrite after chapter \ref{ch:qc+hpc} is
%written!}

Proving the correctness of programs in the presence of concurrency is
notoriously difficult. Ultimately we would like to have a formal proof, but
the randomised testing approach---using QuickCheck and HPC, as described in
Chapter \ref{ch:qc+hpc}---can provide a high level of assurance with
relatively minimal effort. In the case of theorem~\ref{thm:model-correct},
we can transcribe it as the following property:
%format prop_Correctness = "\func{prop\_Correctness}"
\begin{code}
prop_Correctness :: Heap -> [Proc] -> Bool
prop_Correctness h ps = eval (h, ps) == exec (h, load ps)
\end{code}
In other words, from any initial heap |h| and process soup |ps|, the
stop-the-world semantics produces the same set of possible outcomes as that
from executing the compiled thread soup using a log-based implementation of
transactions.

Given suitable |Arbitrary| instances for |Prop| and |Heap|, we can use
QuickCheck to generate a large number of random test cases, and check that
the theorem holds in each and every one:
\begin{spec}
hsPrompt quickCheck prop_Correctness
{-"\texttt{OK, passed 100 tests.}"-}
\end{spec}
Having performed many thousands of tests in this manner, we can be highly
confident in the validity of our compiler correctness theorem. However, as
with any testing process, it is important to ensure that all the relevant
parts of the program have been exercised in the process. Repeating the
coverage checking procedure described in \S\ref{sec:testing-hpc}, we obtain
the following report of unevaluated expressions\footnote{As before, unused
expressions corresponding to compiler-generated instances have been
omitted.}:
\begin{verbatim}
module "Main" {
  inside "reduceTran" {
    tick "Set.empty" on line 303;
  }
}
\end{verbatim}
The |Set.empty| corresponds to the |ValT| case of the |redT| function, which
remains unused simply because we never ask it for the reduct of |ValT m|
expressions.

%if False
\begin{code}
prop_Correct :: Heap -> Proc -> Bool
prop_Correct h p = eval (h, [p]) == exec (h, load [p])

main :: IO ()
main = do
	quickCheck prop_Correct
\end{code}
%endif

%}}}%

%}}}%


% 1 page / 1 page
%if True
\section{Conclusion}%{{{%

In this chapter we have shown how to implement software transactional memory
correctly, for a simplified language inspired by STM Haskell. Using
QuickCheck and HPC, we tested a low-level, log-based implementation of
transactions with respect to a high-level, stop-the-world semantics, by
means of a compiler and its correctness theorem.  This appears to be the
first time that the correctness of a compiler for a language with
transactions has been mechanically tested.

The lightweight approach provided by QuickCheck and HPC was indispensable in
allowing us to experiment with the design of the language and its
implementation, and to quickly check any changes. Our basic definitions were
refined many times during the development of this work, both as a result of
correcting errors, and streamlining the presentation. Ensuring that our
changes were sound was simply a matter of re-running QuickCheck and HPC.

On the other hand, it is important to recognise the limitations of this
approach. First of all, randomised testing does not constitute a formal
proof, and the reliability of QuickCheck depends heavily on the quality of
the test-case generators. Secondly, achieving 100\% code coverage with HPC
does not guarantee that all possible interactions between parts of the
program have been tested. Nonetheless, we have found the use of these tools
to be invaluable in our work.

%\note{refinements: nested atomic / fork, delayed IO}

%\note{retry block on read set}
% interaction with effects

% implementation
% alternative / more sophisticated logs
%\note{transactions with trivial commits (and expensive rollback)}
% beauty in the beast

%}}}%
%endif

% vim: ft=tex:

