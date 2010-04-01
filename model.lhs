%{{{%
%include local.fmt
%include haskell.fmt

\def\Z{\mathbb Z}

%\def\finmap{\hookrightarrow}
%\def\finsert#1#2#3{#1{\left[ #2 \mapsto #3 \right]}}
\def\finsert#1#2#3{#1 \uplus \{ #2 \mapsto #3 \}}
\def\flookup#1#2{#1 \mathbin{?} #2}

\def\expr#1#2{#2\ensuremath{_\mathsf{\scriptscriptstyle#1}}}

\def\starred#1{#1^\star}
\def\red#1{\expr{#1}{\mapsto}}

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
\begin{code}
module Main where

import Prelude
import Control.Arrow (first, second)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Traversable


type Var = Char
type List = []
\end{code}
%}}}%

\chapter{A Model of STM}

%\begin{itemize}
%\item expand TFP paper
%\item why not full STM Haskell a là Beauty in the Beast?
%\item something that I could be reasonably expected to produce a proof for
%\item also contrast with Wouter's stop-the-world approach in his thesis
%\end{itemize}

In this chapter, we identify a simplified subset of STM Haskell and
a stop-the-world semantics for this language, suitable for exploring design
issues. We then specify a low-level virtual machine for this language, in
which the transactions are executed concurrently. Finally we give a compiler
correctness statement for the combination. Since the model is implemented as
a Haskell program, we can test its correctness using QuickCheck and HPC.

\TODO{this chapter is based on previous paper?}

\section{A Simple Transactional Language}%{{{%

% provide a consistent snapshot of the current state of the shared heap

In chapter \S\ref{ch:stm}, we introduced STM Haskell, which provides a small
set of primitives for working with |TVar|s inside transactions,
\begin{spec}
newTVar    ::                alpha ->  STM (TVar alpha)
readTVar   :: TVar alpha ->            STM alpha
writeTVar  :: TVar alpha ->  alpha ->  STM Unit
\end{spec}
along with an |atomically| primitive for running transactions, and |forkIO|
for explicit concurrency:
\begin{spec}
atomically  :: STM alpha ->  IO alpha
forkIO      :: IO Unit ->    IO Unit
\end{spec}
The |STM| and |IO| types are monads (\S\ref{sec:haskell}), so we may
use \emph{bind} and |return| on both levels for sequencing effectful
computations.

\subsection{Syntax}%{{{%

%format Var = "\type{Var}"
%format Tran = "\type{Tran}"
%format ValT = "\cons{Val\sub T}"
%format `AddT` = "\mathbin{\cons{\oplus\sub T}}"
%format Read = "\cons{Read}"
%format Write = "\cons{Write}"
%format Proc = "\type{Proc}"
%format ValP = "\cons{Val\sub P}"
%format `AddP` = "\mathbin{\cons{\oplus\sub P}}"
%format Atomic = "\cons{Atomic}"
%format Fork = "\cons{Fork}"
As a first step towards a verified implementation of STM, let us consider
a simplified model of the above, without concerning ourselves with
orthogonal issues. The language we consider has a two-level
syntax---mirroring that of the STM Haskell primitives---which can be
represented as the following |Tran| and |Proc| data types in Haskell:
\def\sub#1{_{\scriptscriptstyle #1}}
\def\const#1{}
\begin{code}
data Tran  = ValT Integer  | Tran `AddT` Tran  | Read Var     | Write Var Tran{-"\const{"-}deriving (Eq, Ord){-"}"-}
data Proc  = ValP Integer  | Proc `AddP` Proc  | Atomic Tran  | Fork Proc{-"\const{"-}deriving (Eq, Ord){-"}"-}
\end{code}
The two syntactic classes correspond to actions in the |STM| and |IO| monads
respectively. The language is intentionally minimal, since issues such as
name binding and performing general-purpose computations are largely
orthogonal to our stated goal of verifying an implementation of STM. Thus,
we replace the \emph{bind} and |return| of both monads with the monoid of
addition and integers, as motivated in section \S\ref{sec:degenerate} of the
previous chapter. In our language, |ValT| and |ValP| correspond to |return|
for the |STM| and |IO| monads, while |`AddT`| and |`AddP`| combine |Tran|
and |Proc| computations in an analogous way to \emph{bind}. By enforcing
a left-to-right reduction semantics for |`Add`|, we nevertheless retain the
fundamental idea of using monads to sequence computations and combine their
results~\cite{p1-11?}.

The remaining constructs emulate the |STM| and |IO| primitives provided by
STM Haskell: |Read| and |Write| correspond to |readTVar| and |writeTVar|,
where |Var| represents a finite collection of transactional variables. Due
to the lack of name binding, we omit an analogue of |newTVar| from our
language, and assume all variables are initialised to zero. |Atomic| runs
a transaction to completion, delivering a value, while |Fork| spawns off its
argument as a concurrent process in the style of |forkIO|.

For simplicity, we do not consider |orElse| or |retry|, as they are not
strictly necessary to illustrate the basic implementation of a log-based
transactional memory system.

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
To increment the same counter concurrently twice using concurrent threads,
we would write:
%format incTwice = "\func{incTwice}"
\begin{code}
incTwice :: Var -> Proc
incTwice c = Fork (Atomic (increment c)) `AddP` Fork (Atomic (increment c))
\end{code}

%}}}%

%}}}%

\subsection{Transaction Semantics}%{{{%

We specify the meaning of transactions in this language using a small-step
operational semantics, following the approach of \cite{p1-9.3.2}. Formally,
we give a reduction relation $\red T$ on pairs $\Hp<h, e>$ consisting of
a heap |h :: Heap| and a transaction |e :: Tran|. In this section we explain
each of the rules defining $\red T$, and simultaneously describe its
implementation in order to highlight their similarity.

Firstly, we model the heap as a map from variable names to their
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
which is implemented by the following code, where we have typeset
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
new value of |v| accordingly:
\restorecolumns
\begin{code}
redT (h, Write v e) = case e of
	ValT n  -> Set.singleton (Map.insert v n h, ValT n)
	_       -> second (Write v) `Set.map` redT (h, e)
\end{code}
The latter case implements \eqName{WriteT} by recursively reducing the
subexpression |e|, then reconstructing |Write v e'| by mapping |second
(Write v)| over the resulting set of |(h', e')|.

As we replace the act of sequencing computations with addition in our
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
where we return the empty set for |ValT m|, since it has no associated
reduction rules.

%format joinSet = "\func{join_{Set}}"
Since $\red T$ only describes a single reduction step, we also need to
implement a helper function to run a given initial expression to completion
for our executable model. Let us first define |joinSet|, which flattens
nested |Set|s:
\begin{code}
joinSet :: {-"\const{"-}Ord alpha => {-"}"-}Set (Set alpha) -> Set alpha
joinSet = Set.fold Set.union Set.empty
\end{code}

%format reduceUntil = "\func{reduceUntil}"
%format step = "\func{step}"
%format partition = "\func{partition}"
\def\stepSig{|step :: (Set alpha, Set beta) -> Set beta|}
\def\partitionSig{|partition :: alpha -> (Set alpha, Set beta) -> (Set alpha, Set beta)|}
\noindent The following definition of |reduceUntil|---parameterised over
a relation |reduce|---reduces the given |init| state to completion,
according to the predicate |p|:
\begin{code}
reduceUntil :: {-"\const{"-}(Ord alpha, Ord beta) => {-"}"-}(alpha -> Maybe beta) -> Rel alpha -> REL alpha beta
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
\begin{code}
isValT :: (Heap, Tran) -> Maybe (Heap, Integer)
isValT (h, ValT n  ) = Just (h, n)
isValT (h, _       ) = Nothing
\end{code}

%}}}%

\subsection{Process Soup Semantics}%{{{%

%format Soup = "\type{Soup}"
%format redP = "\func{reduce_{Proc}}"
\begin{code}
type Soup = [Proc]

redP :: Proc -> Rel (Heap, Soup)
redP (ValP n)      (h, s) = Set.empty

redP (Fork q)      (h, s) = Set.singleton (h, ValP 0 : q : s)
redP (Atomic t)    (h, s) = second (\ n -> ValP n : s)
	`Set.map` (reduceUntil isValT redT (h, t))

redP (a `AddP` b)  (h, s) = case (a, b) of
		(ValP m  , ValP n  ) -> Set.singleton (h, ValP (m + n) : s)
		(ValP m  , _       ) -> second (\ (b' : s') -> ValP m `AddP` b' : s')
			`Set.map` redS (h, b : s)
		(_       , _       ) -> second (\ (a' : s') -> a' `AddP` b : s')
			`Set.map` redS (h, a : s)
\end{code}

%format redS = "\func{reduce_{Soup}}"
\begin{code}
redS :: Rel (Heap, Soup)
redS (h, []     ) = Set.empty
redS (h, p : s  ) = (second (p : {-"{}"-}) `Set.map` redS (h, s))
	`Set.union` redP p (h, s)
\end{code}

%format isValP = "\func{isVal_P}"
%format isValS = "\func{isVal_S}"
\begin{code}
isValP :: Proc -> Maybe Integer
isValP (ValP n)  = Just n
isValP _         = Nothing

isValS :: (Heap, Soup) -> Maybe (Heap, [Integer])
isValS (h, s) = case traverse isValP s of
	Nothing   -> Nothing
	Just ns   -> Just (h, ns)
\end{code}

The reduction relation $\red P$ for processes acts on pairs $\Hp<h, s>$
consisting of a heap |h| as before, and a `soup' |s| of running
processes~\cite{peyton-jones01-awkward}. The soup itself is a multi-set,
which we represent as a list of type |[Proc]| for implementation reasons.
The process rules are in general defined by matching on the first process in
the soup. However, we begin by giving the \eqName{Preempt} rule, which
allows the rest of the soup to make progress, giving rise to non-determinism
in the language:
\[
	\inferrule%
		{\Hp<h, s> \red P \Hp<h', s'>}%
		{\Hp<h, p : s> \red P \Hp<h', p : s'>}
	\eqTag{Preempt}
\]

Executing |Fork p| adds |p| to the process soup, and evaluates to |ValP 0|
(which corresponds to |return ()| in Haskell) as the result of this action:
\[
	\Hp<h, |Fork p : s|> \red P \Hp<h, |ValP 0 : p : s|>
	\eqTag{Fork}
\]

\noindent Next, the \eqName{Atomic} rule has a premise which evaluates the
given expression until it reaches a value (where $\starred{\red T}$ denotes
the reflexive, transitive closure of $\red T$), and a conclusion which
encapsulates this as a single transition on the process level:
\begin{gather*}
	\inferrule%
		{\Hp<h, e> \starred{\red T} \Hp<h', |ValT n|>}%
		{\Hp<h, |Atomic e : s|> \red P \Hp<h', |ValP n : s|>}
	\eqTag{Atomic}
\end{gather*}
In this manner we obtain a \emph{stop-the-world} semantics for atomic
transactions, preventing interference from other concurrently executing
processes. Note that while the use of $\starred{\red T}$ may seem odd in
a small-step semantics, it expresses the intended meaning in a clear and
concise manner~\cite{harris05-composable}.

Finally, it is straightforward to handle |`AddP`| on the process level using
three rules, in an analogous manner to |`AddT`| on the transaction level:
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

\noindent In summary, the above semantics for transactions and processes
mirror those for STM Haskell, but for a simplified language. Moreover, while
the original semantics uses evaluation contexts to identify the point at
which transition rules such as \eqName{\AddZP} can be applied, our language
is sufficiently simple to allow the use of explicit structural rules such as
\eqName{\AddLP} and \eqName{\AddRP}, which for our purposes have the
advantage of being directly implementable.

%}}}%

%}}}%

\section{A Simple Transactional Machine}\label{sec:machine}%{{{%

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
                  |  BEGIN | COMMIT | FORK Code{-"\const{"-}deriving (Eq, Ord){-"}"-}
\end{code}
The |PUSH| instruction leaves its argument on top of the stack, while |ADD|
replaces the top two numbers with their sum. The behaviour of the remaining
instructions is more complex in order to maintain atomicity, but
conceptually, |READ| pushes the value of the named variable onto the stack,
while |WRITE| updates the variable with the topmost value. In turn, |BEGIN|
and |COMMIT| mark the start and finish of a transactions, and |FORK|
executes the given code concurrently.

%}}}%

\subsection{Compiler}%{{{%

%format compileT = "\func{\expr T{compile}}"
%format compileP = "\func{\expr P{compile}}"
We define the |compileT| and |compileP| functions to provide translations
from |Tran| and |Proc| to |Code|, both functions taking an additional |Code|
argument to be appended to the instructions produced by the compilation
process; using such a \emph{code continuation} both simplifies reasoning and
results in more efficient compilers~\cite[\S13.7]{hutton07-haskell}. In both
cases, integers and addition are compiled into |PUSH| and |ADD|
instructions, while the remaining language constructs map directly to their
analogous machine instructions. The intention is that executing a compiled
transaction or process always leaves a single result value on top of the
stack.
\begin{spec}
compileT :: Tran -> Code -> Code
compileT e cc = case e of
	ValT i      -> PUSH i : cc
	x `AddT` y  -> compileT x (compileT y (ADD : cc))
	Read v      -> READ v : cc
	Write v e'  -> compileT e' (WRITE v : cc)

compileP :: Proc -> Code -> Code
compileP e cc = case e of
	ValP i      -> PUSH i : cc
	x `AddP` y  -> compileP x (compileP y (ADD : cc))
	Atomic e'   -> BEGIN : compileT e' (COMMIT : cc)
	Fork x      -> FORK (compileP x []) : cc
\end{spec}
For example, invoking |compileP (incTwice counter) []| delivers the
following code:
\begin{spec}
[ FORK [ BEGIN, READ counter, PUSH 1, ADD, WRITE counter, COMMIT ]
, FORK [ BEGIN, READ counter, PUSH 1, ADD, WRITE counter, COMMIT ]
, ADD ]
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


\subsubsection*{Interference}

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


\subsubsection*{Equality}

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
changed in the interim. Is this acceptable? i.e.~are the two zeros `equal'?
We can consider a hierarchy of notions of equality, in increasing order of
permissiveness:
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
consistent with the wagers made in the log. Hence in our instance, there is
no need at commit time to distinguish between the two zeroes in our example,
as they are equal in the high-level expression language.

From a semantics point of view, therefore, value or user-defined equality
are the best choices. Practical implementations may wish to adopt a more
efficient notion of equality (e.g.~STM Haskell utilises pointer equality),
but for the purposes of this article, we will use value equality.

%}}}%

\subsection{Virtual Machine}%{{{%

The state of the virtual machine is given by a pair $\Hp<h, s>$, comprising
a heap $h$ mapping variables to integers, and a soup $s$ of concurrent
\emph{threads}. Each |Thread| consists of a tuple of the form |(c, sigma, f,
r, w)|, where |c| is the code to be executed, |sigma| is the local stack,
|f| gives the code to be rerun if a transaction fails to commit, and
finally, |r| and |w| are two logs (partial maps from variables to integers)
acting as read and write caches between a transaction and the heap.
%format Thread = "\type{Thread}"
%format Stack = "\type{Stack}"
%format Log = "\type{Log}"
\begin{code}
type Thread  =  (Code, Stack, Code, Log, Log)
type Stack   =  [Integer]
type Log     =  Map Var Integer
\end{code}

%format sigma'
%format sigma_1
%format sigma_2
%format stepM = "\func{step_M}"
%format stepT = "\func{step_T}"
%format stepI = "\func{step_I}"
\begin{code}
stepM :: Rel (Heap, [Thread])
stepM (h, []     ) = Set.empty
stepM (h, t : s  ) = (second (t : {-"{}"-}) `Set.map` stepM (h, s))
	`Set.union` stepT t (h, s)

stepT :: Thread -> Rel (Heap, [Thread])
stepT ([]   ,  sigma, f, r, w) (h, s) = Set.empty
stepT (i : c,  sigma, f, r, w) (h, s) = stepI i where
	~(n : sigma_1@ ~(m : sigma_2)) = sigma

	stepI :: Instruction -> Set (Heap, [Thread])
	stepI (FORK c')  = Set.singleton (h,   (c,      0  :  sigma,    f,        r,          w) : t      : s)
		where t = (c', [], [], Map.empty, Map.empty)
	stepI (PUSH n)   = Set.singleton (h,   (c,      n  :  sigma,    f,        r,          w)          : s)

	stepI ADD        = Set.singleton (h,   (c, m +  n  :  sigma_2,  f,        r,          w)          : s)
	stepI BEGIN      = Set.singleton (h,   (c,            sigma, BEGIN : c,   Map.empty,  Map.empty)  : s)

	stepI (READ v)   = Set.singleton (h,   (c,      n  :  sigma,    f,        r',         w)          : s)
		where (n, r') = case Map.lookup v w of
			Just n'  -> (n', r)
			Nothing  -> case Map.lookup v r of
				Just n'  -> (n', r)
				Nothing  -> (h ? v, Map.insert v (h ? v) r)

	stepI (WRITE v)  = Set.singleton (h,   (c,      n :  sigma_1,   f,        r,          w')         : s)
		where w' = Map.insert v n w
	stepI COMMIT     = Set.singleton (h',  (c',          sigma',    f,        r,          w)          : s)
		where (h', c', sigma') = case (r `Map.intersection` h) `Map.isSubmapOf` h of
			True   -> (w `Map.union`  h,  c, n :  sigma_1)
			False  -> (               h,  f,      sigma)
\end{code}

We specify the behaviour of the machine using a transition relation $\red M$
between machine states, defined via a collection of transition rules that
proceed by case analysis on the first thread in the soup. As with the
previous semantics, we begin by defining a \eqName{PREEMPT} rule to allow
the rest of the soup to make progress, giving rise to non-determinism in the
machine:
\[
	\inferrule%
		{\Hp<h, s> \red M \Hp<h', s'>}%
		{\Hp<h, |t : s|> \red M \Hp<h', |t : s'|>}
	\eqTag{PREEMPT}
\]
This rule corresponds to an idealised scheduler that permits context
switching at every instruction, as our focus is on the implementation of
transactions rather than scheduling policies. We return to this issue when
we consider the correctness of our compiler in \S\ref{sec:model-correctness}.

Executing |FORK| adds a new thread |t| to the soup, comprising the given
code |c'| with an initially empty stack, restart code and read and write
logs:
\begin{align*}
	&
		\Hp<h, \Td(|FORK c' : c|,     |sigma|, f, r, w) : s> \red M
		\Hp<h, \Td(          |c|, |0 : sigma|, f, r, w) : t : s>
	\eqTag{FORK} \\[1ex]
	&	\text{where }t = \Td(c', |[]|, |[]|, \emptyset, \emptyset)
\end{align*}

The |PUSH| instruction places the integer |n| on top of the stack, while
|ADD| takes the top two integer from the stack and replaces them with their
sum:
\begin{align*}
	\langle|h, (PUSH n, c, sigma, f, r, w) : s|\rangle &\red M \langle|h, (c, n : sigma, f, r, w)  : s|\rangle
	\eqTag{PUSH} \\
	\langle|h, (ADD, c, n : m : sigma, f, r, w) : s|\rangle &\red M \langle|h, (c, m + n : sigma, f, r, w)  : s|\rangle
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

Executing |BEGIN| starts a transaction, which involves clearing the read and
write logs, while making a note of the code to be executed if the
transaction fails:
\[
	\Hp<h, \Td(|BEGIN : c|, \sigma,          |f|,       |r|,       |w|) : s> \red M
	\Hp<h, \Td(        |c|, \sigma,  |BEGIN : c|, \emptyset, \emptyset) : s> \\
	\eqTag{BEGIN}
\]

Next, |READ| places the appropriate value for the variable |v| on top of the
stack. The instruction first consults the write log. If the variable has not
been written to, the read log is then consulted. Otherwise, if the variable
has also not been read, its value is looked up from the heap and the read
log updated accordingly:
\begin{align*}
	&
	\Hp<h, \Td(|READ v : c|,     \sigma, f, r,  w) : s> \red M
	\Hp<h, \Td(         |c|, n : \sigma, f, r', w) : s>
	\eqTag{READ} \\
	&\text{where }\Hp<n, r'> = \begin{cases}
		\Hp<w(v), r> & \text{if }v \in \text{dom}(w) \\
		\Hp<r(v), r> & \text{if }v \in \text{dom}(r) \\
		\Hp<h(v), \finsert r v {h(v)}> & \text{otherwise}
	\end{cases}
\end{align*}

In turn, |WRITE| simply updates the write log for the variable |v| with the
value on the top of the stack, without changing the heap or the stack:
\begin{align*}
	&
	\Hp<h, \Td(|WRITE v : c|, |n : sigma|, f, r, w ) : s> \red M
	\Hp<h, \Td(          |c|, |n : sigma|, f, r, w') : s>
	\eqTag{WRITE} \\
	&\text{where }w' = \finsert w v n
\end{align*}

Finally, |COMMIT| first checks the read log |r| for consistency with the
current heap |h|, namely that the logged value for each variable read is
equal to its value in the heap. Note that the write log may contain
variables not in the read log, for which no check is necessary. Using our
representation of logs and heaps, this condition can be concisely stated as
$r \subseteq h$. If they are consistent, then the transaction has succeeded,
so we may commit its write log to the heap. This update is expressed in
terms of the overriding operator on maps as $h \uplus w$. Otherwise the
transaction has failed, in which case the heap is not changed, the result on
the top of the stack is discarded, and the transaction is restarted at |f|:
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
is taken care of by the first instruction of |f| always being a |BEGIN|.

%}}}%

%}}}%

% 2 pages / 1 page
\section{Correctness of Implementation}%{{{%

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
auxiliary definitions. First of all, since our semantics is
non-deterministic, we define a relation |eval| that encapsulates the idea of
completely evaluating a process using our high-level semantics:
\[
	p \infix{eval} \Hp<h, s> \quad\leftrightarrow\quad \Hp<\emptyset, |[p]|> \starred{\red P} \Hp<h, s> \not\red P
\]
That is, a process |p :: Proc| can evaluate to any heap |h| and process soup
|s| that results from starting with the empty heap and completely reducing
|p| using our high-level semantics, where $\not\red{\mbox{}}$ expresses that
no further transitions are possible. Similarly, we define a relation
|exec| that encapsulates complete execution of a thread |t :: Thread|
using our virtual machine, resulting in a heap |h| and a thread soup |s|:
\[
	t \infix{exec} \Hp<h, s> \quad\leftrightarrow\quad \Hp<\emptyset, |[t]|> \starred{\red M} \Hp<h, s> \not\red M
\]

Next, we define a function |load :: Proc -> Thread| that converts a process
into a corresponding thread for execution, which comprises the compiled code
for the process, together with an empty stack, restart code and read and
write logs:
\[
	|load p = (compileP p [], [], [], Map.empty, Map.empty)|
\]
Dually, we define a partial function |unload :: Map Thread Proc| that
extracts the resulting integer from a completely executed thread into
our process language:
\[
	|unload ([], [n], f, r, w) = ValP n|
\]

Using these definitions, the correctness of our compiler can now be
expressed by the following relational equation, in which $\relcomp$ denotes
composition of relations, and the functions |load| and |unload| are viewed
as relations by taking their graph:
\begin{theorem}[Compiler Correctness]\label{thm:correct}%
~\\[-3ex]
\begin{align*}
	 |eval| \;=\; |load| \relcomp |exec| \relcomp (|id| \times |map unload|)
\end{align*}
\end{theorem}
That is, evaluating a process using our high-level semantics is equivalent
to compiling and loading the process, executing the resulting thread using
the virtual machine, and unloading each of the final values.

The above theorem can also be split into two inclusions, where $\supseteq$
corresponds to soundness, and states that the compiled code will always
produce a result that is permitted by the semantics. Dually, $\subseteq$
corresponds to completeness, and states that the compiled code can produce
every result permitted by the semantics.

In practice, some language implementations are not complete with respect to
the semantics for the language by design, because implementing every
behaviour that is permitted by the semantics may not be practical. For
example, a real implementation may utilise a scheduler that only permits
a context switch between threads at particular intervals, rather than after
every transition as in our semantics, because doing so would be
prohibitively expensive.

%}}}%

\subsection{Validation of Correctness}%{{{%

Proving the correctness of programs in the presence of concurrency is
notoriously difficult. Ultimately we would like to have a formal proof of
theorem~\ref{thm:correct}, but to date we have adopted a mechanical approach
to validating this result, using randomised testing.

QuickCheck~\cite{claessen00-quickcheck} is a system for testing properties
of Haskell programs. It is straightforward to implement our semantics,
virtual machine and compiler in Haskell, and to define a property
|prop_Correctness :: Proc -> Bool| that corresponds to theorem
\ref{thm:correct}. Non-deterministic transitions in our system are
implemented as set-valued functions, which are used to build up a tree that
captures all possible evaluation sequences, thus ensuring all possible
interleavings are accounted for. QuickCheck can then be used to generate
a large number of random test processes, and check that the theorem holds in
each one of these cases:
\begin{verbatim}
*Main> quickCheck prop_Correctness
OK, passed 100 tests.
\end{verbatim}
Having performed many thousands of tests in this manner, we gain a high
degree of confidence in the validity of our compiler correctness theorem.
However, as with any testing process, it is important to ensure that all the
relevant parts of the program have been exercised during testing.

The Haskell Program Coverage (HPC) toolkit~\cite{gill07-hpc} supports just
this kind of analysis, enabling us to quickly visualise and identify
unexecuted code. Using HPC confirms that testing our compiler correctness
result using QuickCheck does indeed give 100\% code coverage, in the sense
that every part of our implementation is actually executed during the
testing process:
%\begin{center}
%\includegraphics[width=\textwidth]{HPC}
%\end{center}

In combination, the use of QuickCheck for automated testing and HPC to
confirm complete code coverage, as pioneered by the XMonad
project~\cite{stewart07-xmonad}, provides high-assurance of the correctness
of our implementation of transactions.

%}}}%

%}}}%


% 1 page / 1 page
%if False
\section{Conclusion and Further Work}\label{sec:further}%{{{%

In this article we have shown how to implement software transactional memory
correctly, for a simplified language based on STM Haskell. Using QuickCheck
and HPC, we tested a low-level, log-based implementation of transactions
with respect to a high-level, stop-the-world semantics, by means of
a compiler and its correctness theorem.  This appears to be the first time
that the correctness of a compiler for a language with transactions has been
mechanically tested.

The lightweight approach provided by QuickCheck and HPC was indispensable in
allowing us to experiment with the design of the language and its
implementation, and to quickly check any changes. Our basic definitions were
refined many times during the development of this work, both as a result of
correcting errors, and streamlining the presentation. Ensuring that our
changes were sound was simply a matter of re-running QuickCheck and HPC.

On the other hand, it is important to be aware of the limitations of this
approach. First of all, randomised testing does not constitute a formal
proof, and the reliability of QuickCheck depends heavily on the quality of
the test-case generators. Secondly, achieving 100\% code coverage with HPC
does not guarantee that all possible interactions between parts of the
program have been tested. Nonetheless, we have found the use of these tools
to be invaluable in our work.

In terms of expanding on the work presented in this article, we have
identified a number of possible directions for further work:

\medskip\noindent\emph{Proof.} The most important step now is to consider
how our correctness result can be formally proved. The standard
approach~\cite{wand95-parallel} to compiler correctness for concurrent
languages involves translating both the source and target languages into
a common process language such as the $\pi$-calculus, where compiler
correctness then amounts to establishing a bisimulation. We are in the
process of developing a new, simpler approach that avoids the introduction
of an intermediate language, by establishing a bisimulation directly between
the source and target languages.

\medskip\noindent\emph{Generalisation.} Our simplified language focuses on
the essence of implementing transactions. However, it is important to take
into account other features in the core language of STM Haskell, namely
binding, input / output, exceptions and |retry| / |orElse|. Previous work by
Huch and Kupke \cite{huch05-highlevel} describes a full implementation of
the STM Haskell semantics given in \cite{harris05-composable}, using
existing Concurrent Haskell primitives, but they do not address the
correctness of their implementation.

We could go further, and consider the implications of allowing limited
effects within transactions, such as the creation of nested transactions or
concurrent processes, with a view to investigate a more liberal variant of
STM in Haskell.

\medskip\noindent\emph{Mechanisation.} Just as QuickCheck and HPC were of
great benefit for testing our compiler correctness theorem, we may similarly
expect to benefit from the use of mechanical support when proving this
result. Indeed, in the presence of concurrency it would not be surprising if
the complexity of the resulting bisimulation proof necessitated some form of
tool support. We are particularly interested in the use of automated
proof-checkers such as Epigram~\cite{mcbride04-left} or
Agda~\cite{norell07-thesis}, in which the provision of dependent types
allows proof to be conducted directly on the program terms, which helps to
shift some of the work from the user to the type-checker
\cite{mckinna08-correct}. Work on proving our correctness theorem in Agda is
currently under way.

\medskip\noindent\emph{Other approaches.} We have verified the basic
log-based implementation of transactions, but it would also be interesting
to consider more sophisticated techniques, such as suspending a transaction
that has retried until a relevant part of the heap has changed. Finally, it
is also important to explore the relationship to other semantic approaches
to transactions, such as the use of functions~\cite{swierstra08-iospec} and
processes~\cite{acciai07-atccs}, as well as relevant semantic properties,
such as linearisability~\cite{herlihy90-linear}.

%\note{refinements: nested atomic / fork, delayed IO}

%\note{retry block on read set}
% interaction with effects

% implementation
% alternative / more sophisticated logs
%\note{transactions with trivial commits (and expensive rollback)}
% beauty in the beast

%}}}%
%endif

% wager

% vim: ft=tex:

