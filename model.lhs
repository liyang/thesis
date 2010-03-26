%include local.fmt
%include haskell.fmt

\def\Z{\mathbb Z}

\def\finmap{\hookrightarrow}
\def\finsert#1#2#3{#1{\left[ #2 \mapsto #3 \right]}}

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
\begin{code}
data Tran  = ValT Integer  | Tran `AddT` Tran  | Read Var     | Write Var Tran
data Proc  = ValP Integer  | Proc `AddP` Proc  | Atomic Tran  | Fork Proc
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
In our STM model, the corresponding |increment| function would be written as
follows:
\begin{code}
increment :: Var -> Tran
increment c = Write c (Read c `AddT` 1)
\end{code}
To increment the same counter concurrently twice using concurrent threads,
we would write:
%format incTwice = "\func{incTwice}"
\begin{code}
incTwice :: Var -> Tran
incTwice c = Fork (Atomic (increment c)) `AddP` Fork (Atomic (increment c))
\end{code}

%}}}%

%}}}%

\subsection{Transaction Semantics}%{{{%

We specify the meaning of transactions in this language using a small-step
operational semantics, following the approach of \cite{p1-9.3.2}. Formally,
we give a reduction relation $\red T$ on pairs $\Hp<h, e>$ consisting of
a heap |h|---a map of type |Var -> Integer| from variable names to their
values---and a transaction |e :: Tran|. In this section we explain each of
the rules defining $\red T$.

Firstly, reading a variable |v| looks up its value in the heap:
\begin{gather*}
	\Hp<h, |Read v|> \red T \Hp<h, |ValT{-"\;h(v)"-}|> \eqTag{Read}
\end{gather*}

Writing to a variable is taken care of by two rules: \eqName{\WriteZ}
updates the heap with the new value for a variable in the same manner as the
published semantics of STM Haskell~\cite{harris05-composable}, while
\eqName{WriteT} allows its argument expression to be repeatedly reduced
until it becomes a value:
\begin{gather*}
	\Hp<h, |Write v (ValT n)|> \red T \Hp<\finsert h v n, |ValT n|>
	\eqTag{\WriteZ} \\[1ex]
	\inferrule%
		{\Hp<h, e> \red T \Hp<h', e'>}%
		{\Hp<h, |Write v e|> \red T \Hp<h', |Write v e'|>}
	\eqTag{WriteT}
\end{gather*}

Because we replace \emph{bind} with addition in our language, it is
important to enforce a sequential evaluation order. The following three
rules define reduction for |`AddT`|, and ensure the left argument is
evaluated to completion before starting on the right one:
\begin{gather*}
	\Hp<h, |ValT m `AddT` ValT n|> \red T \Hp<h, |ValT (m + n)|>
		\eqTag{\AddZT}
		\\[1ex]
	\inferrule%
		{\Hp<h, b> \red T \Hp<h', b'>}%
		{\Hp<h, |ValT m `AddT` b|> \red T \Hp<h', |ValT m `AddT` b'|>}
		\eqTag{\AddRT}
		\\[1ex]
	\inferrule%
		{\Hp<h, a> \red T \Hp<h', a'>}%
		{\Hp<h, |a `AddT` b|> \red T \Hp<h', |a' `AddT` b|>}
		\eqTag{\AddLT}
\end{gather*}

%}}}%

\subsection{Process Soup Semantics}%{{{%

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
                  |  BEGIN | COMMIT | FORK Code
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

%if False

\subsubsection*{Equality}

But what constitutes \emph{equality}? To see why this is an important
question, and what the design choices are, let us return to our earlier
example of a transaction that deposits a given amount into an account.
%\nopagebreak
%\begin{spec}
%[BEGIN, READ account, PUSH 10, ADD, WRITE account, COMMIT]
%\end{spec}
Consider the following timeline:
{\footnotesize
\begin{longtable}{@@{}l@@{\hspace{1ex}}llclclclc}
& \multicolumn{8}{l}{|deposit 10|} \\
\cline{2-9}
1 & \multicolumn{1}{||l||}{|BEGIN|} & \multicolumn{1}{l||}{|READ account|}
	& \multicolumn{5}{c}{\ldots} & \multicolumn{1}{||l||}{|COMMIT|} & \\
\cline{2-9}
&&&& \rule{0pt}{3ex}|deposit 20| \\
\cline{5-5}
2 &&&& \multicolumn{1}{||c||}{\ldots} \\
\cline{5-5}
&&&&&& \rule{0pt}{3ex}|withdraw 20| & \\
\cline{7-7}
3 &&&&&& \multicolumn{1}{||c||}{\ldots} \\
\cline{7-7}
\multicolumn{10}{@@{}c@@{}}{\rule[0.5ex]{\textwidth}{0.5pt}\makebox[1pt][r]{$\rightarrow$}}\\
% \hline
\multicolumn{10}{c}{Time}
\end{longtable}}\vspace{-1ex}%
\noindent Suppose that |account| starts with a balance of zero, which is
read by the first transaction and logged. Prior to its final |COMMIT|,
a second concurrent transaction successfully makes a deposit, which is
subsequently withdrawn by a third transaction. When the first finally
attempts to commit, the balance is back to zero as originally logged, even
though it has changed in the interim. Is this acceptable? i.e.~are the two
zeros `equal'? We can consider a hierarchy of notions of equality, in
increasing order of permissiveness:
\begin{itemize*}

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

\end{itemize*}
Which of the above is the appropriate notion of equality when committing
transactions? Recall that under a stop-the-world semantics, a transaction
can be considered to be executed in its entirely at the point when it
successfully commits, and any prior reads are bets on the state of the heap
at this point. Any intermediate writes that may have been committed by other
transactions do not matter, as long as the final heap is consistent with the
bets made in the log. Hence, there is no need at commit time to distinguish
between the two zeroes in our example, as they are equal in the high-level
expression language.

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
\begin{spec}
type Thread  =  (Code, Stack, Code, Log, Log)
type Stack   =  [Integer]
type Log     =  Map Var Integer
\end{spec}

We specify the behaviour of the machine using a transition relation $\red M$
between machine states, defined via a collection of transition rules that
proceed by case analysis on the first thread in the soup. As with the
previous semantics, we begin by defining a \ruleName{PREEMPT} rule to allow
the rest of the soup to make progress, giving rise to non-determinism in the
machine:
\[
	\inferrule%
		{\Hp<h, s> \red M \Hp<h', s'>}%
		{\Hp<h, |t : s|> \red M \Hp<h', |t : s'|>}
	\tag*{\ruleName{PREEMPT}}
\]
This rule corresponds to an idealised scheduler that permits context
switching at every instruction, as our focus is on the implementation of
transactions rather than scheduling policies. We return to this issue when
we consider the correctness of our compiler in \S\ref{sec:correctness}.

Executing |FORK| adds a new thread |t| to the soup, comprising the given
code |c'| with an initially empty stack, restart code and read and write
logs:
\begin{align*}
	&
		\Hp<h, \Td(|FORK c' : c|,     |sigma|, f, r, w) : s> \red M
		\Hp<h, \Td(          |c|, |0 : sigma|, f, r, w) : t : s>
	\tag*{\ruleName{FORK}} \\[1ex]
	&	\text{where }t = \Td(c', |[]|, |[]|, \emptyset, \emptyset)
\end{align*}

The |PUSH| instruction places the integer |n| on top of the stack, while
|ADD| takes the top two integer from the stack and replaces them with their
sum:
\[
	\begin{array}{l@@{$\,:\,$}l@@{\:}r@@{\;}c@@{\;}l@@{\,}r}
	%	 11111111111 | 22 | 3333333333333333333333333  | 44444 |  5555555 | 666666666666666666666666666
		\langle|h, (PUSH n|&|c,|&|        sigma, f, r, w) : s|\rangle & \red M & \langle|h, (c,|&|     n : sigma, f, r, w)  : s|\rangle \\[1ex]
		\langle|h, (ADD   |&|c,|&|n : m : sigma, f, r, w) : s|\rangle & \red M & \langle|h, (c,|&| m + n : sigma, f, r, w)  : s|\rangle
	\end{array}
% HaX: My eyes. They bleed.
	\tag*{\parbox{8ex}{\makebox[8ex][r]{\ruleName{PUSH}}\\\makebox[8ex][r]{\ruleName{ADD}}}}
\]

Executing |BEGIN| starts a transaction, which involves clearing the read and
write logs, while making a note of the code to be executed if the
transaction fails:
\[
	\Hp<h, \Td(|BEGIN : c|, \sigma,          |f|,       |r|,       |w|) : s> \red M
	\Hp<h, \Td(        |c|, \sigma,  |BEGIN : c|, \emptyset, \emptyset) : s> \\
	\tag*{\ruleName{BEGIN}}
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
	\tag*{\ruleName{READ}} \\
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
	\tag*{\ruleName{WRITE}} \\
	&\text{where }w' = \finsert w v n
\end{align*}

Finally, |COMMIT| first checks the read log |r| for consistency with the
current heap |h|, namely that the logged value for each variable read is
equal to its value in the heap. Note that the write log may contain
variables not in the read log, for which no check is necessary. Using our
representation of logs and heaps, this condition can be concisely stated as
$r \subseteq h$. If they are consistent, then the transaction has succeeded,
so it may commit its write log to the heap. This update is expressed in
terms of the overriding operator on maps as $h \oplus w$. Otherwise the
transaction has failed, in which case the heap is not changed, the result on
the top of the stack is discarded, and the transaction is restarted at |f|:
\begin{align*}
	&\Hp<h,  \Td(|COMMIT  : c|,  |n : sigma|,  f, r, w) : s> \red M
		\Hp<h', \Td(          |c'|,     |sigma'|, f, r, w) : s> \\
	&\text{where }\Tr<h', c', \sigma'> = \begin{cases}
		\Tr<h \oplus w, c, n : \sigma>
			&\text{if }r \subseteq h \\
		\Tr<h, f, \sigma>
			&\text{otherwise}
	\end{cases}
	\tag*{\ruleName{COMMIT}}
\end{align*}
There is no need to explicitly clear the logs in the above rule, since this
is taken care of by the first instruction of |f| always being a |BEGIN|.

%}}}%
%endif

%}}}%

% wager

% vim: ft=tex:

