%include polycode.fmt
%include local.fmt

\begin{code}
{-# LANGUAGE NoImplicitPrelude, EmptyDataDecls, TypeSynonymInstances #-}

import qualified Prelude as P
import Prelude
	( Int, Integer, Num ((+), fromInteger)
	, Ord ((<)), Bool (..), (/=)
	, IO, getChar, putChar, putStrLn )
import Control.Monad
import Control.Concurrent
import Control.Concurrent.STM
import Data.IORef
\end{code}

\chapter{Software Transactional Memory}

While mutual exclusion is the dominant paradigm for shared memory concurrent
programming, it can be difficult to reason about and extremely error-prone
in practice. Taking a cue from the distributed databases community, software
transactional memory applies the concept of transactions to shared memory
concurrent programming, which has a pleasingly simple semantics. In this
chapter, we introduce the notion of transactions and transactional memory,
along with high-level overviews of how transactional memory can potentially
be implemented. We then give a brief history of the development of STM up to
the present day, followed by a detailed look at the implementation of STM
found in the Glasgow Haskell Compiler.

%\begin{itemize}
%\item what are transactions?
%\item what is TM?
%\item pros and cons of TM
%\item what is (development of) STM (Shavit \& al. '93)
%\item implementation sketch (different approaches?)
%\item STM Haskell \& examples
%\end{itemize}

\section{Database Transactions}%{{{%

Consider a database server which must support multiple concurrent clients.
Each client may need to carry out some complex sequence of operations, and
it is up to the database management server to ensure that different clients
do not make conflicting changes to the data store. As with any concurrent
software, the clients could obtain exclusive access to part of the database
by taking a lock to the relevant parts of the data store, but without
careful coordination between clients this can result in deadlock situations
like what we have seen in the previous chapter. This problem is only
exacerbated by the possibility of failure on the part of the client software
or hardware: a failed client could be holding a lock to critical parts of
the database, thus preventing others from making progress.

The alternative is to make use of the concept of
\emph{transactions}~\cite{date95-introdb}, which takes a higher-level
approach to managing concurrency than explicit locking or mutial exclusion.
A client starts a transaction by issuing a \emph{begin} command to the
server. Thereafter, all subsequent operations until the final \emph{commit}
command are considered part of the transaction. In particular, transactions
ideally have the following properties, neatly summed up by the acronym
`ACID'~\cite{yacht-accident-and-other}:
\begin{description}

\item[Atomicity] The sequence of operations take place as if they were
a single indivisible operation, ensuring that transactions follow a simple
`all-or-nothing' semantics: if any of its constituent operations fail, or if
the transaction is aborted for whatever reason, the server guarantees that
the resulting state of the database is as if none of the operations took
place at all.

\item[Consistency] The sequence of operations cannot put the data store into
a state that is inconsistent with pre-defined invariants of the database.
Were this the case, the server would cause the commit operation to fail.
Typically, such invariants would be specific to the particular database
application, and serves as a safety net to catch client-side bugs.

\item[Isolation] As a transaction is running, other clients cannot observe
any of its intermediate states. Conversely, until the transaction has
completed and been committed to the data store, it cannot influence the
behaviour other concurrent clients.

\item[Durability] Once the database server has accepted a transaction as
being committed, the effects of the operations on the database store should
persist, even in the event of system failure.

\end{description}

\noindent This approach to concurrency significantly simplifies client
implementation. If a transaction fails---say because another client
successfully committed a conflicting change---the original client will be
notified and may simply retry the transaction at a later point. Atomicity
ensures that the partially completed transaction is rolled back: the client
need not carefully undo the changes it had made so far to avoid affecting
subsequent transactions, while isolation ensures that potentially
inconsistent intermediate states of the transaction is not visible to
others.

Furthermore, this approach is \emph{optimistic} in the sense that we can
always proceed with any given transaction, as there are no locks to acquire,
making deadlock a non-issue. The trade-off is that the transaction may later
fail or be unable to commit, should a different transaction commit
a conflicting change in the meantime. Nevertheless, the system as a whole
has made progress. \TODO{wait-free, lock-free, obstruction-free}

%}}}%

\section{Transactional Memory}%{{{%

Transactional memory applies the idea of the previous section to concurrent
software, with shared memory taking the r\^ole of the database store and
individual program threads acting as the clients. Clearly there will be some
differences: with shared random-access memory being volatile, we cannot hope
to satisfy the durability aspect of the ACID properties in the event of
a power failure, for example. In addition, consistency is more an issue of
sequential program correctness and hence largely orthogonal to our main
concern of concurrency. The focus of transactional memory is therefore on
providing atomicity and isolation in the presence of concurrency.

In this section, we give a brief overview of various developments leading up
to the current state of the art in the application of transactional memory
to concurrent software.

\subsection{Hardware Transactional Memory}%{{{%

While it is possible to implement synchronisation between multiple parties
using only primitive read and write operations, for example with Lamport's
bakery algorithm~\cite{lamport?}, such software-only techniques do not scale
well with the addition of further participants. Rather, most modern
architectures feature in one form or another a \emph{compare-and-swap} (CAS)
instruction that compares a given value to a word in memory and
conditionally swapping in a new value if the comparison yields true. The key
property of a CAS instruction is that it does so in an atomic and isolated
manner, implemented at the hardware level. This is a much more powerful
primitive on which more sophisticated synchronisation constructs can be
built.

\TODO{Hang on a minute: did Herlihy show that CAS can *strictly* implement
more synchronisation primitives than R/W? Or is only at similar levels of
time/memory complexity?}

In a sense, this already allows us to implement simple word-sized
transactions on the hardware level: the CAS instruction can detect
interference by comparing the current value of the word with what we had
read during the transaction, and if they match, commit the new value to
memory. Features resembling transactions are more readily observed on other
architectures---such as the DEC Alpha~\cite{jensen87-exclusive}---that
provided pairs of \emph{load-linked} and \emph{store-conditional} (LL and
SC) primitives. The load-linked instruction---as well as fetching a word
from memory---additionally places a watch on the system memory bus for its
address. The subsequent store-conditional instruction succeeds only when no
writes to the aforementioned address has occurred in the meantime.

Herlihy and Moss~\cite{herlihy93-hardware} later extended this approach to
explicitly support multi-word transactions, building upon existing
cache-coherency~\cite{?} protocols for multiprocessor architectures. In
effect, a \emph{transactional cache} local to the processor buffers any
tentative writes, which are only propagated to the rest of the system after
a successfully commit. They leverage existing cache-coherency protocols to
efficiently guard against potential interference. As the size of the
transactional cache is limited by hardware, this sets an upper bound on the
size of the transactions that can occur. To this end, Herlihy and Moss
suggest virtualisation as a potential solution, transparently falling back
to a software-based handler in much the same way as virtual
memory~\cite{?}(?).

\TODO{Any more recent work? Was it IBM who had something recently? Couldn't
find concrete details back then though.}

%}}}%

\subsection{Software Transactional Memory}%{{{%

While some form of hardware support beyond the basic compare-and-swap would
be desirable for the implementation of transactional memory, Shavit and
Touitou~\cite{shavit97-stm} propose a software-only version of Herlihy and
Moss's~\cite{herlihy93-hardware} approach, which can be efficiently
implemented on any existing architecture supporting the CAS or LL/SC
instructions. In purely pragmatic terms, it does not require the level of
initial investment required by a hardware-assisted solution.

Fraser for his thesis~\cite{fraser03-freedom} demonstrated that non-trivial
data structures based on his implementation of STM had comparable
performance to other lock-based or intricately crafted lock-free designs,
running on a selection of existing modern hardware. In this sense, STM can
now be considered practical for everyday use.

However, while transactional algorithms can be derived from existing
sequential ones by simply replacing memory accesses with calls to the STM
library, the impedance mismatch of using library calls for such basic
operations made programming in the large impractical. Furthermore, it was
not possible to prevent a programmer from directly accessing shared data and
circumventing the atomicity and isolation guarantees bestowed by
the transaction.

Harris and Fraser~\cite{harris03-language} experimented with transactional
extensions to the Java language, along with an STM run-time library. Simply
wrapping an existing block of code within an \texttt{atomic} construct
executes it within a transaction. Upon execution reaching the end of said
block of code, the run-time system implicitly attempts to commit its
changes, and should this fail, retries the transaction from the beginning.
Such \texttt{atomic} blocks may be nested, further improving code
reusability.

Their Java bytecode translator traps in-language read and writes to the
program heap, replacing them with transaction-safe alternatives. However,
this does not prevent Java's native methods from surreptitiously modifying
the heap or performing irreversible side-effects such as input or output,
which would be problematic given that a transaction may execute more than
once before it successfully commits. As arbitrary code is permitted within
\texttt{atomic} blocks, calls to native methods within a transaction will
raise run-time exceptions.

\TODO{Unfortunately this work does not seem to be widely adopted by the Java
community? \ldots \url{http://www.deucestm.org/}}

Following on from this work, Harris et al.~\cite{harris05-composable}
presented an implementation of software transactional memory for the Glasgow
Haskell Compiler (GHC) as part of their paper entitled \emph{Composable
Memory Transactions}. The contribution of this work is the introduction of
a left-biased operator for composing pairs of transactions, such that if the
first transaction fails to commit or is aborted programmatically, an
alternative transaction is attempted instead. In later work, they introduce
`data invariants'~\cite{harris06-invariants} for enforcing consistency.

More recent work has brought transactional memory to other programming
languages~\cite{?}, as well as more efficient or alternative low-level
implementations~\cite{?}.

%}}}%

\subsection{STM versus Mutual Exclusion}%{{{%


%}}}%

%}}}%

\section{Implementing Transactions}%{{{%

The high-level view of transactions is that each one is executed atomically
and in isolation from other concurrent threads, as if the entire transaction
took place in a single instant without any of its intermediate states being
visible by concurrently running threads. Indeed, a correct implementation
could simply suspend all other threads upon starting a transaction, and
resume them after the transaction has ended. Pragmatically, this
\emph{stop-the-world} view can be easily achieved by ensuring that only one
transaction is ever executing at any point in time, say using a global
mutual-exclusion lock. While this approach would be trivial to implement, it
prevents transactions from proceeding concurrently, and would not be make
efficient use of multi-core hardware.

\subsection{Log-Based Transactions}\label{sec:log-based}%{{{%

A concurrent implementation of transactions might make use of the notion of
a \emph{transaction log}. During the execution of a transaction, its
associated log serves the purpose of isolating it from other concurrently
running threads. Rather than immediately acting on any side-effecting
operations, the transactional run-time makes a record of these in the log,
applying the side-effects globally only when the transaction successfully
commits.

In the case of shared mutable variables, the log essentially acts as
a transaction-local buffer for read and write operations: for each variable,
only the first read would come from, and only the last value written goes to
the shared variable; all intermediate reads and writes operate solely on the
log. At commit time, if any undesired interference occurs due to another
transaction having completed in the meantime, the run-time need only discard
the log and re-run the transaction, since no globally-visible changes have
been made. Therefore it would be only be appropriate to allow operations
that can be buffered in the transaction log, such as changes to shared
mutable variables; side-effects external to the system---such as launching
missiles~\cite{launch-missiles}---cannot be undone, and must be prevented.
If the transaction log corresponds to a consistent state of the current
shared heap on the other hand, the new values recorded in the log can then
be applied to the global heap in an atomic manner.

A simplistic implementation of transaction commits need only ensure that
globally, only one commit is taking place at any time, say using a global
lock. Even then, we can still make gains on multicore systems, as the bodies
of transactions still run concurrently. A more sophisticated implementation
could even allow transactions to commit concurrently, for example by making
use of specialised lock-free data structures. While concurrent commits would
be trickier to implement, any additional complexities are restricted to the
run-time system, and the proletarian programmer is not required to
understand any of the under-the-hood details.

%}}}%

\subsection{Compensating Transactions}%{{{%

\TODO{Advantages: allows arbitrary I/O.}

\TODO{Disadvantages: roll-back is manual and hard to ensure correct.}

%}}}%

\subsection{Transactions via Lock Inference}%{{{%

\TODO{Advantages: allows arbitrary I/O; isolation---at least wrt
transactional variables---obtained for-free from the locking discipline.}

\TODO{Disadvantages: inference is static, and necessarily conservative, so
does not give optimal concurrency.}

%}}}%

%}}}%

\section{Haskell}%{{{%

In this section we will revisit some Haskell basics required for the
understanding of the implementation of STM given by Harris et
al.~\cite{harris05-composable}. The material should be accessible to the
reader with a general understanding of functional programming; no working
knowledge of Haskell in particular is required.

\subsection{Yet Another Monad Tutorial}%{{{%

The Haskell programming language~\cite{haskell98-report}---eponymously named
after the logician H.\ B.\ Curry---can be characterised by its three key
attributes: functional, pure, and lazy. Functional programming languages are
rooted in Alonzo Church's $\lambda$-calculus~\cite{church}, and emphasise
the evaluation of mathematical functions and compositions thereof, over the
manipulation of state. The core $\lambda$-calculus ideas of abstraction and
application are typically given prominent status in such languages. By pure,
we mean that functions depend only on their arguments, eschewing state or
mutable variables, which coincides with the mathematical notion of
functions. The same program expression will always evaluate to the same
result regardless of its context, and replacing an expression with its value
leaves the meaning of the program unchanged. In other words, the language is
\emph{referentially transparent}. The laziness aspect of Haskell means that
expressions are only evaluated when their values are required, thus the
evaluation order---or even whether something was evaluated at all---is not
immediately apparent from the program text. Together, these properties meant
that for some time, it was not clear how to write programs that are more
naturally expressed in an imperative, sequential style, or to deal with
input and output.

A solution was found in the form of \emph{monads}, which Wadler~\cite{?} and
Moggi~\cite{?} borrowed from category theory~\cite{pierce?,maclane?}. In the
context of computer science, a monad could be viewed as a `container' for
some general notion of computation, together with an operation for combining
such computations. As it turns out, sequential computation is just one
instance of a monad, as we shall see in the following section.

%}}}%

\subsection{Modelling Mutable State}%{{{%

Since Haskell is referentially transparent, we cannot directly work with
mutable variables, but we can certainly model them. Without loss of
generality, we will consider the case of a single mutable variable. A rather
inelegant solution would involve passing the current value of the mutable
variable---say, of type |sigma|---around as an extra argument. Thus, rather
than implementing a function of type |alpha -> beta|, we write instead one
of type |alpha -> sigma -> (sigma, beta)|, which gives back a potentially
mutated value paired with the original return value. As we will frequently
make use of similar types that mutate some given state, it is convenient to
define the following |State| synonym:
\begin{spec}
type State sigma alpha = sigma -> (sigma, alpha)
\end{spec}
%if False
\begin{code}
newtype State sigma alpha = St { runSt :: sigma -> (sigma, alpha) }
\end{code}
%endif
%format St (a) = a
%format runSt (a) = a
A value of type |State sigma alpha| can be regarded as a computation
involving some mutable |sigma| state that delivers an |alpha| result. Thus
we can write the following definitions of |read| and |write|, corresponding
to our intuition of a mutable variable:
\begin{code}
read :: State sigma sigma
read = St (\ s -> (s, s))

write :: sigma -> State sigma ()
write s' = St (\ s -> (s', ()))
\end{code}
The |read| computation results in a value that happens to be the current
state, without changing it in any way. On the other hand, the |write|
computation replaces the current state |s| with the supplied |s'|, giving
a meaningless result of the singleton-valued |()| type.

With these two primitives, we can implement a stateful |increment|
procedure as follows:
\begin{code}
increment :: State Integer ()
increment = St (\ s ->
	let (s', n) = runSt read s
	in runSt (write (n + 1)) s')
\end{code}
\noindent The result of |read| is bound to the name |n|, then the state is
updated with |n + 1| by the subsequent |write|. The initial state |s| we
have been given is passed to |read|---potentially resulting in a different
state |s'|---which is then passed along to |write|.

In the above instance we know that |read| does not change the state, but in
general any |State sigma alpha| computation could, therefore we must
carefully thread it through each computation in order to maintain the
illusion of mutable state. The following definition increments the counter
twice:
\begin{code}
twice :: State Integer ()
twice = St (\ s ->
	let (s', _) = runSt increment s
	in runSt increment s')
\end{code}
\noindent Were we to inadvertently pass the initial |s| to the second
invocation of |increment| as well, we would have made a copy of the initial
state, having discarded the updated |s'|. The resulting |twice| would only
appear to increment the counter once, despite its two invocations of
|increment|. Explicit state threading can not only become somewhat tedious,
small errors can silently lead to very unexpected results.

Fortunately, the act of threading state around is sufficiently regular that
we can implement a general purpose operator that hides away the details of
the plumbing:
%format >>== = >>=
\begin{code}
(>>==) :: State sigma alpha -> (alpha -> State sigma beta) -> State sigma beta
ma >>== fmb = St (\ s -> let (s', a) = runSt ma s in runSt (fmb a) s')
\end{code}
\noindent The |>>=| operator---pronounced `bind'---takes on its left
a computation delivering an |alpha|; its right argument is a function from
|alpha| to a second computation delivering a |beta|. Bind then passes the
result of its left argument along with the modified state |s'| and threads
both through its right argument, delivering a stateful computation of type
|beta|. Using this, we can rewrite |increment| and |twice| as follows:
\begin{code}
increment' :: State Integer ()
increment' =
	read >>= \ n ->
	write (n + 1)

twice' :: State Integer ()
twice' =
	increment' >>= \ _ ->
	increment'
\end{code}
In the above definitions, we no longer need to explicitly thread state
around, and the resulting code has a much more imperative appearance. In
fact Haskell provides a few helper functions as well as some lightweight
syntactic sugar to support exactly this style of programming:
\begin{code}
increment'' :: State Integer ()
increment'' = do
	n <- read
	write (n + 1)

twice'' :: State Integer ()
twice'' = do
	increment''
	increment''
\end{code}
Here, we may think of the |<-| in |increment''| as binding the result of
|read| to the name |n|, and results in the same code as |increment'| after
desugaring. Should we merely want to run a computation for its side-effects,
as we do in the definition of |twice''|, we simply omit |<-| and the name.

To prevent direct manipulation or duplication of the threaded state, we can
make |State| an opaque data type to its users, hiding the above
implementations, and offer only |read| and |write| as primitives for
accessing the state.

%if False
\begin{code}
instance Monad (State sigma) where
	(>>=) = (>>==)
	return = return_State
\end{code}
%endif

%http://research.microsoft.com/en-us/um/people/simonpj/papers/haskell-retrospective/index.htm

%}}}%

\subsection{Monad Properties}%{{{%

So far in this subsection I have deliberately avoided using the word
`monad'. In fact, some members of the Haskell community would rather have
used the phrase `warm fuzzy thing'~\cite{spj} instead. The |>>=| operator
above already constitutes the interesting part of the definition of the
|State sigma| monad, and we need only one further function to complete it.
%format return_State = return
\begin{code}
return_State :: alpha -> State sigma alpha
return_State a = St (\ s -> (s, a))
\end{code}
\noindent Here, the |return| function produces a trivial computation that
results in the value of its given argument. Being an abstract mathematical
structure, our definitions of bind and |return| for the |State sigma| monad
must satisfy certain laws, which are as follows:
\begin{gather*}
	\begin{align*}
		|return a >>= fmb| &\equiv |fmb a| \tag{ident-left} \\
		|ma >>= return| &\equiv |ma| \tag{ident-right}
	\end{align*} \\
	|(ma >>= fmb) >>= fmc| \equiv  |ma >>= (\ a -> fmb a >>= fmc)| \tag{assoc}
\end{gather*}
\noindent The first two laws states that |return| is a left as well as
right-identity for |>>=|, while the third says that the |>>=| operator is
associative. Using the power of equational reasoning afforded to us in this
pure functional setting, we can show that our definition of |>>=| and
|return| for the |State sigma| monad satisfies the above laws by simply
expanding the relevant definitions.~\cite{?}

\TODO{Show proof? Shouldn't be too long; might serve as a gentle intro to
equational reasoning.}

\TODO{Where can I cram monoids in?}

%}}}%

\subsection{Input, Output and Control Structures}%{{{%

Now that I have shown how we can sequence operations on mutable state, what
about input and output? In a sense, we can conceptually think of I/O as
mutating the real world, and indeed this is the approach used in Haskell. By
threading a token representation of the state of the real world through
a program via the |State sigma| monad, we ensure that real-world
side-effects occur in a deterministic order. For example, Haskell's |IO|
monad could be defined as follows,
\begin{spec}
type IO alpha = State RealWorld alpha
\end{spec}
\noindent where |RealWorld| is the opaque type of the aforementioned token,
inaccessible to the end-programmer. Assuming two primitves |getChar :: IO
Char| and |putChar :: Char -> IO ()| for interacting with the user, we can
implement an |echo| procedure as follows:
\begin{code}
echo :: IO ()
echo = do
	c <- getChar
	putChar c
\end{code}
In Haskell, monadic actions such as |getChar| or the above |echo| are
first-order, and when we write a program, we are in fact just composing
values---evaluating |echo| for example does not prompt the user for
a character nor print one out, it merely results in a value of type |IO ()|
corresponding to the composition of |getChar| and |putChar|. The only way to
make |echo| actually perform input and output is to incorporate it into the
definition of the system-invoked |main :: IO ()| procedure.

Being able to manipulate monadic actions is a very powerful concept, and
allows us to easily create high-level control structures within the
language itself in a completely safe manner. For example, there's no need
for Haskell to have a built-in \emph{for-loop} construct, because we can
implement it ourselves:
\begin{code}
for :: Integer -> Integer -> (Integer -> State sigma ()) -> State sigma ()
for m n body = case m < n of
	False -> return ()
	True -> do
		body m
		for (m + 1) n body
\end{code}
\noindent The |for| function invokes |body| with successive integers
arguments, starting at |m| and stopping before |n|. While the type of |for|
explicitly mentions the |State sigma| monad, |IO| is a particular instance
of this, so the expression |for 0 10 (\ _ -> echo)| corresponds to an |IO|
action that echoes $10$ characters entered by the user. As a second example,
the following |square| function---consisting of two nested
|for|-loops---invokes |increment| $n^2$ times:
\begin{code}
square :: Integer -> State Integer ()
square n = do
	for 0 n (\ m -> do
		increment''
		for 0 m (\ _ -> do
			increment''
			increment''))
\end{code}

\noindent Using Haskell's typeclasses---a form of ad-hoc polymorphism---we
can in fact give type-specific instances of |>>=| and |return|, so the above
definition of |for| in fact works in any monad we care to define. However
a discussion of typeclasses is beyond the scope of this
thesis.~\cite{typeclasses?}

%}}}%

%}}}%

\section{Haskell and I/O}%{{{%

While the Haskell language is pure and lazy, occasionally we still need to
make use of certain imperative features~\cite{awkward-squad}. By keeping
such features within the |IO| monad---where a token of the external world
state is implicitly threaded through each |IO| action---not only can we then
guarantee a particular execution order, we also preserve the purity of the
rest of the language.

For example, in those rare cases where the only known efficient solution to
a problem is explicitly imperative, Haskell's standard library provides true
mutable variables in the form of the |IORef alpha| datatype. Its basic
interface is given below:
\begin{spec}
newIORef    :: alpha -> IO (IORef alpha)
readIORef   :: IORef alpha -> IO alpha
writeIORef  :: IORef alpha -> alpha -> IO ()
\end{spec}
While an |atomicModifyIORef| primitive is also provided, the accompanying
documentation notes that ``extending the atomicity to multiple |IORef|s is
problematic''~\cite{stdlib?}, a point we had explored back in Chapter
\ref{chapter:introduction}.

For multiprocessor programming, Parallel Haskell~\cite{mph?} provides
a combinator |par :: alpha -> beta -> beta|, which hints to the run-time
system that it may be worth evaluating its first argument in parallel
(cf.~section \ref{sec:parallel}), and otherwise acting as the identity
function on its second argument. As is evident from its type, the |par|
combinator cannot have any side-effects, nor could either of its two
arguments. Thus no concurrent interaction can take place and it would be
perfectly sound for an implementation of |par| to simply ignore its first
argument.

However, explicit concurrency is a necessity as well as a convenience when
used as a mechanism for structuring many real-world programs. Concurrent
Haskell~\cite{pj96-concurrent} introduced the |forkIO :: IO () -> IO ()|
primitive, which provides a mechanism analogous to the Unix \texttt{fork()}
system call, sparking a separate thread to run its argument |IO ()| action.
Forking is considered impure as threads can interact with each other via
a variety of mechanisms, and this fact is correspondingly reflected in the
type of |forkIO|. With the mutability provided by |IORef|s, we can create
concurrent applications in the same imperative manner as other low-level
programming languages. For example, the following program launches
a secondary thread to repeatedly print the letter `\texttt{y}', while |main|
carries on to print `\texttt{n}'s:
%format main_Char
\begin{code}
main_Char :: IO ()
main_Char = do
	forkIO (forever (putChar 'y'))
	forever (putChar 'n')
\end{code}
The user would observe an unending stream of `\texttt{y}'s and
`\texttt{n}'s, interleaved in an unspecified manner.

%format forkOS = forkIO
%format n_a
%format n_b
%format n_c
%format n_sum
%format Counter_IORef
%format increment_IORef
%format incBoth_IORef
%format main_IORef
%format Counter_IORef

The following program launches two threads, both forever incrementing
a shared counter, as well as an individual one. (Suppose it were counting
votes, and the individual counts were required for auditing purposes\ldots)
The |main_IORef| function meanwhile repeatedly asserts that the shared
counter indeed equals the sum of the two thread-local counters.
\begin{code}
type Counter_IORef = IORef Integer

increment_IORef :: Counter_IORef -> IO ()
increment_IORef c = do
	n <- readIORef c
	writeIORef c (n + 1)

incBoth_IORef :: Counter_IORef -> Counter_IORef -> IO ()
incBoth_IORef sum local = do
	increment_IORef sum
	increment_IORef local

main_IORef :: IO ()
main_IORef = do
	sum <- newIORef 0
	a <- newIORef 0
	b <- newIORef 0

	forkOS (forever (incBoth_IORef sum a))
	forkOS (forever (incBoth_IORef sum b))

	forever (do
		n_sum <- readIORef sum
		n_a <- readIORef a
		n_b <- readIORef b
		when (n_sum /= n_a + n_b) (do
			putStrLn "oh dear."))
\end{code}
Such a program, while seemingly straightforward in intent, can leave the
programmer with exponential number of possibilities to consider as it
scales; it would simply be impractical to apply sequential reasoning to each
potential interleaving. Worse still is the fact that the unwanted
interleavings are often the least likely to occur, and can easily slip
through otherwise thorough empirical testing.

The above program has a number of potentially rare and unexpected
behaviours. (A discourse on how these bugs could be exploited for election
fraud would be tangential to this thesis.) Firstly, the two forked-off
children both increment the |sum| counter, and it is quite possible for one
thread's execution of |increment_IORef| to interleave the |readIORef| and
|writeIORef| of the other thread---as we have witnessed in section
\ref{sec:counter-interleaved}---losing counts in the process. Requiring our
implementation of |increment| to follow a locking discipline for each
counter in question would eliminate this particular race condition. Even
with this fix in place, another issue remains: each thread first increments
|sum|, followed by its own specific counter; meanwhile, the main thread may
interleave either child in-between the two aforementioned steps, and observe
a state in which the value of |sum| disagrees with the sum of the values of
|a| and |b|.

As a concurrent program grows further in size, race condition- and
deadlock-related issues becomes much more subtle. Transactional
memory---amongst other high-level approaches---aims to avoid such bugs,
while retaining the speed benefits of a concurrent implementation.

%}}}%

\section{STM Haskell}%{{{%

The previous section outlined the standard approach to concurrency in
Haskell, which makes use of explicit threading and mutable variables via
|forkIO| and |IORef|s within the |IO| monad. In an analogous fashion, STM
Haskell provides mutable \emph{transactional variables} with the following
interface:
%format new_TVar
%format read_TVar
%format write_TVar
%format newTVar = new_TVar
%format readTVar = read_TVar
%format writeTVar = write_TVar
\begin{spec}
newTVar    :: alpha -> STM (TVar alpha)
readTVar   :: TVar alpha -> STM alpha
writeTVar  :: TVar alpha -> alpha -> STM ()
\end{spec}
\noindent The |newTVar| function creates a transactional variable
initialised to some given value, while |readTVar| and |writeTVar| inspect
and mutate |TVar|s. The type |STM alpha| can be read as \emph{a transaction
which delivers a result of type |alpha|}, and the three aforementioned
primitives are used to construct more elaborate transactions within the
|STM| monad:
\begin{spec}
(>>=)   :: STM alpha -> (alpha -> STM beta) -> STM beta
return  :: alpha -> STM alpha
\end{spec}
\noindent The definition of \emph{bind} for the |STM| monad composes
transactions in a sequential manner, while |return| takes a given value to
a trivial transaction resulting in the same. Transactions can be converted
to runnable |IO| actions via the |atomically| primitive,
\begin{spec}
atomically :: STM alpha -> IO alpha
\end{spec}
\noindent while explicit threading is achieved through |forkIO| as before.

STM Haskell makes use of the notion of a transaction log (as we mentioned
previously in section \ref{sec:log-based}) and may automatically re-run
transactions when conflicts are detected. Therefore it is important that
|STM| actions only make changes to transactional variables---which can be
encapsulated within its corresponding log---rather than arbitrary and
possibly irrevocable |IO| actions. This an easy guarantee to enforce since
the Haskell type system strictly and statically differentiates between |IO
alpha| and |STM alpha|, and there is no facility for actually performing an
|IO| action while inside the |STM| monad. Of course, a transaction can
always manipulate and return |IO| actions as first-order values, to be
performed post-commit. In any case, as the bulk of computations in Haskell
are idiomatically pure, they are necessarily free from side-effects. Thus
they do not need to be kept track of by the transaction implementation and
may simply be discarded in the event of a conflict. The ability to
statically make this three-fold distinction between irrevocable (namely
|IO|) and revocable (or |STM|) side-effecting computations---used relatively
infrequently in practice---alongside pure ones, makes Haskell an ideal
environment for an implementation of STM.

Let us now revisit the example of the previous section, with two threads
competing to incrementing the same shared counter. Using STM, we can make
the previous program behave in the intended manner without changing its
structure: \TODO{use a figure here?}
%format Counter_TVar
%format increment_TVar
%format incBoth_TVar
%format main_TVar
\begin{code}
type Counter_TVar = TVar Integer

increment_TVar :: Counter_TVar -> STM ()
increment_TVar c = do
	n <- readTVar c
	writeTVar c (n + 1)

incBoth_TVar :: Counter_TVar -> Counter_TVar -> STM ()
incBoth_TVar sum local = do
	increment_TVar sum
	increment_TVar local

main_TVar :: IO ()
main_TVar = do
	sum <- atomically (newTVar 0)
	a <- atomically (newTVar 0)
	b <- atomically (newTVar 0)

	forkOS (forever (atomically (incBoth_TVar sum a)))
	forkOS (forever (atomically (incBoth_TVar sum b)))

	forever (do
		(n_sum, n_a, n_b) <- atomically (do
			n_sum <- readTVar sum
			n_a <- readTVar a
			n_b <- readTVar b
			return (n_sum, n_a, n_b))
		when (n_sum /= n_a + n_b) (do
			putStrLn "oh dear."))
\end{code}
\noindent Here the counter is represented as an integer |TVar| rather than
an |IORef|. Correspondingly, the |increment_TVar| primitive and the
|incBoth_TVar| function now result in |STM| rather than |IO| actions.
Likewise |main_TVar| atomically samples the three counters inside a single
transaction to avoid potential race conditions.

With STM, the intention is that when implementing some data structure, we
need only expose the basic operations as |STM alpha| actions, without the
need to anticipate all the potential ways in which a user may wish to
compose said operations in the future.

While the sequencing of transactions provides a convenient and composable
way to access shared data structures, a concurrency framework ought to also
provide efficient ways to wait on some collection of resources, or to allow
coordination between threads. With mutual exclusion, waiting on a number of
objects could be implemented by waiting on each one in turn, taking care to
avoid deadlocks. However, there are often cases where we might want to
proceed whenever \emph{any} one of some collection of objects becomes ready.
For example, Haskell's standard concurrency library offers generalised
counting semaphores, which could be used for coordination between multiple
threads. Similarly, most flavours of Unix provides a \texttt{select(2)}
system call, which takes a set of file descriptors and blocks until at least
one is ready to be read from, or written to. Unfortunately, these techniques
do not scale: for example in the latter case, all the file descriptors being
waited upon must be collated up to a single top-level \texttt{select()},
which runs contrary to the philosophy of modular software development.

STM Haskell answers this problem with a pair of primitives for blocking and
composing alternative transactions:
\begin{spec}
retry :: STM alpha
orElse :: STM alpha -> STM alpha -> STM alpha
\end{spec}
The |retry| primitive forces the current transaction to fail, which allows
us a great degree of flexibility, in contrast to e.g.~Hoare's
\emph{conditional critical regions} (CCRs)~\cite{?}. The following function
decrements the given counter only when its value is strictly positive, and
blocks otherwise.
%format decrement_TVar
\begin{code}
decrement_TVar :: Counter_TVar -> STM ()
decrement_TVar c = do
	n_c <- readTVar c
	unless (n_c > 0)
		retry
	writeTVar c (n_c - 1)
\end{code}
However, rather than immediately retrying the transaction, the STM run-time
will suspend the current thread until one or more of the |TVar|s read up to
the |retry| has changed. This ensures that the thread does not waste
processor cycles in a busy-waiting situation: since any variations in the
control flow leading up to the |retry| can only arise from changes in the
|TVar|s read so far, this does not impact the semantics of the program.

Suppose we now wish to implement a function to decrement |sum| in the
earlier example. In order to maintain the invariant $|a| + |b| = |sum|$, we
must also decrement either one of |a| or |b|. Knowing that |decrement_TVar|
blocks when the counter is zero, we may conclude that if |decrement_TVar
sum| succeeds, then |a| and |b| cannot both be zero, and we ought to be able
to decrement one of the two without blocking. But how do we choose? With
the |orElse| combinator, of course:
\begin{code}
decEither_TVar :: Counter_TVar -> Counter_TVar -> Counter_TVar -> STM ()
decEither_TVar sum a b = do
	decrement_TVar sum
	decrement_TVar a `orElse` decrement_TVar b
\end{code}
The |orElse| primitive---written here in infix notation---provides us with
a left-biased choice operator. The expression |t `orElse` u| corresponds to
a transaction that runs either one of |t| or |u|. It is left-biased in the
sense that |t| is run first: if it retries, any changes due to |t| is rolled
back, and |u| is attempted instead. Only when both |t| and |u| cannot
proceed, would the transaction as a whole retry. Thus the final line of the
above fragment would preferentially decrement |a|, opting for |b| when this
is not possible.

\TODO{(|STM alpha|, |retry|, |orElse|) is a monoid!}

A rather elegant use case for |orElse| is to make a blocking operation
non-blocking, or vice versa. For example, we can derive a non-blocking
|decrement_TVar| as follows, returning a boolean to indicate success or
failure:
\begin{code}
decrement_TVar' :: Counter_TVar -> STM Bool
decrement_TVar' c = do
		decrement_TVar c
		return True
	`orElse` do
		return False
\end{code}

%converting the composition to an |IO| action only at those points where we
%require the transaction to execute atomically.

%failure handled with alternatives or retry.

% Hoare / conditional critical regions

\TODO{OH LOOK! We've just implemented composable counting semaphores!}

%}}}%

\section{Conclusion}%{{{%

%}}}%


% vim: ft=tex:

