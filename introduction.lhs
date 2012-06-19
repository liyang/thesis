%let showMiscCode = False

\pagenumbering{arabic}

%if False -- %{{{%
\begin{code}
module Main where

import Prelude
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad
import Data.IORef
import Test.QuickCheck
import Test.QuickCheck.Monadic
\end{code}
%endif -- %}}}%

\chapter{Introduction}\label{ch:introduction}

% \TODO{Race conditions break sequential assumptions about program behaviour}

In this chapter we set the scene for this thesis. We begin with a brief
background on the history of concurrent computing, and the concepts and
issues involved in developing software that takes advantage of the
additional computational capability. We then describe a number of mainstream
approaches to constructing concurrent software, along with the transactional
memory approach that is the focus of this thesis, illustrated with some
simple examples. We conclude with a synopsis of each chapter and a summary
of our primary contributions.

\section{Background}%{{{%

\subsection{A Brief Note on Moore's Law}%{{{%

Since the invention of the integrated circuit over 50 years ago and the
subsequent development of the microprocessor, the number of transistors that
engineers can manufacture on a single silicon chip for the same cost has
been increasing at an exponential pace, roughly doubling every two years.
This growth has been remained consistent, so much so that it has been
informally codified as `Moore's Law'~\cite{moore65-law}. The related
statement\footnote{Due to David House---an Intel executive at the time---as
claimed by Moore:\\\url{http://news.cnet.com/2100-1001-984051.html}} that
``microprocessors \emph{performance} roughly doubles every 18 months'' has
also held true, once we factor in the improved performance of individual
transistors.

The popular understanding of Moore's Law tends to be simplified to
``computer speed doubles roughly every 18 months.'' Until half a decade ago,
this interpretation sufficed, because in order to pack more transistors next
to each other, each one had to be made smaller. This in turn meant faster
signal propagation between components, and so faster switching (or clock
speeds), increasing performance. The implication of this is that one could
expect the same piece of software to run twice as fast on the available
hardware, 18 months down the line.

% TODO: yeah sure, but what about asynchronous processors?
% There's too much legacy investment in traditional processor designs\ldots


%}}}%

\subsection{The End of the Free Lunch}%{{{%

%While the individual processor speeds eventually plateaued at $3$--$4$ GHz
%over the last decade, the transistor count per chip carried on doubling
%with barely a blip, with the trend set to continue for the foreseeable
%future.

Moore's Law had become self-perpetuating as the industry assumed its truth
to make projections for their technology roadmaps. By shrinking the size of
individual transistors, not only were silicon manufacturers able to increase
how many transistors can be economically placed on a single piece of
silicon, they were also able to clock their processors at progressively
higher frequencies due to reduced switching and signal propagation delays.

% signal integrity ~\cite{?}


Sadly, miniaturisation has some undesirable side-effects: on the sub-micron
scales of a modern microprocessor, current leakage due to quantum tunnelling
effects across the on-chip insulation is very much detrimental to signal
integrity: the smaller the features, the more power the integrated
circuit needs to counteract these side-effects. This additional power must
be dissipated in the form of waste heat, limiting the extent to which we can
simply increase the clock speed. Indeed, some recent desktop processors
expend up to a third~\cite{lal-shimpi08-atom} of their power solely to
ensure accurate clock signal distribution to outlying areas of the silicon
die, and expel as much as $150\text{W}$ of excess heat in an area less than
$15\text{mm}^2$.

% area less than 15mm² ~\cite{?}

Given the restriction that we cannot reasonably clock individual processors
at increasingly higher speeds, how could we pack more computing power onto
each silicon die? With the extra transistors afforded to us by Moore's Law,
the most obvious and easiest solution is to resort to \emph{symmetric
multiprocessing} (SMP), by fabricating multiple independent processors on
the same die that share access to the same memory.

%}}}%

\subsection{A Brief Look at Parallel and Concurrent Computing}%{{{%

The concept of SMP had been put to practice as early as the 1960s with the
introduction of the Burroughs B5500
mainframe~\footnote{\url{https://wiki.cc.gatech.edu/folklore/index.php/Burroughs_Third-Generation_Computers}}.
In the decades that followed, the entire computing industry resorted one by
one to some form of parallelism in order to achieve their stated
performance. First steps in this dirction included the development of vector
processors, where each instruction simultaneously operate on tens or
sometimes hundreds of words of data. In today's parlance, we refer to such
architectures as \emph{single instruction multiple data} (SIMD).

In contrast, a \emph{multiple instruction multiple data} (MIMD) architecture
comprises a number of independent processing units, each concurrently
executing its own sequence of instructions. However, programming for
multiprocessing systems is a task fraught with pitfalls, as Seymour Cray was
alleged to have once quipped: ``If you were ploughing a field, which would
you rather use: two strong oxen or 1024 chickens?'' His remark alludes to
the challenge of synchronising a large number of independent processors with
each one working on a small part of a larger problem while sharing the same
working memory. It is much easier for people to work with a few oxen than to
try and herd a large number of chickens.

Such systems with multiple, independent processors are therefore suited to
domains involving very large datasets and have intrinsically parallelisable
solutions that do not require much synchronisation or communication between
individual processors. This correlates closely with many scientific
computation and simulation problems, and the insatiable demand for
computational power in these domains drove the development of massively
parallel computers in the decades that followed. Even Cray eventually
conceded to the fact that multiprocessing was inevitable, as the costs and
resources required to breed and feed the two hypothetical oxen became
prohibitive compared to breeding, feeding and herding 1024 chickens.

Meanwhile, as multiprocessor computers grew increasingly larger, it became
difficult to maintain fast access to the same shared memory for all
processor nodes. Cutting-edge systems therefore moved towards a more
\emph{non-uniform memory architecture} (NUMA), where each node had fast
access to local memory, but access to globally shared or non-local data took
correspondingly longer. The lessons learnt have strongly influenced the
design today's high-performance hardware, even in the context of personal
computing, as seen with the recent development of \emph{general-purpose
graphical processing units} (GPGPUs). On a more distributed and larger
scale, Beowulf clusters of networked computers may be seen as a looser
interpretation of the NUMA paradigm. Such systems typically form the
workhorse behind many of today's large-scale scientific simulations, at
least in part due to the fact that they can be and often are built from
cheap and readily available commodity hardware.

%}}}%

\subsection{A Supercomputer on Every Desk}%{{{%

Moving back to the sphere of personal computing, it was not until the last
decade that shared memory SMP computers managed to establish a presence. The
explanation for this is twofold, yet complementary: on the one hand, the
cost of motherboards that can accommodate multiple processor packages were
significantly more expensive, and so were only sought after by users with
specialist needs. On the other, the inability for predominantly
single-threaded software---such as a game or a word-processor---to take
advantage of multiple processors, meant that the vast majority of users had
no interest in resorting to SMP: simply waiting another 18 months had been
sufficient.

However as raw processor speeds have plateaued in recent years, we can no
longer afford to dismiss multiprocessor systems as being too difficult to
program. Traditional supercomputing problems---large-scale, loosely-coupled
computations such as physical simulations or graphical rendering---have been
well-catered for, but they encompass only a small fraction of our day-to-day
software usage. We need to figure out how to make concurrency accessible and
manageable for everyday software.

%and I hope this monograph makes a small contribution towards how we might
%safely and correctly achieve that goal.

%}}}%

%}}}%

\section{Approaches to Concurrent Software}%{{{%

We resort to concurrency with the hope that the more computational power we
have at our disposal, the faster our programs will run. How successfully
this is in practice depends on how much concurrency we can exploit in our
programs. How we model concurrency has a large influence on how we---as
software engineers---think and reason about our concurrent programs, which
in turn influences the ease with which we can exploit concurrency. This
chapter demonstrates using a few examples why concurrent programming has
such a reputation for being difficult, then review some of the basic models
of concurrency.

% main interest: tapping in to the power of concurrency for personal
% computing

\subsection{Concurrency versus Parallelism}\label{sec:introduction-parallelism}%{{{%

In general computing literature, the terms `concurrency' and `parallelism'
are often taken as synonyms and used interchangeably by many, while others
make a clear distinction between the two. We will afford a few sentences to
clarify what we mean by each, in the context of this thesis.

When we say \emph{parallelism}, we mean the extraction of better
\emph{performance} from a program by inferring computations that do not
interact with each other then simultaneously carrying them out, and the
writing of programs in such a way as to make this process easy or possible
for the compiler. \emph{Concurrency} on the other hand means the use of
interdependent threads of execution as a means of \emph{structuring} the
control flow of programs. The focus of this thesis is on explicit
concurrency.

%}}}%

\subsection{Counting: easy as 0, 1, 2\ldots}\label{sec:counter-interleaved}%{{{%

Consider the problem of incrementing a counter, represented in Haskell using
a mutable reference:
%format Counter_IORef = "\type{Counter_{IORef}}"
%format makeCounter_IORef = "\func{makeCounter_{IORef}}"
\begin{code}
type Counter_IORef = IORef Integer

makeCounter_IORef :: IO Counter_IORef
makeCounter_IORef = newIORef 0
\end{code}
%format increment_IORef = "\func{increment_{IORef}}"
The |increment_IORef| program could then be implemented as follows:
%format readIORef = "\func{read_{IORef}}"
%format writeIORef = "\func{write_{IORef}}"
\begin{code}
increment_IORef :: Counter_IORef -> IO ()
increment_IORef counter = do
	n <- readIORef counter
	writeIORef counter (n + 1)
\end{code}
When only a single instance of |increment_IORef| is executing, the above
code behaves as expected. Suppose however, that two instances of
|increment_IORef| were executing at the same time. This results in four
possible interleavings of the two |readIORef| and |writeIORef| operations,
not all of which would have the intended effect of incrementing the counter
twice. For example, the following interleaving would only increment the
counter by one:
%format n_A
%format n_B
\begin{longtable}{l||l||c}%{{{%
Thread A & Thread B & |counter| \\
\hline
|n_A <- readIORef counter|
	&
		& 0 \\
	& |n_B <- readIORef counter|
		& 0 \\
	& |writeIORef counter (n_B + 1)|
		& 1 \\
|writeIORef counter (n_A + 1)|
	&
        & 1
\end{longtable}%}}}%

\noindent Typically, reading from and writing to mutable variables are
relatively fast primitive operations. When they occur in immediate
succession, the probability of Thread A being interleaved by Thread B in the
above manner is very small, and can easily slip through seemingly thorough
empirical testing. Such errors are termed \emph{race conditions},
and can occur whenever there is the possibility of concurrent access to any
shared resource.
%FIXME: citation for `race condition' ??? ~\cite{?}

%}}}%

\subsection{Shared Memory and Mutual Exclusion}%{{{%

The most widely used approach to prevent the kind of race conditions we have
seen in the previous section is to simply prevent concurrent accesses to the
shared resource, via a selection of related techniques---locks, semaphores,
critical sections, mutexes---all of which are based on the principle of
mutual exclusion.

Without discussing implementation details, let us assume the existence of
two primitives operations---|lock| and |release|---with the following
behaviour: |lock| attempts to acquire exclusive access to a given mutable
variable; if the variable is already locked, |lock| waits until it becomes
available before proceeding. Its counterpart |release| relinquishes the
exclusivity previously obtained.

%format Counter_lock = "\type{Counter_{lock}}"
%format increment_lock' = "\func{increment_{lock}}"
%format lock = "\func{lock}"
%format release = "\func{release}"
%if showMiscCode -- %{{{%
\begin{code}
type Counter_lock = (Counter, MVar ())

makeCounter_lock :: IO Counter_lock
makeCounter_lock = do
	value <- makeCounter
	lock <- newMVar ()
	return (value, lock)

lock :: Counter_lock -> IO ()
lock (value, lock) = takeMVar lock

release :: Counter_lock -> IO ()
release (value, lock) = putMVar lock ()

increment_lock' :: Counter_lock -> IO ()
increment_lock' (value, lock) = do
	n <- readIORef value
	yield
	yield
	writeIORef value (n + 1)

query_lock :: Counter_lock -> IO Integer
query_lock counter = do
	lock counter
	n <- readIORef (fst counter)
	release counter
	return n
\end{code}
%endif -- %}}}%

We can now eliminate the earlier race condition as follows:
%format increment_lock = "\func{increment_{lock}}"
\begin{code}
increment_lock :: Counter_lock -> IO ()
increment_lock counter = do
	lock counter
	increment_lock' counter
	release counter
\end{code}
Even if Thread A were interleaved mid-way, Thread B cannot proceed past the
|lock| primitive until Thread A releases |counter|, ruling out the earlier
race condition:
\begin{longtable}{l||l||c}%{{{%
Thread A & Thread B & |counter| \\
\hline
|lock counter|
	&
		& 0 \\
|n_A <- readIORef counter|
	&
		& 0 \\
	& |lock counter|
		& 0 \\
|writeIORef counter (n_A + 1)|
	& \multirow{2}{*}{\parbox[c]{19ex}{\emph{%
		\vdots\\[-1.5ex]
		\textup{blocked on |counter|}\\[-1.5ex]
		\vdots%
	}}}
        & 1 \\
|release counter|
	&
        & 1 \\
	& |n_B <- readIORef counter|
		& 1 \\
	& |writeIORef counter (n_B + 1)|
		& 2 \\
	& |release counter|
		& 2
\end{longtable}%}}}%

%if showMiscCode -- %{{{%
\begin{code}
check_lock = do
	counter <- makeCounter_lock
	s <- newQSemN 0
	forkIO $ do increment_lock counter; signalQSemN s 1
	forkIO $ do increment_lock counter; signalQSemN s 1
	waitQSemN s 2
	n <- query_lock counter
	return (n == 2)
	
check = do
	(quickCheck . monadicIO . run) check_lock
\end{code}
%endif -- %}}}%

\noindent Such two-state locks can easily be generalised to $n$ states with
\emph{counting semaphores} where some limited concurrent sharing may take
place.

%or to two-stage read/write locks in the case where we wish to allow
%concurrent reading---but not modification---of the shared variable.

%}}}%

\subsection{Example: Deadlock}%{{{%

Let us consider a slightly more interesting example: we are required to
implement a procedure to increment two given counters in lock-step. A first
attempt may be as follows:
%format increment_pair = "\func{increment_{pair}}"
%format increment_pair' = "\func{increment_{pair}\Prime}"
%format c_0 = "c_0"
%format c_1 = "c_1"
\begin{code}
increment_pair' :: Counter_lock -> Counter_lock -> IO ()
increment_pair' c_0 c_1 = do
	increment_lock c_0
	increment_lock c_1
\end{code}
However, this does not have the desired effect, because there is an
intermediate state between the two calls to |increment_lock| when |c_0| has
been incremented but |c_1| has not, yet neither is locked. A better
implementation might lock both counters before incrementing:
\begin{code}
increment_pair :: Counter_lock -> Counter_lock -> IO ()
increment_pair c_0 c_1 = do
	lock c_0
	lock c_1
	increment_lock' c_0
	increment_lock' c_1
	release c_0
	release c_1
\end{code}
While this version ensures that the two counters are updated together, it
however suffers from a more subtle problem. If two threads A and B both
attempt to increment the same pair of counters passed to |increment_pair| in
a different order, a potential deadlock situation can occur:
\begin{longtable}{l||l}%{{{%
A: |increment_pair c_0 c_1| & B: |increment_pair c_1 c_0| \\
\hline
|lock c_0| & |lock c_1| \\
|lock c_1| & |lock c_0| \\
\multirow{2}{*}{\parbox[c]{14ex}{%
	\emph{\vdots\\[-1.5ex]\textup{blocked on |c_1|}\\[-1.5ex]\vdots}}}
	& \multirow{2}{*}{\parbox[c]{14ex}{%
		\emph{\vdots\\[-1.5ex]\textup{blocked on |c_0|}\\[-1.5ex]\vdots}}} \\
	& \\
	&
\end{longtable}%}}}%
\noindent Neither thread can make progress, as they attempt to acquire
a lock on the counter which is being held by the other. This could be solved
by always acquiring locks in a specific order, but enforcing this is not
always straightforward.

Correctness considerations aside, there are the issues of code reuse and
scalability to consider. In terms of reuse, ideally we would not want to
expose |increment|, as only |increment_lock| is safe for concurrent use. On
the other hand, to build more complex operations on top of the basic
`increment' operation, chances are that we would need access to the unsafe
|increment| implementation. Unfortunately exposing this breaks the
abstraction barrier, with nothing to enforce the safe use of |increment|
other than trust and diligence on the part of the programmer.

On the issue of scalability, there is also some tension regarding lock
granularity, inherent to mutual-exclusion. Suppose we have a large shared
data structure, and our program makes use of as many threads as there are
processors. In order to allow concurrent access to independent parts of the
data structure, we would need to associate a lock with each constituent
part. However acquiring a large number of locks has unacceptable overheads;
particularly noticeable when there are only a small number of threads
contending for access to the shared data. On the other hand, increasing lock
granularity would reduced the number of locks required, and in turn the
overheads associated with taking the locks, but this would also rule out
some potential for concurrency.

%}}}%

\subsection{Message Passing and Implicit Synchronisation}%{{{%

The message passing paradigm focuses on the sending of messages between
threads in the computation as a primitive, rather than the explicit use of
shared memory and mutual exclusion as a medium and protocol for
communication. Conceptually, this is a higher-level notion which abstracts
the act of sending a message from the how, leaving it to the run-time system
to choose the appropriate means. As a result, programs written using this
approach have the potential to scale from single processors to distributed
networks of multiprocessor computers.

Established languages and frameworks supporting message passing concurrency
include Erlang~\cite{armstrong96-erlang}, the Parallel Virtual Machine
(PVM)~\cite{geist94-pvm} and the Message Passing Interface
(MPI)~\cite{gropp99-mpi}. In Haskell, we can implement our previous counter
example using channels, where |Chan alpha| is the polymorphic type of
channels carrying messages of type |alpha|:
%format Action = "\type{Action}"
%format Increment = "\cons{Increment}"
%format Get = "\cons{Get}"
%format Counter_chan = "\type{Counter_{Chan}}"
\begin{code}
data Action = Increment | Get (Chan Integer)
type Counter_chan = Chan Action
\end{code}
Here we have defined a new datatype |Action| enumerating the operations the
counter supports. A counter is then represented by a channel accepting such
|Action|s, to which we can either send an |Increment| command, or another
channel on which to return the current count via the |Get| command.

% \url{http://www.kirit.com/Blog:/2007-08-09/Erlang%20as%20an%20OO%20language}

%format makeCounter_chan = "\func{makeCounter_{Chan}}"
%format increment_chan = "\func{increment_{Chan}}"
The |makeCounter_chan| function returns a channel, to which other threads may
send |Action|s to increment or query the counter:
\begin{code}
makeCounter_chan :: IO Counter_chan
makeCounter_chan = do
	counter <- newChan
	value <- newIORef 0
	forkIO . forever $ do
		action <- readChan counter
		n <- readIORef value
		case action of
			Increment -> writeIORef value (n + 1)
			Get result -> writeChan result n
	return counter
\end{code}
Even though we make use of an |IORef| to store the current count, we have
implicitly avoided the mutual exclusion problem by only allowing the forked
thread access, essentially serialising access to the mutable variable.
Implementing an |increment_chan| operation is now straightforward:
\begin{code}
increment_chan :: Counter_chan -> IO ()
increment_chan counter = writeChan counter Increment
\end{code}
If concurrent threads invoke |increment_chan| on the same counter, the
atomicity of the |writeChan| primitive rules out any unwanted interleavings.

Unfortunately, just like the previous mutual exclusion-based solution, it is
not trivial to build upon or to reuse |increment_chan|---say---to increment
two counters in lock-step.

%}}}%

\subsection{Software Transactional Memory}%{{{%

The popularity of mutual exclusion could be partially attributed to the fact
that its implementation is relatively easy to comprehend. On the other hand,
managing and composing lock-based code is rather error-prone in practice.

Automatic garbage collection frees the programmer from having to manually
manage memory allocation. Laziness in functional programming allows us to
write efficient higher-level programs without having to manually schedule
the order of computation. In a similar vein~\cite{grossman07-analogy},
software transactional memory (STM)~\cite{shavit97-stm} allows us to write
programs in a compositional style in the presence of concurrency, without
requiring us to manually manage undesired interleavings of operations in
a shared memory environment.

The idea of using \emph{transactions} to tackle concurrency originated in
the context of concurrent databases\source{Date?}, which face similar
issues of undesirable interleavings of basic operations when different
clients attempt to access the same database at the same time. Rather than
explicitly locking any requisite resources before proceeding with some
sequence of operations on shared data, the client simply informs the
database server that the operations are to be treated as a single
transaction. From the perspective of other database clients, the server
ensures that none of the intermediate states of the transaction is visible,
as if the entire transaction took place as a single indivisible operation.
Should it fail for whatever reason, the outside perspective would be as if
the transaction hadn't taken place at all.

STM implements the same concept, but with shared memory being the `database'
and individual program threads taking the r\^ole of the `clients'. STM takes
an optimistic approach to concurrency: transactions are allowed to overlap
in their execution, making the most of the available hardware. Conflicts
between transactions arise only when an earlier transaction commits a change
to a shared variable which a later transaction depended on. Should this
happen, the later one is aborted and retried. In particular, a transaction
is only aborted when another one has successfully committed, thereby
ensuring overall progress and the absence of deadlocks.

%format Counter_STM = "\type{Counter_{STM}}"
%format increment_STM = "\func{increment_{STM}}"
Under the Haskell implementation of STM, transactional computations
returning a value of type |alpha| have the type |STM alpha|. We can give an
almost identical implementation of |increment_STM| as that of
|increment_IORef|, but uses |TVar|s (\emph{transactional variables}) instead
of |IORef|s, and results in an |STM| action rather than an arbitrary |IO|
action:
\begin{code}
type Counter_STM = TVar Integer

increment_STM :: Counter_STM -> STM ()
increment_STM counter = do
	n <- readTVar counter
	writeTVar counter (n + 1)
\end{code}
To effect a transaction, we have at our disposal an |atomically| primitive,
which takes an |STM alpha| and returns a runnable |IO alpha| action. The
following program fragment increments the given counter twice.
\begin{spec}
do
	counter <- atomically (newTVar 0)
	forkIO (atomically (increment_STM counter))
	forkIO (atomically (increment_STM counter))
\end{spec}
In particular, the |atomically| primitive guarantees that the two instances
of |increment_STM| do not interleave each other in any way of consequence.

STM makes it straightforward to reuse existing code: simply sequencing two
transactions one after another creates a larger composite transaction that
increments both counters atomically when executed:
%format incrementBoth = "\func{incrementBoth}"
\begin{code}
incrementBoth :: Counter_STM -> Counter_STM -> STM ()
incrementBoth c_0 c_1 = do
	increment_STM c_0
	increment_STM c_1
\end{code}
%%Furthermore, STM Haskell provides an innovative |`orElse`| primitive which
%%provides a form of left-biased choice:
%%\begin{code}
%%incrementEither :: Counter_STM -> Counter_STM -> STM ()
%%incrementEither c0 c1 = increment_STM c0 `orElse` increment_STM c1
%%\end{code}
%%Should |increment_STM c0| abort, |incrementEither| would attempt to
%%increment the second counter instead of immediately retrying, doing so only
%%if the alternative also failed.

\noindent This section presented but a brief overview of STM. We will
examine and discuss it in more depth in Chapter \ref{ch:stm}.
% TODO: doesn't read well

%}}}%

%}}}%

%if False
\section{Approaches to Program Correctness}%{{{%

Software ought to behave how we intend it to. To this end, we would like to
establish that a given program satisfies various high-level properties.
Clearly it ought to terminate with the expected result, but there are also
other important considerations such as its time or space complexity, or that
some algorithmic invariant is always maintained. With the introduction of
concurrency, we have further properties such as freedom from deadlock and
interference to consider, and demonstrating all of these can be particularly
difficult due to the non-determinism arising from multiple threads of
control. In this section, we briefly describe a number of approaches to
program correctness that are relevant to this thesis, ranging from empirical
testing to formal verification techniques.

\subsection{Correctness Properties}%{{{%

In the realm of program semantics, we can differentiate between extensional
and intensional properties. While the distinction is not necessarily
immediately clear in all cases, in general, the former is concerned with the
end result of a program, while the latter deals with its execution
behaviour.

Two programs $p$ and $q$ that sorts lists of numbers are extensionally
equivalent, in the sense that they would produce the same output given the
same input. Intensional equality on the other hand reduces to the question
of whether $p$ and $q$ perform the same sequence of operations to obtain
their respective sorted output, i.e~if they implement the same sorting
algorithm. Other instances of extensional properties might be concerned with
program termination or complexity, while intensional properties would deal
with properties such as progress or type preservation under reduction. We
often make use of intensional reasoning to prove extensional properties of
programs: going back to the earlier question of equality, $p$ and $q$ being
intensionally equal trivially implies their extensional equality, although
the converse does not hold.


%A more pertinent example of the distinction between intensional and
%extensional is perhaps the \TODO{want to mention explicit lock-taking
%(intensional) versus lock-inference, or even transactional memory}

\TODO{Also mention operational versus denotational}

\TODO{The following makes no sense:}

Define intensional (operational) / extensional (denotational); examples:
\begin{itemize}
\item ``if program terminates, output is sorted''
\item ``program will eventually terminate''
\item ``program only uses linear time/space''
\item ``lock acquisition eventually succeeds''
\end{itemize}

%}}}%

\subsection{Calculi / logics}%{{{%

Abstract descriptions of programs\ldots

imperative programs --- Hoare logic

State transition systems --- various logics for above, e.g. CTL, LTL,
variations of modal logic

\begin{itemize}
\item Hoare -- standard for imperative programs (NB: Morrisett / Hoare State
monad)
\item modal / temporal
\item CCS / various process calculi
\end{itemize}

%}}}%

\subsection{Equational Reasoning}%{{{%

\begin{itemize}
\item FP \& purity
\item e.g. fold/unfold transformation (Burstall and Darlington)
\item e.g. Squiggol (combinator and properties) library
\item derivation vs proof
\end{itemize}

%}}}%

\subsection{Formal Proof Assistants}%{{{%

\begin{itemize}
\item Coq and Agda \&c.
\end{itemize}

%}}}%

\subsection{Empirical Testing}%{{{%

\begin{itemize}
\item unit testing / HUnit -- example based; I/O pairs
\item QC -- property-based
\item HPC
\end{itemize}

%}}}%

\begin{itemize}
\item not necessarily concurrent
\item approaches: process calculi, modal/temporal logics
\item equational reasoning \& functional programming
\item tools (Quickcheck, HPC, Agda)
\end{itemize}

%}}}%

\section{Approaches to Compiler Correctness}%{{{%

% a compiler is a program too!
\begin{itemize}
\item that triangular diagram thing
\item semantics -- denotational for sequential, operational for concurrent?
\item calculation from specification
\end{itemize}

%}}}%
%endif

\section{Thesis Overview}%{{{%

The remaining chapters of this thesis comprise of the following:
\begin{description}

\item[Chapter 2] provides additional background on the use and
implementation of transactional memory, followed by a brief primer on
STM Haskell.

\item[Chapter 3] reviews the notions of denotational, big- and small-step
operational semantics along with some reasoning techniques, illustrated
using a small language. We then present a compiler for this language and its
corresponding virtual machine, to show the essence of a compiler correctness
proof.

\item[Chapter 4] implements executable semantics for the above language as
a Haskell program. We demonstrate the use of QuickCheck in conjunction with
the Haskell Program Coverage toolkit for randomised testing of the results
established in the previous chapter.

\item[Chapter 5] puts the above empirical approach into practice, on
a simplified subset of STM Haskell with a high-level stop-the-world
semantics, linked by a compiler to a virtual machine with a log-based
implementation of transactions.

\item[Chapter 6] gently introduces the Agda proof assistant, for the purpose
of constructing formal machine-checked proofs, and culminates in a verified
formalisation of the results of chapter 3.

\item[Chapter 7] extends the notion of compiler correctness to
non-deterministic languages using our new notion of combined machines,
illustrated using the simple Zap language, for which a complete compiler
correctness result is produced and discussed.

\item[Chapter 8] scales our new technique to include explicit concurrency,
by introducing a `fork' primitive and threads. We replay the compiler
correctness proof of the previous chapter in this new setting with the help
of a few extra concurrency lemmas.

\item[Chapter 9] develops the concept of consistency between transaction
logs and the heap, which we use to establish the correctness of a log-based
implementation of software transactional memory in the presence of arbitrary
interference by an external agent.

\item[Chapter 10] concludes with a summary of this thesis, and a list of
various future research directions.

\end{description}

\noindent The reader is assumed to be familiar with functional programming
and their type systems; knowledge of Haskell would be a bonus. Relevant
ideas are introduced when appropriate, with references for further reading.

%}}}%

\section{Contributions}%{{{%

The contributions of this thesis are as follows:
\begin{itemize}

\item Identification of a simplified subset of STM Haskell with a high-level
stop-the-world semantics for transactions.

\item A virtual machine for this language, in which transactions are
implemented following a low-level log-based approach, along with a semantics
for this machine.

\item A compiler linking the language to the virtual machine with
a statement of compiler correctness, empirically tested using QuickCheck and
HPC.

\item The core idea of a combined machine and semantics, that allows us to
establish a direct bisimulation between the high-level language and the
low-level virtual machine.

\item Putting the above technique into practice using the Agda proof
assistant, giving a formal compiler correctness proof for a language with
a simple notion of non-determinism.

\item Showing that our technique scales to a language with explicit
concurrency, complete with a formal proof.

\item A formal correctness proof for a transactional language that shows the
equivalence of the log-based approach and the stop-the-world semantics for
transactions.

\end{itemize}
Earlier accounts of some of these have been published in the following
papers,
\begin{itemize}

\item Liyang HU and Graham Hutton~\cite{hu08-verified}. ``Towards a Verified
Implementation of Software Transactional Memory''. In \emph{Proceedings of
the Symposium on Trends in Functional Programming}. Nijmegen, The
Netherlands, May 2008.

\item Liyang HU and Graham Hutton~\cite{hu09-concurrency}. ``Compiling
Concurrency Correctly: Cutting Out the Middle Man''. In \emph{Proceedings of
the Symposium on Trends in Functional Programming}. Kom\'arno, Slovakia,
June 2009.

\end{itemize}
but have since been refined and expanded upon in this thesis.

The complete source code to this thesis, in the form of literate Haskell and
Agda documents, may be found online at \url{http://liyang.hu/#thesis}~.

%}}}%

% vim: ft=tex:

