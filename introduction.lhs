%include polycode.fmt
%include local.fmt

%format n_A
%format n_B
%format increment_lock

\chapter{Introduction}

\section{Preface}%{{{%

\TODO{What's supposed to go here anyway? Extended abstract?}

%}}}%

\section{Background}%{{{%

\subsection{A Brief Note on `Moore's Law'}%{{{%

Since the invention of the integrated circuit over 50 years ago and the
subsequent development of the microprocessor, the \emph{number of
transistors} that engineers can manufacture on a single silicon chip per
unit cost has been increasing at an exponential pace, roughly doubling every
two years. This growth has been remained consistent, so much so that it has
been informally codified as `\emph{Moore's
Law}'\source{http://www.intel.com/technology/mooreslaw/}. The related but
misattributed\source{actually by David House} statement that ``microprocessors
\emph{performance} roughly doubles every 18 months'' has also held true,
once we factor in the increased performance of individual transistors.

On the other hand, the popular understanding of `Moore's Law' tend to be
simplified to ``computer speed roughly doubles every 18 months.'' Until half
a decade ago, this alternative but technically incorrect interpretation has
sufficed, since in order to pack more transistors next to each other, each
one had to be made smaller. This in turn meant faster signal propagation
between components, and so faster switching (or clock speeds), increasing
performance. The implication of this (mis-)interpretation is that one could
expect the same piece of software to run twice as fast on the available
hardware, 18 months down the line.

%TODO: yeah sure, but what about asynchronous processors?
% There's too much legacy investment in traditional processor designs\ldots


%}}}%

\subsection{The End of the Free Lunch}%{{{%

%While the individual processor speeds eventually plateaued at $3$--$4$ GHz
%over the last decade, the transistor count per chip carried on doubling with
%barely a blip, with the trend set to continue for the foreseeable future.

Moore's Law---including its misinterpretation---had become self-perpetuating
as the industry assumed its truth to make projections for their technology
roadmaps. By shrinking the size of individual transistors, not only were the
manufacturers able to increase how many transistors that can be economically
placed on a single piece of silicon, they were also able to clock their
processors at higher frequencies due to reduced switching and signal
propagation times.

Sadly miniaturisation has some undesirable side-effects: on the sub-micron
scales of a modern microprocessor, current leakage due to quantum tunnelling
across the on-chip insulation is very much detrimental to signal integrity:
the smaller the features, the more power the integrated circuit requires to
counteract these side-effects. This additional power must be dissipated in
the form of waste heat, limiting the extent to which we can simply crank up
the clock speed. Indeed, some \emph{desktop} processors expended up to
a third\source{http://www.anandtech.com/printarticle.aspx?i=3276} of their
entire power budget solely to ensure accurate clock signal distribution to
outlying areas of the same silicon die, and gave out as much as
$150\text{W}$ of heat in an area less than $15\text{mm}^2$.

Given the restriction that we cannot reasonably clock individual processors
at increasingly higher speeds, how could we pack more compute power onto
each silicon die? The most obvious and easiest solution is to resort to
symmetric multiprocessing (SMP), and use the extra transistors afforded to
us by Moore's Law to fabricate multiple processors on the same die, packaged
as a single unit.

%}}}%

\subsection{A Brief Look at Parallel Computing}%{{{%

The concept of SMP had been put to practice as early as the 1960s with the
introduction of the Burroughs B5500
mainframe\source{https://wiki.cc.gatech.edu/folklore/index.php/Burroughs_Third-Generation_Computers}.
In the decades that followed, the entire computing industry resorted one by
one to some form of parallelism---typically at a architecturally fundamental
level---in order to achieve the stated performance. First steps in this
regard included the development of vector processors, where each single
instruction can operate on multiple pieces of data (SIMD in today's
parlance), often in the tens or perhaps hundreds.

In contrast, a multiple-instruction-multiple-data (\TODO{acronym!}MIMD)
architecture comprise a number of independent processing units, each
concurrently executing its own sequence of instructions. However,
programming for multiprocessing systems is a task fraught with pitfalls, as
Seymour Cray once quipped: ``If you were ploughing a field, which would you
rather use: two strong oxen or 1024 chickens?'' His remark alludes to the
challenge of synchronising a large number of independent processors with
each one working on a small part of a larger problem while sharing the same
working memory. It is much easier for people to work with two oxen than to
try and herd 1024 chickens.

Multiprocessing systems are therefore suited to domains involving extremely
large datasets and have intrinsically parallelisable solutions that do not
require much synchronisation. This closely correlates with the majority of
scientific computation problems, and the insatiable demand for computational
power drove the development of massively parallel computers in the decades
that followed. Even Cray eventually had to concede to the fact that
multiprocessing was inevitable, as the costs and resources required to breed
and feed the two hypothetical oxen became prohibitive compared to breeding,
feeding and herding 1024 chickens, to continue the earlier analogy.

Meanwhile, as multiprocessor computers grew increasingly larger, it became
difficult to maintain fast access to the same shared memory for all
processor nodes. Cutting-edge systems therefore moved towards a more
non-uniform memory architecture (NUMA), where each node had fast access to
some local pool of memory, but slower access to globally shared data. The
lessons learnt from evolution has strongly influenced the design today's
high-performance hardware, even in the context of personal computing, as
seen with the recent development of general-purpose graphical processing
units (GPGPUs). On a more distributed and larger scale, Beowulf clusters of
networked computers may be seen as a looser interpretation of the NUMA
paradigm. Such systems typically form the workhorse behind many of today's
large-scale scientific simulations, at least in part due to the fact that
they can be and often are built from cheap and readily available commodity
hardware.

%}}}%

\subsection{A Supercomputer on Every Desk}%{{{%

Moving back to the sphere of everyday IT and personal computing, it was not
until the last decade that shared memory SMP computers managed to establish
a presence. The explanation for its relative obscurity is twofold, yet
complementary: on the one hand, the cost of motherboards that can
accommodate multiple processor packages were significantly more expensive,
and so were only sought after by users with specialist needs. On the other,
the inability for predominantly single-threaded software---such as a game or
a word-processor---to take advantage of multiple processors meant that the
proletarian user had no interest in resorting to SMP; simply waiting another
18 months had been sufficient.

However as raw processor speeds have plateaued in recent years, we can no
longer afford to dismiss multiprocessor systems as being too difficult to
program for. Traditionally supercomputing problems---large-scale,
loosely-coupled computations such as physical simulations or graphical
rendering---have been well-catered for, but they encompass only a small
fraction of our day-to-day software usage. We need to figure out how to make
concurrency accessible and manageable for everyday software, and I hope this
monograph makes a small contribution towards how we might safely and
correctly achieve that goal.

%}}}%

%}}}%

% Parallelism?

\section{Approaches to Concurrent Software}%{{{%

We resort to concurrency with the hope that the more computational power we
throw in to the mix, the faster our programs will run. How successfully this
scales in practice depends on how much concurrency we can exploit in our
programs. How we model concurrency has a large influence on how we---as
software engineers---think and reason about our concurrent programs, which
in turn influences the ease with which we can exploit concurrency. I will
begin this chapter by giving some intuition of why concurrent programming
has such a notorious reputation, then review some of the basic models of
concurrency.

% main interest: tapping in to the power of concurrency for personal
% computing

\subsection{Concurrency versus Parallelism}%{{{%

In general computing literature, the terms `concurrency' and `parallelism'
are often taken as synonyms and used interchangeably by many, while others
make a clear distinction between the two. I will afford a few sentences to
clarify what I mean by each, in the context of this monograph.

By \emph{parallelism}, I mean  \TODO{Write this when you're more awake.
Vaguely remember an elegant phrasing of this distinction, from ICFP
perhaps?}

The focus of this thesis is on explicit concurrency.

%}}}%

\subsection{Example: Easy as 0, 1, 2, 3\ldots}%{{{%

Consider the simple example of incrementing a counter variable. The
algorithm---to somewhat overstate its complexity---might read like the
following:
\begin{spec}
increment counter = do
	n <- read counter
	write counter (n + 1)
\end{spec}
When only a single instance of |increment| is executing, the above code
behaves as expected. Suppose however, that two instances of |increment| were
executing at the same time. This results in four possible interleavings of
the two |read| and |write| operations, not all of which would have the
intended effect of incrementing the counter twice, for example:
\begin{longtable}{l||l||c}%{{{%
Thread A & Thread B & |counter| \\
\hline
|n_A <- read counter|
	&
		& 0 \\
	& |n_B <- read counter|
		& 0 \\
	& |write counter (n_B + 1)|
		& 1 \\
|write counter (n_A + 1)|
	&
        & 1
\end{longtable}%}}}%

\noindent Typically, reading from and writing to a mutable variable are
relatively fast primitive operations, so when they take place in immediate
succession, the odds of Thread A being interleaved by Thread B in the above
manner is unlikely, and can easily slip through seemingly thorough empirical
testing. Such errors are termed \emph{race conditions}, and can occur
whenever there is the possibility of concurrent access to any shared
resource.

%}}}%

\subsection{Shared Memory and Mutual Exclusion}%{{{%

The current market leader in terms of preventing the kind of race conditions
as we have seen in the previous section is to simply prevent concurrent
accesses to the shared resource. A variety of names are used for such
techniques---locks, semaphores, critical sections, mutexes---all of which
are based on the principle of mutual exclusion.

Without discussing implementation details, let us assume the existence of
two indivisible primitives---|lock| and |release|---with the following
behaviour: |lock| attempts to acquire exclusive access to a given mutable
variable; if the variable is already locked, wait until it becomes available
before proceeding. Its counterpart |release| relinquishes the exclusivity
previously obtained.

We can now eliminate the earlier race condition as follows:
\begin{spec}
increment_lock counter = do
	lock counter
	increment counter
	release counter
\end{spec}
Even if Thread A were interleaved mid-way, Thread B cannot proceed past the
|lock| primitive until Thread A releases |counter|, ruling out the earlier
race condition:
\begin{longtable}{l||l||c}%{{{%
Thread A & Thread B & |counter| \\
\hline
|lock counter|
	&
		& 0 \\
|n_A <- read counter|
	&
		& 0 \\
	& |lock counter|
		& 0 \\
|write counter (n_A + 1)|
	& \multirow{2}{*}{\parbox[c]{19ex}{\emph{%
		\vdots\\[-1.5ex]
		blocked on |counter|\\[-1.5ex]
		\vdots%
	}}}
        & 1 \\
|release counter|
	&
        & 1 \\
	& |n_B <- read counter|
		& 1 \\
	& |write counter (n_B + 1)|
		& 2 \\
	& |release counter|
		& 2
\end{longtable}%}}}%

\noindent Such two-state locks can be generalised to n states with
\emph{counting semaphores} where some limited concurrent sharing may take
place, or to two-stage read/write locks in the case where we wish to allow
concurrent reading---but not modification---of the shared variable.

%}}}%

\subsection{Example: Deadlock}%{{{%

Let us consider a slightly more interesting example: we are required to
implement a procedure to increment two given counters in lock-step. The
following is a non-solution,
%format increment_pair
%format c_0
%format c_1
%format n_0
%format n_1
\begin{spec}
increment_pair c_0 c_1 = do
	increment_lock c_0
	increment_lock c_1
\end{spec}
as there is an intermediate state between the two calls to |increment_lock|
when neither |c_0| nor |c_1| is locked. A better implementation might lock
both counters before incrementing:
\begin{spec}
increment_pair c_0 c_1 = do
	lock c_0
	lock c_1
	increment c_0
	increment c_1
	release c_0
	release c_1
\end{spec}
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
	\emph{\vdots\\[-1.5ex]blocked on |c_1|\\[-1.5ex]\vdots}}}
	& \multirow{2}{*}{\parbox[c]{14ex}{%
		\emph{\vdots\\[-1.5ex]blocked on |c_0|\\[-1.5ex]\vdots}}}
\end{longtable}%}}}%
\noindent Neither thread can make progress, as they attempt to acquire
a lock on the counter which is being held by the other. This could be solved
by always acquiring locks in a specific order, but enforcing this is not
always straightforward.

Correctness considerations aside, there are the two issues of code reuse and
scalability to consider. In terms of the former, ideally we would not want
to expose |increment|, as only |increment_lock| is safe for concurrent use.
On the other hand, to build more complex operations on top of the basic
`increment' operation, chances are that we would need access to the unsafe
|increment| implementation. Unfortunately exposing this breaks the
abstraction barrier, with nothing to enforce the safe use of |increment|
other than trust and diligence on the part of the programmer.

On the issue of scalability, there is also some tension regarding lock
granularity, inherent to mutual-exclusion. Supposing we have a large shared
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
threads in the computation as a primitive, shunning the explicit use of
shared memory and mutual exclusion as a medium and protocol respectively for
communication. Conceptually, this is a higher level notion which abstracts
the act of sending a message from the how, leaving it to the run-time system
to choose the appropriate means. As a result, programs written using this
approach can scale naturally from single processors to distributed networks
of multiprocessor computers.

Established languages and frameworks supporting message passing concurrency
include Erlang, the Parallel Virtual Machine (PVM), or the Message Passing
Interface (MPI). In Haskell, we can implement our previous counter example
using channels:
\begin{comment}%{{{%
\begin{code}
module Main where

import Prelude
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad
import Data.IORef
\end{code}
\end{comment}
%}}}%
%format increment_chan
\begin{code}
data Action = Increment | Get (Chan Integer)
type Counter = Chan Action
\end{code}
Here we have defined a new datatype |Action| enumerating the operations the
counter supports. A counter is then represented by a channel accepting such
|Action|s, to which we can either send an |Increment| command, or another
channel on which to return the current count via the |Get| command.

The |makeCounter| function returns a channel, to which other threads may
send |Action|s to increment or query the counter. Even though we do make use
of an |IORef| to store the current count, we have implicitly avoided the
mutual exclusion problem by only allowing the forked thread access,
essentially serialising access to the mutable variable.
\begin{code}
makeCounter :: IO Counter
makeCounter = do
	counter <- newChan
	value <- newIORef 0
	forkIO $ forever $ do
		action <- readChan counter
		n <- readIORef value
		case action of
			Increment -> writeIORef value (n + 1)
			Get result -> writeChan result n
	return counter

increment_chan :: Counter -> IO ()
increment_chan counter = writeChan counter Increment
\end{code}
When concurrent threads invoke |increment_chan| on the same counter, the
atomicity of the |writeChan| primitive rules out any unwanted interleavings
as we had with the original implementation of |increment|.

Unfortunately, just like the previous mutual exclusion-based solution, it is
non-trivial to build upon and not possible to reuse |increment_chan|, say,
to implement a function to increment two counters in lock-step.

%}}}%

\subsection{Software Transactional Memory}%{{{%

The popularity of mutual exclusion could be partially attributed to the fact
that its implementation is relatively easy to comprehend. On the other hand,
managing and composing lock-based code is extremely error-prone in practice.

Automatic garbage collection\source{Dan Grossman} frees the programmer from
having to manually manage memory allocation. Laziness in functional
programming allows us to write higher-level programs without having to
manually schedule the order of computation. In a similar vein, software
transactional memory (STM) gives us a way to mark any composite operation as
being atomic, without requiring us to manually manage undesired
interleavings of operations in a shared memory environment.

%}}}%

%}}}%

\section{Approaches to Program Correctness}%{{{%



%}}}%

\section{Approaches to Compiler Correctness}%{{{%

% a compiler is a program too!

%}}}%


\cite{hu08-verified}
\cite{hu09-concurrency}

% vim: ft=tex:

