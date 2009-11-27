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

The meaning of the terms \emph{concurrency} and \emph{parallelism} are not
very well defined, and vary widely from one writer to another. To make clear
the focus of this thesis, I shall clarify their intended meanings in the
context of this monograph.

\TODO{Write this when you're more awake. Vaguely remember an elegant
phrasing of this distinction, from ICFP perhaps?}

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

\subsection{Mutual Exclusion}%{{{%

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
	n <- read counter
	write counter (n + 1)
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
	& \multirow{2}{*}{\parbox[c]{7ex}{\emph{%
		\vdots\\[-1.5ex]
		blocked\\[-1.5ex]
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
	n_0 <- read c_0
	n_1 <- read c_1
	write c_0 (n_0 + 1)
	write c_1 (n_1 + 1)
	release c_0
	release c_1
\end{spec}
While this version ensures that the two counters are updated together, it
however suffers from a more subtle problem. If two threads A and B both
attempt to increment the same pair of counters, but passed to
|increment_pair| in the opposite order, a potential deadlock situation
occurs.

\TODO{picture}

Correctness considerations aside, there is the further issue of code
reusability.


%}}}%

\subsection{Message Passing}%{{{%

%}}}%

\subsection{Process Calculus}%{{{%

%}}}%

\subsection{Software Transactional Memory}%{{{%

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

