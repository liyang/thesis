%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
\end{comment}
%endif

%if False
\begin{code}
module Logs where

open import Common
open import Heap
\end{code}
%endif

%if False
\begin{code}
infix 5 _&_
\end{code}
%endif

\subsection{Transaction Logs}

%format Logs = "\type{Logs}"
%format Logs.ρ = "\func{Logs.\rho}"
%format Logs.ω = "\func{Logs.\omega}"
%format ∅ = "\func{\varnothing}"
Before we give the log-based semantics for |atomic| blocks, let us first
define what transaction logs are. Recall from chapter \ref{ch:model} that we
modelled them as partial maps from variables to numbers, where an entry for
a variable exists only when it has been read from or written to. We take
a similar approach to |Heap|s, using vectors of |Maybe ℕ|\footnote{For
aesthetic reasons I have renamed |nothing| and |just| of |Maybe| to |○| and
|●| respectively.} initialised to |○|:
%format & = "\infix{\cons{{\&}}}"
%format _&_ = "\cons{\anonymous{\&}\anonymous}"
%{
%format ρ = "\name{\rho}"
%format ω = "\name{\omega}"
\begin{code}
record Logs : Set where
  constructor _&_
  field
    ρ {-"\;"-} ω : Vec (Maybe ℕ) ∣Heap∣

∅ : Logs
∅ = Vec.replicate ○ & Vec.replicate ○
\end{code}
The |ρ| and |ω| fields of a |Logs| record correspond to the read and write
logs of chapter \ref{ch:model}, and are used in an identical manner to keep
track of variables during a running transaction. Let us quickly review the
rules for log-based writes and reads in the the context of the current
chapter.
%}

%format « = "\prefix{\func{\!\texttt[\!}}"
%format »≔ = "\postfix{\func{\!\texttt]\!{:}{=}}}"
%if False
\begin{code}
infix 8 _«_»≔_
_«_»≔_ : {α : Set} {N : ℕ} → Vec α N → Fin N → α → Vec α N
_«_»≔_ = Vec._[_]≔_
\end{code}
%endif

%format Write = "\func{Write}"
Writing to a transaction variable is the most straightforward of the two
operations, and is implemented by the following |Write| function that
returns a new pair of logs with the entry for |v| in |ω| updated to the new
value |m|.
\begin{code}
Write : Logs → Variable → ℕ → Logs
Write (ρ & ω) v m = ρ & ω « v »≔ ● m
\end{code}

%format Read = "\func{Read}"
\noindent The |Read| function on the other hand takes a heap, a pair of logs
and a variable as arguments, and returns a potentially modified read log
along with the in-transaction value of the variable:
\begin{code}
Read : Heap → Logs → Variable → Logs × ℕ
Read h (ρ & ω) v with Vec.lookup v ω
... |  ● m = ρ & ω , m
... |  ○ with Vec.lookup v ρ
...    | ● m = ρ & ω , m
...    | ○ = ρ « v »≔ ● m & ω , m where m = Vec.lookup v h
\end{code}
If a variable has been written to according to |ω|, we immediately return
the new value. Otherwise we consult the read log |ρ|: if a previous value
for |v| exists, we return that. In both cases the transaction logs remain
unchanged. Only when no cached value for |v| exists---that is, when we are
reading a variable for the first time---do we update the read log |ρ| with
the value of |v| from the current heap. Note that if a variable is written
to before it is read, the corresponding read log entry will never be filled.

%format Update-lookup = "\func{Update\text-lookup}"
%format Update = "\func{Update}"
Finally when a transaction is ready to commit, we can use the |Update|
function to commit the contents of the write log to the heap:
\begin{code}
Update-lookup : Heap → Logs → Variable → ℕ
Update-lookup h (ρ & ω) v = maybe id (Vec.lookup v h) (Vec.lookup v ω)

Update : Heap → Logs → Heap
Update h l = Vec.tabulate (Update-lookup h l)
\end{code}
This is implemented using the library function |Vec.tabulate| that takes
a function that gives the new value for each index or variable. We have
factored out |Update-lookup| in order to leverage existing proofs in the
standard library.

% vim: ft=tex fo-=m fo-=M:
