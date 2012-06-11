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
infix 5 _∧_
\end{code}
%endif

%format Logs = "\type{Logs}"
%format Logs.ρ = "\func{Logs.\rho}"
%format Logs.ω = "\func{Logs.\omega}"
%format ∅ = "\func{\varnothing}"
\noindent Transaction logs on the other hand are modelled as partial maps
from variables to numbers, where an entry for a variable is created only
when it has been read from or written to. We can use the same approach as
with heaps, using vectors of |Maybe ℕ| initialised to |nothing| instead:
%{
%format ρ = "\name{\rho}"
%format ω = "\name{\omega}"
\begin{code}
record Logs : Set where
  constructor _∧_
  field
    ρ {-"\;"-} ω : Vec (Maybe ℕ) ∣Heap∣

∅ : Logs
∅ = Vec.replicate ○ ∧ Vec.replicate ○
\end{code}
The |ρ| and |ω| fields of |Logs| correspond to the read and write logs of
chapter \ref{ch:model}, and are used in an identical manner to keep track of
variables during a running transaction.
%}

%format « = "\prefix{\func{\!\texttt[}}"
%format »≔ = "\postfix{\func{\texttt]\!{:}{=}}}"
%if False
\begin{code}
infix 8 _«_»≔_
_«_»≔_ : {α : Set} {N : ℕ} → Vec α N → Fin N → α → Vec α N
_«_»≔_ = Vec._[_]≔_
\end{code}
%endif

%format Write = "\func{Write}"
The rule for writing to a transaction variable is the simplest of the two,
and is implemented by a |Write| function that returns a new pair of logs
with the entry for |v| in |ω| updated to the new value |m|.
\begin{code}
Write : Logs → Variable → ℕ → Logs
Write (ρ ∧ ω) v m = ρ ∧ ω « v »≔ ● m
\end{code}

%format Read = "\func{Read}"
The |Read| function on the other hand takes a heap, a pair of logs and
a variable as arguments, and returns a potentially modified read log along
with the in-transaction value of the variable:
\begin{code}
Read : Heap → Logs → Variable → Logs × ℕ
Read h (ρ ∧ ω) v with Vec.lookup v ω
... | ● m = ρ ∧ ω , m
... | ○ with Vec.lookup v ρ
...   | ● m = ρ ∧ ω , m
...   | ○ = ρ « v »≔ ● m ∧ ω , m where m = Vec.lookup v h
\end{code}
If a variable has been written to according to |ω|, we immediately return
the new value. Otherwise we consult the read log |ρ|: if a previous value
for |v| exists, we return that. In both cases the transaction logs remain
unchanged. Only when no cached value for |v| exists---that is, we are
reading a variable for the first time---do we update the read log |ρ| with
the value of |v| from the current heap. Note that with this definition of
|Read|, if a variable is written to before it is read, the corresponding
read log entry will never be filled.

%if False
\begin{code}
Update : Heap → Logs → Heap
Update h (ρ ∧ ω) = Vec.tabulate (λ v → Maybe.from (Vec.lookup v h) (Vec.lookup v ω))
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:
