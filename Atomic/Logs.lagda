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

\subsection{Transaction Logs and Consistency}\label{sec:atomic-logs}

%format Logs = "\type{Logs}"
%format Logs.Logs = "\type{Logs}"
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
%format & = "\infix{\cons{{\texttt\&}}}"
%format _&_ = "\cons{\anonymous{\texttt\&}\anonymous}"
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

%format _«_» = "\func{\anonymous\!\texttt[\anonymous\texttt]}"
%format « = "\prefix{\func{\!\texttt[\!}}"
%format »≔ = "\postfix{\func{\!\texttt]\!{:}{=}}}"
%format » = "\postfix{\func{\!\texttt]\!}}"
%if False
\begin{code}
infix 8 _«_»≔_
infix 9 _«_»
_«_»≔_ : {α : Set} {N : ℕ} → Vec α N → Fin N → α → Vec α N
_«_»≔_ = Vec._[_]≔_

_«_» : {α : Set} {N : ℕ} → Vec α N → Fin N → α
_«_» = flip Vec.lookup
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
Read h (ρ & ω) v with ω « v »
... |  ● m = ρ & ω , m
... |  ○ with ρ « v »
...    | ● m = ρ & ω , m
...    | ○ = ρ « v »≔ ● m & ω , m where m = h « v »
\end{code}
If a variable has been written to according to |ω|, we immediately return
the new value. Otherwise we consult the read log |ρ|: if a previous value
for |v| exists, we return that. In both cases the transaction logs remain
unchanged. Only when no cached value for |v| exists---that is, when we are
reading a variable for the first time---do we update the read log |ρ| with
the value of |v| from the current heap. Note that if a variable is written
to before it is read, the corresponding read log entry will never be filled.

%format Consistent = "\type{Consistent}"
%format ∅-Consistent = "\func{\varnothing\text-Consistent}"
On reaching the end of a transaction we either commit or roll back,
depending on whether the values of the variables gleaned from the heap
during the transaction are consistent with their corresponding values at the
end. That is, all values recorded in the read log must match those currently
in the heap for corresponding variables. The following predicate allows us
to state this succinctly:
\begin{code}
Consistent : Heap → Logs → Set
Consistent h (ρ & _) = ∀ v m → ρ « v » ≡ ● m → h « v » ≡ m
\end{code}
A read log |ρ| is consistent with the heap |h| precisely when all non-empty
entries in |ρ| have the same values as the corresponding entries in |h|.
Note that a transactional variable that is written to before being read from
will not have a corresponding entry in |ρ|; this is acceptable since its
original value in the heap could not possibly have influenced the behaviour
of the transaction. Naturally the empty log |∅| is consistent with any heap:
\begin{code}
∅-Consistent : ∀ {h} → Consistent h ∅
∅-Consistent v m rewrite Vec.lookup∘replicate v (○ ∶ Maybe ℕ) = λ ()
\end{code}
The above uses the |Vec.lookup∘replicate| function to obtain a proof that
the entry for |v| in the newly-initialised read log is |○|, in which case we
can use an absurd lambda to eliminate the |○ ≡ ● m| argument.

%format Consistent? = "\func{Consistent?}"
%format ¬p = "\Varid{\lnot{}p}"
%format dec = "\func{dec}"
%format h«v» = "\Varid{h_v}"
%format ρ«v» = "\Varid{\rho_v}"
%format h«v»≡n = "\Varid{h_v{\equiv}n}"
%format h«v»≢n = "\Varid{h_v{\not\equiv}n}"
The |Dec P| type corresponds to the decidability of some proposition |P|. It
has two constructors |yes| and |no|, carrying the appropriate evidence in
either case:
\begin{spec}
data Dec (P : Set) : Set where
  yes  : ( p  :    P) → Dec P
  no   : (¬p  : ¬  P) → Dec P
\end{spec}
Thus an element of |Dec P| is strictly more informative than a boolean
value. Using this, we can give a decision procedure for whether a given heap
and read log are indeed consistent. This is implemented below as
|Consistent?|, via the |dec| helper that decides consistency for one
particular variable:
\begin{code}
Consistent? : (h : Heap) (l : Logs) → Dec (Consistent h l)
Consistent? h (ρ & ω) =  Dec.map′ Vec.Pointwise.app Vec.Pointwise.ext
                         (Vec.Pointwise.decidable dec h ρ) where
  dec : (h«v» : ℕ) (ρ«v» : Maybe ℕ) → Dec (∀ m → ρ«v» ≡ ● m → h«v» ≡ m)
  dec h«v» ○ = yes (λ m ())
  dec h«v» (● n) with h«v» ≟ℕ n
  ... | yes h«v»≡n rewrite h«v»≡n = yes (λ m → ●-inj)
  ... | no h«v»≢n = no (λ p → h«v»≢n (p n ≡.refl))
\end{code}
The library fuctions |Dec.map′| and |Vec.Pointwise.decidable| are used to
generalise the pointwise decision procedure over all variables.

%format Update-lookup = "\func{Update\text-lookup}"
%format Update = "\func{Update}"
Finally when a transaction is ready to commit, we can use the |Update|
function to commit the contents of the write log to the heap:
\begin{code}
Update-lookup : Heap → Logs → Variable → ℕ
Update-lookup h (ρ & ω) v = maybe id (h « v ») (ω « v »)

Update : Heap → Logs → Heap
Update h l = Vec.tabulate (Update-lookup h l)
\end{code}
This is implemented using the library function |Vec.tabulate| that takes
a function that gives the new value for each index or variable. We have
factored out |Update-lookup| in order to leverage existing proofs in the
standard library.

% vim: ft=tex fo-=m fo-=M:
