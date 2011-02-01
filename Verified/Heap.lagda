%if False
\begin{code}
import Level
open import Common

module Verified.Heap where

Heap′ : ℕ → Set
Heap′ = Vec ℕ
\end{code}
%endif

\subsection{Heaps, Variables and Logs}\label{sec:verified-heap}

%format ∣Heap∣ = "\func{{|}Heap{|}}"
Recall that previously in chapter \ref{ch:model}, we modelled the heap as
a total map from a fixed set of variable names to their values, initialised
to zero. In Agda, we can realise this using the indexed |Vec| type
(\S\ref{sec:agda-dependent}) from the standard library. As our proof is to
be independent of the heap size, we simply postulate a number |∣Heap∣|,
\begin{code}
postulate ∣Heap∣ : ℕ
\end{code}
%format Heap = "\func{Heap}"
%format initHeap = "\func{initHeap}"
with the |Heap| type defined and initialised as follows:
\begin{code}
Heap : Set
Heap = Vec ℕ ∣Heap∣

initHeap : Heap
initHeap = Vec.replicate 0
\end{code}
%format Variable = "\func{Variable}"
Correspondingly, a |Variable| is just a synonym for the finite set
(\S\ref{sec:agda-dependent}) with |∣Heap∣| distinct elements:
\begin{code}
Variable : Set
Variable = Fin ∣Heap∣
\end{code}

%if False
\begin{code}
Log′ : ℕ → Set
Log′ = Vec (Maybe ℕ)

newLog′ : ∀ {N} → Log′ N
newLog′ = Vec.replicate nothing
\end{code}
%endif

\noindent Transaction logs on the other hand are modelled as partial maps
from variables to numbers, where an entry for a variable is created only
when it has been read from or written to. We can use the same approach as
with heaps, using a vector of |Maybe ℕ| initialised to |nothing| instead:
%format Log = "\func{Log}"
%format newLog = "\func{newLog}"
\begin{code}
Log : Set
Log = Vec (Maybe ℕ) ∣Heap∣

newLog : Log
newLog = Vec.replicate nothing
\end{code}

%format « = "\prefix{\func{\!\texttt[}}"
%format » = "\postfix{\func{\texttt]\!}}"
%format _«_» = "\func{\anonymous\index[\anonymous]}"
%format »≔ = "\infix{\func{\texttt]\!{:}{=}}}"
%format _«_»≔_ = "\func{\anonymous\index[\anonymous]{:}{=}}"
%if False
\begin{code}
-- I've run out of distinct bracket symbols.
-- Also, lhs2TeX refuses to see [] as a single symbol.
-- 〖 and 【 display as double-width in terminal. :(
infix 6 _«_»
_«_» : ∀ {X N} → Vec X N → Fin N → X
xs « v » = Vec.lookup v xs
\end{code}
%endif

%format lookupTVar = "\func{lookupTVar}"
During a running transaction, a pair of read (|ρ|) and write (|ω|) logs
keeps track of any heap updates. The |lookupTVar| gives the in-transaction
value of a variable, taking the outer heap and the pair of logs as
arguments:
\def\lookupTVarSig#1{|Heap → Log → Log → Variable → ℕ|}
\begin{code}
lookupTVar : {-"\lookupTVarSig{"-}∀ {N} → Heap′ N → Log′ N → Log′ N  → Fin N → ℕ{-"}"-}
lookupTVar h ρ ω v with ω « v »
lookupTVar h ρ ω v | just m = m
lookupTVar h ρ ω v | nothing with ρ « v »
lookupTVar h ρ ω v | nothing | just m = m
lookupTVar h ρ ω v | nothing | nothing = h « v »
\end{code}
If a variable has been updated according to |ω|, we immediately return the
new value. Otherwise we consult the read log |ρ|: if there is a previously
cached value for |v|, then return that; if not, then look it up from the
heap.

%format update-rLog = "\func{update\text-\!\rho}"
When reading a variable within a transaction for the first time, we also
need to update the read log, when certain conditions are met. This task is
fulfilled by the following |update-rLog| function:
\begin{code}
update-rLog : Heap → Log → Log → Variable → Log
update-rLog h ρ ω v with ω « v »
update-rLog h ρ ω v | just m = ρ
\end{code}
An entry in |ω| means that |v| has previously been written to, in which case
we return |ρ| unchanged---even if |v| has never been read from---as the
written value logged in |ω| takes precedence. If |ω « v »| is |nothing| on
the other hand, we proceed to inspect |ρ|:
\begin{code}
update-rLog h ρ ω v | nothing with ρ « v »
update-rLog h ρ ω v | nothing | just m = ρ
update-rLog h ρ ω v | nothing | nothing = ρ « v »≔ just (h « v »)
\end{code}
The former of the two |with ρ « v »| clauses handles the case where
a previous read had already logged |m| as the heap value of |v|, so we may
return |ρ| as it is. The latter corresponds to an initial read of |v| within
a transaction with no preceding writes to it, in which case we update |ρ|
with the value of |v| from the current heap.

% vim: ft=tex fo-=m fo-=M:

