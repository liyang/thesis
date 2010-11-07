%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Language.lagda
%include Verified/Commit.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Verified.Lemmas where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language
open import Verified.Commit as Commit

\end{code}
%endif

%Proposition:
%\begin{spec}
%  IO ‣ h ∧ atomic e ↦‹ ☢ (ρ ∧ ω) › h′ ∧ # m → update h ω ≡ h′
%\end{spec}
%PS: why do we emit the read log at all?

\section{Reasoning Transactionally}

In this section, we will cover some useful lemmas concerning heaps and
transaction logs that are used to show that the stop-the-world transaction
semantics of the expression language corresponds to the log-based
transaction semantics of the virtual machine.

\subsection{Equivalence}%{{{%

%format Equivalent = "\func{Equivalent}"
To start off, recall that a pair of read and write logs is used give an
local view of the heap within transactions on the virtual machine. For our
compiler correctness proof, it will be convenient to define a predicate
stating that the view of the heap within and throughout a transaction---that
is, |h| overlaid with read and write logs---is equivalent to a heap |h′|
that is accessed directly using the stop-the-world semantics of the
expression language:
\def\EquivalentSig#1{|Heap → Heap → Log → Log → Set|}
\begin{code}
Equivalent : {-"\EquivalentSig{"-}∀ {N} → Heap′ N → Heap′ N → Log′ N → Log′ N → Set₀{-"}"-}
Equivalent h′ h ρ ω = ∀ v → lookupTVar h ρ ω v ≡ h′ « v »
\end{code}
That is for any variable, |lookupTVar h ρ ω| gives the same result as
looking it up directly from |h′|.

On commencing a transaction, both read and write logs are initialised to
|newLog| by the |BEGIN| instruction, while the heaps according to both
semantics have yet to diverge. The following definition shows that every
heap |h| is equivalent to itself overlaid with a pair of empty logs:
%format Equivalent-refl = "\func{Equivalent\text-refl}"
%format newLog≡nothing = "\func{newLog{\equiv}}"
%format replicate-get = "\func{replicate\text-get}"
%if False
\begin{code}
mutual
\end{code}
%endif
\begin{code}
  Equivalent-refl : ∀ {h} → Equivalent h h newLog newLog
  Equivalent-refl v rewrite replicate-get v {Maybe ℕ} {nothing}
    | replicate-get v {Maybe ℕ} {nothing} = ≡.refl
\end{code}
The two |rewrite| clauses correspond to showing that the new write and read
logs are always empty, making use of the |replicate-get| lemma showing that
every element of |Vec.replicate x| is in fact just |x|:
\begin{code}
  replicate-get : ∀ {N} (v : Fin N) {X} {x : X} → Vec.replicate x « v » ≡ x
  replicate-get zero     = ≡.refl
  replicate-get (suc v)  = replicate-get v
\end{code}
Since every entry of |newLog| is |nothing|, this forces |lookupTVar| on the
left of the |Equivalent| equality type to evaluate to just |h « v »|, and
the goal of |Equivalent-refl| is trivially satisfied by reflexivity.

%}}}%

\subsection{Consistency}%{{{%

Recall earlier that in \S\ref{sec:verified-commit} we also defined the
notion of consistency between a heap and a read log,
\begin{spec}
Consistent : REL Heap Log
Consistent h ρ = ∀ v {n} → ρ « v » ≡ just n → h « v » ≡ n
\end{spec}
which simply states that the read log must be a subset of the heap. In much
the same way as our previous definition of equivalence, we can show that
a newly-initialised read log at the start of a transaction is always
consistent with any heap:
%if False
\begin{code}
mutual
\end{code}
%endif
%format consistent-newLog = "\func{Consistent\text-newLog}"
%format newLog«v»≡m = "newLog\index[v]{\equiv}just"
\begin{code}
  consistent-newLog : ∀ {h : Heap} → Consistent h newLog
  consistent-newLog v newLog«v»≡m
    rewrite replicate-get v {Maybe ℕ} {nothing} with newLog«v»≡m
  consistent-newLog v newLog«v»≡m  | ()
\end{code}
Given that |newLog| was defined as |Vec.replicate nothing| in
\S\ref{sec:verified-heap}, we can once again use the |replicate-get| lemma
to refine the type of the |newLog«v»≡m| argument to the uninhabitable
|nothing ≡ just m|.

%}}}%

\subsection{Heap and Log Updates}%{{{%

Given any heap |h|, looking up a variable |v| that has just been set to |m|
ought to give back the same |m|, shown by the following lemma:
%format set-get = "\func{set\text-get}"
\begin{code}
set-get : ∀ {X N} v (h : Vec X N) m → (h « v »≔ m) « v » ≡ m
set-get zero     (_ ∷ h) m = ≡.refl
set-get (suc v)  (_ ∷ h) m = set-get v h m
\end{code}
We have generalised the above for any instance of |Vec| however, as the same
lemma is equally applicable for our representation of read and write logs.

%format set-get′ = "\func{set\text-get\Prime}"
%format v≢v′ = "v{\not\equiv}v\Prime{}"
Conversely, looking up a different variable |v′| from the above---as
witnessed by the |v ≢ v′| argument---gives the same value as looking it up
directly in the original heap |h|:
\begin{code}
set-get′ : ∀ {X N v v′} (h : Vec X N) m → v ≢ v′ →
  (h « v »≔ m) « v′ » ≡ h « v′ »
set-get′ {v = zero}   {zero}    (_ ∷ h) m v≢v′ = ⊥-elim (v≢v′ ≡.refl)
set-get′ {v = suc v}  {zero}    (_ ∷ h) m v≢v′ = ≡.refl
set-get′ {v = zero}   {suc v′}  (_ ∷ h) m v≢v′ = ≡.refl
set-get′ {v = suc v}  {suc v′}  (_ ∷ h) m v≢v′
  = set-get′ h m (v≢v′ ∘ ≡.cong suc)
\end{code}

\noindent Recall that the |WRITE v| instruction simply updates the entry for
|v| in the write log with the newly written value. In an analogous sense,
using |lookupTVar| to retrieve |v| immediately afterwards ought to give back
the same value:
%format set-lookup = "\func{write\text-lookup}"
%set-lookup : ∀ {N} v {ρ} ω m {h : Heap′ N} → lookupTVar h ρ (ω « v »≔ just m) v ≡ m
\begin{code}
set-lookup : ∀ {h : Heap} {ρ} ω v m →
  lookupTVar h ρ (ω « v »≔ just m) v ≡ m
set-lookup ω v m rewrite set-get v ω (just m) = ≡.refl
\end{code}
%format set-lookup′ = "\func{write\text-lookup\Prime}"
This is in fact just a corollary of |set-get|. The associated |set-lookup′|
for looking up a different variable |v′| is also easily obtained as
a corollary of |set-get′|, as follows:
\def\setLookupPSig#1{|∀ {v h} ρ ω m {v′} → v ≢ v′ →|}
\begin{code}
set-lookup′ : {-"\setLookupPSig{"-}∀ {N v} {h : Heap′ N} ρ ω m {v′} → v ≢ v′ →{-"}"-}
  lookupTVar h ρ (ω « v »≔ just m) v′ ≡ lookupTVar h ρ ω v′
set-lookup′ ρ ω m {v′} v≢v′ rewrite set-get′ ω (just m) v≢v′ with ω « v′ »
set-lookup′ ρ ω m {v′} v≢v′ | just _ = ≡.refl
set-lookup′ ρ ω m {v′} v≢v′ | nothing with ρ « v′ »
set-lookup′ ρ ω m {v′} v≢v′ | nothing | just _ = ≡.refl
set-lookup′ ρ ω m {v′} v≢v′ | nothing | nothing = ≡.refl
\end{code}

%}}}%

\subsection{Committing Transaction Logs}%{{{%

If a transaction completes successfully, we proceed to update the as-yet
unmodified heap with the contents of the write log, using the |update : Heap
→ Log → Heap| function given in \S\ref{sec:verified-commit}. In the same
style as the earlier proofs of this section, we can show that looking up
a variable |v| in the updated heap gives the same value as that recorded in
the write log, provided such an entry exists:
%format update-get = "\func{apply\text-get}"
%format ω«v»≡m = "\omega\text[v\text]{\equiv}m"
\def\updateGetSig#1{|∀ h ω v {m} → ω « v » ≡ just m → update h ω « v » ≡ m|}
\begin{code}
update-get : {-"\updateGetSig{"-}∀ {N} (h : Heap′ N) ω v {m} → ω « v » ≡ just m → update h ω « v » ≡ m{-"}"-}
update-get []       []             ()       ω«v»≡m
update-get (_ ∷ h)  (_ ∷ ω)        zero     ω«v»≡m rewrite ω«v»≡m = ≡.refl
update-get (_ ∷ h)  (just _ ∷ ω)   (suc v)  ω«v»≡m = update-get h ω v ω«v»≡m
update-get (_ ∷ h)  (nothing ∷ ω)  (suc v)  ω«v»≡m = update-get h ω v ω«v»≡m
\end{code}
Conversely, looking up a variable without a corresponding entry in the write
log gives the same value as the original heap:
%format update-get′ = "\func{apply\text-get\Prime}"
%format ω«v»≡ = "\omega\text[v\text]{\equiv}"
\def\updateGetPSig#1{|∀ h ω v → ω « v » ≡ nothing → update h ω « v » ≡ h « v »|}
\begin{code}
update-get′ : {-"\updateGetPSig{"-}∀ {N} (h : Heap′ N) ω v → ω « v » ≡ nothing → update h ω « v » ≡ h « v »{-"}"-}
update-get′ []       []              ()       ω«v»≡
update-get′ (_ ∷ h)  (_        ∷ ω)  zero     ω«v»≡ rewrite ω«v»≡ = ≡.refl
update-get′ (_ ∷ h)  (just _   ∷ ω)  (suc v)  ω[v]≡ = update-get′ h ω v ω[v]≡
update-get′ (_ ∷ h)  (nothing  ∷ ω)  (suc v)  ω[v]≡ = update-get′ h ω v ω[v]≡
\end{code}

%}}}%

\subsection{Equality of Heaps}%{{{%

%format ≗→≡ = "\func{h{\circeq}h\Prime{\rightarrow}h{\equiv}h\Prime}"
% format h≗h′ = "h{\circeq}h\Prime"
%if False
\begin{code}
≗→≡ : ∀ {N} {h h′ : Heap′ N} → (∀ v → h « v » ≡ h′ « v ») → h ≡ h′
≗→≡ {h = []}     {h′ = []}       h≗h′ = ≡.refl
≗→≡ {h = m ∷ h}  {h′ = m′ ∷ h′}  h≗h′ with h≗h′ zero
≗→≡ {h = m ∷ h}  {h′ = .m ∷ h′}  h≗h′ | ≡.refl = ≡.cong (_∷_ m) (≗→≡ (h≗h′ ∘ suc))
\end{code}
%endif

% want hω = h′: equivalence gives hρω = h′ while consistency hρ = h

Given an |h′| that is equivalent to some heap |h| overlaid with logs |ρ| and
|ω|, and that |h| and |ρ| are mutually consistent, we can proceed to show
the following key result:
%format hω≡h′ = "\func{h\omega{\equiv}h\Prime}"
%format hω≗h′ = "\func{h\omega{\circeq}h\Prime}"
%format hρω≗h′ = "h\rho\omega{\circeq}h\Prime{}"
%format h⊇ρ = "h{\supseteq}\rho"
%format ρ«v»≡m = "\rho\index[v]{\equiv}m"
%format ρ«v»≡ = "\rho\index[v]{\equiv}"
%format m≡h′«v» = "m{\equiv}h\Prime\index[v]"
%format hρ«v»≡h′«v» = "h\rho\index[v]{\equiv}h\Prime\index[v]"
%format h«v»≡h′«v» = "h\index[v]{\equiv}h\Prime\index[v]"
\savecolumns
\begin{code}
hω≡h′ : ∀ {h′ h : Heap} {ρ ω} →
  Equivalent h′ h ρ ω → Consistent h ρ → update h ω ≡ h′
hω≡h′ {h′} {h} {ρ} {ω} hρω≗h′ h⊇ρ = ≗→≡ hω≗h′ where
  hω≗h′ : ∀ v → update h ω « v » ≡ h′ « v »
\end{code}
That is, updating |h| with the contents of |ω| results in an identical heap
as that which is modified in-place by the stop-the-world semantics.

Note that we make use of the |≗→≡| lemma to show that pointwise equality for
heaps implies definitional equality, which happens holds for our vector
representation. Were this not the case, we could nevertheless proceed using
only pointwise equality.

The |hω≗h′| part of the proof is on the structure of |lookupTVar|---used in
the definition of |Equivalent|---and begins by inspecting the write log.
We also instantiate |hρω≗h′| at |v| so that its type becomes more refined as
we proceed:
\restorecolumns
\begin{code}
  hω≗h′ v with hρω≗h′ v  | ≡.inspect (ω « v »)
  hω≗h′ v | m≡h′«v»      | just m with-≡ ω«v»≡m
    rewrite ω«v»≡m | update-get h ω v ω«v»≡m = m≡h′«v»
\end{code}
If an entry |m| exists for |v| in |ω|, we can use the |update-get| lemma to
show that |update h ω « v » ≡ m|; meanwhile |lookupTVar h ρ ω v| reduces to
|m|, so the type of |hρω≗h′ v| is refined to |m ≡ h′ « v »|. These two
equalities together gives us the desired goal.

Were |ω| not to contain an entry for |v|, we first use the |update-get′|
lemma to rewrite the goal---which is refined to |h « v » ≡ h′
« v »|---before proceeding to inspect the read log:
\restorecolumns
\begin{code}
  hω≗h′ v | hρ«v»≡h′«v»  | nothing with-≡ ω«v»≡
    rewrite ω«v»≡ | update-get′ h ω v ω«v»≡ with ≡.inspect (ρ « v »)
  hω≗h′ v | m≡h′«v»      | nothing with-≡ ω«v»≡
    | just m with-≡ ρ«v»≡m
      rewrite ρ«v»≡m = ≡.trans (h⊇ρ v ρ«v»≡m) m≡h′«v»
\end{code}
If an entry |m| exists for |v| in |ρ|, then we can instantiate the |h⊇ρ|
premise---that witnesses the consistency of |ρ| and |h|---to give a proof of
|h « v » ≡ m|. Meanwhile |lookupTVar h ρ ω v| reduces to the same |m|,
refining the type of |hρω≗h′ v| to |m ≡ h′ « v »|, which we have renamed as
|m≡h′«v»| accordingly. The goal of |h « v » ≡ h′ « v »| is therefore
obtained simply by applying transitivity.

Finally, if |v| is found in neither the write nor the read logs, |lookupTVar
h ρ ω| resorts to looking it up directly from |h|. Consequently, the
equality witnessed by |hρω≗h′ v| is refined to |h « v » ≡ h′
« v »|---precisely the type of the goal:
\restorecolumns
\begin{code}
  hω≗h′ v | h«v»≡h′«v»   | nothing with-≡ ω«v»≡
    | nothing with-≡ ρ«v»≡ rewrite ρ«v»≡ = h«v»≡h′«v»
\end{code}

%}}}%

% vim: ft=tex fo-=m fo-=M:

