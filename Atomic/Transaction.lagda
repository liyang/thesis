%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
\end{comment}
%endif

%if False
\begin{code}
module Transaction where

open import Common
open import Heap
open import Logs
open import Language
\end{code}
%endif

\subsection{Consistency-Preserving Transitions}

%format Read-Consistent = "\func{Read\text-Consistent}"
%format v′≡v = "\Varid{v\Prime{\equiv}v}"
%format v′≢v = "\Varid{v\Prime{\not\equiv}v}"
First up, recall that when the log-based semantics needs to read a variable
|v| and it is not present in either of the read and write logs, we update
the read log with the value of |v| from the heap. The following lemma shows
that this operation preserves log consistency:
\savecolumns
\begin{code}
Read-Consistent : ∀ {h} l v → Consistent h l →
  Consistent h (Logs.ρ l « v »≔ ● (h « v ») & Logs.ω l)
Read-Consistent {h} (ρ & ω) v cons v′ m with v′ ≟Fin v
... | yes v′≡v rewrite v′≡v | Vec.lookup∘update v ρ (● (h « v »)) = ●-inj
... | no v′≢v rewrite Vec.lookup∘update′ v′≢v ρ (● (h « v »)) = cons v′ m
\end{code}
We have $\eta$-expanded |Read-Consistent| with a second variable |v′| and
|m| taken by the resulting |Consistent| type, and need to show that |ρ « v′
» ≡ ● m → h « v′ » ≡ m|.

There are two cases to consider, depending on whether |v′| coincides with
the variable |v| whose read log entry is being updated. If they are indeed
the same, we can use |Vec.lookup∘update| to show that the updated read log
entry is |● h«v»|, in which case the goal of |● h « v′ » ≡ ● m → h « v′
» ≡ m| can be satisfied by injectivity of |●|. When |v| and |v′| correspond
to different variables, |Vec.lookup∘update′| gives us a proof that the read
log entry for |v′| remains unchanged, and the |cons| argument suffices.

Using the above result, we can demonstrate that any transaction transition
under the log-based semantics preserves consistency:
%format ↣′-Consistent = "\func{{\rightarrowtail}\Prime\text-Consistent}"
\begin{code}
↣′-Consistent : ∀ {h l e l′ e′} → Consistent h l →
  h ⊢ l , e ↣′ l′ , e′ → Consistent h l′
↣′-Consistent cons ↣′-ℕ = cons
↣′-Consistent cons (↣′-R  m    b↣b′)  = ↣′-Consistent cons b↣b′
↣′-Consistent cons (↣′-L  b    a↣a′)  = ↣′-Consistent cons a↣a′
↣′-Consistent cons (↣′-writeE  e↣e′)  = ↣′-Consistent cons e↣e′
↣′-Consistent cons ↣′-writeℕ = cons
↣′-Consistent cons (↣′-read l v) with Logs.ω l « v »
... |  ● m = cons
... |  ○ with Logs.ρ l « v »
...    | ● m = cons
...    | ○ = Read-Consistent l v cons
\end{code}
The proof proceeds by induction on the structure of the reduction rules,
making use of the |Read-Consistent| lemma when the read log changes.
Naturally, we can extend the above to an arbitrary |_⊢_↣′⋆_| sequence by
folding over it:
%format ↣′⋆-Consistent = "\func{{\rightarrowtail\Prime^\star}\text-Consistent}"
\begin{code}
↣′⋆-Consistent : ∀ {h l e l′ e′} → Consistent h l →
  h ⊢ l , e ↣′⋆ l′ , e′ → Consistent h l′
↣′⋆-Consistent {h} {l} {e} =
  Star.gfoldl fst (const (Consistent h)) ↣′-Consistent {i = l , e}
\end{code}


%format Read-Consistent′ = "\func{Read\text-Consistent\Prime}"
%format ρ«v»≡○ = "\Varid{\rho_v{\equiv}{\circ}}"
%format cons′ = "\Varid{cons\Prime}"
\noindent In the opposite direction, we can show a pair of similar but
slightly more general consistency-preservation lemmas. This extra generality
in fact turns out to be crucial to our later proofs. The |Read-Consistent′|
lemma shares an analogous structure to that of |Read-Consistent|, but
requires an extra argument showing that the pre-transition read log entry
for |v| is empty:
\begin{code}
Read-Consistent′ : ∀ {h n} l v → Logs.ρ l « v » ≡ ○ →
  Consistent h (Logs.ρ l « v »≔ ● n & Logs.ω l) → Consistent h l
Read-Consistent′ {h} {n} (ρ & ω) v ρ«v»≡○ cons′ v′ m with v′ ≟Fin v
... | yes v′≡v rewrite v′≡v | ρ«v»≡○ = λ ()
... | no v′≢v rewrite ≡.sym (Vec.lookup∘update′ v′≢v ρ (● n)) = cons′ v′ m
\end{code}
As before, there are two alternatives: when |v′| coincides with the variable
|v| whose read log entry is being updated, we use the |ρ«v»≡○| argument to
rewrite the goal to |○ ≡ ● m → h « v » ≡ m|, which is then discharged with
an absurd $\lambda$. This is essentially making use of the fact that that
each read log entry is only ever updated once, from |○| to |●|. When |v′|
differs, the |cons′| argument suffices.

%format ↣′-Consistent′ = "\func{{\rightarrowtail}\Prime\text-Consistent\Prime}"
In the |yes| case of |Read-Consistent|, we required that the post-transition
read log entry for |v| be |● (h « v »)|. Since the corresponding case here
is absurd, this is no longer necessary, and the proof can be generalised to
any |● n|. This means that the heap |h| under which the logs and expression
make their transition need not be the same as the heap |h′| with which |l|
and |l′| are consistent in the following lemma:
\begin{code}
↣′-Consistent′ : ∀ {h h′ l e l′ e′} → Consistent h′ l′ →
  h ⊢ l , e ↣′ l′ , e′ → Consistent h′ l
↣′-Consistent′ cons′ ↣′-ℕ = cons′
↣′-Consistent′ cons′ (↣′-R  m    b↣b′)  = ↣′-Consistent′ cons′ b↣b′
↣′-Consistent′ cons′ (↣′-L  b    a↣a′)  = ↣′-Consistent′ cons′ a↣a′
↣′-Consistent′ cons′ (↣′-writeE  e↣e′)  = ↣′-Consistent′ cons′ e↣e′
↣′-Consistent′ cons′ ↣′-writeℕ = cons′
↣′-Consistent′ cons′ (↣′-read (ρ & ω) v) with ω « v »
... |  ● m = cons′
... |  ○ with ρ « v » | ≡.inspect (_«_» ρ) v
...    | ● m  | _ = cons′
...    | ○    | ‹ ρ«v»≡○ › = Read-Consistent′ (ρ & ω) v ρ«v»≡○ cons′
\end{code}
This follows an identical structure to |↣′-Consistent|, with the only
difference being the use of the |≡.inspect| idiom to obtain a proof of |ρ
« v » ≡ ○|.


\subsection{Heaps and Logs Equivalence}

%format Equivalent = "\type{Equivalent}"
Recall that a pair of read and write logs is used to give an local
view of the heap during a running transaction. For our correctness proof, it
will be convenient to define a predicate stating that the view of the heap
during the transaction---that is, |h| overlaid with read and write
logs---is equivalent to another heap |h′| that is accessed directly using
the stop-the-world semantics:
\begin{code}
Equivalent : Heap → Logs → Heap → Set
Equivalent h l h′ = snd ∘ Read h l ≗ _«_» h′
\end{code}
We write |f ≗ g| to mean pointwise equality of |f| and |g|, and is a synonym
for |∀ x → f x ≡ g x|. In other words, |Read h l v| gives the same value as
|h′ « v »| for all variables.

On commencing a transaction, the logs are initialised to |∅| by the
|↣-begin| rule, while the heaps according to both semantics have yet to
diverge. The following definition shows that every heap |h| is equivalent to
itself overlaid with empty logs:
%format ∅-Equivalent = "\func{\varnothing\text-Equivalent}"
\begin{code}
∅-Equivalent : ∀ {h} → Equivalent h ∅ h
∅-Equivalent v rewrite Vec.lookup∘replicate v (○ ∶ Maybe ℕ)
  | Vec.lookup∘replicate v (○ ∶ Maybe ℕ) = ≡.refl
\end{code}
The two rewrites correspond to showing that the write and read logs are
always empty, using the |Vec.lookup∘replicate| lemma to obtain proofs of
|Vec.replicate ○ « v » ≡ ○|, so that the value returned by |Read| reduces to
just |h « v »|. The goal is then trivially satisfied by reflexivity.

%format Read-Equivalent = "\func{Read\text-Equivalent}"
%format cons-v′ = "\Varid{cons\text-v\Prime}"
%format equiv-v′ = "\Varid{equiv\text-v\Prime}"
%format ρ«v»≡m = "\Varid{\rho_v{\equiv}m}"
In a similar manner to |Read-Consistent|, the operation of updating the read
log for a variable |v| when it is first read preserves heap-log equivalence.
\savecolumns
\begin{code}
Read-Equivalent : ∀ {h l h′ v} → Logs.ρ l « v » ≡ ○ →
  Equivalent h l h′ → Equivalent h (Logs.ρ l « v »≔ ● (h « v ») & Logs.ω l) h′
Read-Equivalent {h} {ρ & ω} {h′} {v} ρ«v»≡○ equiv v′ with equiv v′
...  |  equiv-v′ with ω « v′ »
...     |  ● m = equiv-v′
...     |  ○ with v′ ≟Fin v
\end{code}
We start by binding the application |equiv v′| to |equiv-v′|, which starts
off with a type of |snd (Read h l v′) ≡ h′ « v′ »|. This is so that the
|Read| function in its type can be refined as we perform case analyses on the
write and read log entries for |v′|. Since the write log does not change,
the types of both the goal and |equiv-v′| reduces to |m ≡ h′ « v′ »| when |ω
« v′ »| is |● m|. Otherwise we must consider whether |v′| refers to the same
variable as |v| whose read log entry is being updated:
\restorecolumns
\begin{code}
...        |  yes v′≡v rewrite v′≡v | ρ«v»≡○
              | Vec.lookup∘update v ρ (● (h « v »)) = equiv-v′
\end{code}
If |v′| is indeed the variable being updated, we can use the |ρ«v»≡○|
argument to refine the type of |equiv-v′| to |h « v » ≡ h′ « v »|, and
a final |Vec.lookup∘update| rewrites the goal to the same type. Otherwise,
we use the |Vec.lookup∘update′| lemma to show that |ρ « v′ »| is unaffected
by the update:
\restorecolumns
\begin{code}
...        |  no v′≢v rewrite Vec.lookup∘update′ v′≢v ρ (● (h « v »)) with ρ « v′ »
...           | ● m = equiv-v′
...           | ○ = equiv-v′
\end{code}
In the two alternatives above, the types of the goals and |equiv-v′| reduce
to |m ≡ h′ « v′ »| and |h « v′ » ≡ h′ « v′ »|, corresponding to the cases
where |v′| was already cached in the read log, and when it is read for the
first time respectively.

%format Write-Equivalent = "\func{Write\text-Equivalent}"
Unlike the |Consistent| property which only involves the read log,
|Equivalent| also depends on the write log (indirectly via |Read|).
Therefore we must demonstrate that write log updates preserve some notion of
heap-log equivalence. We proceed by applying |equiv| to |v′|, and checking
whether |v′| and |v| are the same variable:
\savecolumns
\begin{code}
Write-Equivalent : ∀ {h l h′ v m} →
  Equivalent h l h′ → Equivalent h (Write l v m) (h′ « v »≔ m)
Write-Equivalent {h} {ρ & ω} {h′} {v} {m} equiv v′ with equiv v′ | v′ ≟Fin v
... |  equiv-v′ | yes v′≡v rewrite v′≡v | Vec.lookup∘update v ω (● m)
       |  Vec.lookup∘update v h′ m = ≡.refl
\end{code}
In the |yes| case, we use |Vec.lookup∘update| to first show that the value
returned by |Read h (Write l v m) v| is in fact |m|, which corresponds to
the left-hand side of the |_≡_| goal. The next clause rewrites the
right-hand side from |(h′ « v »≔ m) « v »| to the same |m|, and |≡.refl|
completes this half of the proof.

For the |no| half where |v′| is not the variable being written to, the write
log entry |ω « v′ »| and the value of |h′ « v′ »| are not updated, which is
taken care of by the two |Vec.lookup∘update′| rewrites. Thus the existing
|equiv-v′| suffices to complete the proof, although we do have to inspect
the appropriate log entries to verify that |equiv-v′| and the goal have the
correct types in all cases:
\restorecolumns
\begin{code}
... |  equiv-v′ | no v′≢v rewrite Vec.lookup∘update′ v′≢v ω (● m)
       |  Vec.lookup∘update′ v′≢v h′ m with ω « v′ »
...       |  ● n = equiv-v′
...       |  ○ with ρ « v′ »
...          | ● n = equiv-v′
...          | ○ = equiv-v′
\end{code}


\subsection{Commit Heap Equality}

%format Commit = "\func{Commit}"
%format hω≗h′ = "\func{h\omega{\circeq}h\Prime}"
%format cons-v = "\Varid{cons\text-v}"
%format equiv-v = "\Varid{equiv\text-v}"
When a transaction completes successfully, we proceed to update the
unmodified heap with the contents of the write log, using the |Update|
function defined at the end of \S\ref{sec:atomic-logs}. Given an |h′| that
is equivalent to some heap |h| overlaid with logs |l| and that |h| and |l|
are mutually consistent, we can proceed to show that updating |h| with the
contents of the write log results in an identical heap as one that is
modified in-place by the stop-the-world semantics:
\savecolumns
\begin{code}
Commit : ∀ {h l h′} →
  Consistent h l → Equivalent h l h′ → Update h l ≡ h′
Commit {h} {l} {h′} cons equiv =
    Equivalence.to Vec.Pointwise-≡ ⟨$⟩ Vec.Pointwise.ext hω≗h′ where
  hω≗h′ : ∀ v → Update h l « v » ≡ h′ « v »
  hω≗h′ v rewrite Vec.lookup∘tabulate (Update-lookup h l) v
       with Logs.ω l « v » | equiv v
  ...  |  ● m  | equiv-v = equiv-v
\end{code}
The main |hω≗h′| part of the proof shows pointwise equality of |Update h l|
and |h′|, by considering the entry for |v| in the write and read logs. When
the write log contains |● m|, the corresponding entry of |h| would be
updated with |m|; not coincidentally |equiv-v| has been refined to a proof
of |m ≡ h′ « v »|. Otherwise the write log contains a |○|, and the goal type
reduces to |h « v » ≡ h′ « v »|:
\restorecolumns
\begin{code}
  ...  |  ○    | equiv-v with Logs.ρ l « v » | ≡.inspect (_«_» (Logs.ρ l)) v
  ...     | ● m  | ‹ ρ«v»≡m › = ≡.trans (cons v m ρ«v»≡m) equiv-v
  ...     | ○    | _ = equiv-v
\end{code}
We then proceed to inspect the read log: if it contains |● m| then |equiv-v|
refines to a proof of |m ≡ h′ « v »|, so we use |cons| to show that |h
« v »| is also equal to |m|, and transitivity completes the proof. In the
last case where both log entries are empty, the |Read| on the left-hand side
of the type of |equiv-v| becomes simply |h « v »|, and so completes the
proof. Finally we use the proof of pointwise/definitional equivalence for
|Vec| from the Agda standard library to convert |hω≗h′| to a proof of
definitional equality.

% vim: ft=tex fo-=m fo-=M:

