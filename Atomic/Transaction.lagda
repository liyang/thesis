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

\section{Reasoning Transactionally}

In this section, we will cover some useful lemmas concerning heaps and
transaction logs that are used to show that the stop-the-world and log-based
transaction semantics coincide.

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
log entry for |v′| remains unchanged, and the existing |cons| proof
suffices.

%if False
\begin{code}
-- sequence of ↣′ transitions with the same heap
infix 3 _⊢_↣′⋆_
_⊢_↣′⋆_ : Heap → Rel (Logs × Expression′)
h ⊢ l , e ↣′⋆ l′ , e′ = Star (_⊢_↣′_ h) (l , e) (l′ , e′)
\end{code}
%endif

%if False
\begin{code}
-- ↣′ preserves consistency
↣′-Consistent : ∀ {h l e l′ e′} →
  h ⊢  l , e  ↣′  l′ , e′ →
  Consistent h l → Consistent h l′
↣′-Consistent ↣′-ℕ = id
↣′-Consistent (↣′-R m b↣b′) = ↣′-Consistent b↣b′
↣′-Consistent (↣′-L b a↣a′) = ↣′-Consistent a↣a′
↣′-Consistent (↣′-writeE e↣e′) = ↣′-Consistent e↣e′
↣′-Consistent ↣′-writeℕ = id
↣′-Consistent (↣′-read (ρ & ω) v) with ω « v »
... |  ● m = id
... |  ○ with ρ « v »
...    | ● m = id
...    | ○ = Read-Consistent (ρ & ω) v
\end{code}
%endif

%if False
% not used?
\begin{spec}
↣′⋆-Consistent : ∀ {h l″ e″ l e} →
  h  ⊢ l , e ↣′⋆ l″ , e″ →
  Consistent h l → Consistent h l″
↣′⋆-Consistent {h} {l″} {e″} = Star.gfold (Consistent h ∘ fst) (λ a b → a → b)
  (λ e↣′e′ l′→l″ → l′→l″ ∘ ↣′-Consistent e↣′e′) {k = l″ , e″} id
\end{spec}
%endif

%if False
\begin{code}
-- sequence of ↣′ transitions with different heaps
infix 3 H⊢_↣′_ H⊢_↣′⋆_
H⊢_↣′_ : Rel (Logs × Expression′)
H⊢ c ↣′ c′ = Σ Heap (λ h → h ⊢ c ↣′ c′)
\end{code}
%endif

%if False
\begin{code}
H⊢_↣′⋆_ : Rel (Logs × Expression′)
H⊢_↣′⋆_ = Star H⊢_↣′_
\end{code}
%endif

%if False
\begin{code}
-- only backwards consistency preservation when heap changes
H↣′-Consistent : ∀ {h′ l e l′ e′} →
  H⊢ l , e ↣′ l′ , e′ →
  Consistent h′ l′ → Consistent h′ l
H↣′-Consistent (h , ↣′-ℕ) cons′ = cons′
H↣′-Consistent (h , ↣′-R m b↣b′) cons′ = H↣′-Consistent (h , b↣b′) cons′
H↣′-Consistent (h , ↣′-L b a↣a′) cons′ = H↣′-Consistent (h , a↣a′) cons′
H↣′-Consistent (h , ↣′-writeE e↣e′) cons′ = H↣′-Consistent (h , e↣e′) cons′
H↣′-Consistent (h , ↣′-writeℕ) cons′ = cons′
\end{code}
%endif

%if False
\begin{code}
H↣′-Consistent {h′} (h , ↣′-read l v) cons′ with Logs.ω l « v »
... | ● m = cons′
... | ○ with Logs.ρ l « v » | ≡.inspect (_«_» (Logs.ρ l)) v
...   | ● m | _ = cons′
...   | ○ | ‹ ρ[v]≡○ › = cons where
  cons : Consistent h′ l
  cons v′ with v′ ≟Fin v
  ... | yes v′≡v rewrite v′≡v | ρ[v]≡○ = λ m ()
  ... | no v′≢v with cons′ v′
  ...   | cons′-v′ rewrite Vec.lookup∘update′ v′≢v (Logs.ρ l) (● (h « v »)) = cons′-v′
\end{code}
%endif

%if False
\begin{code}
H↣′⋆-Consistent : ∀ {h′ l′ e′ l e} →
  H⊢ l , e ↣′⋆ l′ , e′ →
  Consistent h′ l′ → Consistent h′ l
H↣′⋆-Consistent {h′} {l′} {e′} = flip $
  Star.gfold fst (const ∘ Consistent h′) H↣′-Consistent {k = l′ , e′}
\end{code}
%endif


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
In other words, |Read h l| gives the same result as looking it up directly
from |h′| for all variables.

On commencing a transaction, the transaction logs are initialised to
|∅| by the |↣-begin| rule, while the heaps according to both
semantics have yet to diverge. The following definition shows that every
heap |h| is equivalent to itself overlaid with empty logs:
%format ∅-Equivalent = "\func{\varnothing\text-Equivalent}"
\begin{code}
∅-Equivalent : ∀ {h} → Equivalent h ∅ h
∅-Equivalent v rewrite Vec.lookup∘replicate v (○ ∶ Maybe ℕ)
  | Vec.lookup∘replicate v (○ ∶ Maybe ℕ) = ≡.refl
\end{code}
The two rewrites correspond to showing that the write and read logs are
always empty, using the |Vec.lookup∘replicate| lemma to obtain proofs of
|Vec.replicate ○ « v » ≡ ○|. In this case, the value returned by
|Read| reduces to just |h « v »|, and the goal is trivially satisfied
by reflexivity.

%format Read-Equivalent = "\func{Read\text-Equivalent}"
%format cons-v′ = "\Varid{cons\text-v\Prime}"
%format equiv-v′ = "\Varid{equiv\text-v\Prime}"
\savecolumns
\begin{code}
Read-Equivalent : ∀ {h l h′ v} → Consistent h l → Equivalent h l h′ →
  Equivalent h (Logs.ρ l « v »≔ ● (h « v ») & Logs.ω l) h′
Read-Equivalent {h} {ρ & ω} {h′} {v} cons equiv v′ with cons v′ | equiv v′
...  |  cons-v′ | equiv-v′ with ω « v′ »
...     |  ● m = equiv-v′
...     |  ○ with v′ ≟Fin v
\end{code}

\restorecolumns
\begin{code}
Read-Equivalent {h} {ρ & ω} {h′} {v} cons equiv v′ | cons-v′ | equiv-v′ | ○
           |  yes v′≡v rewrite v′≡v | Vec.lookup∘update v ρ (● (h « v »))
              with ρ « v »
...           | ● m = ≡.trans (cons-v′ m ≡.refl) equiv-v′
...           | ○ = equiv-v′
\end{code}

\restorecolumns
\begin{code}
Read-Equivalent {h} {ρ & ω} {h′} {v} cons equiv v′ | cons-v′ | equiv-v′ | ○
           |  no v′≢v rewrite Vec.lookup∘update′ v′≢v ρ (● (h « v »))
              with ρ « v′ »
...           | ● m = equiv-v′
...           | ○ = equiv-v′
\end{code}

%if False
% not used
\begin{code}
Read-Equivalent′ : ∀ h l {h′} v →
  Consistent h l → Equivalent h l h′ →
  Equivalent h (fst (Read h l v)) h′
Read-Equivalent′ h (ρ & ω) v cons equiv v′ with ω « v »
... | ● m = equiv v′
... | ○ with ρ « v »
...   | ● m = equiv v′
...   | ○ = Read-Equivalent cons equiv v′
\end{code}
%endif

%format Write-Equivalent = "\func{Write\text-Equivalent}"
\begin{code}
Write-Equivalent : ∀ {h l h′ m v} →
  Equivalent h l h′ → Equivalent h (Write l v m) (h′ « v »≔ m)
Write-Equivalent {v = v} equiv v′ with equiv v′
... |  equiv-v′ with v′ ≟Fin v

Write-Equivalent {l = ρ & ω} {h′} {m} equiv v′ | equiv-v′
       |  yes ≡.refl rewrite Vec.lookup∘update v′ ω (● m)
          | Vec.lookup∘update v′ h′ m = ≡.refl

Write-Equivalent {l = ρ & ω} {h′} {m} equiv v′ | equiv-v′
       |  no v′≢v rewrite Vec.lookup∘update′ v′≢v ω (● m)
          |  Vec.lookup∘update′ v′≢v h′ m with ω « v′ »

...          |  ● n = equiv-v′
...          |  ○ with ρ « v′ »
...             | ● n = equiv-v′
...             | ○ = equiv-v′
\end{code}

lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum
lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum
lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum
lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum
lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum lorem ipsum
lorem ipsum 

\subsection{Commit Update}

%format Commit-Update = "\func{Commit\text-Update}"
%format h′≗hω = "\func{h\Prime{\circeq}h\omega}"
%format cons-v = "\Varid{cons\text-v}"
%format equiv-v = "\Varid{equiv\text-v}"
%format ρ«v»≡m = "\Varid{\rho_v{\equiv}m}"
\begin{code}
Commit-Update : ∀ {h l h′} →
  Consistent h l → Equivalent h l h′ → Update h l ≡ h′
Commit-Update {h} {l} {h′} cons equiv =
    Equivalence.to Vec.Pointwise-≡ ⟨$⟩ Vec.Pointwise.ext h′≗hω where
  open Logs.Logs l
  h′≗hω : ∀ v → Update h l « v » ≡ h′ « v »
  h′≗hω v rewrite Vec.lookup∘tabulate (Update-lookup h l) v
       with ω « v » | equiv v
  ...  |  ● m  | equiv-v = equiv-v
  ...  |  ○    | equiv-v with ρ « v » | ≡.inspect (_«_» ρ) v
  ...     | ● m  | ‹ ρ«v»≡m › = ≡.trans (cons v m ρ«v»≡m) equiv-v
  ...     | ○    | _ = equiv-v
\end{code}

% vim: ft=tex fo-=m fo-=M:

