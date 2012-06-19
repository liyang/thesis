%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
%include Atomic/Combined.lagda
%include Atomic/Transaction.lagda
%include Atomic/Complete.lagda
\end{comment}
%endif

%if False
\begin{code}
module Sound where

open import Common
open import Heap
open import Logs
open import Language
open import Combined
open import Transaction
\end{code}
%endif

\subsection{Soundness of Log-Based Transactions}

%if False
\begin{code}
infix 3 H⊢_↣′_ H⊢_↣′⋆_
\end{code}
%endif

The soundness part of transactional correctness involves showing that the
stop-the-world semantics can match the log-based semantics when the latter
successfully commits. This is more difficult as the heap can be changed at
any point during a log-based transaction by the |↣-mutate| rule. Let us
begin by defining a variation on |_⊢_↣′_| that encapsulates the heap used
for each transition:
%format H⊢_↣′_ = "\type{H{\vdash}\anonymous{\rightarrowtail\Prime}\anonymous}"
%format H⊢_↣′⋆_ = "\type{H{\vdash}\anonymous{\rightarrowtail\Prime^\star}\anonymous}"
%format H⊢ = "\prefix{\type{H{\vdash}}}"
\begin{code}
H⊢_↣′_ : Rel (Logs × Expression′)
H⊢ x ↣′ x′ = Σ Heap (λ h → h ⊢ x ↣′ x′)

H⊢_↣′⋆_ : Rel (Logs × Expression′)
H⊢_↣′⋆_ = Star H⊢_↣′_
\end{code}
We write |H⊢_↣′⋆_| for its reflexive, transitive closure. Every step of this
transition potentially uses a different heap, in contrast to the |_⊢_↣′⋆_|
relation where the entire sequence runs with the same heap.

%if False
\begin{code}
private
\end{code}
%endif

%format ↣-extract′ = "\func{{\rightarrowtail}\text-extract\Prime}"
%format r↣′⋆e = "\Varid{r{\rightarrowtail\Prime^\star}\!e}"
%format e′↠⋆e″ = "\Varid{e\Prime{\twoheadrightarrow^\star_\tau}e\PPrime}"
%format e″↠e‴ = "\Varid{e\PPrime{\twoheadrightarrow}e\PPPrime}"
Next we define a function that discards the steps from any aborted
transactions, leaving only the final sequence of transitions leading up to
a |↣-commit|, along with the heaps used at each step:
\savecolumns
\begin{code}
  ↣-extract′ : ∀ {h α r l e h′ c′ e′ h″ c″ e″} →
    H⊢ ∅ , r ↣′⋆ l , e →
    α ≢ τ → h , ↣: ● (r , l) , atomic e  ↠⋆  h′ , c′ , e′ →
    α ▹  h′ , c′ , e′  ↠  h″ , c″ , e″ →
    ∃₂ λ l′ m → α , h″ , c″ , e″ ≡ ☢ , Update h′ l′ , ↣: ○ , # m ×
    Consistent h′ l′ × H⊢ ∅ , r ↣′⋆ l′ , # m
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-step e↣e′)) = ⊥-elim (α≢τ ≡.refl)
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-mutate h′)) = ⊥-elim (α≢τ ≡.refl)
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-abort ¬cons)) = ⊥-elim (α≢τ ≡.refl)
\end{code}
The first argument to |↣-extract′| accumulates the sequence of transactions
steps starting from the initial |r|, while the next three correspond to
the three fields of a visible transition. The three clauses above eliminate
the cases where a silent transition appears in the non-silent position.

If no further transaction steps remain, the only possible rule is
|↣-commit|, in which case we return the accumulated sequence |r↣′⋆e| and the
proof of consistency carried by |↣-commit|, along with an equality showing
the values of |α|, |h″|, |c″| and |e″|:
\restorecolumns
\begin{code}
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-commit cons)) =
    _ , _ , ≡.refl , cons , r↣′⋆e
\end{code}
When the transaction makes a single step, we append it to the end of the
accumulator, taking a copy of the heap used for that step:
\restorecolumns
\begin{code}
  ↣-extract′ {h} r↣′⋆e α≢τ (↠-↣ (↣-step e↣e′) ◅ e′↠⋆e″) e″↠e‴ =
    ↣-extract′ (r↣′⋆e ◅◅ (h , e↣e′) ◅ ε) α≢τ e′↠⋆e″ e″↠e‴
\end{code}

\noindent Should we encounter a |↣-mutate| rule, we simply move on to the
next step, albeit with a different heap:
\restorecolumns
\begin{code}
  ↣-extract′ r↣′⋆e α≢τ (↠-↣ (↣-mutate h′) ◅ e′↠⋆e″) e″↠e‴ =
    ↣-extract′ r↣′⋆e α≢τ e′↠⋆e″ e″↠e‴
\end{code}

\noindent Lastly if |e| has reduced completely to a number, but the read log
was not consistent with the heap at that point, the transaction aborts and
retries. In this case, we reset the accumulator to |ε| and carry on with the
rest of the sequence:
\restorecolumns
\begin{code}
  ↣-extract′ r↣′⋆e α≢τ (↠-↣ (↣-abort ¬cons) ◅ e′↠⋆e″) e″↠e‴ =
    ↣-extract′ ε α≢τ e′↠⋆e″ e″↠e‴
\end{code}

%format ↣-extract = "\func{{\rightarrowtail}\text-extract}"
\noindent We can write a wrapper for the above that takes a visible
transition, and strips off the initial |↣-begin| rule before invoking
|↣-extract′| itself:
\begin{code}
↣-extract : ∀ {α h r h″ c″ e″} →
  α ▹ h , ↣: ○ , atomic r ⤇ h″ , c″ , e″ →
  ∃₃ λ h′ l′ m → α , h″ , c″ , e″ ≡ ☢ , Update h′ l′ , ↣: ○ , # m ×
  Consistent h′ l′ × H⊢ ∅ , r ↣′⋆ l′ , # m
↣-extract (⤇: α≢τ ε (↠-↣ ↣-begin)) = ⊥-elim (α≢τ ≡.refl)
↣-extract (⤇: α≢τ (↠-↣ ↣-begin ◅ e↠⋆e′) e′↠e″) =
  _ , ↣-extract′ ε α≢τ e↠⋆e′ e′↠e″
\end{code}

%format ↣′-swap = "\func{{\rightarrowtail\Prime}\text-swap}"
%format cons′-v-h«v» = "\Varid{cons\Prime\text-v\text-h_v}"
%format ↣′-read-l-v = "\Varid{{\rightarrowtail\Prime}\text-read\text-l\text-v}"
\noindent The next lemma says that we can swap the heap used for any
|_⊢_↣′_| transition, as long as the target heap is consistent with the
original post-transition log |l′|:
\begin{code}
↣′-swap : ∀ {h h′ l e l′ e′} → Consistent h′ l′ →
  h ⊢ l , e ↣′ l′ , e′ → h′ ⊢ l , e ↣′ l′ , e′
↣′-swap cons′ ↣′-ℕ = ↣′-ℕ
↣′-swap cons′ (↣′-R  m    b↣b′) = ↣′-R  m    (↣′-swap cons′ b↣b′)
↣′-swap cons′ (↣′-L  b    a↣a′) = ↣′-L  b    (↣′-swap cons′ a↣a′)
↣′-swap cons′ (↣′-writeE  e↣e′) = ↣′-writeE  (↣′-swap cons′ e↣e′)
↣′-swap cons′ ↣′-writeℕ = ↣′-writeℕ
\end{code}
The first few cases are trivial since they either don't interact with the
heap, or the proof burden can be deferred to a recursive call. The last
|↣′-read| case however does require our attention:
\begin{code}
↣′-swap {h} {h′} cons′ (↣′-read l v) with ↣′-read {h′} l v
...  |  ↣′-read-l-v with Logs.ω l « v »
...     |  ● m = ↣′-read-l-v
...     |  ○ with Logs.ρ l « v »
...        |  ● m = ↣′-read-l-v
...        |  ○ rewrite cons′ v (h « v »)
              (Vec.lookup∘update v (Logs.ρ l) (● (h « v »))) = ↣′-read-l-v
\end{code}
As long as one of the log entries for |v| is not empty, the transaction does
not interact with the heap, so |↣′-read-l-v| by itself suffices. Otherwise
by the time we see that both entries are empty, |Logs.ρ l′| has been refined
to |Logs.ρ l « v »≔ ● (h « v »)|, so the type of |cons′| is now:
\begin{spec}
cons′ : ∀ v′ m → (Logs.ρ l « v »≔ ● (h « v »)) « v′ » ≡ ● m → h′ « v′ » ≡ m
\end{spec}
Instantiating |v′| and |m| to |v| and |h « v »| respectively, then invoking
the |Vec.lookup∘update| lemma leads to a witness of |h′ « v » ≡ h « v »|,
which we use in a rewrite clause to show that |↣′-read| under |h′| does
indeed result in the same |l′| and |e′| as it did under |h|, completing the
proof of |↣′-swap|.

%format ↣′⋆-swap = "\func{{\rightarrowtail\Prime^\star}\text-swap}"
%format cons″ = "\Varid{cons\PPrime}"
%format e′↣⋆e″ = "\Varid{e\Prime{\rightarrowtail^\star}\!e\PPrime}"
%format C⊢_↣′⋆_ = "\type{C{\vdash}\anonymous{\rightarrowtail\Prime^\star}\anonymous}"
%format C⊢ = "\prefix{\type{C{\vdash}}}"
%format trans = "\func{trans}"
Of course, we can generalise |↣′-swap| to |H⊢_↣′⋆_| sequences of any length:
\begin{code}
↣′⋆-swap : ∀ {h′ l e l″ e″} → Consistent h′ l″ →
  H⊢ l , e ↣′⋆ l″ , e″ → h′ ⊢ l , e ↣′⋆ l″ , e″
↣′⋆-swap {h′} cons″ = snd ∘ Star.gfold id C⊢_↣′⋆_ trans (cons″ , ε) where
  C⊢_↣′⋆_ : Logs × Expression′ → Logs × Expression′ → Set
  C⊢ (l , e) ↣′⋆ (l′ , e′) = Consistent h′ l × h′ ⊢ l , e ↣′⋆ l′ , e′
  trans : ∀ {x x′ x″} → H⊢ x ↣′ x′ → C⊢ x′ ↣′⋆ x″ → C⊢ x ↣′⋆ x″
  trans (h , e↣e′) (cons′ , e′↣⋆e″) =
    ↣′-Consistent′ cons′ e↣e′ , ↣′-swap cons′ e↣e′ ◅ e′↣⋆e″
\end{code}
The auxiliary |C⊢_↣′⋆_| relation pairs |_⊢_↣′⋆_| with a proof of the
consistency of |h′| with the read logs at the start of the sequence, while
|trans| corresponds to the transitivity of a one-step |H⊢_↣′_| and
|C⊢_↣′⋆_|. The proof of |↣′⋆-swap| results from folding |trans| over the
|H⊢_↣′⋆_| argument, using a final |snd| to discard the consistency part of
the |C⊢_↣′⋆_| pair.

What we have shown with |↣′⋆-swap| is that provided the read log is
consistent with the heap just before the commit, then regardless of what
different heaps the transaction had originally used, re-running the
transaction with just the pre-commit heap---without any intervening heap
mutations---delivers the same result.

%format ↣′→↦′ = "\func{{\rightarrowtail\Prime}{\rightarrow}{\mapsto\Prime}}"
%format ↦′-read-h-v = "\Varid{{\rightarrowtail\Prime}\text-read\text-h\text-v}"
It remains for us to show that we can construct an equivalent transition
under the stop-the-world semantics, given one that uses the same pre-commit
heap. We start by taking a single log-based transition step and returning
its corresponding stop-the-world rule, while showing that heap-log
equivalence is preserved:
\begin{code}
↣′→↦′ : ∀ {h l e l′ e′ h₀} →
            Equivalent h₀ l h    →  h₀ ⊢ l , e ↣′ l′ , e′ →
  ∃ λ h′ →  Equivalent h₀ l′ h′  ×  h , e ↦′ h′ , e′
↣′→↦′ equiv ↣′-ℕ = _ , equiv , ↦′-ℕ
↣′→↦′ equiv (↣′-R  m    b↣b′)  = Σ.map₃ (↦′-R  m)  (↣′→↦′ equiv b↣b′)
↣′→↦′ equiv (↣′-L  b    a↣a′)  = Σ.map₃ (↦′-L  b)  (↣′→↦′ equiv a↣a′)
↣′→↦′ equiv (↣′-writeE  e↣e′)  = Σ.map₃ ↦′-writeE  (↣′→↦′ equiv e↣e′)
↣′→↦′ equiv ↣′-writeℕ = _ , Write-Equivalent equiv , ↦′-writeℕ
↣′→↦′ {h} equiv (↣′-read l v) with equiv v | ↦′-read h v
... |  equiv-v | ↦′-read-h-v with Logs.ω l « v »
...    |  ● m rewrite equiv-v = _ , equiv , ↦′-read-h-v
...    |  ○ with Logs.ρ l « v » | ≡.inspect (_«_» (Logs.ρ l)) v
...       |  ● m | _ rewrite equiv-v = _ , equiv , ↦′-read-h-v
...       |  ○ | ‹ ρ«v»≡○ › rewrite ≡.sym equiv-v = _
             , Read-Equivalent ρ«v»≡○ equiv , ↦′-read-h-v
\end{code}
The above definition has an identical structure to that of |↦′→↣′| from the
previous section, using the same |Write-Equivalent| and |Read-Equivalent|
lemmas for the |↣′-writeℕ| and |↣′-read| cases respectively, so we will let
the code speak for itself.

%format ↣′⋆→↦′⋆ = "\func{{\rightarrowtail\Prime^\star}{\rightarrow}{\mapsto\Prime^\star}}"
%format e′↦⋆e″ = "\Varid{e\Prime{\mapsto^\star}\!e\PPrime}"
%format cons″ = "\Varid{cons\PPrime}"
%format equiv′ = "\Varid{equiv\Prime}"
%format equiv″ = "\Varid{equiv\PPrime}"
Finally we extend |↣′→↦′| to handle any |_⊢_↣′⋆_| sequence, in the same
manner as |↦′⋆→↣′⋆|:
\begin{code}
↣′⋆→↦′⋆ : ∀ {h l e l′ e′ h₀} →
            Equivalent h₀ l h    →  h₀ ⊢ l , e ↣′⋆ l′ , e′ →
  ∃ λ h′ →  Equivalent h₀ l′ h′  ×  h , e ↦′⋆ h′ , e′
↣′⋆→↦′⋆ equiv ε = _ , equiv , ε
↣′⋆→↦′⋆ equiv (e↣e′ ◅ e′↣⋆e″) with ↣′→↦′ equiv e↣e′
... |  h′ , equiv′ , e↦e′ with ↣′⋆→↦′⋆ equiv′ e′↣⋆e″
...    | h″ , equiv″ , e′↦⋆e″ = h″ , equiv″ , e↦e′ ◅ e′↦⋆e″
\end{code}

\noindent To summarise, given a visible transition in which the log-based
semantics commits a transaction, we can use |↣-extract| to obtain the final
successful sequence of |_⊢_↣′_| transitions leading up to the commit, along
with the heaps used at each step. The |↣′⋆-swap| lemma then lets us swap the
different heaps for the pre-commit heap, while |↣′⋆→↦′⋆| maps each log-based
transition to their corresponding stop-the-world ones, allowing us to
construct an equivalent transaction under the stop-the-world semantics.

% vim: ft=tex fo-=m fo-=M:

