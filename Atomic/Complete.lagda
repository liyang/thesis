%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
%include Atomic/Combined.lagda
%include Atomic/Transaction.lagda
\end{comment}
%endif

%if False
\begin{code}
module Complete where

open import Common
open import Heap
open import Logs
open import Language
open import Combined
open import Transaction
\end{code}
%endif

\subsection{Completeness of Log-Based Transactions}

%-- Zero or more ↦-mutate rules followed by ↦-atomic.
%format ↦-extract = "\func{{\mapsto}\text-extract}"
%format e↦′⋆m = "\Varid{e{\mapsto\Prime^\star}m}"
%format h₁≟h₀ = "\Varid{h_1{\stackrel?=}h_0}"
We shall tackle the completeness part of transactional correctness first, as
it is the simpler of the two directions. Let us begin by defining a function
that extracts the |_↦′⋆_| sequence from a visible transition starting from
|atomic e|:
\begin{code}
↦-extract : ∀ {α h e h″ c″ e″} →
  α ▹ h , ↦: , atomic e ⤇ h″ , c″ , e″ →
  ∃₂ λ h₀ m → α , c″ , e″ ≡ ☢ , ↦: , # m ×
  Dec (h ≡ h₀) × h₀ , e ↦′⋆ h″ , # m
↦-extract (⤇: α≢τ ε (↠-↦ (↦-mutate h₁))) = ⊥-elim (α≢τ ≡.refl)
↦-extract (⤇: α≢τ ε (↠-↦ (↦-atomic e↦′⋆m))) =
  _ , _ , ≡.refl , yes ≡.refl , e↦′⋆m
↦-extract (⤇: α≢τ (↠-↦ (↦-mutate h₁) ◅ e↠⋆e′) e′↠e″)
     with ↦-extract (⤇: α≢τ e↠⋆e′ e′↠e″)
...  |  h₀ , m , ≡.refl , h₁≟h₀ , e↦′⋆m =
        h₀ , m , ≡.refl , _ ≟Heap h₀ , e↦′⋆m
\end{code}
Under the stop-the-world semantics, the only non-silent transition |atomic
e| can make is |↦-atomic|, which carries the |e↦′⋆m| we desire. The silent
sequence preceding it may contain some number of |↦-mutate| rules, for which
we return an element of |Dec (h ≡ h₀)| to indicate whether the heap was
changed before the transaction itself. We also give a proof that will allows
us to refine |α|, |c″| and |e″|.

%format ↦′→↣′ = "\func{{\mapsto\Prime}{\rightarrow}{\rightarrowtail\Prime}}"
%format ↣′-read-l-v = "\Varid{{\rightarrowtail\Prime}\text-read\text-l\text-v}"
Next, we show that for each of the transaction rules under the
stop-the-world semantics, there is an corresponding rule that preserves the
equivalence of the heap and log of the log-based semantics with the in-place
modified heap of the stop-the-world semantics:
\begin{code}
↦′→↣′ : ∀ {l h₀ h e h′ e′} →
            Equivalent h₀ l h    →  h , e ↦′ h′ , e′ →
  ∃ λ l′ →  Equivalent h₀ l′ h′  ×  h₀ ⊢ l , e ↣′ l′ , e′
↦′→↣′ equiv ↦′-ℕ = _ , equiv , ↣′-ℕ
↦′→↣′ equiv (↦′-R  m    b↦b′)  = Σ.map₃ (↣′-R  m)  (↦′→↣′ equiv b↦b′)
↦′→↣′ equiv (↦′-L  b    a↦a′)  = Σ.map₃ (↣′-L  b)  (↦′→↣′ equiv a↦a′)
↦′→↣′ equiv (↦′-writeE  e↦e′)  = Σ.map₃ ↣′-writeE  (↦′→↣′ equiv e↦e′)
\end{code}
For |↦′-ℕ|, this is simply |↣′-ℕ|; the corresponding rules for |↦′-R|,
|↦′-L| and |↦′-writeE| are similarly named, and we can simply map them over
a recursive call to fulfil the goal.

The |↦′-writeℕ| rule that modifies the heap directly has a counterpart
|↣′-writeℕ| that updates the write log, and we use the |Write-Equivalent|
lemma given previously to show that equivalence is maintained:
\begin{code}
↦′→↣′ equiv ↦′-writeℕ = _ , Write-Equivalent equiv , ↣′-writeℕ
↦′→↣′ {l} equiv (↦′-read h₀ v) with equiv v | ↣′-read l v
... |  equiv-v | ↣′-read-l-v with Logs.ω l « v »
...    |  ● m rewrite equiv-v = _ , equiv , ↣′-read-l-v
...    |  ○  with Logs.ρ l « v » | ≡.inspect (_«_» (Logs.ρ l)) v
...       |  ● m  | _ rewrite equiv-v = _ , equiv , ↣′-read-l-v
...       |  ○    | ‹ ρ«v»≡○ › rewrite ≡.sym equiv-v = _
             , Read-Equivalent ρ«v»≡○ equiv , ↣′-read-l-v
\end{code}
The matching rule for |↦′-read| is of course |↣′-read| in all cases,
although we need to pre-apply it with |l| and |v| and inspect the write and
read logs to allow its type and that of the goal to refine so that they
coincide. In the last alternative when both both logs are empty, the
|Read-Equivalent| lemma lets us show that heap-log equivalence still holds
with the updated read log.

%format ↦′⋆→↣′⋆ = "\func{{\mapsto\Prime^\star}{\rightarrow}{\rightarrowtail\Prime^\star}}"
%format e′↦⋆e″ = "\Varid{e\Prime{\mapsto^\star}e\PPrime}"
%format e′↣⋆e″ = "\Varid{e\Prime{\rightarrowtail^\star}e\PPrime}"
%format cons″ = "\Varid{cons\PPrime}"
%format equiv′ = "\Varid{equiv\Prime}"
%format equiv″ = "\Varid{equiv\PPrime}"
Lastly we generalise the above to transition sequences of any length,
proceeding in the usual manner by applying |↦′→↣′| to each transition from
left to right:
\begin{code}
↦′⋆→↣′⋆ : ∀ {h₀ l h e h′ e′} →
            Equivalent h₀ l h    →  h , e  ↦′⋆  h′ , e′ →
  ∃ λ l′ →  Equivalent h₀ l′ h′  ×  h₀ ⊢ l , e  ↣′⋆ l′ , e′
↦′⋆→↣′⋆ equiv ε = _ , equiv , ε
↦′⋆→↣′⋆ equiv (e↦e′ ◅ e′↦⋆e″) with ↦′→↣′ equiv e↦e′
... |  l′ , equiv′ , e↣e′ with ↦′⋆→↣′⋆ equiv′ e′↦⋆e″
...    | l″ , equiv″ , e′↣⋆e″ = l″ , equiv″ , e↣e′ ◅ e′↣⋆e″
\end{code}

\noindent Using the combination of |↦-extract| and |↦′⋆→↣′⋆|, we can
construct a transition sequence under the log-based semantics given
a visible transition under the stop-the-world semantics, such that the heap
and final log of the former is equivalent to the final heap of the latter.

% vim: ft=tex fo-=m fo-=M:

