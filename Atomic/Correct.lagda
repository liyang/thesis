%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
%include Atomic/Combined.lagda
%include Atomic/Bisimilar.lagda
%include Atomic/Transaction.lagda
%include Atomic/Complete.lagda
%include Atomic/Sound.lagda
%include Atomic/Lemmas.lagda
\end{comment}
%endif

%if False
\begin{code}
module Correct where

open import Common
open import Heap
open import Logs
open import Language
open import Combined
open import Bisimilar
open import Transaction
open import Complete
open import Sound
open import Lemmas
\end{code}
%endif

\section{Bisimilarity of Semantics}

The proof that the stop-the-world semantics for our Atomic language is
bisimilar to the log-based semantics proceeds for the most part by
corecursion on the applicable transition rules, as well as structural
recursion in the case of |a ⊕ b : Expression|s when either |a| or |b| can
make further transitions. We will show each of the cases individually, then
assemble the pieces to give the full correctness property.

%format correct-# = "\func{correct\text-\texttt\#}"
We begin by showing that bisimilarity holds for numbers, where no further
transitions are possible:
\begin{code}
correct-# : ∀ {h m} → h , # m ⊢ ↦: ≈ ↣: ○
correct-# = ♯ (⊥-elim ∘ #⤇̸) & ♯ (⊥-elim ∘ #⤇̸)
\end{code}
The proof makes use of a trivial |#⤇̸| lemma showing that no visible
transitions are possible from expressions of the form |# m|, under either
semantics.


%format correct-⊕ℕ = "\func{correct\text-{\oplus}\mathbb{N}}"
\subsection{Addition}

%format ↦≼↣ = "\func{{\mapsto}{\preccurlyeq}{\rightarrowtail}}"
%format ↣≼↦ = "\func{{\rightarrowtail}{\preccurlyeq}{\mapsto}}"
For the first non-trivial case, we define |correct-⊕ℕ| which handles
expressions of the form |# m ⊕ # n|. In this case, the only applicable rules
are |↦-ℕ| and |↣-ℕ|. We show each direction of bisimilarity separately:
\savecolumns
\begin{code}
correct-⊕ℕ : ∀ {h m n} → h , # m ⊕ # n ⊢ ↦: ≈ ↣: ○
correct-⊕ℕ {h} {m} {n} = ♯ ↦≼↣ & ♯ ↣≼↦ where
  ↦≼↣ : h , # m ⊕ # n ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ ε (↠-↦ ↦-ℕ)) =
    _ , ⤇: α≢τ ε (↠-↣ ↣-ℕ) , correct-#
  ↦≼↣ (⤇: α≢τ ε (↠-↦ (↦-R ._ b↦b′))) = ⊥-elim (#↦̸ b↦b′)
  ↦≼↣ (⤇: α≢τ ε (↠-↦ (↦-L ._ a↦a′))) = ⊥-elim (#↦̸ a↦a′)
  ↦≼↣ (⤇: α≢τ (↠-↦ (↦-R ._ b↦b′) ◅ _) _) = ⊥-elim (#↦̸ b↦b′)
  ↦≼↣ (⤇: α≢τ (↠-↦ (↦-L ._ a↦a′) ◅ _) _) = ⊥-elim (#↦̸ a↦a′)
\end{code}
To show that the log-based semantics can simulate the stop-the-world
semantics we inspect the visible transition that |# m ⊕ # n| makes under the
latter. As hinted above, the only applicable transition is |↦-ℕ|, for which
we use |↣-ℕ| to show that the log-based semantics can follow. The resulting
expression of |# (m + n)| is then bisimilar by the |correct-#| lemma. The
remaining clauses amount to showing that further transitions by |# m| or |#
n| alone are impossible.

The proof for the opposite direction proceeds in exactly the same way:
\restorecolumns
\begin{code}
  ↣≼↦ : h , # m ⊕ # n ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ ε (↠-↣ ↣-ℕ)) =
    _ , ⤇: α≢τ ε (↠-↦ ↦-ℕ) , ≈-sym correct-#
  ↣≼↦ (⤇: α≢τ ε (↠-↣ (↣-R ._ b↣b′))) = ⊥-elim (#↣̸ b↣b′)
  ↣≼↦ (⤇: α≢τ ε (↠-↣ (↣-L ._ a↣a′))) = ⊥-elim (#↣̸ a↣a′)
  ↣≼↦ (⤇: α≢τ (↠-↣ (↣-R ._ b↣b′) ◅ _) _) = ⊥-elim (#↣̸ b↣b′)
  ↣≼↦ (⤇: α≢τ (↠-↣ (↣-L ._ a↣a′) ◅ _) _) = ⊥-elim (#↣̸ a↣a′)
\end{code}


%format correct-⊕R = "\func{correct\text-{\oplus}R}"
\subsection{Right Evaluation}

%format b⊢↦≈↣ = "\Varid{b{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format b″⊢↦≈↣ = "\Varid{b\PPrime{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format b″⊢↣≈↦ = "\Varid{b\PPrime{\vdash}{\rightarrowtail}{\approx}{\mapsto}}"
\noindent Given an induction hypothesis of |h , b ⊢ ↦: ≈ ↣: ○|, we can show
that the two semantics are bisimilar for expressions of the form |# m ⊕ b|:
\savecolumns
\begin{code}
correct-⊕R : ∀ {h m b} → h , b ⊢ ↦: ≈ ↣: ○ → h , # m ⊕ b ⊢ ↦: ≈ ↣: ○
correct-⊕R {h} {m} {b} b⊢↦≈↣ = ♯ ↦≼↣ & ♯ ↣≼↦ where
\end{code}
%format b≡n = "\Varid{b{\equiv}n}"
%format b↠⋆b′ = "\Varid{b{\twoheadrightarrow^\star_\tau}b\Prime}"
%format b′↠b″ = "\Varid{b\Prime{\twoheadrightarrow}b\PPrime}"
%format b⤇b″ = "\Varid{b{\Mapsto}b\PPrime}"
%format c″≡↣ = "\Varid{c\PPrime{\equiv}{\rightarrowtail}}"
%format c″≡↦ = "\Varid{c\PPrime{\equiv}{\mapsto}}"
%format m⊕b⤇m⊕b″ = "\Varid{m{\oplus}b{\Mapsto}m{\oplus}b\PPrime}"
For the completeness direction, we first use a |↠⋆/↦-R| helper that peels
off any |↦-R| rules in the visible transition starting from |# m ⊕ b|. This
is not always possible: when |b| is already a number |# n|, the full
expression cannot make any transitions under |↦-R|, so it returns a witness
|b≡n| that allows us to defer the rest of the proof to one half of the
|correct-⊕ℕ| lemma given earlier:
\restorecolumns
\begin{code}
  ↦≼↣ : h , # m ⊕ b ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↦-R α≢τ e↠⋆e′ e′↠e″
  ... |  inl (n , b≡n , ≡.refl , ≡.refl , ≡.refl) rewrite b≡n =
         ♭ (≈→≼ correct-⊕ℕ) (⤇: α≢τ ε (↠-↦ ↦-ℕ))
\end{code}
Otherwise |b| must make some visible transition under |↦-R|, and |↠⋆/↦-R|
returns |b↠⋆b′ : h , ↦: , b ↠⋆ h′ , ↦: , b′| as well as |b′↠b″ : α ▹ h′ , ↦:
, b′ ↠ h″ , ↦: , b″|, essentially constituting a visible transition made by
just |b| itself. The latter transition is labelled with the same |α| as the
original |e′↠e″|, which in turn has been refined to |h′ , ↦: , # m ⊕ b′ ↠⋆
h″ , ↦: , # m ⊕ b″| by the two equality proofs returned from |↠⋆/↦-R|:
\restorecolumns
\begin{code}
  ... |  inr (h′ , b′ , h″ , b″ , ≡.refl , ≡.refl , b↠⋆b′ , b′↠b″)
         with ♭ (≈→≼ b⊢↦≈↣) (⤇: α≢τ b↠⋆b′ b′↠b″)
  ...    |  c″ , b⤇b″ , b″⊢↦≈↣ with ⤇∘↣-R m b⤇b″
  ...       |  c″≡↣ , m⊕b⤇m⊕b″ rewrite c″≡↣ =
               _ , m⊕b⤇m⊕b″ , correct-⊕R b″⊢↦≈↣
\end{code}
Next we invoke one half of the induction hypothesis |b⊢↦≈↣| with the
aforementioned stop-the-world visible transition of |⤇: α≢τ b↠⋆b′ b′↠b″|,
which returns an equivalent log-based visible transition |b⤇b″ : α ▹ h , ↣:
○ , b ⤇  h″ , ↣: ○ , b″|. Another lemma |⤇∘↣-R| then replaces the |↦-R|
rules peeled off earlier with their corresponding |↣-R| rules, and
a corecursive call to |correct-⊕R| completes this part of the proof.

The definitions of |↠⋆/↦-R| and |⤇∘↣-R| are straightforward but rather
tedious, and they can be found in the full source code on the author's
website.

%format ↦≈↣ = "\func{{\mapsto}{\approx}{\rightarrowtail}}"
%format ↣≈↦ = "\func{{\rightarrowtail}{\approx}{\mapsto}}"
The soundness direction operates in exactly the same fashion, so we shall be
brief with the similar details, and focus on the differences:
\restorecolumns
\begin{code}
  ↣≼↦ : h , # m ⊕ b ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↣-R α≢τ e↠⋆e′ e′↠e″
  ... |  inl (n , b≡n , ≡.refl , ≡.refl , ≡.refl) rewrite b≡n =
         ♭ (≈→≽ correct-⊕ℕ) (⤇: α≢τ ε (↠-↣ ↣-ℕ))
  ... |  inr (h′ , t′ , b′ , h″ , b″ , ≡.refl , ≡.refl , b↠⋆b′ , b′↠b″)
         with ♭ (≈→≽ b⊢↦≈↣) (⤇: α≢τ b↠⋆b′ b′↠b″)
  ...    |  c″ , b⤇b″ , b″⊢↣≈↦ with ⤇∘↦-R m b⤇b″
  ...       |  c″≡↦ , m⊕b⤇m⊕b″ rewrite c″≡↦ =
               _ , m⊕b⤇m⊕b″ , ≈→≽ ↦≈↣ & ≈→≼ ↦≈↣ where
    ↦≈↣ = correct-⊕R (≈-sym b″⊢↣≈↦)
\end{code}
A |↠⋆/↣-R| helper first attempts to peel off any |↣-R| from |e↠⋆e′| and
|e′↠e″|; we invoke |correct-⊕ℕ| should this not be possible. Otherwise the
induction hypothesis gives us a stop-the-world visible transition |b⤇b″|,
and we can use |⤇∘↦-R| to turn this back into |m⊕b⤇m⊕b″|. To show that the
semantics are bisimilar for |h″ , # m ⊕ b″|, one might be tempted to write
|≈-sym (correct-⊕R (≈-sym b″⊢↣≈↦))|. However Agda's termination/productivity
checker requires all corecursive calls be guarded by constructors, and
cannot see that the function |≈-sym| preserves productivity. We get around
this issue by inlining the outer |≈-sym|, since record projections---namely
|≈→≼| and |≈→≽|---are seen to be productivity-preserving.


%format correct-⊕L = "\func{correct\text-{\oplus}L}"
\subsection{Left Evaluation}

%format a⊢↦≈↣ = "\Varid{a{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format a″⊢↦≈↣ = "\Varid{a\PPrime{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format a″⊢↣≈↦ = "\Varid{a\PPrime{\vdash}{\rightarrowtail}{\approx}{\mapsto}}"
%format ∀b⊢↦≈↣ = "\Varid{{\forall}b{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
The |correct-⊕L| lemma handles cases where the expression on the left of
a |_⊕_| can make further visible transitions. It requires suitable induction
hypotheses on |a| and |b|; in particular that for |b| must be generalised
over any heap:
\savecolumns
\begin{code}
correct-⊕L : ∀ {h a b} → h , a ⊢ ↦: ≈ ↣: ○ →
  (∀ h′ → h′ , b ⊢ ↦: ≈ ↣: ○) → h , a ⊕ b ⊢ ↦: ≈ ↣: ○
correct-⊕L {h} {a} {b} a⊢↦≈↣ ∀b⊢↦≈↣ = ♯ ↦≼↣ & ♯ ↣≼↦ where
\end{code}
%format a≡m = "\Varid{a{\equiv}m}"
%format a↠⋆a′ = "\Varid{a{\twoheadrightarrow^\star_\tau}a\Prime}"
%format a′↠a″ = "\Varid{a\Prime{\twoheadrightarrow}a\PPrime}"
%format a⤇a″ = "\Varid{a{\Mapsto}a\PPrime}"
%format a⊕b⤇a″⊕b = "\Varid{a{\oplus}b{\Mapsto}a\PPrime{\oplus}b}"
The |↠⋆/↦-L| lemma then lets us distinguish between the case when |a| is
just a number |# m|, and the case where |a| makes a visible transition. In
the former case, we pass the proof obligation on to the |correct-⊕R| lemma,
instantiating |∀b⊢↦≈↣| with the current heap:
\restorecolumns
\begin{code}
  ↦≼↣ : h , a ⊕ b ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↦-L α≢τ e↠⋆e′ e′↠e″
  ... |  inl (m , a≡m) rewrite a≡m =
         ♭ (≈→≼ (correct-⊕R (∀b⊢↦≈↣ h))) (⤇: α≢τ e↠⋆e′ e′↠e″)
  ... |  inr (h′ , a′ , h″ , a″ , ≡.refl , ≡.refl , a↠⋆a′ , a′↠a″)
         with ♭ (≈→≼ a⊢↦≈↣) (⤇: α≢τ a↠⋆a′ a′↠a″)
  ...    |  c″ , a⤇a″ , a″⊢↦≈↣ with ⤇∘↣-L b a⤇a″
  ...       |  c″≡↣ , a⊕b⤇a″⊕b rewrite c″≡↣ =
               _ , a⊕b⤇a″⊕b , correct-⊕L a″⊢↦≈↣ ∀b⊢↦≈↣
\end{code}
Otherwise we have a visible transition |⤇: α≢τ a↠⋆a′ a′↠a″|, and the first
inductive hypothesis allows us to obtain a corresponding visible transition
|a⤇a″| under the log-based semantics. Next we replace the |b| on the right
hand side of |_⊕_| using the |⤇∘↣-L| lemma to obtain the transition
|a⊕b⤇a″⊕b|. Since |b| has not made any transitions, a corecursive call with
|a″⊢↦≈↣| and the original |∀b⊢↦≈↣| completes the proof.

We proceed with the soundness half of |correct-⊕L| in exactly the same way
as that of |correct-⊕R|:
\restorecolumns
\begin{code}
  ↣≼↦ : h , a ⊕ b ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↣-L α≢τ e↠⋆e′ e′↠e″
  ... |  inl (m , a≡m) rewrite a≡m =
         ♭ (≈→≽ (correct-⊕R (∀b⊢↦≈↣ h))) (⤇: α≢τ e↠⋆e′ e′↠e″)
  ... |  inr (h′ , t′ , a′ , h″ , a″ , ≡.refl , ≡.refl , a↠⋆a′ , a′↠a″)
         with ♭ (≈→≽ a⊢↦≈↣) (⤇: α≢τ a↠⋆a′ a′↠a″)
  ...    |  c″ , a⤇a″ , a″⊢↣≈↦ with ⤇∘↦-L b a⤇a″
  ...       |  c″≡↦ , a⊕b⤇a″⊕b rewrite c″≡↦ =
               _ , a⊕b⤇a″⊕b , ≈→≽ ↦≈↣ & ≈→≼ ↦≈↣ where
    ↦≈↣ = correct-⊕L (≈-sym a″⊢↣≈↦) ∀b⊢↦≈↣
\end{code}
Observe how |correct-⊕L| shares the same overall structure as |correct-⊕R|.


%format correct-atomic = "\func{correct\text-atomic}"
\subsection{Transactions}

%format mutate? = "\func{mutate?}"
%format e⤇m = "\func{e{\Mapsto}m}"
%format e⤇e″ = "\Varid{e{\Mapsto}e\PPrime}"
%format h≟h₀ = "\Varid{h{\stackrel?=}h_0}"
%format e↣′⋆m = "\Varid{e{\rightarrowtail\Prime^\star}m}"
Finally we arrive at the correctness proof for |atomic| expressions, where
we need to show that transactions run under the stop-the-world semantics
coincide with those using our log-based semantics:
\restorecolumns
\begin{code}
correct-atomic : ∀ {h e} → h , atomic e ⊢ ↦: ≈ ↣: ○
correct-atomic {h} {e} = ♯ ↦≼↣ & ♯ ↣≼↦ where
\end{code}
In the completeness direction, we show that the log-based semantics can
follow the stop-the-world one by simply running the entire transaction
uninterrupted at the same point as the |↦-atomic| rule. First the
|↦-extract| helper from \S\ref{sec:atomic-complete} picks out the |e↦′⋆m|
sequence:
\restorecolumns
\begin{code}
  ↦≼↣ : h , atomic e ⊢ ↦: ≼ ↣: ○
  ↦≼↣ e⤇e″ with ↦-extract e⤇e″
  ... |  h₀ , m , ≡.refl , e↦′⋆m
         with ↦′⋆→↣′⋆ ∅-Equivalent e↦′⋆m
  ...    |  l′ , equiv′ , e↣′⋆m with ↣′⋆-Consistent ∅-Consistent e↣′⋆m
  ...       |  cons′ rewrite ≡.sym (Commit cons′ equiv′) =
               _ , e⤇m , correct-# where
\end{code}
The |↦′⋆→↣′⋆| function from the same section then translates each transition
of |e↦′⋆m| to its log-based equivalent, as well as constructing a proof
|equiv′| of the equivalence of |h₀| and |l′| with the heap |h′| at the end
of the |e↦′⋆m| sequence. By the |↣′⋆-Consistent| lemma, we show that the
consistency of |h₀| and the logs is preserved along the |e↣′⋆m| sequence,
culminating in a witness |cons′| of |Consistent h₀ l′ h′|. Finally,
a rewrite clause using the |Commit| lemma convinces Agda that |Update h₀ l′|
and |h′| are definitionally equal. Since running a transaction results in
just a number |# m|, |correct-#| suffices to show that both semantics are
bisimilar in this case.

%format h≡h₀ = "\Varid{h{\equiv}h_0}"
%format h≢h₀ = "\Varid{h{\not\equiv}h_0}"
It remains for us to construct the visible transition |e⤇m| that uses the
log-based semantics. Should the heap be changed just before the
stop-the-world semantics runs the transaction, we need a corresponding
|↣-mutate| rule in the log-based transition sequence. The |mutate?| helper
checks whether this is necessary:
\restorecolumns
\begin{code}
    mutate? : h  , ↣: ● (e , ∅) , atomic e ↠⋆ h₀ , ↣: ● (e , ∅) , atomic e
    mutate? with h ≟Heap h₀
    ... | yes h≡h₀ rewrite h≡h₀ = ε
    ... | no h≢h₀ = ↠-↣ (↣-mutate h₀) ◅ ε
\end{code}
%{
%format e↠⋆m = "\func{e{\twoheadrightarrow^\star_\tau}m}"
Next, the auxiliary definition |e↠⋆m| lifts each transition of |e↣′⋆m| up to
the |_▹_↠_| level using the |↣-step| rule, prepending a |↣-mutate| rules
when necessary:
\restorecolumns
\begin{code}
    e↠⋆m : h , ↣: ● (e , ∅) , atomic e ↠⋆ h₀ , ↣: ● (e , l′) , atomic (# m)
    e↠⋆m = mutate? ◅◅ Star.gmap _ (↠-↣ ∘ ↣-step) e↣′⋆m

    e⤇m : ☢ ▹ h , ↣: ○ , atomic e ⤇ Update h₀ l′ , ↣: ○ , # m
    e⤇m = ⤇: (λ ()) (↠-↣ ↣-begin ◅ e↠⋆m) (↠-↣ (↣-commit cons′))
\end{code}
Lastly we add a |↣-begin| to beginning of the visible transition to
initialise the transaction state, followed by |e↠⋆m| as the main body of the
transaction. A final non-silent |↣-commit| carrying the |cons′| witness
produces the desired visible transition.
%}

The proof of soundness relies on us having shown that for every transaction
that commits successfully, re-running the entire transaction without any
interference at the point of |↣-commit| computes the same result.
We can then use this uninterrupted transaction sequence to derive
a corresponding visible transition under the stop-the-world semantics.

We start with a similar |↣-extract| lemma defined in
\S\ref{sec:atomic-sound} that returns a sequence |e↣′⋆m : H⊢ ∅ , e ↣′⋆ l′
, # m| where each transition potentially uses a different heap, as well as
the |cons′| proof carried by the final |↣-commit|:
\restorecolumns
\begin{code}
  ↣≼↦ : h , atomic e ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ e⤇e″ with ↣-extract e⤇e″
  ... |  h₀ , l′ , m , ≡.refl , cons′ , e↣′⋆m
         with ↣′⋆→↦′⋆ ∅-Equivalent (↣′⋆-swap cons′ e↣′⋆m)
  ...    |  h′ , equiv′ , e↦′⋆m rewrite ≡.sym (Commit cons′ equiv′) =
            _ , e⤇m , ≈-sym correct-# where
\end{code}
There is one additional step involved: we must use the |↣′⋆-swap| lemma to
replace the different heaps used throughout |e↣′⋆m| with |h₀|---to give
a witness of |h₀ ⊢ ∅ , e ↣′⋆ l′ , # m|---before we can use |↣′⋆→↦′⋆| to
convert this to the sequence |e↦′⋆m : h₀ , e ↦′⋆ h′ , # m|. This is
necessary because the |↣′⋆→↦′⋆| lemma requires its input log-based
transitions to be under the same heap in order to show equivalence
preservation.

The result of both transaction is the same expression |# m|, and we use the
symmetry of the earlier |correct-#| lemma to provide evidence of
bisimilarity. All that is left is to wrap up the stop-the-world
transactional transition sequence |e↦′⋆m| as the visible transition |e⤇m|.
We define a |mutate?| sequence to correspond to any necessary
pre-transaction |↦-mutate| rules,
\restorecolumns
\begin{code}
    mutate? : h , ↦: , atomic e ↠⋆ h₀ , ↦: , atomic e
    mutate? with h ≟Heap h₀
    ... | yes h≡h₀ rewrite h≡h₀ = ε
    ... | no h≢h₀ = ↠-↦ (↦-mutate h₀) ◅ ε

    e⤇m : ☢ ▹ h , ↦: , atomic e ⤇ Update h₀ l′ , ↦: , # m
    e⤇m = ⤇: (λ ()) mutate? (↠-↦ (↦-atomic e↦′⋆m))
\end{code}
which simply slots in as the silent transitions before the final |↦-atomic|,
to give the desired visible transition |e⤇m|. This completes the
bisimilarity proof for transactions.

% deconstructs


\subsection{Putting It Together}

Having shown for each individual case that our stop-the-world and log-based
semantics are indeed bisimilar, all that remains for us is to combine them
to give the proof of bisimilarity for any |Expression|:
%format correct = "\func{correct}"
\begin{code}
correct : ∀ h e → h , e ⊢ ↦: ≈ ↣: ○
correct h (# m) = correct-#
correct h (a ⊕ b) = correct-⊕L (correct h a) (λ h′ → correct h′ b)
correct h (atomic e) = correct-atomic
\end{code}
In the |a ⊕ b| case, observe how |correct-⊕L| is supplied with the induction
hypothesis on |a|, but that for |b| is abstracted over an arbitrary heap
|h′|.

% vim: ft=tex fo-=m fo-=M:

