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

module Verified.InspectExp where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language
\end{code}
%endif

\subsection{Classifying Expression Transitions}

% this is really half-way to a big-step semantics\ldots

%format ExpCase = "\type{ExpCase}"
%format exp-# = "\cons{exp\text-\texttt\#}"
%format exp-⊕ = "\cons{exp\text-\oplus}"
%format exp-read = "\cons{exp\text-read}"
%format exp-write = "\cons{exp\text-write}"
%format a↦⋆m = "a{\mapsto}^\star{}m"
%format a′↦⋆m = "a\Prime{\mapsto}^\star{}m"
%format b↦⋆n = "b{\mapsto}^\star{}n"
%format b′↦⋆n = "b\Prime{\mapsto}^\star{}n"
%format a⊕b↦⋆m+n = "a{\oplus}b{\mapsto}^\star{}m{+}n"
%format rwLog-≗ = "rwLog\text-{\circeq}"
Rather than working directly with unstructured sequences of expression
transitions, we can classify them into one of four cases. The following
|ExpCase| type---indexed on sequences from expressions to their final
values---enumerates the possibilities:
\savecolumns
\begin{code}
data ExpCase {h} : ∀ {e h′ m} → STM‣ h ∧ e ↦⋆ h′ ∧ # m → Set where
  exp-# : ∀ {m} → ExpCase {m = m} ε
\end{code}
In the first case, we have the empty sequence, where the initial expression
is already in the form of a value. Here, |ε| forces the implicit indices |e|
and |h′| to |# m| and |h| respectively. The second constructor |exp-⊕|
corresponds to transitions starting from expressions of the form |a ⊕ b|:
\restorecolumns
\begin{code}
  exp-⊕ : ∀ {a h′} m b {h″ n}
    (a↦⋆m : STM‣ h ∧ a ↦⋆ h′ ∧ # m)
    (b↦⋆n : STM‣ h′ ∧ b ↦⋆ h″ ∧ # n) → let
    a⊕b↦⋆m+n = ↦⋆-L b a↦⋆m ◅◅ ↦⋆-R m b↦⋆n ◅◅ ↦-⊞ ◅ ε in
    (rwLog-≗ : rwLog a⊕b↦⋆m+n ≗ rwLog b↦⋆n ∘ rwLog a↦⋆m) →
    ExpCase a⊕b↦⋆m+n
\end{code}
A complete sequence |a⊕b↦⋆m+n| comprises of the concatenation of two
subsequences |a↦⋆m| and |b↦⋆n|---suitably lifted using |↦⋆-L| and |↦⋆-R|, to
transition from |a ⊕ b| to |# m ⊕ b|, then |# m ⊕ # n|---followed by a single
invocation of the |↦-⊞| rule to give |# (m + n)| as the final value. The
final |rwLog-≗| argument gives a proof of the fact that the overall
transition sequence has the same heap side-effects as the composition of the
two unlifted subsequences.

For an expression |read v|, the transition sequence comprises of a single
|↦-read| rule, which forces the indices |h′| and |m| to |h| and |h « v »|
respectively:
\restorecolumns
\begin{code}
  exp-read : ∀ {v} → ExpCase (↦-read {v} ◅ ε)
\end{code}

%format wm↦⋆m = "wm{\mapsto}^\star{}m"
%format we↦⋆m = "we{\mapsto}^\star{}m"
\noindent Finally the |exp-write| case corresponds to initial expressions of
the form |write v e|:
\restorecolumns
\begin{code}
  exp-write : ∀ {h′ e} v m
    (e↦⋆m : STM‣ h ∧ e ↦⋆ h′ ∧ # m) → let
    wm↦⋆m = ↦-writeℕ ◅ ε
    we↦⋆m = ↦⋆-writeE v e↦⋆m ◅◅ wm↦⋆m in
    (rwLog-≗ : rwLog we↦⋆m ≗ rwLog wm↦⋆m ∘ rwLog e↦⋆m) →
    ExpCase we↦⋆m
\end{code}
Here, the complete transition sequence |we↦⋆m| from |write v e| to |# m|
comprises of a subsequence |e↦⋆m|---suitably lifted using the |↦⋆-writeE|
helper---followed by a |↦-writeℕ| rule. As per the |exp-⊕| constructor, we
also include a proof that the side effects of the each component composes in
a compatible manner.

%format inspectExp = "\func{inspectExp}"
It remains for us to show that any sequence |STM‣ h ∧ e ↦⋆ h′ ∧ # m| falls
into one of the four possibilities given by the |ExpCase| type. This is
given by the following |inspectExp| function, which proceeds by induction on
such sequences:
\begin{code}
inspectExp : ∀ {h e h′ m} →
  (e↦⋆m : STM‣ h ∧ e ↦⋆ h′ ∧ # m) → ExpCase e↦⋆m
inspectExp ε = exp-#
\end{code}
For an empty sequence, the proof is trivial as the initial expression must
be just |# m|. Otherwise, we perform case analysis on the first rule of the
sequence.

The |↦-⊞| rule applies to expressions of the form |# m ⊕ # n|, after which
no further transitions are possible. This is handled using an impossible
pattern in the first clause below:
\begin{code}
inspectExp (↦-⊞ ◅ () ◅ _)
inspectExp (↦-⊞ ◅ ε) = exp-⊕ _ _ ε ε λ _ → ≡.refl
\end{code}
In the second clause, the first two arguments of |exp-⊕| are inferable from
the implicit arguments to |inspectExp|, so we need not supply them
explicitly. Since |# m| and |# n| are already in value form, their
respective transition sequences are just the empty ones. The final argument
showing that |rwLog (↦-⊞ ◅ ε) ≗ rwLog ε ∘ rwLog ε| is trivial, as both sides
reduce to the identity function.

The |↦-R| rule on the other hand applies to expressions of the form |#
m ⊕ b|:
%format rwLog-≗-b′ = "rwLog\text-{\circeq}\text-b\Prime{}"
%format rwLog-≗-b = "\func{rwLog\text-{\circeq}\text-b}"
%format m⊕b↦⋆m+n = "m{\oplus}b{\mapsto}^\star{}m{+}n"
%format m⊕b′↦⋆m+n = "m{\oplus}b\Prime{\mapsto}^\star{}m{+}n"
\begin{code}
inspectExp (↦-R b↦b′ ◅ m⊕b′↦⋆m+n) with inspectExp m⊕b′↦⋆m+n
inspectExp (↦-R b↦b′ ◅ ._) | exp-⊕ m b′ (() ◅ _) b′↦⋆n rwLog-≗-b′
inspectExp (↦-R b↦b′ ◅ ._) | exp-⊕ m b′ ε        b′↦⋆n rwLog-≗-b′
  = exp-⊕ m _ ε b↦⋆n rwLog-≗-b where
    b↦⋆n = b↦b′ ◅ b′↦⋆n
    m⊕b↦⋆m+n = ↦⋆-R m b↦⋆n ◅◅ ↦-⊞ ◅ ε
    rwLog-≗-b : rwLog m⊕b↦⋆m+n ≗ rwLog b↦⋆n
    rwLog-≗-b (ρ ∧ ω) with STM→rw b↦b′
    ... | nothing = rwLog-≗-b′ (ρ ∧ ω)
    ... | just (v ∧ inj₁ h) = rwLog-≗-b′ (update-rLog h ρ ω v ∧ ω)
    ... | just (v ∧ inj₂ n) = rwLog-≗-b′ (ρ ∧ ω « v »≔ just n)
\end{code}
Induction on the remainder of the sequence supplies us with |b′↦⋆n| and the
witness |rwLog-≗-b′|. We can derive a corresponding proof |rwLog-≗-b| for
|b| by invoking the latter with a updated pair of logs, dependent on whether
the |b↦b′| transition constitutes a read or write, or neither. The |↦-L|
rule is handled in the same way:
%format rwLog-≗-a′ = "rwLog\text-{\circeq}\text-a\Prime{}"
%format rwLog-≗-a = "\func{rwLog\text-{\circeq}\text-a}"
\begin{code}
inspectExp (↦-L a↦a′ ◅ a′⊕b↦⋆m+n) with inspectExp a′⊕b↦⋆m+n
inspectExp (↦-L a↦a′ ◅ ._) | exp-⊕ m b a′↦⋆m b↦⋆n rwLog-≗-a′
  = exp-⊕ m b a↦⋆m b↦⋆n rwLog-≗-a where
  a↦⋆m = a↦a′ ◅ a′↦⋆m
  a⊕b↦⋆m+n = ↦⋆-L b a↦⋆m ◅◅ ↦⋆-R m b↦⋆n ◅◅ ↦-⊞ ◅ ε
  rwLog-≗-a : rwLog a⊕b↦⋆m+n ≗ rwLog b↦⋆n ∘ rwLog a↦⋆m
  rwLog-≗-a (ρ ∧ ω) with STM→rw a↦a′
  ... | nothing = rwLog-≗-a′ (ρ ∧ ω)
  ... | just (v ∧ inj₁ h) = rwLog-≗-a′ (update-rLog h ρ ω v ∧ ω)
  ... | just (v ∧ inj₂ n) = rwLog-≗-a′ (ρ ∧ ω « v »≔ just n)
\end{code}

\noindent Next, a transition sequence comprising a single |↦-read| rule is
handled with the |exp-read| constructor:
\begin{code}
inspectExp (↦-read ◅ ε) = exp-read
inspectExp (↦-read ◅ () ◅ _)
\end{code}
No further rules can follow a |↦-read|, since the resulting expression is
just a value. The same reasoning also applies when writing a value to the
heap:
\begin{code}
inspectExp (↦-writeℕ ◅ () ◅ _)
inspectExp (↦-writeℕ ◅ ε) = exp-write _ _ ε λ _ → ≡.refl
\end{code}
For a transition sequence comprising a single |↦-writeℕ|, we just return the
|exp-write| constructor. The heap, variable and value arguments can be
inferred by Agda; we need only supply the empty reduction sequence |ε : STM‣
h ∧ # m ↦⋆ h ∧ # m| and a trivial proof regarding the side-effects of the
transition sequences.

The remaining rule is |↦-writeE|, covering expressions of the form
|write v e|, where |e| has yet to reduce to a value. This is handled in
a manner similar to the |↦-L| and |↦-R| rules, by induction on the remainder
of the transition sequence:
%format rwLog-≗-e′ = "rwLog\text-{\circeq}\text-e\Prime{}"
%format rwLog-≗-e = "\func{rwLog\text-{\circeq}\text-e}"
%format we′↦⋆m = "we\Prime{\mapsto}^\star{}m"
%format e′↦⋆m = "e\Prime{\mapsto}^\star{}m"
%format wm↦⋆m = "wm{\mapsto}^\star{}m"
\begin{code}
inspectExp (↦-writeE e↦e′ ◅ we′↦⋆m) with inspectExp we′↦⋆m
inspectExp (↦-writeE e↦e′ ◅ ._) | exp-write v m e′↦⋆m rwLog-≗-e′
  = exp-write v m e↦⋆m rwLog-≗-e where
  e↦⋆m = (e↦e′ ◅ e′↦⋆m); wm↦⋆m = ↦-writeℕ ◅ ε
  we↦⋆m = ↦⋆-writeE v e↦⋆m ◅◅ wm↦⋆m
  rwLog-≗-e : rwLog we↦⋆m ≗ rwLog wm↦⋆m ∘ rwLog e↦⋆m
  rwLog-≗-e (ρ ∧ ω) with STM→rw e↦e′
  ... | nothing = rwLog-≗-e′ (ρ ∧ ω)
  ... | just (v′ ∧ inj₂ n) = rwLog-≗-e′ (ρ ∧ ω « v′ »≔ just n)
  ... | just (v′ ∧ inj₁ h) = rwLog-≗-e′ (update-rLog h ρ ω v′ ∧ ω)
\end{code}


% vim: ft=tex fo-=m fo-=M:

