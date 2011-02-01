%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Language.lagda
%include Verified/Commit.lagda
%include Verified/Lemmas.lagda
%include Verified/InspectExp.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Verified.Completeness where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language
open import Verified.Commit as Commit
open import Verified.Lemmas as Lemmas
open import Verified.InspectExp as InspectExp

open ≡.Reasoning
\end{code}
%endif

\section{Completeness of Log-Based Transactions}

During a transaction, the high-level stop-the-world semantics of the
expression language directly manipulates the heap. A virtual machine on the
other hand accumulates its reads and writes in its transaction log; upon
reaching the |COMMIT| instruction, it either applies the contents of the
write log to the heap, or retries the transaction, depending on wither the
read log is found to be consistent with the heap at that point.

By `completeness of log-based transactions', we mean that the log-based
semantics of the virtual machine can match anything the stop-the-world
semantics of the expression language does. That is, given any complete
sequence of transitions (within a transactional context) from some
expression to its final value, there exists an equivalent sequence of
virtual machine transitions computing the same value such that if the latter
then commits, its side-effects on the heap would be indistinguishable from
that of the former. We will spell this out in concrete terms soon in
\S\ref{sec:verified-complete}.

\input{Verified/InspectExp.lagda}

\subsection{Proof of Completeness}\label{sec:verified-complete}

%Our proof strategy in one direction requires showing that the heap according
%to the stop-the-world semantics is equivalent to the view of the heap from
%within a transaction---that is, overlaid with read and write logs---after
%each corresponding step.

%Given equivalence
%commit -> consistency

The completeness proof takes the straightforward approach of simply running
the entire transaction uninterrupted on the virtual machine, at the same
point as the corresponding |atomic e| expression is evaluated under its
stop-the-world semantics. The bulk of the proof involves showing that
|compile e| performs heap updates equivalent to those made by the expression
|e| itself.
%format STM↦⋆→↣⋆ = "\func{STM{\mapsto}^\star{\rightarrow}{\rightarrowtail}^\star}"
%format ρ′∧ω′ = "\rho\Prime{\wedge}\omega\Prime{}"
%format h₀ρω≗h = "h_0\rho\omega{\circeq}h"
%format h₀⊇ρ = "h_0{\supseteq}\rho{}"
This corresponds to the following definition of |STM↦⋆→↣⋆| that takes an
expression transition sequence from |h ∧ e| to |h′ ∧ # m| with a pair of
equivalence and consistency witnesses for the initial heap and transaction
logs, and returns the corresponding virtual machine transition sequence that
computes the same |m|, together with equivalence and consistency witnesses
for the updated heap and transaction logs:
\begin{code}
STM↦⋆→↣⋆ : ∀ {h h′ e m}
  (e↦⋆m : STM‣ h ∧ e ↦⋆ h′ ∧ # m) {h₀ c σ γ ρ ω} →
  Equivalent h h₀ ρ ω → Consistent h₀ ρ → let
  ρ′∧ω′ = rwLog e↦⋆m (ρ ∧ ω); ρ′ = proj₁ ρ′∧ω′; ω′ = proj₂ ρ′∧ω′ in
  h₀ ∧ ⟨ compile e c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆
    h₀ ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩ ×
  Equivalent h′ h₀ ρ′ ω′ × Consistent h₀ ρ′
STM↦⋆→↣⋆ e↦⋆m h₀ρω≗h h₀⊇ρ with inspectExp e↦⋆m
\end{code}
%format .ε = ".\cons{\varepsilon}"
Using the |inspectExp| defined earlier in this section, we have only four
cases to consider. Matching on the |exp-#| constructor in the first
instance, |e↦⋆m| is forced to be the empty sequence on |h ∧ # m|, written as
the dotted pattern |.ε| below:
\begin{code}
STM↦⋆→↣⋆ .ε h₀ρω≗h h₀⊇ρ | exp-# = ↣τ-PUSH ◅ ε ∧ h₀ρω≗h ∧ h₀⊇ρ
\end{code}
The corresponding virtual machine of |h₀ ∧ ⟨ PUSH m ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩|
can follow by the |↣-PUSH| rule; the supplied equivalence and consistency
witnesses are sufficient as neither |ρ| nor |ω| have changed.

Next, the |exp-⊕| constructor corresponds to matching on transitions from |a
⊕ b| to |# (m + n)|, which carries with it the respective subsequences
|a↦⋆m| and |b↦⋆n|. Note that |e↦⋆m| is forced to be |↦⋆-L b a↦⋆m ◅◅ ↦⋆-R
m b↦⋆n ◅◅ ↦-⊞ ◅ ε|, and we have written in its place the dotted anonymous
pattern rather than to spell it out explicitly:
%format a↣⋆m = "a{\rightarrowtail}^\star{}m"
%format b↣⋆n = "b{\rightarrowtail}^\star{}n"
%format h₀ρ′ω′≗h′ = "h_0\rho\Prime\omega\Prime{\circeq}h\Prime{}"
%format h₀ρ″ω″≗h″ = "h_0\rho\PPrime\omega\PPrime{\circeq}h\PPrime{}"
%format h₀⊇ρ′ = "h_0{\supseteq}\rho\Prime{}"
%format h₀⊇ρ″ = "h_0{\supseteq}\rho\PPrime{}"
\begin{code}
STM↦⋆→↣⋆ {h} ._ {h₀} {c} {σ} {γ} {ρ} {ω} h₀ρω≗h h₀⊇ρ
  | exp-⊕ m b a↦⋆m b↦⋆n rwLog-≗
    with STM↦⋆→↣⋆ a↦⋆m {h₀} {compile b (ADD ∷ c)} {σ} {γ} h₀ρω≗h h₀⊇ρ
... | a↣⋆m ∧ h₀ρ′ω′≗h′ ∧ h₀⊇ρ′
      with STM↦⋆→↣⋆ b↦⋆n {h₀} {ADD ∷ c} {m ∷ σ} {γ} h₀ρ′ω′≗h′ h₀⊇ρ′
...   | b↣⋆n ∧ h₀ρ″ω″≗h″ ∧ h₀⊇ρ″ rewrite rwLog-≗ (ρ ∧ ω)
      = a↣⋆m ◅◅ b↣⋆n ◅◅ ↣τ-ADD ◅ ε ∧ h₀ρ″ω″≗h″ ∧ h₀⊇ρ″
\end{code}
Suitably instantiating the inductive hypotheses for the |a| subexpression,
followed by |b| gives the pair of virtual machine transitions |a↣⋆m| and
|b↣⋆n|, taking us
\begin{spec}
{-"\text{from}\quad"-}  h   ∧ ⟨ ⟨ compile a (compile b (ADD ∷ c)) ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩
{-"\text{to}"-}         h′  ∧ ⟨ ⟨ compile b (ADD ∷ c) ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩ ⟩ {-"\quad\text{,}"-}
{-"\text{then}"-}       h″  ∧ ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ‚ γ ‚ ρ″ ‚ ω″ ⟩ ⟩ {-"\quad\text{.}"-}
\end{spec}
Appending a final |↣τ-ADD| takes the virtual machine to the desired state of
|h″ ∧ ⟨ ⟨ c ‚ m + n ∷ σ ‚ γ ‚ ρ″ ‚ ω″ ⟩ ⟩|. Simply threading the initial
|h₀ρω≗h| and |h₀⊇ρ| through the two inductive hypotheses is sufficient to
construct appropriate witnesses of |h₀ρ″ω″≗h″| and |h₀⊇ρ″|.

For |exp-read|, the |e↦⋆m| argument is forced be to the single transition
|↦-read|, taking |read v| to |# (h « v »)|. This gives the virtual machine
a target of |h₀ ∧ ⟨ c ‚ h « v » ∷ σ ‚ γ ‚ ρ″ ‚ ω ⟩|, along with proof
obligations of |Equivalent h h₀ ρ″ ω| and |Consistent h₀ ρ″|:
%format ↣τ-READ′ = "\func{{\rightarrowtail}\tau\text-READ\Prime}"
%format h₀ρ′ω≗h = "\func{h_0\rho\Prime\omega{\circeq}h}"
%format h₀⊇ρ′ = "\func{h_0{\supseteq}\rho\Prime}"
%format ρ″≡ρ′ = "\func{\rho\PPrime{\equiv}\rho\Prime}"
%format h₀ρω«v»≡h«v» = "h_0\rho\omega\index[v]{\equiv}h\index[v]"
%format ρ′«v′»≡n = "\rho\Prime\index[v\Prime]{\equiv}n"
%format just-inj = "\func{just\text-inj}"
\savecolumns
\begin{code}
STM↦⋆→↣⋆ {h} ._ {h₀} {c} {σ} {γ} {ρ} {ω} h₀ρω≗h h₀⊇ρ | exp-read {v}
  = ↣τ-READ′ ◅ ε ∧ h₀ρ′ω≗h ∧ h₀⊇ρ′ where
  ρ′  = update-rLog h₀  ρ ω v
  ρ″  = update-rLog h   ρ ω v
\end{code}
However note that |ρ″| is in terms of |h|, being derived from the
expression semantics. On the other hand, while |ρ′| corresponds to the
updated read log given by the virtual machine semantics, which is more
convenient for conducting our proofs. These two are in fact the same, as
shown by the |ρ″≡ρ′| lemma:
\restorecolumns
\begin{code}
  ρ″≡ρ′ : ρ″ ≡ ρ′
  ρ″≡ρ′ with h₀ρω≗h v
  ... |  h₀ρω«v»≡h«v» with ω « v »
  ...    |  just m = ≡.refl
  ...    |  nothing with ρ « v »
  ...       | just m = ≡.refl
  ...       | nothing rewrite h₀ρω«v»≡h«v» = ≡.refl
\end{code}
A soon-to-be familiar proof strategy is that of inspect the write log
followed by the read log, mimicking the structure of both |update-rLog| and
|lookupTVar|. Each pattern match refines any terms in the environment
involving either of these functions. For example, matching |ω « v »| with
|just m|, the goal of |update-rLog h ρ ω v ≡ update-rLog h₀ ρ ω v| reduces
to just |ρ ≡ ρ| by the definition of |update-rLog|, which is trivially met
with |≡.refl|. The instantiated heap equivalence term |h₀ρω«v»≡h«v»| is also
eventually refined to a proof of |h₀ « v » ≡ h « v »|, used in the final
case to show the equality of |ρ « v »≔ just (h « v »)| and |ρ « v »≔ just
(h₀ « v »)|.

Using the above lemma, the |↣τ-READ′| transition may be realised in terms of
|↣τ-READ|, after rewriting |ρ″| to |ρ′|, and |h « v »| on top of the goal
stack to |lookupTVar h₀ ρ ω v|:
\restorecolumns
\begin{code}
  ↣τ-READ′ : h₀ ∧ ⟨ READ v ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ
    h₀ ∧ ⟨ c ‚ h « v » ∷ σ ‚ γ ‚ ρ″ ‚ ω ⟩
  ↣τ-READ′ rewrite ≡.sym (h₀ρω≗h v) | ρ″≡ρ′ = ↣τ-READ
\end{code}
For the proof of |Equivalent h h₀ ρ″ ω|, we first simplify the goal with
a pair of rewrites to |lookupTVar h₀ ρ′ ω v′ ≡ lookupTVar h₀ ρ ω v′|, after
which the proof takes one of two paths conditioned on whether |v′| refers to
the same variable as |v|:
\restorecolumns
\begin{code}
  h₀ρ′ω≗h : Equivalent h h₀ ρ″ ω
  h₀ρ′ω≗h v′ rewrite ≡.sym (h₀ρω≗h v′) | ρ″≡ρ′ with v ≟Fin v′
\end{code}
If |v′| and |v| are in fact the same variable, we simply proceed with the
aforementioned recipe, varying only in the use of the |≡.inspect| idiom:
\restorecolumns
\begin{code}
  h₀ρ′ω≗h .v | yes ≡.refl with ω « v »
  ...  |  just m = ≡.refl
  ...  |  nothing with ≡.inspect (ρ « v »)
  ...     |  just m with-≡ ρ«v»≡m
             rewrite ρ«v»≡m | ρ«v»≡m = ≡.refl
  ...     |  nothing with-≡ ρ«v»≡
             rewrite ρ«v»≡ | set-get v ρ (just (h₀ « v »)) = ≡.refl
\end{code}
The two successive rewrites by |ρ«v»≡m| first refines |lookupTVar| then
|update-rLog|, giving a goal of |m ≡ m| that is satisfied by reflexivity.
The last of the above clauses corresponds to reading |v| for the first time,
where we need to show that the newly updated entry in |ρ′| agrees with what
|lookupTVar h₀ ρ ω v| returns, namely that |ρ′ « v » ≡ h₀ « v »|. This is
achieved via the |set-get| lemma.

When |v′| and |v| differ, we have a few more cases to consider. If the
write log already has an entry for |v′|, our proof obligation reduces to
merely |m ≡ m|. Alternatively if |ω « v »| matches |just m|, the read log is
not updated, so both sides of the goal equality becomes |lookupTVar h₀ ρ ω v|:
\restorecolumns
\begin{code}
  h₀ρ′ω≗h v′ | no v≢v′ with ω « v′ » | ω « v »
  ...  |  just m   | _       = ≡.refl
  ...  |  _        | just m  = ≡.refl
  ...  |  nothing  | nothing with ρ « v »
  ...     |  just m = ≡.refl
  ...     |  nothing rewrite set-get′ ρ (just (h₀ « v »)) v≢v′ with ρ « v′ »
  ...        | just m = ≡.refl
  ...        | nothing = ≡.refl
\end{code}
Similarly |ρ′| reduces to just |ρ| itself, if |ρ| already contains an entry
for |v|. Otherwise, we invoke the |set-get′| lemma with the |v≢v′| witness
to show that |ρ′ « v′ » ≡ ρ « v′ »|; that both the original and updated read
logs coincide at |v′|, whatever that may be. After a final inspection of |ρ
« v′ »|, we supply a proof of either |m ≡ m| or |h₀ « v′ » ≡ h₀ « v′ »| to
complete the proof of equivalence.

Moving on to the proof of consistency, we repeat the familiar outline of
inspecting the read log followed by the write log. When entries exist for
|v| in either log, the updated |ρ′| reduces to just |ρ|, so the existing
consistency witness |h₀⊇ρ| for |ρ| is adequate:
%format v≡v′ = "v{\equiv}v\Prime{}"
\restorecolumns
\begin{code}
  h₀⊇ρ′ : Consistent h₀ ρ″
  h₀⊇ρ′ v′ ρ′«v′»≡n rewrite ρ″≡ρ′ with ω « v »
  ... |  just m = h₀⊇ρ v′ ρ′«v′»≡n
  ... |  nothing with ρ « v »
  ...    |  just m = h₀⊇ρ v′ ρ′«v′»≡n
  ...    |  nothing with v ≟Fin v′
  ...       |  yes v≡v′ rewrite v≡v′ | set-get v′ ρ (just (h₀ « v′ »))
               = just-inj ρ′«v′»≡n
  ...       |  no v≢v′ rewrite set-get′ ρ (just (h₀ « v »)) v≢v′
               = h₀⊇ρ v′ ρ′«v′»≡n
\end{code}
Otherwise, the updated read log |ρ′| reduces to |ρ « v »≔ just (h₀ « v »)|.
If |v′| in fact coincides with |v|, we can appeal to the |set-get| lemma to
obtain a proof that |ρ′ « v′ » ≡ just (h₀ « v′ »)|. A rewrite transforms the
type of |ρ′«v′»≡n| to |just (h₀ « v′ ») ≡ just n|, then an appeal to the
injectivity of |just| does the rest. When |v′| differs from |v|, the
alternative |set-get′| lemma can be used to rewrite the type of |ρ′«v′»≡n|
to |ρ « v′ » ≡ just n|. Finally, invoking the prior witness |h₀⊇ρ| with this
refined |ρ′«v′»≡n| completes the proof for the |exp-read| case.

The final part of the completeness proof tackles transition sequences from
expressions of the form |write v e|. The proof for this case is fairly
modest unlike the preceding one, as the proof for the |e| subexpression is
delegated to the inductive hypothesis. We need only show that a |WRITE v|
instruction with some |m| on top of the stack has an equivalent outcome to
the corresponding expression |write v m|:
%format e↣⋆m = "e{\rightarrowtail}^\star{}m"
%format h₀ρ′ω″≗h″ = "\func{h_0\rho\Prime\omega\PPrime{\circeq}h\PPrime}"
\savecolumns
\begin{code}
STM↦⋆→↣⋆ {h} ._ {h₀} {c} {σ} {γ} {ρ} {ω} h₀ρω≗h h₀⊇ρ
  | exp-write {h′} v m e↦⋆m rwLog-≗
    with STM↦⋆→↣⋆ e↦⋆m {h₀} {WRITE v ∷ c} {σ} {γ} h₀ρω≗h h₀⊇ρ
... | e↣⋆m ∧ h₀ρ′ω′≗h′ ∧ h₀⊇ρ′ rewrite rwLog-≗ (ρ ∧ ω)
      = e↣⋆m ◅◅ ↣τ-WRITE ◅ ε ∧ h₀ρ′ω″≗h″ ∧ h₀⊇ρ′ where
  ρ′∧ω′ = rwLog e↦⋆m (ρ ∧ ω); ρ′ = proj₁ ρ′∧ω′; ω′ = proj₂ ρ′∧ω′
\end{code}
As the |WRITE| instruction never modifies the read log, the consistency
proof |h₀⊇ρ′| resulting from the inductive hypothesis already suffices. The
only proof burden is to show that the updated heap according to the
expression semantics is matched by the updated write log. Since |↣τ-WRITE|
updates the write log directly, the proof of |h₀ρ′ω″≗h″| has only two
alternative clauses, conditioned on whether |v′| matches the variable being
written:
\restorecolumns
\begin{code}
  h₀ρ′ω″≗h″ : Equivalent (h′ « v »≔ m) h₀ ρ′ (ω′ « v »≔ just m)
  h₀ρ′ω″≗h″ v′  with v ≟Fin v′
  h₀ρ′ω″≗h″ .v  | yes ≡.refl =
    begin
      lookupTVar h₀ ρ′ (ω′ « v »≔ just m) v
    ≡⟪ set-lookup ω′ v m ⟫
      m
    ≡⟪ set-get v h′ m ⁻¹⟫
      (h′ « v »≔ m) « v »
    ∎
  h₀ρ′ω″≗h″ v′  | no v≢v′ =
    begin
      lookupTVar h₀ ρ′ (ω′ « v »≔ just m) v′
    ≡⟪ set-lookup′ ρ′ ω′ m v≢v′ ⟫
      lookupTVar h₀ ρ′ ω′ v′
    ≡⟪ h₀ρ′ω′≗h′ v′ ⟫
      h′ « v′ »
    ≡⟪ set-get′ h′ m v≢v′ ⁻¹⟫
      (h′ « v »≔ m) « v′ »
    ∎
\end{code}

% vim: ft=tex fo-=m fo-=M:

