%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Language.lagda
%include Verified/Commit.lagda
%include Verified/Bisimilarity.lagda
%include Verified/Lemmas.lagda
%include Verified/Completeness.lagda
%include Verified/Misc.lagda
\end{comment}
%endif

%format elide-τ = "\func{elide\text-\tau}"
%format elide-τ⋆ = "\func{elide\text-\tau^\star}"
%if False
\begin{code}
import Level
open import Common

module verified where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language
open import Verified.Commit as Commit
open import Verified.Bisimilarity as Bisimilarity
open import Verified.Lemmas as Lemmas
open import Verified.Completeness as Completeness
open import Verified.Misc as Misc

-- Rethink this: same heap for both? Surely not…
-- r and s are bisimilar iff : ∀ h → h ∧ r ≈ h ∧ s
-- i.e. both soups should do the same thing to the heap

-- was: ∀ {rˡ rʳ sˡ sʳ h} → h ∧ rˡ ≈ h ∧ sˡ → h ∧ rʳ ≈ h ∧ sʳ → h ∧ rˡ ++ rʳ ≈ h ∧ sˡ ++ sʳ
-- abstract postulate ≈-cong₂ : _++_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
abstract postulate elide-τ : ∀ {r r′} → r ↠τ r′ → r ≈ r′
elide-τ⋆ : ∀ {r r′} → r ↠τ⋆ r′ → r ≈ r′
elide-τ⋆ = Star.fold _≈_ ≈-trans ≈-refl ∘ Star.map elide-τ
\end{code}

Lemma (unproven): if two thread soups are bisimilar, they do the same thing
regardless of the contents of the heap.
\begin{spec}
abstract postulate ≈⇒≈∀ : h ∧ x ≈ h ∧ y → ∀ h′ → h′ ∧ x ≈ h′ ∧ y
\end{spec}
%endif


\chapter{Compiling STM Correctly}\label{ch:verified}

The previous chapter scaled our new proof technique to an explicitly
concurrent language. In this chapter, we extend our language with an
|atomic| construct, bringing it up to par with the model of STM Haskell from
chapter \ref{ch:stm}.

\input{Verified/Language.lagda}

\input{Verified/Lemmas.lagda}

\input{Verified/Completeness.lagda}

%* low-level implies high-level: run |atomic e| at commit point, using
%consistency to show that it does the same thing.

\input{Verified/Soundness.lagda}

\section{Compiler Correctness}\label{sec:verified-correct}

Being based on the Fork language, the compiler correctness property for this
Atomic language takes the same form as that of \S\ref{sec:fork-correct},
differing only the pairing of a heap with each thread soup and the
transactional extensions to the virtual machine state:
%format correctness = "\func{correctness}"
\begin{code}
correctness : ∀ h e c σ →
  h ∧ ⟨ e ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ [] ≈
    h ∧ ⟨ ⟨ compile e c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
\end{code}
We may proceed to prove |correctness| in the familiar way, by case analysis
on the expression |e|. The same lemmas we had shown for the Fork
language---modulo the above differences---are equally applicable for this
Atomic language. Therefore we need not repeat ourselves for the |# m|, |a
⊕ b| and |fork e| cases.

The proof for the |atomic e| case comprises of two halves showing each
direction of the bisimulation. Before we begin, let us factor out the
transition corresponding to |BEGIN| on the virtual machine:
%format atomic≼COMMIT = "\func{a{\preccurlyeq}C}"
%format COMMIT≼atomic = "\func{C{\preccurlyeq}a}"
\savecolumns
\begin{code}
correctness h (atomic e) c σ =
  begin
    h ∧ ⟨ atomic e ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  ≈⟪ ♯ atomic≼COMMIT & ♯ COMMIT≼atomic ⟫
    h ∧ ⟨ ⟨ γ ‚ σ ‚ γ ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  ≈⟪ elide-τ (τ ∧ is-τ ∧ ↠-↣ ↣-BEGIN) ⁻¹⟫
    h ∧ ⟨ ⟨ compile (atomic e) c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  ∎
  where
  open ≈-Reasoning
  γ = compile e (COMMIT ∷ c)
\end{code}
For the completeness half---that is, the compiled program can always follow
the expression language---we first eliminate three impossible cases:
%format h′∧m = "h\Prime{\wedge}m"
\restorecolumns
\begin{code}
  atomic≼COMMIT : h ∧ ⟨ atomic e ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ [] ≼
    h ∧ ⟨ ⟨ γ ‚ σ ‚ γ ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  atomic≼COMMIT h′∧m (⤇-↠ ((._ ∧ () ∧ ↠-↦ (↦-atomic e↦⋆m)) ◅ _) _ _)
  atomic≼COMMIT h′∧m (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ _) _ _)
  atomic≼COMMIT h′∧m (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) _)
\end{code}
The first of these correspond to the fact that the |↦-atomic| rule cannot be
silent, while the remaining two handle the fact that the empty tail of the
soup cannot make any transitions.

The salient part of the completeness proof proceeds by simply running the
transaction uninterrupted on the virtual machine when we encounter the
|↦-atomic| rule. Invoking our earlier |STM↦⋆→↣⋆| lemma
(\S\ref{sec:verified-complete}) on the |e↦⋆m| premise of |↦-atomic| gives
back a matching sequence of virtual machine transitions that computes the
same |m|,
\begin{spec}
e↣⋆m : h ∧ ⟨ ⟨ γ ‚ σ ‚ γ ‚ newLog ‚ newLog ⟩ ⟩ ∷ [] ↣τ⋆
  h ∧ ⟨ ⟨ COMMIT ∷ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ []
\end{spec}
along with the proofs |hρω≗h′ : Equivalent h′ h ρ ω| and |h⊇ρ : Consistent
h ρ|:
%format h′∧m≈hω∧m∷σ = "\func{h\Prime{\wedge}m{\approx}h\omega{\wedge}m}"
\restorecolumns
\begin{code}
  atomic≼COMMIT h′∧m (⤇-↠ ε ({-"\;\;"-}._ ∧ α≄τ ∧ ↠-↦
        (↦-atomic {m = m} {h′ = h′} e↦⋆m){-"\;\;"-}) s₁↠τ⋆s′)
      with STM↦⋆→↣⋆ e↦⋆m {h} {COMMIT ∷ c} {σ}
        {compile e (COMMIT ∷ c)} Equivalent-refl consistent-newLog
  ... | e↣⋆m ∧ hρω≗h′ ∧ h⊇ρ
        = _ ∧ ⤇-↠ (↣τ⋆→↠τ⋆ e↣⋆m) (_ ∧ (λ ()) ∧ ↠-↣ (↣-COMMIT (yes h⊇ρ))) ε
        ∧ ≈′-≈ (≈-trans (≈-sym (elide-τ⋆ s₁↠τ⋆s′)) h′∧m≈hω∧m∷σ) where
\end{code}
Thus in response to |↦-atomic e↦⋆m|, the virtual machine makes the silent
transitions |e↣⋆m| followed by the non-silent |↣-COMMIT|. The requirement
that the resulting states are bisimilar is taken care of by an application
of |elide-τ⋆| and an appeal to the following |h′∧m≈hω∧m∷σ| lemma:
\restorecolumns
\begin{code}
    ω = (proj₂ ∘ rwLog e↦⋆m) (newLog ∧ newLog)
    h′∧m≈hω∧m∷σ : h′ ∧ ⟨ # m ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ [] ≈
      update h ω ∧ ⟨ ⟨ c ‚ m ∷ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
    h′∧m≈hω∧m∷σ rewrite hω≡h′ hρω≗h′ h⊇ρ = elide-τ ↠τ-switch
\end{code}
The rewrite using |hω≡h′| (\S\ref{sec:verified-heapeq}) gives definitional
equality of the resulting heaps, while a silent |↠τ-switch| moves the |# m|
onto the virtual machine stack, concluding the completeness part of the
|correctness| property.


-- Given t↠τ⋆t₀ and t₀↠≄τt₁, derive that t₀↠≄τt₁ must be h₀ ∧ ⟨ ⟨ COMMIT ∷ c ‚ … ⟩ ⟩ 

%format t↠τ⋆t₀ = "t{\twoheadrightarrow}\tau^\star{}t_0"
%format t₀↠≄τt₁ = "t_0{\twoheadrightarrow}{\not\simeq}\tau{}t_1"
%format t₁↠τ⋆t′ = "t_1{\twoheadrightarrow}\tau^\star{}t\Prime{}"
%format t↣τ⋆t₀ = "t{\rightarrowtail}\tau^\star{}t_0"
For the soundness half of |correctness|, we are provided with a visible
virtual machine transition comprising |t↠τ⋆t₀|, |t₀↠≄τt₁| and |t₁↠τ⋆t′|:
\restorecolumns
\begin{code}


  COMMIT≼atomic : h ∧ ⟨ ⟨ γ ‚ σ ‚ γ ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
    ≼ h ∧ ⟨ atomic e ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  COMMIT≼atomic h′∧m (⤇-↠ t↠τ⋆t₀ t₀↠≄τt₁ t₁↠τ⋆t′)
      with ↠τ⋆→↣τ⋆ t↠τ⋆t₀
  ... | t₀ ∧ h≡h₀ ∧ s₀≡⟨t₀⟩ ∧ t↣τ⋆t₀ = {!!} where
    postulate
      guarded : ∀ {h₁∧t₁} → h ∧ ⟨ γ ‚ σ ‚ γ ‚ newLog ‚ newLog ⟩ ↣τ⋆ h ∧ t₀ → (t₀↣≄τt₁ : (h ∧ t₀) ↣≄τ h₁∧t₁) →
        ∃ λ m → ∃₂ λ ρ ω → t₀ ≡ ⟨ COMMIT ∷ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩
-- × t₀↣≄τt₁ ≡ ☢ (ρ ∧ ω) ∧ (λ ()) ∧ {!↣-COMMIT (yes ?)!}
--     guarded foo bar = {!!}

\end{code}
The initial silent combined machine sequence |t↠τ⋆t₀| can neither fork,
modify the heap nor emit a |∎ m| action, so we may extract a sequence of
silent virtual machine transitions with the following type,
\begin{spec}
t↣τ⋆t₀ : h ∧ ⟨ γ ‚ σ ‚ γ ‚ newLog ‚ newLog ⟩ ↣τ⋆ h ∧ t₀
\end{spec}
keeping in mind that |γ| was earlier defined to be |compile e (COMMIT ∷ c)|.
The above procedure also refines the type of |t₀↠≄τt₁| to |h ∧ ⟨ t₀ ⟩ ↠≄τ
s₁|. \emph{(What follows is a sketch of the proof; the fully mechanised
version is currently in progress.)} Then, using the fact that the |t↠τ⋆t₀|
sequence is guarded at the end with this non-silent |t₀↠≄τt₁|, we can show
that |t₀| must be equal to |⟨ COMMIT ∷ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩| and that
|t₀↠≄τt₁| is in fact an instance of |↣-COMMIT|.

Following a loosely inverse procedure to that of |STM↦⋆→↣⋆|, we can derive
a corresponding |e↦⋆m : STM‣ h ∧ e ↦⋆ h′ ∧ # m| sequence that calculates the
same |m|, and finishes with a heap |h′| that satisfies |Equivalent h′
h ρ ω|. Thus, the expression |atomic e| may follow with |↦-atomic e↦⋆m| in
response to the virtual machine's |↣-COMMIT|. Two invocations of |elide-τ⋆|
on the silent transition sequences before and after the commit completes the
proof.

%  -- COMMIT≼atomic h′∧m (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↣ ↣-BEGIN) s₁↠τ⋆s′) = ⊥-elim (α≄τ is-τ)
%  -- COMMIT≼atomic h′∧m (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₁↠τ⋆s′)
%  -- COMMIT≼atomic h′∧m (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↣ ↣-BEGIN) ◅ h∧e↣⋆h∧m) s₀↠≄τs₁ s₁↠τ⋆s′) = {!!}
%  -- COMMIT≼atomic h′∧m (⤇-↠ ((… α ∧ is-… α≃τ ∧ ↠-preempt ()) ◅ xs) s₀↠≄τs₁ s₁↠τ⋆s′)
%-- rewrite ↠τ⋆-heap s↠τ⋆s₀ = {!!}

% correctness for #, fork and ⊕
%{{{%

%if False
\begin{code}
correctness h (# m) c σ =
  begin
    h ∧ ⟨ # m ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  ≈⟪ elide-τ ↠τ-switch ⟫
    h ∧ ⟨ ⟨ c ‚ m ∷ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  ≈⟪ elide-τ ↠τ-PUSH ⁻¹⟫
    h ∧ ⟨ ⟨ PUSH m ∷ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
  ∎ where open ≈-Reasoning

correctness h (fork e) c σ = foo where postulate foo : _
--  ♯ fork≼FORK & ♯ FORK≼fork where
--   fork≼FORK : h ∧ ⟨ fork e ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ [] ≼ h ∧ ⟨ ⟨ FORK (compile e []) ∷ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
--   fork≼FORK s′ (⤇-↠ ((._ ∧ () ∧ ↠-↦ ↦-fork) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
--   fork≼FORK s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
--   fork≼FORK s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
--   fork≼FORK s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ ↦-fork) s₀↠τ⋆s′)
--     = (h ∧ ⟨ ⟨ c ‚ 0 ∷ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ ⟨ ⟨ compile e [] ‚ [] ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ [])
--     ∧ ⤇-↠ ε (⁺ _ ∧ (λ ()) ∧ ↠-↣ ↣-FORK) ε
--     ∧ ≈′-≈ (≈-trans (≈-sym (elide-τ⋆ s₀↠τ⋆s′)) (≈-cong-++ (elide-τ (↠τ-switch {s = []})) (correctness h e [] [])))

--   FORK≼fork : h ∧ ⟨ ⟨ FORK (compile e []) ∷ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ [] ≼ h ∧ ⟨ fork e ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ []
--   FORK≼fork s′ (⤇-↠ ((._ ∧ () ∧ ↠-↣ ↣-FORK) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
--   FORK≼fork s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
--   FORK≼fork s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
--   FORK≼fork s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↣ ↣-FORK) s₀↠τ⋆s′)
--     = (h ∧ ⟨ # 0 ‚ ⟨ c ‚ σ ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ ⟨ e ‚ ⟨ [] ‚ [] ‚ [] ‚ newLog ‚ newLog ⟩ ⟩ ∷ [])
--     ∧ ⤇-↠ ε (⁺ _ ∧ (λ ()) ∧ ↠-↦ ↦-fork) ε
--     ∧ ≈′-≈ (≈-sym (≈-trans (≈-cong-++ (elide-τ (↠τ-switch {s = []})) (correctness h e [] [])) (elide-τ⋆ s₀↠τ⋆s′)))

correctness h (a ⊕ b) c σ = foo where postulate foo : _
\end{code}
%endif

%}}}%

\section{Conclusion}

In this penultimate chapter, we have come full circle by extending our
object language and its virtual machine with transactional constructs, to
coincide with the simplified STM model first identified in chapter
\ref{ch:model}. We were able to reuse the existing proofs for the Fork
language, requiring only an additional case for |atomic e| in the final
proof of |correctness|, along with the handful of transaction log and heap
lemmas given in \S\ref{sec:verified-lemmas}. The completeness half of
transactional correctness entailed showing that every visible transition
arising from the stop-the-world |↦-atomic| rule on expressions had
a corresponding visible transition in the virtual machine world that
computed the same result and having the same heap side-effects, and
vice-versa for soundness.

% vim: ft=tex fo-=m fo-=M:

