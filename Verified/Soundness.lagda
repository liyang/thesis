%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Language.lagda
%include Verified/Commit.lagda
%include Verified/Lemmas.lagda
%include Verified/InspectExp.lagda
%include Verified/Completeness.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Verified.Soundness where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language
open import Verified.Commit as Commit
open import Verified.Lemmas as Lemmas
\end{code}
%endif

\section{Soundness of Log-Based Transactions}

To be completed. Please refer to proof sketch at the end of
\S\ref{sec:verified-correct} in the meantime.

Given a sequence of silent virtual machine transitions from the start of
a transaction, guarded at the end with a non-silent transition, we can show
that the former computes some |m| and the logs |ρ| and |ω|, and that the
non-silent transition must be a |↣-COMMIT (yes h⊇ρ)|:
%format guarded = "\func{guarded}"
%format t₀↣≄τt₁ = "t_0{\rightarrowtail}{\not\simeq}\tau{}t_1"
\begin{code}
postulate
  guarded : ∀ {c σ γ h t₀ h₁ t₁} (e : Expression STM) →
    h ∧ ⟨ compile e (COMMIT ∷ c) ‚ σ ‚ γ ‚ newLog ‚ newLog ⟩ ↣τ⋆ h ∧ t₀ →
    (t₀↣≄τt₁ : h ∧ t₀ ↣≄τ h₁ ∧ t₁) →
    ∃ λ m → ∃₂ λ ρ′ ω′ →
      t₀ ≡ ⟨ COMMIT ∷ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩ ×
      t₁ ≡ ⟨ c ‚ m ∷ σ ‚ [] ‚ newLog ‚ newLog ⟩ ×
      h₁ ≡ update h ω ×
      visible (proj₁ (proj₂ t₀↣≄τt₁) ∘ M⁺≃τ-inj) ≡ ☢ (ρ′ ∧ ω′)
\end{code}
There's some technical difficulty giving a direct proof of |t₀↣≄τt₁
≡ ↣-COMMIT (yes h⊇ρ)|, so we return four properties implied by it instead.

%format STM↣⋆→↦⋆ = "\func{STM{\rightarrowtail}^\star{\rightarrow}{\mapsto}^\star}"
%format e↣⋆m = "e{\rightarrowtail}^\star{}m"
%format ρ′∧ω′ = "\rho\Prime{\land}\omega\Prime{}"
The |STM↣⋆→↦⋆| lemma is the moral dual of |STM↦⋆→↣⋆|, showing that there
exists some transition sequence |e↦⋆m : STM‣ h ∧ e ↦⋆ h′ ∧ # m| from |e| to
the same |m| as that computed by |e↣⋆m|, and furthermore that the
reconstructed logs from |e↦⋆m| match those of |e↣⋆m|:
\begin{code}
postulate
  STM↣⋆→↦⋆ : ∀ {h h₀ m c σ γ ρ ω ρ′ ω′} (e : Expression STM) →
    (e↣⋆m : h₀ ∧ ⟨ compile e c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆
      h₀ ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩) →
    Equivalent h h₀ ρ ω → Consistent h₀ ρ → ∃ λ h′ →
    Σ (STM‣ h ∧ e ↦⋆ h′ ∧ # m) λ e↦⋆m → let
      ρ′∧ω′ = rwLog e↦⋆m (ρ ∧ ω) in
      ρ′ ≡ proj₁ ρ′∧ω′ × ω′ ≡ proj₂ ρ′∧ω′ ×
      Equivalent h′ h₀ ρ′ ω′ × Consistent h₀ ρ′
\end{code}

% vim: ft=tex fo-=m fo-=M:

