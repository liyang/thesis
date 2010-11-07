%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Language.lagda
%include Verified/Commit.lagda
%include Verified/Lemmas.lagda
% include Verified/InspectExp.lagda
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

Soundness follows a similar strategy.

\begin{verbatim}
We are given a visible transition by the VM, which must be due to
>->-COMMIT; silent transitions before non-silent >->-COMMIT imply
bisimilarity to |compile e (COMMIT c), sigma| by elide-tau.

Non-silent >->-COMMIT also implies consistency, and prior silent transitions
cannot modify heap. Construct uninterrupted VM transition sequence from
|compile e (COMMIT c), stack| to |COMMIT :: c, m :: stack|
Then use STM>->*->|->* to derive corresponding expression
sequence from |e| to matching |m|. Evaluate using |->-atomic to match
>->-COMMIT.

QED.
\end{verbatim}

%if False
\begin{code}
STM↣⋆→↦⋆ : ∀ {h₀ ρ ω} h (e : Expression STM) →
--   (e↣τ⋆m : h₀ ∧ ⟨ compile e c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆
--     h₀ ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩) →
  Equivalent h h₀ ρ ω → Consistent h₀ ρ → ∃₂ λ h′ m →
  Σ (STM‣ h ∧ e ↦⋆ h′ ∧ # m) λ e↦⋆m → let
    ρ′∧ω′ = rwLog e↦⋆m (ρ ∧ ω); ρ′ = proj₁ ρ′∧ω′; ω′ = proj₂ ρ′∧ω′ in
    Equivalent h′ h₀ ρ′ ω′ × Consistent h₀ ρ′
STM↣⋆→↦⋆ h (# m) h₀ρω≗h h₀⊇ρ = h ∧ m ∧ ε ∧ h₀ρω≗h ∧ h₀⊇ρ
STM↣⋆→↦⋆ h (a ⊕ b) h₀ρω≗h h₀⊇ρ = {!!}
STM↣⋆→↦⋆ h (read v) h₀ρω≗h h₀⊇ρ = h ∧ h « v » ∧ ↦-read ◅ ε ∧ {!!} ∧ {!!}
STM↣⋆→↦⋆ h (write v e) h₀ρω≗h h₀⊇ρ with STM↣⋆→↦⋆ h e h₀ρω≗h h₀⊇ρ
STM↣⋆→↦⋆ h (write v e) h₀ρω≗h h₀⊇ρ | h′ ∧ m ∧ e↦⋆m ∧ h₀ρ′ω′≗h′ ∧ h₀⊇ρ′ = h′ « v »≔ m ∧ m ∧ ↦⋆-writeE v e↦⋆m ◅◅ ↦-writeℕ ◅ ε ∧ {!!} ∧ {!h₀⊇ρ′!}
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:

