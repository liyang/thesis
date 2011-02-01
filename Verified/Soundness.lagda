%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Language.lagda
%include Verified/Commit.lagda
%include Verified/Lemmas.lagda
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

% Soundness follows a similar strategy.

%if False
\begin{code}
foo : ∀ h (e : Expression STM) c σ {t₀ h₁∧s₁} →
  h ∧ ⟨ compile e (COMMIT ∷ c) ‚ σ ‚ compile e (COMMIT ∷ c) ‚ newLog ‚ newLog ⟩ ↣τ⋆ h ∧ t₀ →
  (h₀∧t₀↠≄τh₁∧s₁ : h ∧ ⟨ t₀ ⟩ ∷ [] ↠≄τ h₁∧s₁) →
    ∃ λ m → ∃₂ λ ρ ω →
      t₀ ≡ ⟨ COMMIT ∷ c ‚ m ∷ σ ‚ compile e (COMMIT ∷ c) ‚ ρ ‚ ω ⟩ ×
      Consistent h ρ
{-
 →
      h₀∧t₀↠≄τh₁∧s₁ ≡ ☢ (ρ ∧ ω) ∧ (λ ()) ∧ ↠-↣ (↣-COMMIT (yes h₀⊆ρ))
-}
foo h e c σ cow moo = {!!}
\end{code}
%endif

% Given a sequence of silent virtual machine transitions, guarded at the end
% with a non-silent one...

%if False
\begin{code}
-- STM↣⋆→↦⋆ : ∀ {h₀ ρ ω} h (e : Expression STM) →
-- --   (e↣τ⋆m : h₀ ∧ ⟨ compile e c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆
-- --     h₀ ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩) →
--   Equivalent h h₀ ρ ω → Consistent h₀ ρ → ∃₂ λ h′ m →
--   Σ (STM‣ h ∧ e ↦⋆ h′ ∧ # m) λ e↦⋆m → let
--     ρ′∧ω′ = rwLog e↦⋆m (ρ ∧ ω); ρ′ = proj₁ ρ′∧ω′; ω′ = proj₂ ρ′∧ω′ in
--     Equivalent h′ h₀ ρ′ ω′ × Consistent h₀ ρ′
-- STM↣⋆→↦⋆ h (# m) h₀ρω≗h h₀⊇ρ = h ∧ m ∧ ε ∧ h₀ρω≗h ∧ h₀⊇ρ
-- STM↣⋆→↦⋆ h (a ⊕ b) h₀ρω≗h h₀⊇ρ = {!!}
-- STM↣⋆→↦⋆ h (read v) h₀ρω≗h h₀⊇ρ = h ∧ h « v » ∧ ↦-read ◅ ε ∧ {!!} ∧ {!!}
-- STM↣⋆→↦⋆ h (write v e) h₀ρω≗h h₀⊇ρ with STM↣⋆→↦⋆ h e h₀ρω≗h h₀⊇ρ
-- STM↣⋆→↦⋆ h (write v e) h₀ρω≗h h₀⊇ρ | h′ ∧ m ∧ e↦⋆m ∧ h₀ρ′ω′≗h′ ∧ h₀⊇ρ′ = h′ « v »≔ m ∧ m ∧ ↦⋆-writeE v e↦⋆m ◅◅ ↦-writeℕ ◅ ε ∧ {!!} ∧ {!h₀⊇ρ′!}
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:

