%include local.fmt

\chapter{Compiling Concurrency Correctly}

\begin{itemize}
\item second half
\item What about a parallel-addition language?
\item Labelled transition systems and bisimulations in excruciating detail
\end{itemize}

\begin{code}
module concurrency where

import Level
open import Common
open import concaux

\end{code}

\begin{code}
module Correctness where
  open Language
  open RawFunctor functorA
  open Bisimulation -- _⤇‹_›_
  open ≈-Reasoning
  open LemAux
  open Lemmas

  -- is bisimilarity substitutive? Don't be silly, of course it isn't.
  --     r ≈ s → P r → P s
  -- but up to visible actions, it is… how do I state this?

  correctness : ∀ e c σ → ⟨ e ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ ⟨ compile e c ‚ σ ⟩ ⟩ ∷ []
  correctness (# m) c σ =
    begin
      ⟨ # m ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
    ≈⟨ elide-τ ↠τ-switch ⟩
      ⟨ ⟨ c ‚ m ∷ σ ⟩ ⟩ ∷ []
    ≈⟨ ≈-sym (elide-τ (τ ∧ is-τ ∧ ↠-↣ ↣-PUSH)) ⟩
      ⟨ ⟨ PUSH m ∷ c ‚ σ ⟩ ⟩ ∷ []
    ≡⟨ ≡.refl ⟩
      ⟨ ⟨ compile (# m) c ‚ σ ⟩ ⟩ ∷ []
    ∎
  correctness (fork e) c σ = ♯ fork≼FORK & ♯ FORK≼fork where
    fork≼FORK : ⟨ fork e ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ ⟨ FORK (compile e []) ∷ c ‚ σ ⟩ ⟩ ∷ []
    fork≼FORK s′ (⤇-↠ ((._ ∧ () ∧ ↠-↦ ↦-fork) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    fork≼FORK s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    fork≼FORK s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
    fork≼FORK s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ ↦-fork) s₀↠τ⋆s′)
      = ⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩ ∷ ⟨ ⟨ compile e [] ‚ [] ⟩ ⟩ ∷ []
      ∧ ⤇-↠ ε (⁺ _ ∧ (λ ()) ∧ ↠-↣ ↣-FORK) ε
      ∧ ≈′-≈ (≈-trans (≈-sym (elide-τ⋆ s₀↠τ⋆s′)) (≈-++ (elide-τ (↠τ-switch {[]})) (correctness e [] [])))

    FORK≼fork : ⟨ ⟨ FORK (compile e []) ∷ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ fork e ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
    FORK≼fork s′ (⤇-↠ ((._ ∧ () ∧ ↠-↣ ↣-FORK) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    FORK≼fork s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    FORK≼fork s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
    FORK≼fork s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↣ ↣-FORK) s₀↠τ⋆s′)
      = ⟨ # 0 ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ ⟨ e ‚ ⟨ [] ‚ [] ⟩ ⟩ ∷ []
      ∧ ⤇-↠ ε (⁺ _ ∧ (λ ()) ∧ ↠-↦ ↦-fork) ε
      ∧ ≈′-≈ (≈-sym (≈-trans (≈-++ (elide-τ (↠τ-switch {[]})) (correctness e [] [])) (elide-τ⋆ s₀↠τ⋆s′)))

  correctness (a ⊕ b) c σ =
    begin
      ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
    ≈⟨ eval-left a b c σ ⟩
      ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
    ≈⟨ correctness a _ _ ⟩
      ⟨ ⟨ compile a (compile b (ADD ∷ c)) ‚ σ ⟩ ⟩ ∷ []
    ≡⟨ ≡.refl ⟩
      ⟨ ⟨ compile (a ⊕ b) c ‚ σ ⟩ ⟩ ∷ []
    ∎ where

    eval-right : ∀ m b c σ → ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
    eval-right m b c σ = ♯ m⊕b≼b b & ♯ b≼m⊕b b where
      m⊕b≼b : ∀ b → ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
      m⊕b≼b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ e↦e₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) e↦e₀)
      m⊕b≼b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      m⊕b≼b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
      m⊕b≼b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-⊕L ())) s₀↠τ⋆s′)
      m⊕b≼b (# n) s′ (⤇-↠ ε (.⊞ ∧ α≄τ ∧ ↠-↦ ↦-⊕ℕ) s₀↠τ⋆s′)
        = ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩ ∷ []
        ∧ ⤇-↠ (↠τ-switch ◅ ε) (⊞ ∧ (λ ()) ∧ ↠-↣ ↣-ADD) ε
        ∧ ≈′-≈ (begin
            s′
          ≈⟨ ≈-sym (elide-τ⋆ s₀↠τ⋆s′) ⟩
            ⟨ # (m + n) ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
          ≈⟨ elide-τ ↠τ-switch ⟩
            ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩ ∷ []
          ∎)
      m⊕b≼b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-⊕R {b′ = b₀} {α = α} b↦b₀)) s₀↠τ⋆s′)
        = ⟨ b₀ ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
        ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ b↦b₀) ε
        ∧ ≈′-trans (≈′-≈ (≈-sym (elide-τ⋆ s₀↠τ⋆s′))) (≈′-++ (≈′-≈ (eval-right m b₀ c σ)) ≈′-refl)

      b≼m⊕b : ∀ b → ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ [] ≼ ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
      b≼m⊕b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ b↦b₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) b↦b₀)
      b≼m⊕b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      b≼m⊕b (# n) s′ (⤇-↠ ((.τ ∧ is-τ ∧ ↠-switch) ◅ (._ ∧ () ∧ ↠-↣ ↣-ADD) ◅ s₁↠τ⋆s₂) s₂↠≄τs₃ s₃↠τ⋆s′)
      b≼m⊕b (# n) s′ (⤇-↠ ((.τ ∧ is-τ ∧ ↠-switch) ◅ (._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₁↠τ⋆s₂) s₂↠≄τs₃ s₃↠τ⋆s′)
      b≼m⊕b (# n) s′ (⤇-↠ ((.τ ∧ is-τ ∧ ↠-switch) ◅ ε) (._ ∧ α≄τ ∧ ↠-preempt ()) s₁↠τ⋆s′)
      b≼m⊕b (# n) s′ (⤇-↠ ((.τ ∧ is-τ ∧ ↠-switch) ◅ ε) (._ ∧ α≄τ ∧ ↠-↣ ↣-ADD) s₁↠τ⋆s′)
        = ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩ ∷ []
        ∧ ⤇-↠ ε (⊞ ∧ (λ ()) ∧ ↠-↦ ↦-⊕ℕ) (↠τ-switch ◅ ε)
        ∧ ≈′-≈ (≈-sym (elide-τ⋆ s₁↠τ⋆s′))
      b≼m⊕b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
      b≼m⊕b (# n) s′ (⤇-↠ ε (.τ ∧ α≄τ ∧ ↠-switch) s₀↠τ⋆s′) = ⊥-elim (α≄τ is-τ)
      b≼m⊕b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ {e′ = b₀} {α = α} b↦b₀) s₀↠τ⋆s′)
        = ⟨ # m ⊕ b₀ ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
        ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ (↦-⊕R b↦b₀)) ε
        ∧ ≈′-trans (≈′-≈ (≈-sym (elide-τ⋆ s₀↠τ⋆s′))) (≈′-++ (≈′-sym (≈′-≈ (eval-right m b₀ c σ))) ≈′-refl)


    eval-left : ∀ a b c σ → ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
    eval-left a b c σ = ♯ a⊕b≼a a b & ♯ a≼a⊕b a where
      case-a≡m : ∀ {m b} → ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ # m ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
      case-a≡m {m} {b} =
        begin
          ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
        ≈⟨ eval-right m b c σ ⟩
          ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
        ≈⟨ correctness b (ADD ∷ c) (m ∷ σ) ⟩
          ⟨ ⟨ compile b (ADD ∷ c) ‚ m ∷ σ ⟩ ⟩ ∷ []
        ≈⟨ ≈-sym (elide-τ ↠τ-switch) ⟩
          ⟨ # m ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
        ∎

      a⊕b≼a : ∀ a b → ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
      a⊕b≼a a b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ e↦e₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) e↦e₀)
      a⊕b≼a a b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      a⊕b≼a a b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
      a⊕b≼a (# m) b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-⊕R b↦b₀)) s₀↠τ⋆s′) = ≈→≼ case-a≡m s′ (⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ (↦-⊕R b↦b₀)) s₀↠τ⋆s′)
      a⊕b≼a (# m) (# n) s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ ↦-⊕ℕ) s₀↠τ⋆s′) = ≈→≼ case-a≡m s′ (⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ ↦-⊕ℕ) s₀↠τ⋆s′)
      a⊕b≼a a b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-⊕L {a′ = a₀} {α = α} a↦a₀)) s₀↠τ⋆s′)
        = ⟨ a₀ ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
        ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ a↦a₀) ε
        ∧ ≈′-trans (≈′-≈ (≈-sym (elide-τ⋆ s₀↠τ⋆s′))) (≈′-++ (≈′-≈ (eval-left a₀ b c σ)) ≈′-refl)

      a≼a⊕b : ∀ a → ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
      a≼a⊕b a s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ a↦a₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) a↦a₀)
      a≼a⊕b a s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      a≼a⊕b (# m) s′ (⤇-↠ ((.τ ∧ α≃τ ∧ ↠-switch) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ≈→≽ case-a≡m s′ (⤇-↠ ((τ ∧ α≃τ ∧ ↠-switch) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      a≼a⊕b a s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
      a≼a⊕b (# m) s′ (⤇-↠ ε (.τ ∧ α≄τ ∧ ↠-switch) s₀↠τ⋆s′) = ⊥-elim (α≄τ is-τ)
      a≼a⊕b a s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ {e′ = a₀} {α = α} a↦a₀) s₀↠τ⋆s′)
        = ⟨ a₀ ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
        ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ (↦-⊕L a↦a₀)) ε
        ∧ ≈′-trans (≈′-≈ (≈-sym (elide-τ⋆ s₀↠τ⋆s′))) (≈′-++ (≈′-sym (≈′-≈ (eval-left a₀ b c σ))) ≈′-refl)


  ≈′→≈ : _≈′_ ⇒ _≈_
  ≈′→≈ (≈′-≈ r≈s) = r≈s
  ≈′→≈ (≈′-++ rˡ≈′sˡ rʳ≈′sʳ) = ≈-++ (≈′→≈ rˡ≈′sˡ) (≈′→≈ rʳ≈′sʳ)
  ≈′→≈ (≈′-sym r≈′s) = ≈-sym (≈′→≈ r≈′s)
  ≈′→≈ (≈′-trans r≈′s s≈′t) = ≈-trans (≈′→≈ r≈′s) (≈′→≈ s≈′t)

\end{code}
-- module Correctness where

--   open Coinduction
--   open Data.List
--   open ⋆
--   open Data.Nat
--   open ≡
--   open Data.Empty
--   open Σ

--   open Language
--   open Bisimulation _⤇‹_›_
--   open Lemmas

--   open ≈-Reasoning

--   private
--     adj : ∀ {e} {t} {f : Expression → Expression} {g : Machine → Machine} →
--       (∀ m → ⟨ # m ‚ g t ⟩ ≈ ⟨ f (# m) ‚ t ⟩) →
--       (∀ {e e′ Λ} → e ↦‹ Λ › e′ → f e ↦‹ Λ › f e′) →
--       (∀ {a b u x Λ} → ⟨ f (a ⊕ b) ‚ u ⟩ ↠‹ Λ › x → ∃ λ e′ → x ≡ ⟨ f e′ ‚ u ⟩ × ⟨ a ⊕ b ‚ u ⟩ ↠‹ Λ › ⟨ e′ ‚ u ⟩) →
--       ⟨ e ‚ g t ⟩ ≈ ⟨ f e ‚ t ⟩
--     adj {# m} base _ _ = base m
--     adj {a ⊕ b} {t} {f} {g} base map-f unmap-f = ♯ e≼fe & ♯ fe≼e where
--       e≼fe : ⟨ a ⊕ b ‚ g t ⟩ ≼ ⟨ f (a ⊕ b) ‚ t ⟩
--       e≼fe x′ (⤇-↠ (↠-↦ e↦e₀ ◅ x₀↠⋆x₁) x₁↠x₂ x₂↠⋆x′) = ⊥-elim (¬↦‹τ› e↦e₀)
--       e≼fe x′ (⤇-↠ ε (↠-↦ e↦e₀) x₀↠⋆x′)
--         = ⟨ f _ ‚ t ⟩
--         ∧ ⤇-↠ ε (↠-↦ (map-f e↦e₀)) ε
--         ∧ ≈′-trans (≈′-≈ (≈-sym (elide-τ⋆ x₀↠⋆x′))) (≈′-≈ (adj {g = g} base map-f unmap-f))

--       fe≼e : ⟨ f (a ⊕ b) ‚ t ⟩ ≼ ⟨ a ⊕ b ‚ g t ⟩
--       fe≼e y′ (⤇-↠ (y↠y₀ ◅ y₀↠⋆y₁) y₁↠y₂ y₂↠⋆y′) with unmap-f y↠y₀
--       fe≼e y′ (⤇-↠ (y↠y₀ ◅ y₀↠⋆y₁) y₁↠y₂ y₂↠⋆y′) | e′ ∧ ≡.refl ∧ (↠-↦ e↦e₀) = ⊥-elim (¬↦‹τ› e↦e₀)
--       fe≼e y′ (⤇-↠ ε y↠y₀ y₀↠⋆y′) with unmap-f y↠y₀
--       fe≼e y′ (⤇-↠ ε y↠y₀ y₀↠⋆y′) | e′ ∧ ≡.refl ∧ (↠-↦ e↦e₀)
--         = ⟨ _ ‚ g t ⟩
--         ∧ ⤇-↠ ε (↠-↦ e↦e₀) ε
--         ∧ ≈′-trans (≈′-≈ (≈-sym (elide-τ⋆ y₀↠⋆y′))) (≈′-sym (≈′-≈ (adj {g = g} base map-f unmap-f)))

--   eval-right : ∀ {m b c σ} → ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ≈ ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
--   eval-right {m} {b} {c} {σ} = adj {f = f} {g = g} base ↦-⊕R ↦-⊕R⁻¹ where
--     f : Expression → Expression
--     f b′ = # m ⊕ b′
--     g : Machine → Machine
--     g ⟨ c′ ‚ σ′ ⟩ = ⟨ ADD ∷ c′ ‚ m ∷ σ′ ⟩

--     ↦-⊕R⁻¹ : ∀ {a b u x Λ} → ⟨ f (a ⊕ b) ‚ u ⟩ ↠‹ Λ › x → ∃ λ e′ → x ≡ ⟨ f e′ ‚ u ⟩ × ⟨ a ⊕ b ‚ u ⟩ ↠‹ Λ › ⟨ e′ ‚ u ⟩
--     ↦-⊕R⁻¹ (↠-↦ (↦-⊕L ()))
--     ↦-⊕R⁻¹ (↠-↦ (↦-⊕R {b′ = e′} a⊕b↦e′)) = e′ ∧ refl ∧ ↠-↦ a⊕b↦e′

--     base : ∀ n → ⟨ # n ‚ g ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ f (# n) ‚ ⟨ c ‚ σ ⟩ ⟩
--     base n = ♯ ADD≼⊕ & ♯ ⊕≼ADD where
--       ADD≼⊕ : ⟨ # n ‚ g ⟨ c ‚ σ ⟩ ⟩ ≼ ⟨ f (# n) ‚ ⟨ c ‚ σ ⟩ ⟩
--       ADD≼⊕ x′ (⤇-↠ ε (↠-↦ ()) x₀↠⋆x′)
--       ADD≼⊕ x′ (⤇-↠ (↠-↦ e↦e₀ ◅ e₀↠⋆e₁) x₁↠x₂ x₂↠⋆x′) = ⊥-elim (¬↦‹τ› e↦e₀)
--       ADD≼⊕ x′ (⤇-↠ (↠-switch ◅ ↠-↣ () ◅ x₀↠⋆x₁) x₁↠x₂ x₂↠⋆x′)
--       ADD≼⊕ x′ (⤇-↠ (↠-switch ◅ ε) (↠-↣ ↣-ADD) x₀↠⋆x′) = x′ ∧ ⤇-↠ ε (↠-↦ ↦-⊕ℕ) (↠-switch ◅ x₀↠⋆x′) ∧ ≈′-refl
--       ADD≼⊕ x′ (⤇-↠ (↠-switch ◅ ε) (↠-↣ ↣-ZAP) x₀↠⋆x′) = x′ ∧ ⤇-↠ ε (↠-↦ ↦-⊕↯) (↠-switch ◅ x₀↠⋆x′) ∧ ≈′-refl

--       switch-≈ : ∀ {k x′} → ⟨ # k ‚ ⟨ c ‚ σ ⟩ ⟩ ↠‹τ›⋆ x′ → x′ ≈ ⟨ ⟨ c ‚ k ∷ σ ⟩ ⟩
--       switch-≈ {k} {x′} x₀↠⋆x′ =
--         begin
--           x′
--         ≈⟨ ≈-sym (elide-τ⋆ x₀↠⋆x′) ⟩
--           ⟨ # k ‚ ⟨ c ‚ σ ⟩ ⟩
--         ≈⟨ elide-τ⋆ (↠-switch ◅ ε) ⟩
--           ⟨ ⟨ c ‚ k ∷ σ ⟩ ⟩
--         ∎

--       ⊕≼ADD : ⟨ f (# n) ‚ ⟨ c ‚ σ ⟩ ⟩ ≼ ⟨ # n ‚ g ⟨ c ‚ σ ⟩ ⟩
--       ⊕≼ADD y′ (⤇-↠ (↠-↦ e↦e₀ ◅ y₀↠⋆y₁) y₁↠y₂ y₂↠⋆y′) = ⊥-elim (¬↦‹τ› e↦e₀)
--       ⊕≼ADD y′ (⤇-↠ ε (↠-↦ (↦-⊕R ())) y₀↠⋆y′)
--       ⊕≼ADD y′ (⤇-↠ ε (↠-↦ (↦-⊕L ())) y₀↠⋆y′)
--       ⊕≼ADD y′ (⤇-↠ ε (↠-↦ ↦-⊕ℕ) y₀↠⋆y′) = ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩ ∧ ⤇-↠ (↠-switch ◅ ε) (↠-↣ ↣-ADD) ε ∧ ≈′-≈ (switch-≈ y₀↠⋆y′)
--       ⊕≼ADD y′ (⤇-↠ ε (↠-↦ ↦-⊕↯) y₀↠⋆y′) = ⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩ ∧ ⤇-↠ (↠-switch ◅ ε) (↠-↣ ↣-ZAP) ε ∧ ≈′-≈ (switch-≈ y₀↠⋆y′)

--   mutual
--     eval-left : ∀ {a b c σ} → ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ≈ ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
--     eval-left {a} {b} {c} {σ} = adj {f = f} {g = g} base ↦-⊕L ↦-⊕L⁻¹ where
--       f : Expression → Expression
--       f a′ = a′ ⊕ b
--       g : Machine → Machine
--       g ⟨ c′ ‚ σ′ ⟩ = ⟨ compile b (ADD ∷ c) ‚ σ′ ⟩

--       ↦-⊕L⁻¹ : ∀ {a b u x Λ} → ⟨ f (a ⊕ b) ‚ u ⟩ ↠‹ Λ › x → ∃ λ e′ → x ≡ ⟨ f e′ ‚ u ⟩ × ⟨ a ⊕ b ‚ u ⟩ ↠‹ Λ › ⟨ e′ ‚ u ⟩
--       ↦-⊕L⁻¹ (↠-↦ (↦-⊕L {a′ = e′} e↦e′)) = e′ ∧ ≡.refl ∧ ↠-↦ e↦e′

--       base : ∀ m → ⟨ # m ‚ g ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ f (# m) ‚ ⟨ c ‚ σ ⟩ ⟩
--       base m =
--         begin
--           ⟨ # m ‚ g ⟨ c ‚ σ ⟩ ⟩
--         ≈⟨ elide-τ⋆ (↠-switch ◅ ε) ⟩
--           ⟨ g ⟨ c ‚ m ∷ σ ⟩ ⟩
--         ≈⟨ correctness ⟩
--           ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩
--         ≈⟨ eval-right ⟩
--           ⟨ f (# m) ‚ ⟨ c ‚ σ ⟩ ⟩
--         ∎

--     correctness : ∀ {e c σ} → ⟨ ⟨ compile e c ‚ σ ⟩ ⟩ ≈ ⟨ e ‚ ⟨ c ‚ σ ⟩ ⟩
--     correctness {# m} {c} {σ} =
--       begin
--         ⟨ ⟨ compile (# m) c ‚ σ ⟩ ⟩
--       ≡⟨ ≡.refl ⟩
--         ⟨ ⟨ PUSH m ∷ c ‚ σ ⟩ ⟩
--       ≈⟨ elide-τ⋆ (↠-↣ ↣-PUSH ◅ ε) ⟩
--         ⟨ ⟨ c ‚ m ∷ σ ⟩ ⟩
--       ≈⟨ ≈-sym (elide-τ⋆ (↠-switch ◅ ε)) ⟩
--         ⟨ # m ‚ ⟨ c ‚ σ ⟩ ⟩
--       ∎
--     correctness {a ⊕ b} {c} {σ} =
--       begin
--         ⟨ ⟨ compile (a ⊕ b) c ‚ σ ⟩ ⟩
--       ≡⟨ ≡.refl ⟩
--         ⟨ ⟨ compile a (compile b (ADD ∷ c)) ‚ σ ⟩ ⟩
--       ≈⟨ correctness ⟩
--         ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩
--       ≈⟨ eval-left ⟩
--         ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
--       ∎

% vim: ft=tex:

