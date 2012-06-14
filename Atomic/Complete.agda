module Complete where

open import Common
open import Heap
open import Logs
open import Language
open import Transaction
open import Combined

-- Equivalence of _↦′_ and _↣′_

-- Zero or more ↦-mutate rules followed by ↦-atomic.
↦-extract : ∀ {α h₀ e h″ c″ e″} →
  α ▹ h₀ , ↦: , atomic e ⤇ h″ , c″ , e″ →
  ∃₂ λ h m →
  α ≡ ☢ ×
  c″ , e″ ≡ ↦: , # m ×
  Dec (h₀ ≡ h) ×
  h , e ↦′⋆ h″ , # m
↦-extract (⤇: α≢τ ε (↠-↦ (↦-mutate h₁))) = ⊥-elim (α≢τ ≡.refl)
↦-extract (⤇: α≢τ ε (↠-↦ (↦-atomic e↦⋆m))) = _ , _ , ≡.refl , ≡.refl , yes ≡.refl , e↦⋆m
↦-extract (⤇: α≢τ (↠-↦ (↦-mutate h₁) ◅ c↠⋆c′) c′↠c″) with ↦-extract (⤇: α≢τ c↠⋆c′ c′↠c″)
... | h , m , ≡.refl , ≡.refl , eq? , e↦⋆m = _ , _ , ≡.refl , ≡.refl , (_ ≟Heap h) , e↦⋆m

↦′→↣′ : ∀ {h₀ l h e h′ e′} →
  Consistent h₀ l →
  Equivalent h₀ l h →
  h , e  ↦′  h′ , e′ →
  ∃ λ l′ →
  Consistent h₀ l′ ×
  Equivalent h₀ l′ h′ ×
  h₀ ⊢  l , e  ↣′  l′ , e′
↦′→↣′ cons equiv ↦′-ℕ = , cons , equiv , ↣′-ℕ
↦′→↣′ cons equiv (↦′-R m b↦b′) = Σ.map id (Σ.map id (Σ.map id (↣′-R m))) (↦′→↣′ cons equiv b↦b′)
↦′→↣′ cons equiv (↦′-L b a↦a′) = Σ.map id (Σ.map id (Σ.map id (↣′-L b))) (↦′→↣′ cons equiv a↦a′)
↦′→↣′ cons equiv (↦′-writeE e↦e′) = Σ.map id (Σ.map id (Σ.map id ↣′-writeE)) (↦′→↣′ cons equiv e↦e′)
↦′→↣′ cons equiv ↦′-writeℕ = , cons , Write-Equivalent equiv , ↣′-writeℕ
↦′→↣′ {h₀} {ρ & ω} cons equiv (↦′-read v) with equiv v | ↣′-read (ρ & ω) v
... | equiv-v | ↣-read′ with ω « v »
...   | ● m rewrite equiv-v = , cons , equiv , ↣-read′
...   | ○ with ρ « v » | ≡.inspect (_«_» ρ) v
...     | ● m | _ rewrite equiv-v = , cons , equiv , ↣-read′
...     | ○   | ‹ ρ[v]≡○ › rewrite ≡.sym equiv-v = _
          , Read-Consistent (ρ & ω) v cons
          , Read-Equivalent ρ[v]≡○ equiv , ↣-read′

↦′⋆→↣′⋆ : ∀ {h₀ l h e h′ e′} →
  Consistent h₀ l →
  Equivalent h₀ l h →
  h , e  ↦′⋆  h′ , e′ →
  ∃ λ l′ →
  Consistent h₀ l′ ×
  Equivalent h₀ l′ h′ ×
  h₀ ⊢ l , e  ↣′⋆ l′ , e′
↦′⋆→↣′⋆ cons equiv ε = _ , cons , equiv , ε
↦′⋆→↣′⋆ cons equiv (e↦e′ ◅ e′↦⋆e″) with ↦′→↣′ cons equiv e↦e′
... | l′ , cons′ , equiv′ , e↣e′ with ↦′⋆→↣′⋆ cons′ equiv′ e′↦⋆e″
...   | l″ , cons″ , equiv″ , e′↣⋆e″ = l″ , cons″ , equiv″ , e↣e′ ◅ e′↣⋆e″
