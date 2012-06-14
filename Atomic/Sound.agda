module Sound where

open import Common
open import Heap
open import Logs
open import Language
open import Transaction
open import Combined

-- sequence of ↣′ transitions with different heaps
infix 3 H⊢_↣′_ H⊢_↣′⋆_
H⊢_↣′_ : Rel (Logs × Expression′)
H⊢ c ↣′ c′ = Σ Heap (λ h → h ⊢ c ↣′ c′)

H⊢_↣′⋆_ : Rel (Logs × Expression′)
H⊢_↣′⋆_ = Star H⊢_↣′_

↣′-swap : ∀ {h h′ l e l′ e′} →
  Consistent h′ l′ →
  h  ⊢ l , e ↣′ l′ , e′ →
  h′ ⊢ l , e ↣′ l′ , e′
↣′-swap cons′ ↣′-ℕ = ↣′-ℕ
↣′-swap cons′ (↣′-R m b↣b′) = ↣′-R m (↣′-swap cons′ b↣b′)
↣′-swap cons′ (↣′-L b a↣a′) = ↣′-L b (↣′-swap cons′ a↣a′)
↣′-swap cons′ (↣′-writeE e↣e′) = ↣′-writeE (↣′-swap cons′ e↣e′)
↣′-swap cons′ ↣′-writeℕ = ↣′-writeℕ
↣′-swap {h} {h′} cons′ (↣′-read l v) with cons′ v (h « v ») | ↣′-read {h = h′} l v
... | cons′-v-h | ↣′-read′ with Logs.ω l « v »
...   | ● m = ↣′-read′
...   | ○ with Logs.ρ l « v »
...     | ● m = ↣′-read′
...     | ○ rewrite Vec.lookup∘update v (Logs.ρ l) (● (h « v »)) | cons′-v-h ≡.refl = ↣′-read′

↣′⋆-swap : ∀ {h′ l e l′ e′} →
  Consistent h′ l′ →
  H⊢ l , e ↣′⋆ l′ , e′ →
  h′ ⊢ l , e ↣′⋆ l′ , e′
↣′⋆-swap {h′} cons = fst ∘ Star.gfold id P f (ε , cons) where
  P : Logs × Expression′ → Logs × Expression′ → Set
  P (l , e) (l′ , e′) = h′ ⊢ l , e ↣′⋆ l′ , e′ × Consistent h′ l
  f : ∀ {c c′ c″} → H⊢ c ↣′ c′ → P c′ c″ → P c c″
  f (h , e↣e′) (e′↣′⋆e″ , cons′)
    = ↣′-swap cons′ e↣e′ ◅ e′↣′⋆e″
    , ↣′-Consistent′ e↣e′ cons′
{-
-- alternative definition with explicit recursion (and recomputing cons′ from scratch)
↣′⋆-swap {h′} cons″ [] = []
↣′⋆-swap {h′} cons″ ((h , e↣e′) ∷ H⊢e′↣e″) = ↣′-swap cons′ e↣e′ ∷ ↣′⋆-swap cons″ H⊢e′↣e″ where
  cons′ = H↣′⋆-Consistent H⊢e′↣e″ cons″
-}

private
  extract : ∀ {α h R l e h′ c′ e′ h″ c″ e″} →
    H⊢ ∅ , R ↣′⋆ l , e →
    α ≢ τ →
    h , ↣: ● (R , l) , atomic e  ↠⋆  h′ , c′ , e′ →
    α ▹  h′ , c′ , e′  ↠  h″ , c″ , e″ →
    ∃₂ λ l′ m →
    α ≡ ☢ ×
    c′ , e′ ≡ ↣: ● (R , l′) , atomic (# m) ×
    h″ , c″ , e″ ≡ Update h′ l′ , ↣: ○ , # m ×
    Consistent h′ l′ ×
    H⊢ ∅ , R ↣′⋆ l′ , # m
  extract R↣′⋆e α≢τ ε (↠-↣ (↣-step e↣e′)) = ⊥-elim (α≢τ ≡.refl)
  extract R↣′⋆e α≢τ ε (↠-↣ (↣-mutate h′)) = ⊥-elim (α≢τ ≡.refl)
  extract R↣′⋆e α≢τ ε (↠-↣ (↣-abort ¬cons)) = ⊥-elim (α≢τ ≡.refl)
  extract R↣′⋆e α≢τ ε (↠-↣ (↣-commit cons)) = _ , _ , ≡.refl , ≡.refl , ≡.refl , cons , R↣′⋆e
  extract R↣′⋆e α≢τ (↠-↣ (↣-step e↣e′)   ◅ c′↠⋆c″) c″↠c‴ = extract (R↣′⋆e ◅◅ (_ , e↣e′) ◅ ε) α≢τ c′↠⋆c″ c″↠c‴
  extract R↣′⋆e α≢τ (↠-↣ (↣-mutate h′)   ◅ c′↠⋆c″) c″↠c‴ = extract R↣′⋆e α≢τ c′↠⋆c″ c″↠c‴
  extract R↣′⋆e α≢τ (↠-↣ (↣-abort ¬cons) ◅ c′↠⋆c″) c″↠c‴ = extract ε α≢τ c′↠⋆c″ c″↠c‴

↣-extract : ∀ {α h R h′ c′ e′ h″ c″ e″} →
  α ≢ τ →
  h , ↣: ○ , atomic R ↠⋆ h′ , c′ , e′ →
  α ▹ h′ , c′ , e′ ↠ h″ , c″ , e″ →
  ∃₂ λ l′ m →
  α ≡ ☢ ×
  c′ , e′ ≡ ↣: ● (R , l′) , atomic (# m) ×
  h″ , c″ , e″ ≡ Update h′ l′ , ↣: ○ , # m ×
  Consistent h′ l′ ×
  H⊢ ∅ , R ↣′⋆ l′ , # m
↣-extract α≢τ ε (↠-↣ ↣-begin) = ⊥-elim (α≢τ ≡.refl)
↣-extract α≢τ (↠-↣ ↣-begin ◅ c↠⋆c′) c′↠c″ = extract ε α≢τ c↠⋆c′ c′↠c″

↣′→↦′ : ∀ {h l e l′ e′ h₀} →
  Consistent h₀ l →
  Equivalent h₀ l h →
  h₀ ⊢ l , e ↣′ l′ , e′ →
  ∃ λ h′ →
  Consistent h₀ l′ ×
  Equivalent h₀ l′ h′ ×
  h , e ↦′ h′ , e′
↣′→↦′ cons equiv ↣′-ℕ = _ , cons , equiv , ↦′-ℕ
↣′→↦′ cons equiv (↣′-R m b↣b′) = Σ.map id (Σ.map id (Σ.map id (↦′-R m))) (↣′→↦′ cons equiv b↣b′)
↣′→↦′ cons equiv (↣′-L b a↣a′) = Σ.map id (Σ.map id (Σ.map id (↦′-L b))) (↣′→↦′ cons equiv a↣a′)
↣′→↦′ cons equiv (↣′-writeE e↣e′) = Σ.map id (Σ.map id (Σ.map id ↦′-writeE)) (↣′→↦′ cons equiv e↣e′)
↣′→↦′ cons equiv ↣′-writeℕ = _ , cons , Write-Equivalent equiv , ↦′-writeℕ
↣′→↦′ {h} cons equiv (↣′-read l v) with equiv v | ↦′-read {h} v
... | equiv-v | ↦′-read′ with Logs.ω l « v »
...   | ● m rewrite equiv-v = _ , cons , equiv , ↦′-read′
...   | ○ with Logs.ρ l « v » | ≡.inspect (_«_» (Logs.ρ l)) v
...     | ● m | _ rewrite equiv-v = _ , cons , equiv , ↦′-read′
...     | ○ | ‹ ρ[v]≡○ › rewrite ≡.sym equiv-v = _
          , Read-Consistent l v cons
          , Read-Equivalent ρ[v]≡○ equiv , ↦′-read′

↣′⋆→↦′⋆ : ∀ {h l e l′ e′ h₀} →
  Consistent h₀ l →
  Equivalent h₀ l h →
  h₀ ⊢ l , e ↣′⋆ l′ , e′ →
  ∃ λ h′ →
  Consistent h₀ l′ ×
  Equivalent h₀ l′ h′ ×
  h , e ↦′⋆ h′ , e′
↣′⋆→↦′⋆ cons equiv ε = _ , cons , equiv , ε
↣′⋆→↦′⋆ cons equiv (e↣′e′ ◅ e′↣′⋆e″) with ↣′→↦′ cons equiv e↣′e′
... | h′ , cons′ , equiv′ , e↦′e′ with ↣′⋆→↦′⋆ cons′ equiv′ e′↣′⋆e″
...   | h″ , cons″ , equiv″ , e′↦′⋆e″ = h″ , cons″ , equiv″ , e↦′e′ ◅ e′↦′⋆e″
