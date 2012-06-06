module Bisimilar where

open import Common
open import Language

mutual
  infix 4 _⊢_≼_ _⊢_≽_ _⊢_≈_
  _⊢_≼_ : Heap × Expression → Rel Combined
  h , e ⊢ x ≼ y = ∀ {h′ x′ e′ α} (x⤇x′ : α ⊢ h , x , e ⤇ h′ , x′ , e′) → ∃ λ y′ → α ⊢ h , y , e ⤇ h′ , y′ , e′ × (h′ , e′ ⊢ x′ ≈ y′)
  _⊢_≽_ : Heap × Expression → Rel Combined
  _⊢_≽_ he = flip (_⊢_≼_ he)

  record _⊢_≈_ (he : Heap × Expression) (x y : Combined) : Set where
    constructor _∧_
    field
      ≈→≼ : ∞ (he ⊢ x ≼ y)
      ≈→≽ : ∞ (he ⊢ x ≽ y)

open _⊢_≈_ public

mutual
  ≼-refl : {he : Heap × Expression} → Reflexive (_⊢_≼_ he)
  ≼-refl x⤇x′ = _ , x⤇x′ , ≈-refl

  ≈-refl : {he : Heap × Expression} → Reflexive (_⊢_≈_ he)
  ≈-refl = ♯ ≼-refl ∧ ♯ ≼-refl

-- A bit useless as the termination checker can't see through it (although
-- record projections are okay), so we end up inlining ≈-sym in such cases.
≈-sym : {he : Heap × Expression} → Symmetric (_⊢_≈_ he)
≈-sym (x≼y ∧ x≽y) = x≽y ∧ x≼y

mutual
  ≼-trans : {he : Heap × Expression} → Transitive (_⊢_≼_ he)
  ≼-trans x≼y y≼z x⤇x′ with x≼y x⤇x′
  ... | y′ , y⤇y′ , x′≈y′ with y≼z y⤇y′
  ...   | z′ , z⤇z′ , y′≈z′ = z′ , z⤇z′ , ≈-trans x′≈y′ y′≈z′

  ≈-trans : {he : Heap × Expression} → Transitive (_⊢_≈_ he)
  ≈-trans (x≼y ∧ x≽y) (y≼z ∧ y≽z) = ♯ ≼-trans (♭ x≼y) (♭ y≼z) ∧ ♯ ≼-trans (♭ y≽z) (♭ x≽y)

