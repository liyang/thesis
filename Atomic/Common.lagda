module Common where

module Level where
  open import Level public
open import Coinduction public using (∞; ♯_; ♭)
open import Function public

open import Function.Equality public using (_⟨$⟩_)

module Equivalence where
  open import Function.Equivalence public
  open Equivalence public
open Equivalence public
  using (Equivalence; equivalence; _⇔_; ⇔-setoid)
  renaming (_∘_ to _⟨∘⟩_)

open import Category.Applicative.Indexed public

module Dec where
  open import Relation.Nullary public
  open import Relation.Nullary.Decidable public
  open import Relation.Nullary.Product public
open Dec public using (Dec; yes; no; ¬_; ⌊_⌋; _×-dec_)

module RBin where
  open import Relation.Binary public
  open import Relation.Binary.Simple public
open RBin public hiding (Rel; Setoid)

Rel : Set → Set₁
Rel A = RBin.Rel A Level.zero

Setoid : Set₁
Setoid = RBin.Setoid Level.zero Level.zero

module ≡ where
  open import Relation.Binary.PropositionalEquality public
open ≡ public using (_≡_; _≢_; _≗_; [_])

module ⊥ where
  open import Data.Empty public
open ⊥ public using (⊥; ⊥-elim)

module ⊤ where
  open import Data.Unit public
open ⊤ public using (⊤; tt)

open import Data.Nat public renaming (_≟_ to _≟ℕ_)

module Fin where
  open import Data.Fin public
  open import Data.Fin.Props public
open Fin public using (Fin; zero; suc) renaming (_≟_ to _≟Fin_)

module Vec where
  open import Data.Vec public
  open import Data.Vec.Properties public

  lookup∘replicate : ∀ {X : Set} {N : ℕ} (i : Fin N) (x : X) → lookup i (replicate x) ≡ x
  lookup∘replicate i = Morphism.op-pure (lookup-morphism i)

  module Pointwise where
    open import Relation.Binary.Vec.Pointwise public
  open Pointwise public using (Pointwise; Pointwise-≡)
open Vec public using (Vec; []; _∷_)

module List where
  open import Data.List public
open List public using (List; []; _∷_; _++_)

module Maybe where
  open import Data.Maybe public renaming (nothing to ○; just to ●)
  from : {A : Set} → A → Maybe A → A
  from = maybe′ id
  ●-inj : ∀ {A : Set} {x y : A} → _≡_ {A = Maybe A} (● x) (● y) → x ≡ y
  ●-inj ≡.refl = ≡.refl
open Maybe public using (Maybe; ○; ●; ●-inj) renaming (maybe′ to maybe)

module Σ where
  open import Data.Product public
  open Level renaming (_⊔_ to _∨_)
  ∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} (D : (x : A) (y : B x) → C x y → Set d) → Set (a ∨ b ∨ c ∨ d)
  ∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c
  ∃₄ : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : (x : A) (y : B x) → C x y → Set d} → (E : (x : A) (y : B x) → (z : C x y) → D x y z → Set e) → Set (a ∨ b ∨ c ∨ d ∨ e)
  ∃₄ E = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → E a b c d
open Σ public using (Σ; ∃; ∃₂; ∃₃; ∃₄; _×_; _,_; uncurry; <_,_>) renaming (proj₁ to fst ; proj₂ to snd)

infix 3 ,_
,_ : ∀ {A : Set} {B : A → Set} {x} → B x → ∃ B
,_ = Σ.,_

module ⊎ where
  open import Data.Sum public
open ⊎ public using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)

module ⋆ where
  open import Data.Star public
open ⋆ public using (Star; _◅◅_) renaming (ε to []; _◅_ to _∷_)
