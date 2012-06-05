module Common where

import Level
open import Coinduction public using (∞; ♯_; ♭)
open import Function public
open import Algebra public
open import Category.Functor public

open import Relation.Nullary public
open import Relation.Nullary.Decidable public using (⌊_⌋)
open import Data.Empty public
open import Data.Unit public using (⊤; tt)

open import Relation.Binary public

module ≡ where
  open import Relation.Binary.PropositionalEquality public hiding (inspect)
  module Reasoning where
    open ≡-Reasoning public renaming
      ( _≡⟨_⟩_ to _≡⟪_⟫_ )
    infixr 2 _≡⟪_⁻¹⟫_
    _≡⟪_⁻¹⟫_ : ∀ {X : Set} (x : X) {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
    _≡⟪_⁻¹⟫_ x = _≡⟪_⟫_ x ∘ sym
  open Deprecated-inspect public
open ≡ public using (_≡_; _≢_; _≗_; _with-≡_)

module ≅ where
  open import Relation.Binary.HeterogeneousEquality public
open ≅ public using (_≅_)

module Bool where
  open import Data.Bool public
open Bool public using (Bool; true; false; if_then_else_)

open import Data.Nat public renaming (_≟_ to _≟ℕ_)

module Maybe where
  open import Data.Maybe public
  just-inj : ∀ {X : Set} {x x′ : X} → (just x ∶ Maybe X) ≡ just x′ → x ≡ x′
  just-inj ≡.refl = ≡.refl
open Maybe public using (Maybe; just; nothing; just-inj)

module Fin where
  open import Data.Fin public
  open import Data.Fin.Props public
open Fin public using (Fin; zero; suc) renaming (_≟_ to _≟Fin_)

module List where
  open import Data.List public
open List public using (List; []; _∷_; _++_)

module Vec where
  open import Data.Vec public
open Vec public using (Vec; []; _∷_) renaming (_[_]≔_ to _«_»≔_)

module Sum where
  open import Data.Sum public
open Sum public using (_⊎_; inj₁; inj₂)

module Star where
  open import Data.Star public
open Star public using (Star; ε; _◅_; _◅◅_)

module Σ where
  open import Data.Product public
open Σ public using (Σ; _×_; proj₁; proj₂; ∃; ∃₂) renaming (_,_ to _∧_)

LTS : Set → Set → Set₁
LTS A X = X → A → X → Set

