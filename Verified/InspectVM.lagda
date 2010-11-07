%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Language.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Verified.InspectVM where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language
\end{code}
%endif

\begin{code}
data VMCase {h c σ γ ρ ω} : ∀ (e : Expression STM) {m ρ′ ω′} → h ∧ ⟨ compile e c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆ h ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩ → Set where
  vm-PUSH : ∀ {m} → VMCase (# m) (↣τ-PUSH ◅ ε)
--   vm-PUSH : ∀ {m} (rest : h ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆ h ∧ ⟨ c′ ‚ σ′ ‚ γ ‚ ρ″ ‚ ω″ ⟩) → VMCase (# m) (↣τ-PUSH ◅ rest)
--   vm-ADD : ∀ {a m ρ′ ω′ b n ρ″ ω″}
--     (a↣τ⋆m : h ∧ ⟨ compile a (compile b (ADD ∷ c)) ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆ h ∧ ⟨ compile b (ADD ∷ c) ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩)
--     (b↣τ⋆n : h ∧ ⟨ compile b (ADD ∷ c) ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩ ↣τ⋆ h ∧ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ‚ γ ‚ ρ″ ‚ ω″ ⟩) →
--     VMCase (a ⊕ b) (a↣τ⋆m ◅◅ b↣τ⋆n ◅◅ ↣τ-ADD ◅ ε)
--   vm-READ : ∀ {v} {- (rest : h ∧ ⟨ c ‚ lookupTVar h ρ ω v ∷ σ ‚ γ ‚ update-rLog h ρ ω v ‚ ω ⟩ ↣τ⋆ h ∧ ⟨ c′ ‚ σ′ ‚ γ ‚ ρ″ ‚ ω″ ⟩) -} → VMCase (read v) (↣τ-READ ◅ rest)
--   vm-WRITE : ∀ {v e m ρ′ ω′} →
--     (e↣τ⋆m : h  ∧ ⟨ compile e (WRITE v ∷ c) ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆ h ∧ ⟨ WRITE v ∷ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩) →
--     VMCase (write v e) (e↣τ⋆m ◅◅ ↣τ-WRITE ◅ ε)
\end{code}

\begin{code}
-- inspectVM : ∀ {h c σ γ ρ ω} (e : Expression STM) {h′ m ρ′ ω′} → (e↣τ⋆m : h ∧ ⟨ compile e c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆ h′ ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩) → VMCase e e↣τ⋆m

-- ∷-inj₂ : ∀ {x y xs ys} → x ∷ xs ≡ (y ∷ ys ∶ List ℕ) → xs ≡ ys
-- ∷-inj₂ ≡.refl = ≡.refl

-- foo : ∀ (xs : List ℕ) {x} → xs ≢ x ∷ xs
-- foo [] ()
-- foo (x ∷ xs) bar = foo xs (∷-inj₂ bar)

inspectVM : ∀ {c σ h γ ρ ω} (e : Expression STM) {m ρ′ ω′} → (e↣τ⋆m : h ∧ ⟨ compile e c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ⋆ h ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ′ ‚ ω′ ⟩) → VMCase e e↣τ⋆m
inspectVM {i ∷ c} {σ} e e↣τ⋆m = {!!}
inspectVM {c} {n ∷ σ} e e↣τ⋆m = {!!}
inspectVM {[]} {[]} (# m) ((.τ ∧ is-τ ∧ ↣-PUSH) ◅ ε) = vm-PUSH
inspectVM {[]} {[]} (# m) ((.τ ∧ is-τ ∧ ↣-PUSH) ◅ (x ∧ y ∧ ()) ◅ xs)
inspectVM {[]} {[]} (# m) ((._ ∧ is-… _ ∧ ()) ◅ _)
inspectVM {[]} {[]} (a ⊕ b) e↣τ⋆m = {!!}
inspectVM {[]} {[]} (read v) e↣τ⋆m = {!!}
inspectVM {[]} {[]} (write v e) e↣τ⋆m = {!!}

-- inspectVM (# m) ε = {!!}
-- inspectVM (# m) ((.τ ∧ is-τ ∧ ↣-PUSH) ◅ rest) = vm-PUSH rest
-- inspectVM (# m) ((._ ∧ is-… _ ∧ ()) ◅ _)
-- inspectVM (a ⊕ b) e↣τ⋆m = {!!}
-- inspectVM (read v) ε = {!!}
-- inspectVM (read v) ((.τ ∧ is-τ ∧ ↣-READ) ◅ rest) = vm-READ rest
-- inspectVM (read v) ((._ ∧ is-… _ ∧ ()) ◅ _)
-- inspectVM (write v e) we↣τ⋆m with inspectVM e we↣τ⋆m
-- inspectVM (write v ._) ._ | vm-PUSH rest = {!!}
-- inspectVM (write v ._) ._ | vm-READ rest = {!!}
\end{code}

% vim: ft=tex fo-=m fo-=M:

