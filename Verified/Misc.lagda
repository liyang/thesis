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

module Verified.Misc where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language

open RawFunctor Action.rawFunctor
\end{code}
%endif

%if False
\begin{code}
-- This is not true anymore, as ⊕ emits a τ
-- ¬↦‹τ› : ∀ {e e′} → ¬ (IO ‣ e ↦‹ τ › e′)
-- ¬↦‹τ› (↦-⊕R b↦b′) = ¬↦‹τ› b↦b′
-- ¬↦‹τ› (↦-⊕L a↦a′) = ¬↦‹τ› a↦a′

-- ¬↦‹…› : ∀ {e e′ α} → ¬ (IO ‣ e ↦‹ … α › e′)
-- ¬↦‹…› (↦-⊕R b↦b′) = ¬↦‹…› b↦b′
-- ¬↦‹…› (↦-⊕L a↦a′) = ¬↦‹…› a↦a′

-- ¬↦τ : ∀ {e e′ α} → α ≃τ → ¬ (IO ‣ e ↦‹ α › e′)
-- ¬↦τ is-τ e↦e′ = ¬↦‹τ› e↦e′
-- ¬↦τ (is-… α) e↦e′ = ¬↦‹…› e↦e′

-- a more general property would be
--   ∀ {h h′ r r′ α} → α ≄☢ → h ∧ r ↠‹ α › h′ ∧ r′ → h ≡ h′
-- is it necessary?
-- Will need separate ≃☢ type and ⁺≃☢-inj lemmas though
↠τ-heap : ∀ {h h′ r r′} → h ∧ r ↠τ h′ ∧ r′ → h′ ≡ h
↠τ-heap {h} (._ ∧ α≃τ ∧ ↠-↦ e↦e′) = ↦τ-heap (E⁺≃τ-inj α≃τ) e↦e′ where
  ↦τ-heap : ∀ {h′ e e′ α} → α ≃τ → IO ‣ h ∧ e ↦‹ α › h′ ∧ e′ → h′ ≡ h
  ↦τ-heap α≃τ ↦-⊞ = ≡.refl
  ↦τ-heap α≃τ (↦-R b↦b′) = ↦τ-heap α≃τ b↦b′
  ↦τ-heap α≃τ (↦-L a↦a′) = ↦τ-heap α≃τ a↦a′
  ↦τ-heap () ↦-fork
  ↦τ-heap () (↦-atomic e↦⋆m)
↠τ-heap {h} (._ ∧ α≃τ ∧ ↠-↣ t↣t′) = ↣τ-heap (M⁺≃τ-inj α≃τ) t↣t′ where
  ↣τ-heap : ∀ {h′ t t′ α} → α ≃τ → h ∧ t ↣‹ α › h′ ∧ t′ → h′ ≡ h
  ↣τ-heap α≃τ ↣-PUSH = ≡.refl
  ↣τ-heap α≃τ ↣-ADD = ≡.refl
  ↣τ-heap () ↣-FORK
  ↣τ-heap α≃τ ↣-BEGIN = ≡.refl
  ↣τ-heap α≃τ ↣-READ = ≡.refl
  ↣τ-heap α≃τ ↣-WRITE = ≡.refl
  ↣τ-heap α≃τ (↣-COMMIT (no _)) = ≡.refl
  ↣τ-heap () (↣-COMMIT (yes _))
↠τ-heap (._ ∧ is-… α≃τ ∧ ↠-preempt s↠s′) = ↠τ-heap (_ ∧ α≃τ ∧ s↠s′)
↠τ-heap (.τ ∧ α≃τ ∧ ↠-switch) = ≡.refl

postulate ↠τ⋆-heap : ∀ {h h′ r r′} → h ∧ r ↠τ⋆ h′ ∧ r′ → h′ ≡ h
-- ↠τ⋆-heap foo = Star.fold _≡_ ≡.trans ≡.refl {! Star.map ↠τ-heap foo !}
-- ↠τ⋆-heap ε = ≡.refl
-- ↠τ⋆-heap (x ◅ xs) = {!≡.trans (↠τ-heap x) !}
\end{code}

%format ↣τ⋆→↠τ⋆ = "\func{{\rightarrowtail}\tau^\star{\rightarrow}{\twoheadrightarrow}\tau^\star}"
\begin{code}
↣τ⋆→↠τ⋆ : ∀ {s h h′ t t′} → h ∧ t ↣τ⋆ h′ ∧ t′ → h ∧ ⟨ t ⟩ ∷ s ↠τ⋆ h′ ∧ ⟨ t′ ⟩ ∷ s
↣τ⋆→↠τ⋆ = Star.gmap liftMachine ↣τ→↠τ where
  liftMachine : ∀ {s} → Heap × Machine → Heap × List Combined
  liftMachine {s} (h ∧ t) = h ∧ ⟨ t ⟩ ∷ s

  ↣τ→↠τ : ∀ {s h∧t h′∧t′} → h∧t ↣τ h′∧t′ → liftMachine {s} h∧t ↠τ liftMachine {s} h′∧t′
  ↣τ→↠τ {s} {h ∧ t} {h′ ∧ t′} (α ∧ α≃τ ∧ t↣t′) = (M⁺ <$> α) ∧ M⁺≃τ α≃τ
    ∧ ≡.subst (λ s′ → liftMachine {s} (h ∧ t) ↠‹ M⁺ <$> α › liftMachine {s′} (h′ ∧ t′))
      (τ⁺∷s≡s (M⁺≃τ α≃τ) s) (↠-↣ t↣t′)
\end{code}
%endif

\begin{code}
postulate ↠τ⋆→↣τ⋆ : ∀ {h t h′∧s′} → h ∧ ⟨ t ⟩ ∷ [] ↠τ⋆ h′∧s′ → ∃ λ t′ → h′∧s′ ≡ h ∧ ⟨ t′ ⟩ ∷ [] × h ∧ t ↣τ⋆ h ∧ t′
{-
↠τ⋆→↣τ⋆ ε = _ ∧ ≡.refl ∧ ε
↠τ⋆→↣τ⋆ ((._ ∧ () ∧ ↠-done) ◅ _)
↠τ⋆→↣τ⋆ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ _)
↠τ⋆→↣τ⋆ ((._ ∧ α≃τ ∧ ↠-↣ t↣t₀) ◅ t₀↠τ⋆t′) with M⁺≃τ-inj α≃τ
↠τ⋆→↣τ⋆ ((._ ∧ α≃τ ∧ ↠-↣ t↣t₀) ◅ t₀↠τ⋆t′) | is-… α′≃τ = {!t↣t₀!}
↠τ⋆→↣τ⋆ ((._ ∧ α≃τ ∧ ↠-↣ t↣t₀) ◅ t₀↠τ⋆t′) | is-τ with ↠τ⋆→↣τ⋆ t₀↠τ⋆t′
↠τ⋆→↣τ⋆ ((._ ∧ α≃τ ∧ ↠-↣ t↣t₀) ◅ t₀↠τ⋆t′) | is-τ | t′ ∧ ≡.refl ∧ t₀↣τ⋆t′ = t′ ∧ ≡.refl ∧ (_ ∧ is-τ ∧ t↣t₀) ◅ t₀↣τ⋆t′
-}
\end{code}

% vim: ft=tex fo-=m fo-=M:

