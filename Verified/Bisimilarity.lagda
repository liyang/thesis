%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
%include Verified/Action.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Verified.Bisimilarity where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Language as Language using (Combined) renaming (_⤇‹_›_ to _↦‹_›_)
\end{code}
%endif

%format _≼_ = "\func{\anonymous{\preccurlyeq}\anonymous}"
%format ≼ = "\infix{\func{{\preccurlyeq}}}"
%format _≈_ = "\type{\anonymous{\approx}\anonymous}"
%format ≈ = "\infix{\type{{\approx}}}"
%format _≈′_ = "\type{\anonymous{\approx}\Prime\anonymous}"
%format ≈′ = "\infix{\type{{\approx}\Prime}}"
%format _&_ = "\cons{\anonymous{\&}\anonymous}"
%format & = "\infix{\cons{{\&}}}"
%format x≼y = "x{\preccurlyeq}y"
%format y≼x = "y{\preccurlyeq}x"
%if False
\begin{code}
mutual
  infix 4 _≼_
  _≼_ : Rel (Heap × List Combined) Level.zero
  x ≼ y = ∀ x′ {α} → x ↦‹ α › x′ → ∃ λ y′ → y ↦‹ α › y′ × x′ ≈′ y′

  infix 4 _≈_
  infix 9 _&_
  data _≈_ (x : Heap × List Combined) : Heap × List Combined → Set where
    _&_ : ∀ {y} → (x≼y : ∞ (x ≼ y)) → (y≼x : ∞ (y ≼ x)) → x ≈ y
\end{code}
%endif

%  _∀≈_ : Rel (List Combined) Level.zero
%  x ∀≈ y = ∀ h → h ∧ x ≈ h ∧ y

%  _∀≈′_ : Rel (List Combined) Level.zero
%  x ∀≈′ y = ∀ h → h ∧ x ≈′ h ∧ y
%    ≈′-cong₂ : _++_ Preserves₂ _∀≈′_ ⟶ _∀≈′_ ⟶ _∀≈′_

%format ≈′-≈ = "\cons{{\approx}\Prime\text-{\approx}}"
%format ≈′-sym = "\cons{{\approx}\Prime\text-sym}"
%format ≈′-trans = "\cons{{\approx}\Prime\text-trans}"
%format ≈′-cong₂ = "\cons{{\approx}\Prime\text-cong_2}"
%format rˡ = "r^l"
%format rʳ = "r^r"
%format sˡ = "s^l"
%format sʳ = "s^r"
%if False
\begin{code}
  infix 4 _≈′_
  data _≈′_ : Rel (Heap × List Combined) Level.zero where
    ≈′-≈ : _≈_ ⇒ _≈′_
--    ≈′-cong₂ : _++_ Preserves₂ _≈′_ ⟶ _≈′_ ⟶ _≈′_
    ≈′-sym : Symmetric _≈′_
    ≈′-trans : Transitive _≈′_
\end{code}
%endif

%format ≈-refl = "\func{{\approx}\text-refl}"
%if False
\begin{code}
mutual
  ≼-refl : Reflexive _≼_
  ≼-refl {x} x′ x↦‹α›x′ = x′ ∧ x↦‹α›x′ ∧ ≈′-≈ ≈-refl

  ≈-refl : Reflexive _≈_
  ≈-refl {x} = ♯ ≼-refl & ♯ ≼-refl
\end{code}
%endif

%format ≈-sym = "\func{{\approx}\text-sym}"
%if False
\begin{code}
≈-sym : Symmetric _≈_
≈-sym (x≼y & y≼x) = y≼x & x≼y
\end{code}
%endif

%format ≈-trans = "\func{{\approx}\text-trans}"
%if False
\begin{code}
mutual
  ≼-trans : Transitive _≼_
  ≼-trans x≼y y≼z x′ x↦x′ with x≼y x′ x↦x′
  ≼-trans x≼y y≼z x′ x↦x′ | y′ ∧ y↦y′ ∧ x′≈′y′ with y≼z y′ y↦y′
  ≼-trans x≼y y≼z x′ x↦x′ | y′ ∧ y↦y′ ∧ x′≈′y′ | z′ ∧ z↦z′ ∧ y′≈′z′ = z′ ∧ z↦z′ ∧ ≈′-trans x′≈′y′ y′≈′z′

  ≈-trans : Transitive _≈_
  ≈-trans (x≼y & y≼x) (y≼z & z≼y) = ♯ ≼-trans (♭ x≼y) (♭ y≼z) & ♯ ≼-trans (♭ z≼y) (♭ y≼x)
\end{code}
%endif

%format ≈→≼ = "\func{{\approx}{\rightarrow}{\preccurlyeq}}"
%format ≈→≽ = "\func{{\approx}{\rightarrow}{\succcurlyeq}}"
%if False
\begin{code}
≈→≼ : ∀ {x y} → x ≈ y → x ≼ y
≈→≼ (x≼y & y≼x) = ♭ x≼y
≈→≽ : ∀ {x y} → x ≈ y → y ≼ x
≈→≽ (x≼y & y≼x) = ♭ y≼x
\end{code}
%endif

%format ≈′-refl = "\func{{\approx}\Prime\text-refl}"
%if False
\begin{code}
≈′-refl : Reflexive _≈′_
≈′-refl = ≈′-≈ ≈-refl
\end{code}
%endif

%if False
\begin{code}
setoid : Setoid Level.zero Level.zero
setoid = record
  { Carrier = Heap × List Combined
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈-refl
    ; sym = ≈-sym
    ; trans = ≈-trans
    }
  }
\end{code}
%endif

%format ≈-Reasoning = "\name{{\approx}\text-Reasoning}"
%if False
\begin{code}
import Relation.Binary.EqReasoning as EqR
module ≈-Reasoning where
  open EqR setoid public renaming
    ( _≈⟨_⟩_ to _≈⟪_⟫_
    ; _≡⟨_⟩_ to _≡⟪_⟫_ )

  infixr 2 _≈⟪_⁻¹⟫_
  _≈⟪_⁻¹⟫_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
  _≈⟪_⁻¹⟫_ x = _≈⟪_⟫_ x ∘ ≈-sym
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:

