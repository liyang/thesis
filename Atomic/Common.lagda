%if False
\begin{code}
module Common where
\end{code}
%endif

%if False
\begin{code}
module Level where
  open import Level public
open import Coinduction public using (∞; ♯_; ♭)
open import Function public
\end{code}
%endif

%format ⟨$⟩ = "\infix{\func{\langle{\$}\rangle}}"
%if False
\begin{code}
open import Function.Equality public using (_⟨$⟩_)
\end{code}
%endif

%format ⇔ = "\infix{\type{\Leftrightarrow}}"
%format equivalence = "\func{equivalence}"
%format Equivalence.id = "\func{Equivalence.id}"
%format Equivalence.to = "\func{Equivalence.to}"
%if False
\begin{code}
module Equivalence where
  open import Function.Equivalence public
  open Equivalence public
open Equivalence public
  using (Equivalence; equivalence; _⇔_; ⇔-setoid)
  renaming (_∘_ to _⟨∘⟩_)
\end{code}
%endif

%if False
\begin{code}
open import Category.Applicative.Indexed public
\end{code}
%endif

%format Dec.map = "\func{Dec.map}"
%format Dec.map′ = "\func{Dec.map\Prime}"
%if False
\begin{code}
module Dec where
  open import Relation.Nullary public
  open import Relation.Nullary.Decidable public
  open import Relation.Nullary.Product public
open Dec public using (Dec; yes; no; ¬_; ⌊_⌋; _×-dec_)
\end{code}
%endif

%if False
\begin{code}
module RBin where
  open import Relation.Binary public
  open import Relation.Binary.Simple public
open RBin public hiding (Rel; Setoid)
\end{code}
%endif

%if False
\begin{code}
Rel : Set → Set₁
Rel A = RBin.Rel A Level.zero
\end{code}
%endif

%if False
\begin{code}
Setoid : Set₁
Setoid = RBin.Setoid Level.zero Level.zero
\end{code}
%endif

%format ‹ = "\prefix{\cons{\!\texttt[\!\!\texttt[\!}}"
%format › = "\postfix{\cons{\!\texttt]\!\!\texttt]\!}}"
%if False
\begin{code}
module ≡ where
  open import Relation.Binary.PropositionalEquality public
open ≡ public using (_≡_; _≢_; _≗_) renaming ([_] to ‹_›)
\end{code}
%endif

%if False
\begin{code}
module ⊥ where
  open import Data.Empty public
open ⊥ public using (⊥; ⊥-elim)
\end{code}
%endif

%if False
\begin{code}
module ⊤ where
  open import Data.Unit public
open ⊤ public using (⊤; tt)
\end{code}
%endif

%if False
\begin{code}
open import Data.Nat public renaming (_≟_ to _≟ℕ_)
\end{code}
%endif

%if False
\begin{code}
module Fin where
  open import Data.Fin public
  open import Data.Fin.Props public
open Fin public using (Fin; zero; suc) renaming (_≟_ to _≟Fin_)
\end{code}
%endif

%format Vec.tabulate = "\func{Vec.tabulate}"
%format Vec.Pointwise.app = "\func{Vec.Pointwise.app}"
%format Vec.Pointwise.ext = "\cons{Vec.Pointwise.ext}"
%format Vec.Pointwise-≡ = "\func{Vec.Pointwise\text-{\equiv}}"
%format Vec.Pointwise.decidable = "\func{Vec.Pointwise.decidable}"
%format Vec.lookup∘replicate = "\func{Vec.lookup{\circ}replicate}"
%format Vec.lookup∘tabulate = "\func{Vec.lookup{\circ}tabulate}"
%format Vec.lookup∘update = "\func{Vec.lookup{\circ}update}"
%format Vec.lookup∘update′ = "\func{Vec.lookup{\circ}update′}"
%if False
\begin{code}
module Vec where
  open import Data.Vec public
  open import Data.Vec.Properties public

  lookup∘replicate : ∀ {X : Set} {N : ℕ} (i : Fin N) (x : X) → lookup i (replicate x) ≡ x
  lookup∘replicate i = Morphism.op-pure (lookup-morphism i)

  module Pointwise where
    open import Relation.Binary.Vec.Pointwise public
  open Pointwise public using (Pointwise; Pointwise-≡)
open Vec public using (Vec; []; _∷_)
\end{code}
%endif

%if False
\begin{code}
module List where
  open import Data.List public
open List public using (List; []; _∷_; _++_)
\end{code}
%endif

%format ○ = "\cons{\circ}"
%format ● = "\cons{\bullet}"
%format maybe = "\func{maybe}"
%format ●-inj = "\func{\bullet\text-inj}"
%if False
\begin{code}
module Maybe where
  open import Data.Maybe public renaming (nothing to ○; just to ●)
  ●-inj : ∀ {A : Set} {x y : A} → _≡_ {A = Maybe A} (● x) (● y) → x ≡ y
  ●-inj ≡.refl = ≡.refl
open Maybe public using (Maybe; ○; ●; ●-inj) renaming (maybe′ to maybe)
\end{code}
%endif

%format , = "\infix{\cons{,}\,}"
%format fst = "\func{fst}"
%format snd = "\func{snd}"
%if False
\begin{code}
module Σ where
  open import Data.Product public
  open Level renaming (_⊔_ to _∨_)
  ∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} (D : (x : A) (y : B x) → C x y → Set d) → Set (a ∨ b ∨ c ∨ d)
  ∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c
  ∃₄ : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : (x : A) (y : B x) → C x y → Set d} → (E : (x : A) (y : B x) → (z : C x y) → D x y z → Set e) → Set (a ∨ b ∨ c ∨ d ∨ e)
  ∃₄ E = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → E a b c d
open Σ public using (Σ; ∃; ∃₂; ∃₃; ∃₄; _×_; _,_; uncurry; <_,_>) renaming (proj₁ to fst ; proj₂ to snd)
\end{code}
%endif

%if False
\begin{code}
infix 3 ,_
,_ : ∀ {A : Set} {B : A → Set} {x} → B x → ∃ B
,_ = Σ.,_
\end{code}
%endif

%if False
\begin{code}
module ⊎ where
  open import Data.Sum public
open ⊎ public using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
\end{code}
%endif

%if False
\begin{code}
module Star where
  open import Data.Star public
open Star public using (Star; _◅◅_; ε; _◅_)
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:
