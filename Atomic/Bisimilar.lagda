%if False
\begin{code}
module Bisimilar where

open import Common
open import Heap
open import Language
open import Combined
\end{code}
%endif

\subsection{Bisimilarity of Semantics}

%if False
\begin{code}
mutual
  infix 4 _⊢_≼_ _⊢_≽_ _⊢_≈_
  _⊢_≼_ : Heap × Expression → Rel Combined
  h , e ⊢ x ≼ y = ∀ {h′ x′ e′ α}
    (x⤇x′ : α ▹ h , x , e ⤇ h′ , x′ , e′) →
    ∃ λ y′ → α ▹ h , y , e ⤇ h′ , y′ , e′ ×
    (h′ , e′ ⊢ x′ ≈ y′)
\end{code}
%endif

%if False
\begin{code}
  _⊢_≽_ : Heap × Expression → Rel Combined
  _⊢_≽_ he = flip (_⊢_≼_ he)
\end{code}
%endif

%if False
\begin{code}
  record _⊢_≈_ (he : Heap × Expression) (x y : Combined) : Set where
    constructor _&_
    field
      ≈→≼ : ∞ (he ⊢ x ≼ y)
      ≈→≽ : ∞ (he ⊢ x ≽ y)
\end{code}
%endif

%if False
\begin{code}
open _⊢_≈_ public
\end{code}
%endif

%if False
\begin{code}
mutual
  ≼-refl : {he : Heap × Expression} → Reflexive (_⊢_≼_ he)
  ≼-refl x⤇x′ = _ , x⤇x′ , ≈-refl
\end{code}
%endif

%if False
\begin{code}
  ≈-refl : {he : Heap × Expression} → Reflexive (_⊢_≈_ he)
  ≈-refl = ♯ ≼-refl & ♯ ≼-refl
\end{code}
%endif

%if False
\begin{code}
-- A bit useless as the termination checker can't see through it (although
-- record projections are okay), so we end up inlining ≈-sym in such cases.
≈-sym : {he : Heap × Expression} → Symmetric (_⊢_≈_ he)
≈-sym (x≼y & x≽y) = x≽y & x≼y
\end{code}
%endif

%if False
\begin{code}
mutual
  ≼-trans : {he : Heap × Expression} → Transitive (_⊢_≼_ he)
  ≼-trans x≼y y≼z x⤇x′ with x≼y x⤇x′
  ... | y′ , y⤇y′ , x′≈y′ with y≼z y⤇y′
  ...   | z′ , z⤇z′ , y′≈z′ = z′ , z⤇z′ , ≈-trans x′≈y′ y′≈z′
\end{code}
%endif

%if False
\begin{code}
  ≈-trans : {he : Heap × Expression} → Transitive (_⊢_≈_ he)
  ≈-trans (x≼y & x≽y) (y≼z & y≽z) = ♯ ≼-trans (♭ x≼y) (♭ y≼z) & ♯ ≼-trans (♭ y≽z) (♭ x≽y)
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:

