%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
%include Atomic/Combined.lagda
\end{comment}
%endif

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
  infix 4 _⊢_≼_ _⊢_≈_
\end{code}
%endif

%format _⊢_≼_ = "\type{\anonymous{\vdash}\anonymous{\preccurlyeq}\anonymous}"
%format ≼ = "\infix{\type{\preccurlyeq}}"
%format _⊢_≽_ = "\type{\anonymous{\vdash}\anonymous{\succcurlyeq}\anonymous}"
%format ≽ = "\infix{\type{\succcurlyeq}}"
%format _⊢_≈_ = "\type{\anonymous{\vdash}\anonymous{\approx}\anonymous}"
%format ≈ = "\infix{\type{\approx}}"
%format x⤇x′ = "\Varid{x{\Mapsto}x\Prime}"
The definition of bisimilarity differs in some details compared with the
previous two chapters. Since we are just comparing two different semantics
for the same expression, we define one half of bisimilarity as follows:
\begin{code}
  _⊢_≼_ : Heap × Expression → Rel Combined
  h , e ⊢ x ≼ y = ∀ {h′ x′ e′ α} →
    (x⤇x′ :   α ▹ h , x ,  e ⤇ h′ , x′ ,  e′) →
    ∃ λ y′ →  α ▹ h , y ,  e ⤇ h′ , y′ ,  e′ × (h′ , e′ ⊢ x′ ≈ y′)
\end{code}
That is given a heap |h| and expression |e|, whenever it can make a visible
transition to |h′| and |e′| under the semantics represented by |x|, an
equivalent transition to the same |h′| and |e′| exists under |y|, such that
|x′| and |y′| are also bisimilar for |h′| and |e′|.

%format ≈→≼ = "\func{{\approx}{\rightarrow}{\preccurlyeq}}"
%format ≈→≽ = "\func{{\approx}{\rightarrow}{\succcurlyeq}}"
%{
%format ≈→≼ = "\name{{\approx}{\rightarrow}{\preccurlyeq}}"
%format ≈→≽ = "\name{{\approx}{\rightarrow}{\succcurlyeq}}"
Bisimilarity is then defined as a pair of coinductive |_⊢_≼_| relations:
\begin{code}
  record _⊢_≈_ (he : Heap × Expression) (x y : Combined) : Set where
    constructor _&_
    field
      ≈→≼ : ∞ (he ⊢ x ≼ y)
      ≈→≽ : ∞ (he ⊢ y ≼ x)
\end{code}
%}

%if False
\begin{code}
open _⊢_≈_ public
mutual
\end{code}
%endif

%format ≼-refl = "\func{{\preccurlyeq}\text-refl}"
%format ≈-refl = "\func{{\approx}\text-refl}"
%format ≈-sym = "\func{{\approx}\text-sym}"
%format x≼y = "\Varid{x{\preccurlyeq}y}"
%format y≼x = "\Varid{y{\preccurlyeq}x}"
%format ≼-trans = "\func{{\preccurlyeq}\text-trans}"
%format ≈-trans = "\func{{\approx}\text-trans}"
%format y≼z = "\Varid{y{\preccurlyeq}z}"
%format z≼y = "\Varid{z{\preccurlyeq}y}"
%format y⤇y′ = "\Varid{y{\Mapsto}y\Prime}"
%format x′≈y′ = "\Varid{x\Prime{\approx}y\Prime}"
%format z⤇z′ = "\Varid{z{\Mapsto}z\Prime}"
%format y′≈z′ = "\Varid{y\Prime{\approx}z\Prime}"
\noindent Utilising the same proofs as before, we can show that |_⊢_≈_| is
reflexive, symmetric, and transitive on |Combined|, given a heap and an
expression:
\begin{code}
  ≼-refl : {he : Heap × Expression} → Reflexive (_⊢_≼_ he)
  ≼-refl x⤇x′ = _ , x⤇x′ , ≈-refl

  ≈-refl : {he : Heap × Expression} → Reflexive (_⊢_≈_ he)
  ≈-refl = ♯ ≼-refl & ♯ ≼-refl

  ≈-sym : {he : Heap × Expression} → Symmetric (_⊢_≈_ he)
  ≈-sym (x≼y & y≼x) = y≼x & x≼y

  ≼-trans : {he : Heap × Expression} → Transitive (_⊢_≼_ he)
  ≼-trans x≼y y≼z x⤇x′ with x≼y x⤇x′
  ... |  y′ , y⤇y′ , x′≈y′ with y≼z y⤇y′
  ...    | z′ , z⤇z′ , y′≈z′ = z′ , z⤇z′ , ≈-trans x′≈y′ y′≈z′

  ≈-trans : {he : Heap × Expression} → Transitive (_⊢_≈_ he)
  ≈-trans (x≼y & y≼x) (y≼z & z≼y) =
    ♯ ≼-trans (♭ x≼y) (♭ y≼z) & ♯ ≼-trans (♭ z≼y) (♭ y≼x)
\end{code}
%-- A bit useless as the termination checker can't see through it (although
%-- record projections are okay), so we end up inlining ≈-sym in such cases.
%format _≈′_ = "\type{\anonymous{\approx\Prime}\anonymous}"
In this chapter, we managed to avoid the use of an embedded language (the
|_≈′_| relation of previous chapters) to convince Agda that our coinductive
definitions are properly constructor-guarded, and hence productive. That
said, we will need to manually inline several uses of |≈-sym| in later
proofs, as the guardedness checker cannot see through function definitions
yet at the time of writing.

% vim: ft=tex fo-=m fo-=M:

