%if include /= True
\begin{comment}
%let include = True
%include Fork/Language.lagda
%include Fork/Combined.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import Fork.Combined as Combined

module Fork.Bisimilarity where

infix 5 _≼_ _≈_ _≈′_
infix 9 _&_
mutual
\end{code}
%endif

\section{Bisimilarity}

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
The definition of bisimilarity remains identical to that of the Zap language
given in \S\ref{sec:nondet-bisimilarity}, save for a change in the carrier
set from |Combined| to |List Combined|:
\begin{code}
  _≼_ : Rel (List Combined) Level.zero
  x ≼ y = ∀ x′ {α} → x ⤇‹ α › x′ → ∃ λ y′ → y ⤇‹ α › y′ × x′ ≈′ y′

  data _≈_ (x : List Combined) : List Combined → Set where
    _&_ : ∀ {y} → (x≼y : ∞ (x ≼ y)) → (y≼x : ∞ (y ≼ x)) → x ≈ y
\end{code}
%format ≈′-≈ = "\cons{{\approx}\Prime\text-{\approx}}"
%format ≈′-sym = "\cons{{\approx}\Prime\text-sym}"
%format ≈′-trans = "\cons{{\approx}\Prime\text-trans}"
%format ≈′-cong₂ = "\cons{{\approx}\Prime\text-cong_2}"
%format rˡ = "r^l"
%format rʳ = "r^r"
%format sˡ = "s^l"
%format sʳ = "s^r"
The embedded language of |_≈′_| gains an extra symbol |≈′-cong₂| that allows
us to combine two pairs of bisimilar thread soups. Formally, it corresponds
to the proposition that |_≈′_| is a congruence relation on the monoid
$(|List Combined|, |++|, |[]|)$,
% Cf. cong₂ : x ≡ y → u ≡ v → f x u ≡ f y v
%format ⟶ = "\infix{\func{\longrightarrow}}"
\begin{code}
  data _≈′_ : Rel (List Combined) Level.zero where
    ≈′-≈      : _≈_ ⇒ _≈′_
    ≈′-sym    : Symmetric _≈′_
    ≈′-trans  : Transitive _≈′_
    ≈′-cong₂  : _++_ Preserves₂ _≈′_ ⟶ _≈′_ ⟶ _≈′_
\end{code}
where the type of the |≈′-cong₂| constructor expands to:
\begin{spec}
≈′-cong₂ : ∀ {rˡ sˡ rʳ sʳ} → rˡ ≈′ sˡ → rʳ ≈′ sʳ → rˡ ++ rʳ ≈′ sˡ ++ sʳ
\end{spec}
The same proofs from \S\ref{sec:nondet-bisimilarity} suffices to show that
|_≈_| forms an equivalence relation on thread soups. The obligation to show
that |_≈′_| implies |_≈_| will be fulfilled at the end of
\S\ref{sec:fork-concat}, as it depends on the proof that |_≈_| is also
a congruence relation on $(|List Combined|, |++|, |[]|)$. Before we can do
that however, we have a few more lemmas to establish.

%format ≈-refl = "\func{{\approx}\text-refl}"
%if False
\begin{code}
mutual
  ≼-refl : Reflexive _≼_
  ≼-refl {x} x′ x⤇‹α›x′ = x′ ∧ x⤇‹α›x′ ∧ ≈′-≈ ≈-refl

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
  ≼-trans x≼y y≼z x′ x⤇x′ with x≼y x′ x⤇x′
  ≼-trans x≼y y≼z x′ x⤇x′ | y′ ∧ y⤇y′ ∧ x′≈′y′ with y≼z y′ y⤇y′
  ≼-trans x≼y y≼z x′ x⤇x′ | y′ ∧ y⤇y′ ∧ x′≈′y′ | z′ ∧ z⤇z′ ∧ y′≈′z′ = z′ ∧ z⤇z′ ∧ ≈′-trans x′≈′y′ y′≈′z′

  ≈-trans : Transitive _≈_
  ≈-trans (x≼y & y≼x) (y≼z & z≼y) = ♯ ≼-trans (♭ x≼y) (♭ y≼z) & ♯ ≼-trans (♭ z≼y) (♭ y≼x)
\end{code}
%endif

%format ≈→≼ = "\func{{\approx}{\rightarrow}{\preccurlyeq}}"
%format ≈→≽ = "\func{{\approx}{\rightarrow}{\succcurlyeq}}"
%if False
\begin{code}
≈→≼ : _≈_ ⇒ _≼_
≈→≼ (x≼y & y≼x) = ♭ x≼y
≈→≽ : _≈_ ⇒ flip _≼_
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
  { Carrier = List Combined
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

