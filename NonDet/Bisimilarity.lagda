%if include /= True
\begin{comment}
%let include = True
%include NonDet/Language.lagda
%include NonDet/Combined.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import NonDet.Language
open import NonDet.Combined

module NonDet.Bisimilarity where
\end{code}
%endif

\section{Weak Bisimilarity}\label{sec:nondet-bisimilarity}

%format _↠‹τ›_ = "\func{\anonymous{\twoheadrightarrow}\texttt{<}\tau\texttt{>}\anonymous}"
%format ↠‹τ› = "\infix{\func{{\twoheadrightarrow}\texttt{<}\tau\texttt{>}}}"
%format _↠‹τ›⋆_ = "\func{\anonymous{\twoheadrightarrow}\texttt{<}\tau\texttt{>}^\star\anonymous}"
%format ↠‹τ›⋆ = "\infix{\func{{\twoheadrightarrow}\texttt{<}\tau\texttt{>}^\star}}"
%format _⤇‹_›_ = "\type{\anonymous{\Mapsto}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ⤇‹ = "\infix{\type{{\Mapsto}\texttt{<}}}"
%format ⤇-↠ = "\cons{{\Mapsto}\text-{\twoheadrightarrow}}"
Now we can give a concrete definition to our notion of bisimilarity. More
specifically, we shall be defining `weak bisimilarity', as we are not
concerned with silent transitions. First of all, it is convenient to define
a `visible transition' |_⤇‹_›_| where only |Action|s are exposed, in terms
of the |_↠‹_›_| relation from the previous section,
%if False
\begin{code}
infix 3 _↠‹τ›⋆_ _⤇‹_›_
mutual
\end{code}
%endif
\begin{code}
  data _⤇‹_›_ : LTS Action Combined where
    ⤇-↠ : ∀ {x x₀ x₁ x′ α}
      (x↠τ⋆x₀ : x ↠‹τ›⋆ x₀) (x₀↠x₁ : x₀ ↠‹ ! α › x₁) (x₁↠τ⋆x′ : x₁ ↠‹τ›⋆ x′) →
      x ⤇‹ α › x′
\end{code}
where we write |_↠‹τ›⋆_| as a shorthand for the reflexive transitive closure
of |↠‹ τ ›|, defined as follows:
\begin{code}
  _↠‹τ›_ : Rel Combined Level.zero
  x ↠‹τ› y = x ↠‹ τ › y

  _↠‹τ›⋆_ : Rel Combined Level.zero
  _↠‹τ›⋆_ = Star _↠‹τ›_
\end{code}

%format _≼_ = "\func{\anonymous{\preccurlyeq}\anonymous}"
%format ≼ = "\infix{\func{{\preccurlyeq}}}"
%format _≈_ = "\type{\anonymous{\approx}\anonymous}"
%format ≈ = "\infix{\type{{\approx}}}"
%format _≈′_ = "\type{\anonymous{\approx}\Prime\anonymous}"
%format ≈′ = "\infix{\type{{\approx}\Prime}}"
%if False
\begin{code}
infix 5 _≼_ _≈_ _≈′_
infix 9 _&_
mutual
\end{code}
%endif
\noindent Two states |x| and |y| are now defined to be `weakly bisimilar' if
and only if whatever visible transition |x| can make, |y| is able to follow
with the same action, resulting in states |x'| and |y'| that are also
bisimilar, and vice versa. Since this is symmetric in both directions, we
will define a helper |_≼_| for ease of readability:
\begin{code}
  _≼_ : Rel Combined Level.zero
  x ≼ y = ∀ x′ {α} → x ⤇‹ α › x′ → ∃ λ y′ → y ⤇‹ α › y′ × x′ ≈′ y′
\end{code}
That is, we write |x ≼ y| iff for whatever state |x′| can be reached from
|x| while emitting the action |α|, |y| can reach a corresponding state |y′|
such that |x′| and |y′| are bisimilar. In turn, a relation |x ≈ y| is simply
a conjunction of |x ≼ y| and |y ≼ x|:
%format _&_ = "\cons{\anonymous{\&}\anonymous}"
%format & = "\infix{\cons{{\&}}}"
%format x≼y = "x{\preccurlyeq}y"
%format y≼x = "y{\preccurlyeq}x"
\begin{code}
  data _≈_ : Rel Combined Level.zero where
    _&_ : ∀ {x y} (x≼y : ∞ (x ≼ y)) (y≼x : ∞ (y ≼ x)) → x ≈ y
\end{code}
The types of both |x≼y| and |y≼x| arguments are coinductive, as indicated by
the use of the |∞| type, since bisimilarity is a coinductive
notion~\cite{milner,sangiorgi09-origins}. The use of coinductive data in
Agda was introduced in section \S\ref{sec:agda-coinduction}.

%format ≈′-≈ = "\cons{{\approx}\Prime\text-{\approx}}"
%format ≈′-sym = "\cons{{\approx}\Prime\text-sym}"
%format ≈′-trans = "\cons{{\approx}\Prime\text-trans}"
Note that in the above definition of |_≼_|, we demand a proof of |x′ ≈′ y′|
rather than a direct proof of |x′ ≈ y′|, in order to `beat Agda's
productivity checker'~\cite{danielsson10-productivity}. The |_≈′_| data type
can be seen as the syntax for an embedded language, where each constructor
corresponds to an operation that we wish to perform on bisimilarity proofs.
In this instance we only require symmetry and transitivity, along with
a constructor |≈′-≈| that embeds |_≈_| proofs:
\begin{code}
  data _≈′_ : Rel Combined Level.zero where
    ≈′-≈ : _≈_ ⇒ _≈′_
    ≈′-sym : Symmetric _≈′_
    ≈′-trans : Transitive _≈′_
\end{code}
We write |_⇒_| as a synomym for relational implication, which is---along
with |Symmetric| and |Transitive|---defined in the standard library in the
obvious manner.
%\footnote{For our purposes, they are effectively defined as
%follows:
%%format _∼_ = "{\anonymous{\sim}\anonymous}"
%%format ∼ = "\infix{{\sim}}"
%\begin{spec}
%Reflexive Symmetric Transitive : ∀ {A : Set} → Rel A Level.zero → Set
%Reflexive   _∼_ = ∀ {x}      → x ∼ x
%Symmetric   _∼_ = ∀ {x y}    → x ∼ y → y ∼ x
%Transitive  _∼_ = ∀ {x y z}  → x ∼ y → y ∼ z → x ∼ z
%\end{spec}%
%}
With this technique, we are obliged to show that |_≈′_| implies |_≈_|,
i.e.~provide an interpretor from this embedded language to an actual |_≈_|
proof. However, as far as comprehension is concerned, the reader can simply
treat the use of |_≈′_| in the definition of |_≼_| as if it were |_≈_|.

%format ≼-refl = "\func{{\preccurlyeq}\text-refl}"
%format ≈-refl = "\func{{\approx}\text-refl}"
%format ≈-sym = "\func{{\approx}\text-sym}"
%format ≼-trans = "\func{{\preccurlyeq}\text-trans}"
%format ≈-trans = "\func{{\approx}\text-trans}"
%format x≼y = "x{\preccurlyeq}y"
%format y≼x = "y{\preccurlyeq}x"
%format y≼z = "y{\preccurlyeq}z"
%format z≼y = "z{\preccurlyeq}y"
%format x⤇x′ = "x{\Mapsto}x\Prime{}"
%format y⤇y′ = "y{\Mapsto}y\Prime{}"
%format z⤇z′ = "z{\Mapsto}z\Prime{}"
Given the above, it is straightforward to prove that |_≈_| is an equivalence
relation on |Combined|. Reflexivity is shown by the following two mutual
definitions:
\begin{code}
mutual
  ≼-refl : Reflexive _≼_
  ≼-refl x′ x⤇x′ = x′ ∧ x⤇x′ ∧ ≈′-≈ ≈-refl

  ≈-refl : Reflexive _≈_
  ≈-refl = ♯ ≼-refl & ♯ ≼-refl
\end{code}
The type of |≼-refl| is synonymous to |∀ {x} → x ≼ x|, which in turn expands
by the definition of |_≼_| to the following:
\begin{spec}
∀ {x} x′ {α} → x ⤇‹ α › x′ → ∃ λ x″ → x ⤇‹ α › x″ × x′ ≈′ x″
\end{spec}
We prove the existence of an |x″| such that |x ⤇‹ α › x″| and |x′ ≈′ x″| by
returning the same |x′| and the witness of |x ⤇‹ α › x′| as we were given.
Proof of |x′ ≈′ x′| is obtained by embedding the result of a corecursive
call to |≈-refl : x′ ≈ x′|.

The proof of |Reflexive _≈_| involves two symmetric invocations to |≼-refl|.
Since both corecursive instances of |≈-refl| are guarded by an unbroken
chain of |_&_|, |♯_|, |_∧_| and |≈′-≈| constructors with no intervening
function invocations, Agda accepts the above definition as productive.

Symmetry on the other hand is much more straightforward,
\begin{code}
≈-sym : Symmetric _≈_
≈-sym (x≼y & y≼x) = y≼x & x≼y
\end{code}
as we need only swap the two halves of the bisimilarity proof. Finally to
show transitivity of |_≈_|, we again make use of the symmetric nature of
bisimilarity, with the help of a mutually corecursive definition |≼-trans|:
%format x′≈′y′ = "x\Prime{\approx}\Prime{}y\Prime{}"
%format y′≈′z′ = "y\Prime{\approx}\Prime{}z\Prime{}"
\begin{code}
mutual
  ≼-trans : Transitive _≼_
  ≼-trans x≼y y≼z x′ x⤇x′ with x≼y x′ x⤇x′
  ≼-trans x≼y y≼z x′ x⤇x′ | y′ ∧ y⤇y′ ∧ x′≈′y′ with y≼z y′ y⤇y′
  ≼-trans x≼y y≼z x′ x⤇x′ | y′ ∧ y⤇y′ ∧ x′≈′y′ | z′ ∧ z⤇z′ ∧ y′≈′z′
    = z′ ∧ z⤇z′ ∧ ≈′-trans x′≈′y′ y′≈′z′

  ≈-trans : Transitive _≈_
  ≈-trans (x≼y & y≼x) (y≼z & z≼y)
    = ♯ ≼-trans (♭ x≼y) (♭ y≼z) & ♯ ≼-trans (♭ z≼y) (♭ y≼x)
\end{code}
The |≼-trans| proof---given |x≼y|, |y≼z|, |x′| and |x⤇x′|---has a goal of:
\begin{spec}
∃ λ z′ → z ⤇‹ α › z′ × x′ ≈′ z′
\end{spec}
We can use |x≼y| and |y≼z| in two steps to construct evidence of |y′| and
|z′| such that,
\begin{spec}
y ⤇‹ α › y′ × x′ ≈′ y′ {-"\quad\text{and}\quad"-} z ⤇‹ α › z′ × y′ ≈′ z′
\end{spec}
with the witness to |x′ ≈′ z′| obtained by |≈′-trans|. The proof for
|Transitive _≈_| proceeds in the same manner as |≈-refl|, with two
corecursive calls to |≼-trans| for each half of the property.

%format ≈′-refl = "\func{{\approx}\Prime\text-refl}"
%if False
\begin{code}
≈′-refl : Reflexive _≈′_
≈′-refl = ≈′-≈ ≈-refl
\end{code}
%endif

Earlier we stated that we are obligated to show that |_≈′_| implies |_≈_|.
Having now implemented all of the functions corresponding to the terms of
the embedded |_≈′_| language, we can proceed quite simply as follows:
%format ≈′→≈ = "\func{{\approx}\Prime{\rightarrow}{\approx}}"
%format x≈y = "x{\approx}y"
%format y≈′x = "y{\approx}\Prime{}x"
%format x≈′z = "x{\approx}\Prime{}z"
%format z≈′y = "z{\approx}\Prime{}y"
\begin{code}
≈′→≈ : _≈′_ ⇒ _≈_
≈′→≈ (≈′-≈ x≈y) = x≈y
≈′→≈ (≈′-sym y≈′x) = ≈-sym (≈′→≈ y≈′x)
≈′→≈ (≈′-trans x≈′z z≈′y) = ≈-trans (≈′→≈ x≈′z) (≈′→≈ z≈′y)
\end{code}
Here it is clear that |≈′→≈| is structurally recursive on its |x ≈′ y|
argument, and therefore must be total.

%≈→≼ : ∀ {x y} → x ≈ y → x ≼ y
%≈→≼ (x≼y & y≼x) = ♭ x≼y
%≈→≽ : ∀ {x y} → x ≈ y → y ≼ x
%≈→≽ (x≼y & y≼x) = ♭ y≼x

We conclude this section by noting that |_≈_| is an equivalence relation on
|Combined| machines, which enables us to use the equational (actually
pre-order) reasoning combinators from the standard library module
$\name{Relation.Binary.PreorderReasoning}$. The plumbing details have been
omitted in this presentation for brevity, however.

%if False
\begin{code}
setoid : Setoid Level.zero Level.zero
setoid = record
  { Carrier = Combined
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

