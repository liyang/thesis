%if include /= True
\begin{comment}
%let include = True
%include NonDet/Language.lagda
%include NonDet/Machine.lagda
%include NonDet/Combined.lagda
%include NonDet/Bisimilarity.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common hiding (LTS)

open import NonDet.Language
open import NonDet.Machine
open import NonDet.Combined
open import NonDet.Bisimilarity

module NonDet.ElideTau where
\end{code}
%endif

%format elide-τ = "\func{elide\text-\tau}"
\section{The |elide-τ| Lemma}\label{sec:nondet-elide}

%format ¬↦‹τ› = "\func{{\lnot}{\mapsto}\texttt<\tau\texttt>}"
%if False
\begin{code}
¬↦‹τ› : ∀ {e e′} → ¬ (e ↦‹ τ › e′)
¬↦‹τ› (↦-R b↦b′) = ¬↦‹τ› b↦b′
¬↦‹τ› (↦-L a↦a′) = ¬↦‹τ› a↦a′
\end{code}
%endif

A key lemma used throughout our correctness proofs states that a silent
transition between two states |x| and |y| implies that they are bisimilar:
% unique′ : ∀ {x x′ Λ y} (x↠x′ : x ↠‹τ› x′) → (x↠y : x ↠‹ Λ › y) → x↠x′ ≅ x↠y
%format unique = "\func{unique}"
%format x↠τy = "x{\twoheadrightarrow}\tau{}y"
%format x↠y′ = "x{\twoheadrightarrow}y\Prime{}"
%format elide-τ⋆ = "\func{elide\text-\tau^\star}"
%format elide-τ⋆′ = "\func{elide\text-\tau^\star{}\Prime}"
%{
%format x≼y = "\func{x{\preccurlyeq}y}"
%format y≼x = "\func{y{\preccurlyeq}x}"
%format y↠τ⋆y₀ = "y{\twoheadrightarrow}\tau^\star{}y_0"
%format y₀↠y₁ = "y_0{\twoheadrightarrow}y_1"
%format y₁↠τ⋆y′ = "y_1{\twoheadrightarrow}\tau^\star{}y\Prime{}"
\savecolumns
\begin{code}
elide-τ : _↠‹τ›_ ⇒ _≈_
elide-τ {x} {y} x↠τy = ♯ x≼y & ♯ y≼x where
  y≼x : y ≼ x
  y≼x y′ (⤇-↠ y↠τ⋆y₀ y₀↠y₁ y₁↠τ⋆y′)
    = y′ ∧ ⤇-↠ (x↠τy ◅ y↠τ⋆y₀) y₀↠y₁ y₁↠τ⋆y′ ∧ ≈′-refl
\end{code}
In the |y≼x| direction, the proof is trivial: whatever |y| does, |x| can
always match it by first making the given |x↠τy| transition, after which it
can follow |y| exactly.

In the |x≼y| direction, the proof relies on the fact that wherever there is
a choice in the reduction of any give state, each possible transition is
identified with a distinct and non-silent label, which we mentioned in
\S\ref{sec:nondet-action}. Conversely given a silent transition |x↠τy
: x ↠‹τ› y|, it must in fact be the \emph{unique} transition from |x|, which
we can show by the following |unique| lemma:
\restorecolumns
\begin{code}
  unique : ∀ {x y Λ y′} → x ↠‹τ› y → x ↠‹ Λ › y′ → Λ ≡ τ × y′ ≡ y
  unique (↠-↦ e↦e′) x↠y′ = ⊥-elim (¬↦‹τ› e↦e′)
  unique (↠-↣ ↣-PUSH) (↠-↣ ↣-PUSH) = ≡.refl ∧ ≡.refl
  unique ↠-switch (↠-↦ ())
  unique ↠-switch ↠-switch = ≡.refl ∧ ≡.refl
\end{code}
Using |unique|, the |x≼y| direction of |elide-τ| is shown in two parts; the
first shows that |x| cannot make a non-silent transition,
%format x↠x₀ = "x{\twoheadrightarrow}x_0"
%format x₀↠τ⋆x′ = "x_0{\twoheadrightarrow}\tau^\star{}x\Prime{}"
%format x₀≡y = "x_0{\equiv}y"
\restorecolumns
\begin{code}
  x≼y : x ≼ y
  x≼y x′ (⤇-↠ ε x↠x₀ x₀↠τ⋆x′) with unique x↠τy x↠x₀
  x≼y x′ (⤇-↠ ε x↠x₀ x₀↠τ⋆x′) | () ∧ x₀≡y
\end{code}
while the second shows that the first silent transition |x| makes must
coincide with |x↠τy|, in which case |y| can transition to |x′| by following
the subsequent transitions:
%format x₀↠τ⋆x₁ = "x_0{\twoheadrightarrow}\tau^\star{}x_1"
%format x₁↠x₂ = "x_1{\twoheadrightarrow}x_2"
%format x₂↠τ⋆x′ = "x_2{\twoheadrightarrow}\tau^\star{}x\Prime{}"
%format y↠τ⋆x₁ = "y{\twoheadrightarrow}\tau^\star{}x_1"
\restorecolumns
\begin{code}
  x≼y x′ (⤇-↠ (x↠x₀  ◅ x₀↠τ⋆x₁)  x₁↠x₂ x₂↠τ⋆x′) with unique x↠τy x↠x₀
  x≼y x′ (⤇-↠ (x↠τy  ◅ y↠τ⋆x₁)   x₁↠x₂ x₂↠τ⋆x′) | ≡.refl ∧ ≡.refl
    = x′ ∧ ⤇-↠ y↠τ⋆x₁ x₁↠x₂ x₂↠τ⋆x′ ∧ ≈′-refl
\end{code}
%}

\noindent Since |_≈_| is transitive and reflexive, we can generalise the
above result to handle silent transition sequences of arbitrary length, as
well as a symmetric variant:
\begin{code}
elide-τ⋆ : _↠‹τ›⋆_ ⇒ _≈_
elide-τ⋆ = Star.fold _≈_ ≈-trans ≈-refl ∘ Star.map elide-τ

elide-τ⋆′ : Sym _↠‹τ›⋆_ _≈_
elide-τ⋆′ = ≈-sym ∘ elide-τ⋆
\end{code}

% vim: ft=tex fo-=m fo-=M:

