%if include /= True
\begin{comment}
%let include = True
%include NonDet/Language.lagda
%include NonDet/Machine.lagda
%include NonDet/justification.lagda
%include NonDet/Combined.lagda
%include NonDet/Bisimilarity.lagda
%include NonDet/ElideTau.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import NonDet.Language
open import NonDet.Machine
open import NonDet.Combined
open import NonDet.Bisimilarity
open import NonDet.ElideTau

module nondet where
\end{code}
%endif

\chapter{Compiling Non-Determinism Correctly}\label{ch:nondet}

\input{NonDet/introduction.lagda}

\input{NonDet/Language.lagda}

\input{NonDet/Machine.lagda}

\input{NonDet/justification.lagda}

\input{NonDet/Combined.lagda}

\input{NonDet/Bisimilarity.lagda}

\input{NonDet/ElideTau.lagda}

%if False
\begin{code}
open ≈-Reasoning
mutual
\end{code}
%endif

\section{Compiler Correctness}

Now we have enough machinery to formulate the compiler correctness theorem,
which states that given a code continuation |c| and an initial stack |σ|,
execution of the compiled code for an expression |e| followed by |c| is
weakly bisimilar to the reduction of the expression |e| followed by the
machine continuation |⟨ c ‚ σ ⟩|,
%format correctness = "\func{correctness}"
%format eval-left = "\func{eval\text-left}"
%format eval-right = "\func{eval\text-right}"
%format x≼y = "\func{x{\preccurlyeq}y}"
%format y≼x = "\func{y{\preccurlyeq}x}"
\savecolumns
\begin{code}
  correctness : ∀ e c σ → ⟨ e ‚ ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ ⟨ compile e c ‚ σ ⟩ ⟩
\end{code}
or equivalently as the following commuting diagram:
\[|correctness : ∀ c σ →|
\xymatrix@@C=6ex@@R=8ex{
	\text{|Expression|}
		\xyar[rr]^{|compile _ c|}
		\xyar[dr]_{|⟨ _ ‚ ⟨ c ‚ σ ⟩ ⟩|}
	&&\text{|List Instruction|}
		\xyar[dl]^{|⟨ ⟨ _ ‚ σ ⟩ ⟩|}
\\
	&\text{|Combined / ≈|}
}\]
In particular, instantiating |c| and |σ| to empty lists results in the
corollary that for any expressions |e|, the bisimilarity |⟨ e ‚ ⟨ [] ‚ []
⟩ ⟩ ≈ ⟨ ⟨ compile e [] ‚ [] ⟩ ⟩| holds.

\subsection{Proof of |correctness|}%{{{%

We proceed to prove |correctness| by structural induction on the expression
|e|. Two additional lemmas corresponding to the following propositions are
required, which we will prove along the way:
\begin{spec}
  eval-left   : ⟨    a  ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ a  ‚ ⟨ compile b (  ADD ∷ c)  ‚      σ ⟩ ⟩
  eval-right  : ⟨ #  m  ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ b  ‚ ⟨              ADD ∷ c   ‚ m ∷  σ ⟩ ⟩
\end{spec}

% mutual induction between |correctness| and |eval-left|
% self-coinduction for |eval-left| and |eval-right|

First, let us consider the base case of |correctness|, where |e ≡ # m|:
\restorecolumns
\begin{code}
  correctness (# m) c σ =
    begin
      ⟨ # m ‚ ⟨ c ‚ σ ⟩ ⟩
    ≈⟪ elide-τ ↠-switch ⟫
      ⟨ ⟨ c ‚ m ∷ σ ⟩ ⟩
    ≈⟪ elide-τ (↠-↣ ↣-PUSH) ⁻¹⟫
      ⟨ ⟨ PUSH m ∷ c ‚ σ ⟩ ⟩
    ≡⟪ ≡.refl ⟫
      ⟨ ⟨ compile (# m) c ‚ σ ⟩ ⟩
    ∎
\end{code}
As we mentioned in the conclusion of chapter \ref{ch:agda}, the equational
reasoning combinators defined in the standard
library~\cite{danielsson10-stdlib} allow us to present the proof in a simple
calculational style. In the code above, proofs of bisimilarity (or
definitional equality) are supplied between the |⟪| and |⟫| brackets, and
are combined using the appropriate reflexivity, symmetry and transitivity
properties. That is, the above proof could have been equivalently written:
%format ≡→≈ = "\func{{\equiv}{\rightarrow}{\approx}}"
\restorecolumns
\begin{spec}
  correctness (# m) c σ = ≈-trans (elide-τ ↠-switch)
    ( ≈-trans (≈-sym (elide-τ (↠-↣ ↣-PUSH))) (≡→≈ ≡.refl) )
\end{spec}
However, the extra annotations in the equational reasoning version makes the
proof almost self-explanatory.

Moving on to the inductive case, where |e ≡ a ⊕ b|:
\restorecolumns
\begin{code}
  correctness (a ⊕ b) c σ =
    begin
      ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
    ≈⟪ eval-left a b c σ ⟫
      ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩
    ≈⟪ correctness a (compile b (ADD ∷ c)) σ ⟫
      ⟨ ⟨ compile (a ⊕ b) c ‚ σ ⟩ ⟩
    ∎
\end{code}
The first bisimilarity is given by the |eval-left| lemma, while the second
uses the inductive hypothesis for the subexpression |a|, instantiating the
code continuation with |compile b (ADD ∷ c)|.

%}}}%

\subsection{The |eval-left| Lemma}%{{{%

The lemma |eval-left| has essentially a coinductive proof on the possible
transitions |∃ λ α → ∃ λ a′ → a ⤇‹ α › a′| starting from |a|, with a base
case---when no transitions are possible---that is mutually inductively
defined with |correctness|. In the instance of this Zap language however, it
suffices to proceed by case analysis on |a|, as the two alternatives happen
to coincide with whether |a| has any possible transitions. For the base case
where |a| is a numeral |# m|, no further transitions are possible, and we
can reason equationally as follows:
\restorecolumns
\begin{code}
  eval-left : ∀ a b c σ →
    ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩
  eval-left (# m) b c σ =
    begin
      ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
    ≈⟪ eval-right m b c σ ⟫
      ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩
    ≈⟪ correctness b (ADD ∷ c) (m ∷ σ) ⟫
      ⟨ ⟨ compile b (ADD ∷ c) ‚ m ∷ σ ⟩ ⟩
    ≈⟪ elide-τ ↠-switch ⁻¹⟫
      ⟨ # m ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩
    ∎
\end{code}
The proof above makes use of the inductive hypothesis for the subexpression
|b| (of |e ≡ a ⊕ b|) in the mutual definition of |correctness|, as well as
the |eval-right| lemma. In the coinductive case, we consider the |x≼y| and
|y≼x| halves of the bisimilarity separately,
%format aˡ = "a^l"
%format aʳ = "a^r"
\restorecolumns
\begin{code}
  eval-left (aˡ ⊕ aʳ) b c σ = ♯ x≼y & ♯ y≼x where
    a = aˡ ⊕ aʳ
\end{code}
As we mentioned earlier, this part of the proof is coinductive on the
possible reductions rather than structural on the expression |a|, so the
fact that |a ≡ aˡ ⊕ aʳ| is besides the point. We define |a| as a synonym for
|aˡ ⊕ aʳ| for clarity as we do not need to refer to |aˡ| or |aʳ| in the
proof. We also adopt the convention of writing |x| for the left, and |y| for
the right hand sides of the |_≈_| bisimilarity.

In the forward direction, we are given a witness to |x ⤇‹ α › x′|, and must
show that |y| can follow with the same action to some |y′|, such that the
resulting |x′| and |y′| are bisimilar\footnote{Recall that the type synonym
|_≼_| was defined in \S\ref{sec:nondet-bisimilarity} as follows:
\begin{spec}
_≼_ : Rel Combined Level.zero
x ≼ y = ∀ x′ {α} → x ⤇‹ α › x′ → ∃ λ y′ → y ⤇‹ α › y′ × x′ ≈′ y′
\end{spec}
That is, |x ≼ y| is a function that given an |x′|, an implicit |α| and
a witness of |x ⤇‹ α › x′|, must return a triple comprising |y′|, a witness
of |y ⤇‹ α › y′|, along with a proof of |x′ ≈′ y′|.}. The coinduction
hypothesis tells us that |a| can make some visible transition to an |a′|
while emitting an action |α|. Since the evaluation of |a ⊕ b| is
left-biased, it must be the case that |a ⊕ b| reduces under the |↦-L| rule.
Therefore, we can extract the witness |a↦a′| and repack it to witness the
following:
\begin{spec}
⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ⤇‹ α › ⟨ a′ ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩
\end{spec}
The proof below does not explicitly mention the action |α| (among others
identifiers) as this is already implied by its type, and is automatically
inferred.
%format a↦a₀ = "a{\mapsto}a_0"
%format a₀⊕b↦a₁⊕b = "a_0{\oplus}b{\mapsto}a_1{\oplus}b"
%format x₁↠τ⋆x′ = "x_1{\twoheadrightarrow}\tau^\star{}x\Prime{}"
%format a⊕b↦a₀⊕b = "a{\oplus}b{\mapsto}a_0{\oplus}b"
%format x₀↠τ⋆x₁ = "x_0{\twoheadrightarrow}\tau^\star{}x_1"
%format x₁↠x₂ = "x_1{\twoheadrightarrow}x_2"
%format x₂↠τ⋆x′ = "x_2{\twoheadrightarrow}\tau^\star{}x\Prime{}"
\restorecolumns
\begin{code}
    x≼y : ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ≼ ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩
    x≼y ._ (⤇-↠ ε (↠-↦ (↦-L {a′ = a′} a↦a′)) ε)
      = ⟨ a′ ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩
      ∧ ⤇-↠ ε (↠-↦ a↦a′) ε
      ∧ ≈′-≈ (eval-left a′ b c σ)
\end{code}
The above clause only matches visible transitions with empty sequences of
silent combined transitions (i.e.~|ε|). Alternative cases are not possible
since |_↦‹_›_| transitions cannot be silent, and are eliminated using the
|¬↦‹τ›| lemma:
\restorecolumns
\begin{code}
    x≼y x′ (⤇-↠ ε (↠-↦ (↦-L a↦a₀)) (↠-↦ a₀⊕b↦a₁⊕b ◅ x₁↠τ⋆x′))
      = ⊥-elim (¬↦‹τ› a₀⊕b↦a₁⊕b)
    x≼y x′ (⤇-↠ (↠-↦ a⊕b↦a₀⊕b ◅ x₀↠τ⋆x₁) x₁↠x₂ x₂↠τ⋆x′)
      = ⊥-elim (¬↦‹τ› a⊕b↦a₀⊕b)
\end{code}

%format a₀ = "a_0"
%format y₀↠τ⋆y′ = "y_0{\twoheadrightarrow}\tau^\star{}y\Prime{}"
%format y₀↠τ⋆y₁ = "y_0{\twoheadrightarrow}\tau^\star{}y_1"
%format y₁↠y₂ = "y_1{\twoheadrightarrow}y_2"
%format y₂↠τ⋆y′ = "y_2{\twoheadrightarrow}\tau^\star{}y_1"
\noindent In the opposite direction, the combined machine |y| makes
a visible transition to |⟨ a₀ ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩| (henceforth
denoted by |y₀|), from which we can extract a witness |a↦a₀|. This is
followed by some sequence of silent transitions |y₀↠τ⋆y′|. In response, |x|
can make a transition to |⟨ a₀ ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩| (|x′| from here on)
emitting the same action, that is bisimilar to |y₀| via the coinductive
hypothesis on |a₀|. Finally, |elide-τ⋆′ y₀↠τ⋆y′| provides a proof of |y′ ≈′
y₀|, with which we can obtain |y′ ≈′ x′| by transitivity:
\restorecolumns
\begin{code}
    y≼x : ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ≼ ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
    y≼x y′ (⤇-↠ ε (↠-↦ {e′ = a₀} a↦a₀) y₀↠τ⋆y′)
      = ⟨ a₀ ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
      ∧ ⤇-↠ ε (↠-↦ (↦-L a↦a₀)) ε
      ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ y₀↠τ⋆y′)) (≈′-sym (≈′-≈ (eval-left a₀ b c σ)))
    y≼x y′ (⤇-↠ (↠-↦ a↦a₀ ◅ y₀↠τ⋆y₁) y₁↠y₂ y₂↠τ⋆y′)
      = ⊥-elim (¬↦‹τ› a↦a₀)
\end{code}
The second clause eliminates the impossible case of |a| making a |τ|
transition, which completes the proof of |eval-left|.

%}}}%

\subsection{The |eval-right| Lemma}%{{{%

%format ⊕≈ADD = "\func{{\oplus}{\approx}ADD}"
The |eval-right| lemma proceeds in a similar manner by coinduction on the
possible |_↦‹_›_| transitions from |b|. In the base case, |b| cannot make
any further such transitions (i.e.~is some number |# n|), and we need to
show:
\begin{spec}
⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ # n ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩
\end{spec}
As the right hand side can make a silent |↠-switch| transition, we can
factor this part out to make the proof a little neater:
\restorecolumns
\begin{code}
  eval-right : ∀ m b c σ → ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩
  eval-right m (# n) c σ =
    begin
      ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩
    ≈⟪ ⊕≈ADD ⟫
      ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩
    ≈⟪ elide-τ ↠-switch ⁻¹⟫
      ⟨ # n ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩
    ∎ where
    ⊕≈ADD : ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ≈ ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩
    ⊕≈ADD = ♯ x≼y & ♯ y≼x where
\end{code}
The |⊕≈ADD| lemma is where we encounter the non-determinism in our Zap
language. The proof for the two halves |x≼y| and |y≼x| are as follows: in
the first instance, |# m ⊕ # n| can transition with either the |↦-⊞| or
|↦-↯| rule, and we must show that |⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩| can follow with
the same action:
%format x₀↠τ⋆x′ = "x_0{\twoheadrightarrow}\tau^\star{}x\Prime{}"
%format e↦e₀ = "e{\mapsto}e_0"
%format x₀↠τ⋆x₁ = "x_0{\twoheadrightarrow}\tau^\star{}x_1"
%format x₁↠x₂ = "x_1{\twoheadrightarrow}x_2"
%format x₂↠τ⋆x′ = "x_2{\twoheadrightarrow}\tau^\star{}x\Prime{}"
\restorecolumns
\begin{code}
      x≼y : ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ≼ ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩
      x≼y x′ (⤇-↠ ε (↠-↦ ↦-⊞) x₀↠τ⋆x′)
        = ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩
        ∧ ⤇-↠ ε (↠-↣ ↣-ADD) ε
        ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ x₀↠τ⋆x′)) (≈′-≈ (elide-τ ↠-switch))
      x≼y x′ (⤇-↠ ε (↠-↦ ↦-↯) x₀↠τ⋆x′)
        = ⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩
        ∧ ⤇-↠ ε (↠-↣ ↣-ZAP) ε
        ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ x₀↠τ⋆x′)) (≈′-≈ (elide-τ ↠-switch))
      x≼y x′ (⤇-↠ ε (↠-↦ (↦-R ())) x₀↠τ⋆x′)
      x≼y x′ (⤇-↠ ε (↠-↦ (↦-L ())) x₀↠τ⋆x′)
      x≼y x′ (⤇-↠ (↠-↦ e↦e₀ ◅ x₀↠τ⋆x₁) x₁↠x₂ x₂↠τ⋆x′)
        = ⊥-elim (¬↦‹τ› e↦e₀)
\end{code}
This is sketched in figure \ref{fig:nondet-evalright}---read from the top
down---where the left and right branches correspond to the first two clauses
above. The third and fourth clauses handle the fact that neither |# m| nor
|# n| by themselves can reduce any further, while the last deals with silent
|_↦‹_›_| transitions.

\begin{figure}[hbtf]
\[\xymatrix@@C=-1.5ex@@R=5ex{
	& {|⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩|}
		\ar@@{}[ddd]||{\xyrot{90}{|≈|}}^{\xyrot{90}{\rule{0pt}{3ex}|⊕≈ADD|}}
		\xyarr@@[type][ddl]^{\xyrot{28}{|! ⊞|}}_{\xyrot{28}{|↠-↦ ↦-⊞|}}
		\xyarr@@[type][ddr]_{\xyrot{-30}{|! ↯|}}^{\xyrot{-30}{|↠-↦ ↦-↯|}}
\\\\
{|⟨ # (m + n) ‚ ⟨ c ‚ σ ⟩ ⟩|}
	\xyarr@@[type][ddd]_{\xyrot{90}{|τ|}}^{\xyrot{90}{|↠-switch|}}
	\ar@@{}@@<-6ex>[ddd]||{\xyrot{90}{|≈|}}^{\xyrot{90}{\rule{0pt}{3ex}|elide-τ|}}
	&	& {|⟨ # 0 ‚ ⟨ c ‚ σ ⟩ ⟩|}
			\xyarr@@[type][ddd]_{\xyrot{90}{|τ|}}^{\xyrot{90}{|↠-switch|}}
			\ar@@{}@@<4ex>[ddd]||{\xyrot{90}{|≈|}}^{\xyrot{90}{\rule{0pt}{3ex}|elide-τ|}}
\\
	& {|⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩|}
		\xyarr@@[type][ddl]_{\xyrot{26}{|! ⊞|}}^(.42){\xyrot{26}{|↠-↣ ↣-ADD|}}
		\xyarr@@[type][ddr]^{\xyrot{-30}{|! ↯|}}_(.45){\xyrot{-30}{|↠-↣ ↣-ZAP|}}
\\\\
{|⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩|}
		&	& {|⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩|}
	\\
	& {|⟨ # n ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩|}
		\xyarr@@[type][uuu]^{\xyrot{90}{|τ|}}_{\xyrot{90}{|↠-switch|}}
		\ar@@{}@@<6ex>[uuu]||{\xyrot{90}{|≈|}}_{\xyrot{90}{\rule{0pt}{3ex}|elide-τ|}}
}\]
\caption{Proof sketch for the base case of the |eval-right|
lemma.}\label{fig:nondet-evalright}
\end{figure}

The other direction of |⊕≈ADD| is illustrated by reading figure
\ref{fig:nondet-evalright} from the bottom up, and proceeds in the same
manner:
\restorecolumns
\begin{code}
      y≼x : ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩ ≼ ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩
      y≼x y′ (⤇-↠ ε (↠-↣ ↣-ADD) y₀↠τ⋆y′)
        = ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩
        ∧ ⤇-↠ ε (↠-↦ ↦-⊞) (↠-switch ◅ ε)
        ∧ ≈′-≈ (elide-τ⋆′ y₀↠τ⋆y′)
      y≼x y′ (⤇-↠ ε (↠-↣ ↣-ZAP) y₀↠τ⋆y′)
        = ⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩
        ∧ ⤇-↠ ε (↠-↦ ↦-↯) (↠-switch ◅ ε)
        ∧ ≈′-≈ (elide-τ⋆′ y₀↠τ⋆y′)
      y≼x y′ (⤇-↠ (↠-↣ () ◅ y₀↠τ⋆y₁) y₁↠y₂ y₂↠τ⋆y′)
\end{code}
The impossible pattern |()| in the final clause corresponds to the fact that
there is no transition in which an |ADD| instruction emits a silent action.

%format bˡ = "b^l"
%format bʳ = "b^r"
%format b₀ = "b_0"
%format b↦b₀ = "b{\mapsto}b_0"
%format m⊕b↦m⊕b₀ = "m{\oplus}b{\mapsto}m{\oplus}b_0"

The coinductive case of the |eval-right| lemma follows a similar structure
to that of |eval-left|, on the possible transitions from |b|:
\restorecolumns
\begin{code}
  eval-right m (bˡ ⊕ bʳ) c σ = ♯ x≼y & ♯ y≼x where
    b = bˡ ⊕ bʳ
\end{code}
In the |x≼y| direction, |⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩| must reduce according to
|b↦b₀|, therefore |y| can follow by transitioning to |⟨ b₀ ‚ ⟨ ADD
∷ c ‚ m ∷ σ ⟩ ⟩|:
\restorecolumns
\begin{code}
    x≼y : ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ≼ ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩
    x≼y x′ (⤇-↠ ε (↠-↦ (↦-R {b′ = b₀} b↦b₀)) x₀↠τ⋆x′)
      = ⟨ b₀ ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩
      ∧ ⤇-↠ ε (↠-↦ b↦b₀) ε
      ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ x₀↠τ⋆x′)) (≈′-≈ (eval-right m b₀ c σ))
    x≼y x′ (⤇-↠ ε (↠-↦ (↦-L ())) x₀↠τ⋆x′)
    x≼y x′ (⤇-↠ (↠-↦ m⊕b↦m⊕b₀ ◅ x₀↠τ⋆x₁) x₁↠x₂ x₂↠τ⋆x′)
      = ⊥-elim (¬↦‹τ› m⊕b↦m⊕b₀)
\end{code}
The second clause shows that |# m ↦‹ Λ › a′| is uninhabited, while the third 
uses the fact that |# m ⊕ b| cannot make a silent |_↦‹_›_| transition,
to show that both cases are impossible.

For the |y≼x| direction, the proof simply runs in reverse, with |x|
following |y| by transitioning to |⟨ # m ⊕ b₀ ‚ ⟨ c ‚ σ ⟩ ⟩|:
\restorecolumns
\begin{code}
    y≼x : ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ≼ ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩
    y≼x y′ (⤇-↠ ε (↠-↦ {e′ = b₀} b↦b₀) y₀↠τ⋆y′)
      = ⟨ # m ⊕ b₀ ‚ ⟨ c ‚ σ ⟩ ⟩
      ∧ ⤇-↠ ε (↠-↦ (↦-R b↦b₀)) ε
      ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ y₀↠τ⋆y′)) (≈′-sym (≈′-≈ (eval-right m b₀ c σ)))
    y≼x y′ (⤇-↠ (↠-↦ b↦b₀ ◅ y₀↠τ⋆y₁) y₁↠y₂ y₂↠τ⋆y′)
      = ⊥-elim (¬↦‹τ› b↦b₀)
\end{code}
The final case deals with the impossibility of silent |b↦b₀| transitions.
This completes the proof of the |eval-right| and |eval-left| lemmas, and in
turn the |correctness| theorem for our Zap language.

%}}}%

\section{Conclusion}%{{{%

In this chapter we introduced a simpler technique for handling
non-determinism in the context of compiler correctness proofs, which we
illustrated using the Zap language. By carefully choosing silent and visible
actions to distinguish between non-deterministic choices in the reduction of
expressions and virtual machines, we were able to show the crucial |elide-τ|
lemma used in the compiler correctness proof that follows. Finally, our
notion of a combined machine allowed us to directly establish a bisimulation
between our source and target languages without the need for an underlying
process calculus.

%}}}%

% vim: ft=tex fo-=m fo-=M:

