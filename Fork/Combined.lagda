%if include /= True
\begin{comment}
%let include = True
%include Fork/Action.lagda
%include Fork/Language.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import Fork.Action as Action
open import Fork.Language

module Fork.Combined where

open RawFunctor Action.rawFunctor
\end{code}
%endif

\section{Combined Machines and Thread Soups}\label{sec:fork-combined}

%format Combined = "\type{Combined}"
%format ⟨_⟩ = "\cons{\langle\anonymous\rangle}"
%format ⟨⟩ = "\cons{\langle\rangle}"
Our definition of a combined machine remains unchanged from the Zap
language, with the constructors |⟨_‚_⟩|, |⟨_⟩| and |⟨⟩| corresponding to the
three phases of executions:
\begin{code}
data Combined : Set where
  ⟨_‚_⟩ : (e : Expression) (t : Machine) → Combined
  ⟨_⟩ : (t : Machine) → Combined
  ⟨⟩ : Combined
\end{code}

%format _⁺∷_ = "\func{\anonymous^{\texttt+}{:}{:}\anonymous}"
%format ⁺∷ = "\infix{\func{^{\texttt+}{:}{:}}}"
%format E⁺ = "\func{E^{\texttt+}}"
%format M⁺ = "\func{M^{\texttt+}}"
%if False
\begin{code}
infixr 5 _⁺∷_
infix 4 _↠‹_›_
mutual
\end{code}
%endif

\noindent So far, the semantics of the Fork language have been given in
terms of individual expression or virtual machine threads. Since the notion
of a `thread soup' is common to both cases, we simply matters by introducing
concurrency at the level of combined machines. It suffices to model our
thread soups as |List|s of combined machines, and we define labelled
transitions between them as follows:
%format _↠‹_›_ = "\type{\anonymous{\twoheadrightarrow}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↠‹ = "\infix{\type{{\twoheadrightarrow}\texttt{<}}}"
%format ↠-↦ = "\cons{{\twoheadrightarrow}\text-{\mapsto}}"
%format ↠-↣ = "\cons{{\twoheadrightarrow}\text-{\rightarrowtail}}"
%format ↠-preempt = "\cons{{\twoheadrightarrow}\text-preempt}"
%format ↠-switch = "\cons{{\twoheadrightarrow}\text-switch}"
%format ↠-done = "\cons{{\twoheadrightarrow}\text-done}"
%format e↦e′ = "e{\mapsto}e\Prime{}"
%format t↣t′ = "t{\rightarrowtail}t\Prime{}"
%format s↠s′ = "s{\twoheadrightarrow}s\Prime{}"
\begin{code}
  data _↠‹_›_ : LTS (Action Combined) (List Combined) where
    ↠-↦ : ∀ {e e′ t s α} →
      (e↦e′  : e ↦‹ α › e′) → let α′ = E⁺ <$> α in
       ⟨ e  ‚ t ⟩  ∷ s  ↠‹ α′ › ⟨ e′ ‚ t ⟩  ∷ α′ ⁺∷ s
    ↠-↣ : ∀ {t t′ s α} →
      (t↣t′  : t ↣‹ α › t′) → let α′ = M⁺ <$> α in
            ⟨ t ⟩  ∷ s  ↠‹ α′ › ⟨ t′ ⟩      ∷ α′ ⁺∷ s
    ↠-done : ∀ {m s} →
      ⟨ ⟨ [] ‚ m ∷ [] ⟩ ⟩ ∷ s ↠‹ ∎ m › ⟨⟩ ∷ s
    ↠-switch : ∀ {m c σ s} →
      ⟨ # m ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ s ↠‹ τ › ⟨ ⟨ c ‚ m ∷ σ ⟩ ⟩ ∷ s
    ↠-preempt : ∀ {x s s′ α} → (s↠s′ : s ↠‹ α › s′) →
      x ∷ s ↠‹ … α › x ∷ s′
\end{code}
As with the Zap language, the |↠-↦| and |↠-↣| rules lift transitions on
expression and virtual machine threads to soups of combined machines. The
trivial |E⁺| and |M⁺| helpers lift |Expression| and |Machine| into
|Combined|, given as follows,
\begin{code}
  E⁺ : Expression → Combined
  E⁺ e = ⟨ e ‚ ⟨ [] ‚ [] ⟩ ⟩

  M⁺ : Machine → Combined
  M⁺ = ⟨_⟩
\end{code}
while |_⁺∷_| inserts any spawned threads into the thread soup, defined
below:
\begin{code}
  _⁺∷_ : Action Combined → List Combined → List Combined
  τ    ⁺∷ s = s
  ⊞    ⁺∷ s = s
  ∎ m  ⁺∷ s = s
  ⁺ x  ⁺∷ s = x ∷ s
  … α  ⁺∷ s = s
\end{code}
Aside from the generalisation to thread soups, the |↠-done| and |↠-switch|
rules are otherwise identical to those defined for the Zap language.

Finally, we allow arbitrary thread interleaving via the |↠-preempt| rule. As
our focus is not on the subtleties of different scheduling algorithms, we
therefore do not place any restrictions on what thread the `scheduler' may
choose to execute next.

%if False
\begin{code}
infix 4 _↠τ_ _↠τ₁_ _↠τ⋆_ _↠τ⋆₁_ _↠≄τ_ _↠≄τ₁_
infixr 5 _◅₁_
\end{code}
%endif

\section{Silent and Visible Transitions}

For our later proofs, it will be convenient to have a canonical definition
of silent and non-silent transitions. We regard a silent transition between
|r| and |s| as a triple comprising an action |α|, a proof of |α ≃τ|, along
with the transition |r ↠‹ α › s|:
%format _↠τ_ = "\func{\anonymous{\twoheadrightarrow}\tau\anonymous}"
%format ↠τ = "\infix{\func{{\twoheadrightarrow}\tau}}"
\begin{code}
_↠τ_ : ∀ r s → Set
r ↠τ s = ∃ λ α → α ≃τ × r ↠‹ α › s
\end{code}
Conversely, a non-silent transition carries a proof of |α ≄τ| instead:
%format _↠≄τ_ = "\func{\anonymous{\twoheadrightarrow}{\not\simeq}\tau\anonymous}"
%format ↠≄τ = "\infix{\func{{\twoheadrightarrow}{\not\simeq}\tau}}"
\begin{code}
_↠≄τ_ : ∀ r s → Set
r ↠≄τ s = ∃ λ α → α ≄τ × r ↠‹ α › s
\end{code}
%format _↠τ⋆_ = "\func{\anonymous{\twoheadrightarrow}\tau^\star\anonymous}"
%format ↠τ⋆ = "\infix{\func{{\twoheadrightarrow}\tau^\star}}"
Finally we may write |_↠τ⋆_| for the reflexive, transitive closure of
|_↠τ_|, using the following definition:
\begin{code}
_↠τ⋆_ : ∀ r s → Set
_↠τ⋆_ = Star _↠τ_
\end{code}

When we are only interested in the transitions of a single thread, the
following synonyms are helpful for stating any relevant properties:
%format _↠τ₁_ = "\func{\anonymous{\twoheadrightarrow}\tau_1\anonymous}"
%format ↠τ₁ = "\infix{\func{{\twoheadrightarrow}\tau_1}}"
%format _↠τ⋆₁_ = "\func{\anonymous{\twoheadrightarrow}\tau^\star_1\anonymous}"
%format ↠τ⋆₁ = "\infix{\func{{\twoheadrightarrow}\tau^\star_1}}"
\begin{code}
_↠τ₁_ : ∀ x y → Set
x ↠τ₁ y = ∀ s → x ∷ s ↠τ y ∷ s

_↠τ⋆₁_ : ∀ x y → Set
x ↠τ⋆₁ y = ∀ s → x ∷ s ↠τ⋆ y ∷ s
\end{code}
%format _↠≄τ₁_ = "\func{\anonymous{\twoheadrightarrow}{\not\simeq}\tau_1\anonymous}"
%format ↠≄τ₁ = "\infix{\func{{\twoheadrightarrow}{\not\simeq}\tau_1}}"
%format x′⁺ = "x\Prime^{\texttt+}"
We subscript the above transitions with `$_1$' as a reminder that the
propositions are |∀|-quantified over the rest of the thread soup. For
|_↠≄τ₁_|, we must concatenate the resulting |x′⁺ : List Combined| to the
rest of the soup,
\begin{code}
_↠≄τ₁_ : ∀ x x′⁺ → Set
x ↠≄τ₁ x′⁺ = ∀ s → x ∷ s ↠≄τ x′⁺ ++ s
\end{code}
%format _◅₁_ = "\func{\anonymous{\lhd}_1\anonymous}"
%format ◅₁ = "\infix{\func{{\lhd}_1}}"
%format x↠τ₁x′ = "x{\twoheadrightarrow}\tau_1x\Prime{}"
%format x′↠τ⋆₁y = "x\Prime{\twoheadrightarrow}\tau^\star_1y"
as non-silent transitions may potentially spawn new threads. Finally, the
|_◅₁_| function allows us to conveniently combine |_↠τ₁_| sequences, in the
same manner as the |_◅_| constructor of the |Star| type:
\begin{code}
_◅₁_ : ∀ {x x′ y} → x ↠τ₁ x′ → x′ ↠τ⋆₁ y → x ↠τ⋆₁ y
x↠τ₁x′ ◅₁ x′↠τ⋆₁y = λ s → x↠τ₁x′ s ◅ x′↠τ⋆₁y s
\end{code}
%if False
\begin{code}
ε₁ : ∀ {x} → x ↠τ⋆₁ x
ε₁ s = ε
\end{code}
%endif

Given the above definitions of silent and non-silent transitions, our notion
of a visible transition is identical in essence to that of the Zap language,
given back in \S\ref{sec:nondet-bisimilarity}:
%if False
\begin{code}
infix 4 _⤇‹_›_
mutual
\end{code}
%endif
%format _⤇‹_›_ = "\type{\anonymous{\Mapsto}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ⤇‹ = "\infix{\type{{\Mapsto}\texttt{<}}}"
%format ⤇-↠ = "\cons{{\Mapsto}\text-{\twoheadrightarrow}}"
%format s↠τ⋆s₀ = "s{\twoheadrightarrow}\tau^\star{}s_0"
%format s₀↠≄τs₁ = "s_0{\twoheadrightarrow}{\not\simeq}\tau{}s_0"
%format s₁↠τ⋆s′ = "s_1{\twoheadrightarrow}\tau^\star{}s\Prime{}"
%format visible = "\func{visible}"
%format ⟦_⟧ = "\func{[\![\anonymous]\!]}"
%format ⟦ = "\prefix{\func{[\![}}"
%format ⟧ = "\postfix{\func{]\!]}}"
\begin{code}
  data _⤇‹_›_ : LTS (Action ⊤) (List Combined) where
    ⤇-↠ : ∀ {s s₀ s₁ s′}
      (s↠τ⋆s₀   : s   ↠τ⋆  s₀)
      (s₀↠≄τs₁  : s₀  ↠≄τ  s₁)
      (s₁↠τ⋆s′  : s₁  ↠τ⋆  s′) →
      s ⤇‹ ⟦ s₀↠≄τs₁ ⟧ › s′
\end{code}
As we do not have direct access to the action emitted by the non-silent
|s₀↠≄τs₁| transition, we require a helper |⟦_⟧| to extract the visible
action:
\begin{code}
  visible : ∀ {α : Action Combined} → α ≄τ → Action ⊤
  visible {τ}    α≄τ   = ⊥-elim (α≄τ is-τ)
  visible {⊞}    α≄τ   = ⊞
  visible {∎ m}  α≄τ   = ∎ m
  visible {⁺ x}  α≄τ   = ⁺ tt
  visible {… α}  …α≄τ  = visible (…α≄τ ∘ is-…)

  ⟦_⟧ : ∀ {s s′} → s ↠≄τ s′ → Action ⊤
  ⟦_⟧ (α ∧ α≄τ ∧ s↠s′) = visible α≄τ
\end{code}
By this point, any spawned threads will have been inserted into the thread
soup already, so we are no longer interested in its particulars, other than
that a fork has taken place. Correspondingly, |⟦_⟧| returns an |Action
⊤|---where |⊤| is the singleton `unit' type---rather than an |Action
Combined|.

%format ↠τ-switch = "\func{{\twoheadrightarrow}\tau\text-switch}"
%format ↠τ-preempt = "\func{{\twoheadrightarrow}\tau\text-preempt}"
%format ↠≄τ-preempt = "\func{{\twoheadrightarrow}{\not\simeq}\tau\text-preempt}"
%format xs↠xs′ = "\mathit{xs}{\twoheadrightarrow}\mathit{xs}\Prime{}"
%if False
%{
%format …α≄τ = "\func{...\alpha{\not\simeq}\tau}"
\begin{code}
↠τ-switch : ∀ {s m c σ} → ⟨ # m ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ s ↠τ ⟨ ⟨ c ‚ m ∷ σ ⟩ ⟩ ∷ s
↠τ-switch = τ ∧ is-τ ∧ ↠-switch

↠τ-preempt : ∀ {x s s′} → s ↠τ s′ → x ∷ s ↠τ x ∷ s′
↠τ-preempt (α ∧ α≃τ ∧ s↠s′) = … α ∧ is-… α≃τ ∧ ↠-preempt s↠s′

↠≄τ-preempt : ∀ {x s s′} → (s↠s′ : s ↠≄τ s′) →
  Σ (x ∷ s ↠≄τ x ∷ s′) λ xs↠xs′ → ⟦ s↠s′ ⟧ ≡ ⟦ xs↠xs′ ⟧
↠≄τ-preempt (α ∧ α≄τ ∧ s↠s′)
  = (… α ∧ …α≄τ ∧ ↠-preempt s↠s′) ∧ ≡.refl where
  …α≄τ : … α ≄τ
  …α≄τ (is-… α≃τ) = α≄τ α≃τ
\end{code}
%}
%endif

% vim: ft=tex fo-=m fo-=M:

