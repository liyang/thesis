%if include /= True
\begin{comment}
%let include = True
%include Fork/Action.lagda
%include Fork/Language.lagda
%include Fork/Combined.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import Fork.Action as Action
open import Fork.Language as Language
open import Fork.Combined as Combined

module Fork.Soup where

open RawFunctor Action.rawFunctor
\end{code}
%endif

\section{Properties of Thread Soups}

In this section, we will highlight various lemmas concerning thread soups
that are used towards the final correctness theorem for this Fork language.
For brevity, we will omit the proofs, and instead hint at the proof method;
the full Agda source code may be found on my website.

%if False
\begin{code}
¬↦‹τ› : ∀ {e e′} → ¬ (e ↦‹ τ › e′)
¬↦‹τ› (↦-R b↦b′) = ¬↦‹τ› b↦b′
¬↦‹τ› (↦-L a↦a′) = ¬↦‹τ› a↦a′

¬↦‹…› : ∀ {e e′ α} → ¬ (e ↦‹ … α › e′)
¬↦‹…› (↦-R b↦b′) = ¬↦‹…› b↦b′
¬↦‹…› (↦-L a↦a′) = ¬↦‹…› a↦a′
\end{code}
%endif

%if False
\begin{code}
¬↦τ : ∀ {e e′ α} → α ≃τ → ¬ (e ↦‹ α › e′)
¬↦τ is-τ e↦e′ = ¬↦‹τ› e↦e′
¬↦τ (is-… α) e↦e′ = ¬↦‹…› e↦e′
\end{code}
%endif

%if False
\begin{code}
E⁺≃τ-inj : ∀ {α} → E⁺ <$> α ≃τ → α ≃τ
E⁺≃τ-inj {τ} is-τ = is-τ
E⁺≃τ-inj {⊞} ()
E⁺≃τ-inj {⁺ child} ()
E⁺≃τ-inj {∎ m} ()
E⁺≃τ-inj {… α} (is-… α′≃τ) = is-… (E⁺≃τ-inj α′≃τ)
\end{code}
%endif

% Prepending and appending constant soups
%{{{%

%format ↠τ-prepend = "\func{{\twoheadrightarrow}\tau\text-prepend}"
%if False
\begin{code}
↠τ-prepend : ∀ r {s s′} → s ↠τ s′ → r ++ s ↠τ r ++ s′
↠τ-prepend [] s↠τs′ = s↠τs′
↠τ-prepend (x ∷ r) s↠τs′ = ↠τ-preempt (↠τ-prepend r s↠τs′)
\end{code}
%endif

%if False
\begin{code}
↠≄τ-prepend : ∀ r {s s′} → (s↠s′ : s ↠≄τ s′) → Σ (r ++ s ↠≄τ r ++ s′) λ rs↠rs′ → ⟦ s↠s′ ⟧ ≡ ⟦ rs↠rs′ ⟧
↠≄τ-prepend [] s↠s′ = s↠s′ ∧ ≡.refl
↠≄τ-prepend (x ∷ r) s↠s′ with ↠≄τ-prepend r s↠s′
↠≄τ-prepend (x ∷ r) s↠s′ | rs↠rs′ ∧ ⟦s↠s′⟧≡⟦rs↠rs′⟧ with ↠≄τ-preempt {x} rs↠rs′
↠≄τ-prepend (x ∷ r) s↠s′ | rs↠rs′ ∧ ⟦s↠s′⟧≡⟦rs↠rs′⟧ | xrs↠xrs′ ∧ ⟦rs↠rs′⟧≡⟦xrs↠xrs′⟧ = xrs↠xrs′ ∧ ≡.trans ⟦s↠s′⟧≡⟦rs↠rs′⟧ ⟦rs↠rs′⟧≡⟦xrs↠xrs′⟧
\end{code}
%endif

% used in ↠-append only
%if False
\begin{code}
⁺∷-assoc : ∀ α {s r} → α ⁺∷ (s ++ r) ≡ (α ⁺∷ s) ++ r
⁺∷-assoc τ = ≡.refl
⁺∷-assoc ⊞ = ≡.refl
⁺∷-assoc (⁺ child) = ≡.refl
⁺∷-assoc (∎ m) = ≡.refl
⁺∷-assoc (… α) = ≡.refl
\end{code}
%endif

%if False
\begin{code}
↠-append : ∀ r {s s′ α} → s ↠‹ α › s′ → s ++ r ↠‹ α › s′ ++ r
↠-append r (↠-↦ {e} {e′} {t} {s} {α} e↦e′)
  = ≡.subst P (⁺∷-assoc (E⁺ <$> α)) (↠-↦ e↦e′) where
  P : List Combined → Set
  P αsr = ⟨ e ‚ t ⟩ ∷ s ++ r ↠‹ E⁺ <$> α › ⟨ e′ ‚ t ⟩ ∷ αsr
↠-append r (↠-↣ {t} {t′} {s} {α} t↣t′)
  = ≡.subst P (⁺∷-assoc (M⁺ <$> α)) (↠-↣ t↣t′) where
  P : List Combined → Set
  P αsr = ⟨ t ⟩ ∷ s ++ r ↠‹ M⁺ <$> α › ⟨ t′ ⟩ ∷ αsr
↠-append r ↠-switch = ↠-switch
↠-append r ↠-done = ↠-done
↠-append r (↠-preempt {x} {s} {s′} {α} s↠s′) = ↠-preempt (↠-append r (s↠s′))
\end{code}
%endif

%format ↠τ-append = "\func{{\twoheadrightarrow}\tau\text-append}"
%if False
\begin{code}
↠τ-append : ∀ r {s s′} → s ↠τ s′ → s ++ r ↠τ s′ ++ r
↠τ-append r (α ∧ α≃τ ∧ s↠s′) = (α ∧ α≃τ ∧ ↠-append r s↠s′)
\end{code}
%endif

%format ↠≄τ-append = "\func{{\twoheadrightarrow}{\not\simeq}\tau\text-append}"
%if False
\begin{code}
↠≄τ-append : ∀ r {s s′} → (s↠s′ : s ↠≄τ s′) → Σ (s ++ r ↠≄τ s′ ++ r) λ sr↠s′r → ⟦ s↠s′ ⟧ ≡ ⟦ sr↠s′r ⟧
↠≄τ-append r (α ∧ α≄τ ∧ s↠s′) = (α ∧ α≄τ ∧ ↠-append r s↠s′) ∧ ≡.refl
\end{code}
%endif

%}}}%

% Decapitating silent transitions
%{{{%

%if False
\begin{code}
↠τ-lop : ∀ {x s x′∷s′} → x ∷ s ↠τ x′∷s′ →
  ∃ (λ x′ → x′∷s′ ≡ x′ ∷ s  × x ↠τ₁ x′) ⊎
  ∃ (λ s′ → x′∷s′ ≡ x  ∷ s′ × s ↠τ  s′)
↠τ-lop (.τ ∧ is-τ ∧ x∷s↠‹τ›x′∷s′) = inj₁ (↠‹τ›-head ≡.refl x∷s↠‹τ›x′∷s′) where
  ↠‹τ›-head : ∀ {x s x′∷s α} → α ≡ τ → x ∷ s ↠‹ α › x′∷s → ∃ λ x′ → x′∷s ≡ x′ ∷ s ×  x ↠τ₁ x′
  ↠‹τ›-head α′≡τ (↠-↦ e↦e′) with E⁺τ-inj α′≡τ where
    E⁺τ-inj : ∀ {α} → E⁺ <$> α ≡ τ → α ≡ τ
    E⁺τ-inj {τ} ≡.refl = ≡.refl
    E⁺τ-inj {⊞} ()
    E⁺τ-inj {⁺ child} ()
    E⁺τ-inj {∎ m} ()
    E⁺τ-inj {… α} ()
  ↠‹τ›-head α′≡τ (↠-↦ e↦e′) | ≡.refl = ⊥-elim (¬↦‹τ› e↦e′)
  ↠‹τ›-head α′≡τ (↠-↣ t↣t′) with M⁺τ-inj α′≡τ where
    M⁺τ-inj : ∀ {α} → M⁺ <$> α ≡ τ → α ≡ τ
    M⁺τ-inj {τ} ≡.refl = ≡.refl
    M⁺τ-inj {⊞} ()
    M⁺τ-inj {⁺ child} ()
    M⁺τ-inj {∎ m} ()
    M⁺τ-inj {… α} ()
  ↠‹τ›-head α′≡τ (↠-↣ t↣t′) | ≡.refl = _ ∧ ≡.refl ∧ λ _ → τ ∧ is-τ ∧ ↠-↣ t↣t′
  ↠‹τ›-head () (↠-preempt s↠s′)
  ↠‹τ›-head α≡τ ↠-switch = _ ∧ ≡.refl ∧ λ _ → τ ∧ is-τ ∧ ↠-switch
  ↠‹τ›-head () ↠-done
↠τ-lop (._ ∧ is-… {α} α≃τ ∧ x∷s↠‹τ›x′∷s′) = inj₂ (↠‹…›-tail ≡.refl x∷s↠‹τ›x′∷s′) where
  ↠‹…›-tail : ∀ {x s x∷s′ α′} → α′ ≡ … α → x ∷ s ↠‹ α′ › x∷s′ → ∃ λ s′ → x∷s′ ≡ x ∷ s′ × s ↠τ s′
  ↠‹…›-tail α′≡…α (↠-↦ e↦e′) with E⁺…-inj α′≡…α where
    E⁺…-inj : ∀ {α β} → E⁺ <$> α ≡ … β → ∃ λ α′ → α ≡ … α′
    E⁺…-inj {τ} ()
    E⁺…-inj {⊞} ()
    E⁺…-inj {⁺ child} ()
    E⁺…-inj {∎ m} ()
    E⁺…-inj {… α} ≡.refl = α ∧ ≡.refl
  ↠‹…›-tail α′≡…α (↠-↦ e↦e′) | α ∧ ≡.refl = ⊥-elim (¬↦‹…› e↦e′)
  ↠‹…›-tail α′≡…α (↠-↣ t↣t′) with M⁺…-inj α′≡…α where
    M⁺…-inj : ∀ {α β} → M⁺ <$> α ≡ … β → ∃ λ α′ → α ≡ … α′
    M⁺…-inj {τ} ()
    M⁺…-inj {⊞} ()
    M⁺…-inj {⁺ child} ()
    M⁺…-inj {∎ m} ()
    M⁺…-inj {… α} ≡.refl = α ∧ ≡.refl
  ↠‹…›-tail α′≡…α (↠-↣ ()) | α ∧ ≡.refl
  ↠‹…›-tail ≡.refl (↠-preempt s↠s′) = _ ∧ ≡.refl ∧ (α ∧ α≃τ ∧ s↠s′)
\end{code}
%endif

%if False
\begin{code}
↠τ⋆-lop : ∀ {x s x′∷s′} → x ∷ s ↠τ⋆ x′∷s′ →
  ∃ λ x′ → ∃ λ s′ → x′ ∷ s′ ≡ x′∷s′ × x ↠τ⋆₁ x′ × s ↠τ⋆ s′
↠τ⋆-lop ε = _ ∧ _ ∧ ≡.refl ∧ ε₁ ∧ ε
↠τ⋆-lop (x∷s↠τx₀∷s₀ ◅ x₀∷s₀↠τ⋆x′∷s′) with ↠τ-lop x∷s↠τx₀∷s₀
↠τ⋆-lop (x∷s↠τx₀∷s₀ ◅ x₀∷s₀↠τ⋆x′∷s′) | inj₁ (x₀ ∧ ≡.refl ∧ x↠τx₀)
  with ↠τ⋆-lop x₀∷s₀↠τ⋆x′∷s′
↠τ⋆-lop (x∷s↠τx₀∷s₀ ◅ x₀∷s₀↠τ⋆x′∷s′) | inj₁ (x₀ ∧ ≡.refl ∧ x↠τx₀)
  | x′ ∧ s′ ∧ ≡.refl ∧ x₀↠τ⋆x′ ∧ s↠τ⋆s′ = x′ ∧ s′ ∧ ≡.refl ∧ x↠τx₀ ◅₁ x₀↠τ⋆x′ ∧ s↠τ⋆s′
↠τ⋆-lop (x∷s↠τx₀∷s₀ ◅ x₀∷s₀↠τ⋆x′∷s′) | inj₂ (s₀ ∧ ≡.refl ∧ s↠τs₀)
  with ↠τ⋆-lop x₀∷s₀↠τ⋆x′∷s′
↠τ⋆-lop (x∷s↠τx₀∷s₀ ◅ x₀∷s₀↠τ⋆x′∷s′) | inj₂ (s₀ ∧ ≡.refl ∧ s↠τs₀)
  | x′ ∧ s′ ∧ ≡.refl ∧ x↠τ⋆x′ ∧ s₀↠τ⋆s′ = x′ ∧ s′ ∧ ≡.refl ∧ x↠τ⋆x′ ∧ s↠τs₀ ◅ s₀↠τ⋆s′
\end{code}
%endif

%}}}%

\subsection{Soups Concatenation Preserves Silent Transitions}%{{{%

Concatenation of thread soups preserve silent transition sequences,
%format ↠τ⋆-++ = "\func{{\twoheadrightarrow}\tau^\star\text-{+}\!\!{+}}"
%{
%format ⟶ = "\infix{\func{\longrightarrow}}"
\begin{code}
↠τ⋆-++ : _++_ Preserves₂ _↠τ⋆_ ⟶ _↠τ⋆_ ⟶ _↠τ⋆_
\end{code}
%}
or equivalently, given |r ↠τ⋆ r′| and |s ↠τ⋆ s′|, we can produce a silent
transition sequence |r ++ s ↠τ⋆ r′ ++ s′|:
\begin{spec}
↠τ⋆-++ : ∀ {r r′ s s′} → r ↠τ⋆ r′ → s ↠τ⋆ s′ → r ++ s ↠τ⋆ r′ ++ s′
\end{spec}
%if False
\begin{code}
↠τ⋆-++ {_} {r′} {s} {_} r↠τ⋆r′ s↠τ⋆s′
  = Star.gmap (λ r → r ++ s) (↠τ-append s) r↠τ⋆r′
  ◅◅ Star.gmap (λ s → r′ ++ s) (↠τ-prepend r′) s↠τ⋆s′
-- ↠τ⋆-++ {[]} ε s↠τ⋆s′ = s↠τ⋆s′
-- ↠τ⋆-++ {[]} ((α ∧ α≃τ ∧ ()) ◅ r₀↠τ⋆r′) s↠τ⋆s′
-- ↠τ⋆-++ {x ∷ r} {_} {s} xr↠τ⋆x′r′ s↠τ⋆s′ with ↠τ⋆-lop xr↠τ⋆x′r′
-- ↠τ⋆-++ {x ∷ r} .{_} {s} xr↠τ⋆x′r′ s↠τ⋆s′ | x′ ∧ r′ ∧ ≡.refl ∧ x↠τ⋆₁x′ ∧ r↠τ⋆r′
--   = x↠τ⋆₁x′ (r ++ s) ◅◅ Star.gmap (_∷_ x′) ↠τ-preempt (↠τ⋆-++ r↠τ⋆r′ s↠τ⋆s′)
\end{code}
%endif
We can proceed by structural induction on the first thread soup argument,
which is |x ∷ r| in the inductive case. Using the fact that forking cannot
be silent, we can decapitate the |x| from the thread soup to obtain a pair
of transitions |x ↠τ⋆₁ x′| and |r ↠τ⋆ r′|. The first of these can be
instantiated to one half of the goal, that is:
\begin{spec}
x ∷ r ++ s ↠τ⋆ x′ ∷ r ++ s
\end{spec}
The induction hypothesis on the other hand uses the second |r ↠τ⋆ r′| to
give the sequence |r ++ s ↠τ⋆ r′ ++ s′|, which we can map |↠-preempt| over
to arrive at the other half of the goal:
\begin{spec}
x′ ∷ r ++ s ↠τ⋆ x′ ∷ r′ ++ s′
\end{spec}
Concatenation of the two halves completes the proof.

%}}}%

\subsection{Partitioning Silent Transitions}%{{{%

%format ↠τ⋆-split = "\func{{\twoheadrightarrow}\tau^\star\text-split}"
%format r′s′ = "r\Prime\!s\Prime{}"
Conversely, the thread soups of a silent transition sequence |r ++ s ↠τ⋆
r′s′| can be partitioned into |r ↠τ⋆ r′| and |s ↠τ⋆ s′|:
\begin{code}
↠τ⋆-split : ∀ r s {r′s′} → r ++ s ↠τ⋆ r′s′ →
  ∃₂ λ r′ s′ → r′ ++ s′ ≡ r′s′ × r ↠τ⋆ r′ × s ↠τ⋆ s′
\end{code}
%if False
\begin{code}
↠τ⋆-split [] s s↠τ⋆s′ = [] ∧ _ ∧ ≡.refl ∧ ε ∧ s↠τ⋆s′
↠τ⋆-split (x ∷ r) s xrs↠τ⋆x′r′s′ with ↠τ⋆-lop xrs↠τ⋆x′r′s′
↠τ⋆-split (x ∷ r) s xrs↠τ⋆x′r′s′ | x′ ∧ r′s′ ∧ ≡.refl ∧ x↠τ⋆x′ ∧ rs↠τ⋆r′s′
  with ↠τ⋆-split r s rs↠τ⋆r′s′
↠τ⋆-split (x ∷ r) s xrs↠τ⋆x′r′s′ | x′ ∧ .(r′ ++ s′) ∧ ≡.refl ∧ x↠τ⋆₁x′ ∧ rs↠τ⋆r′s′
  | r′ ∧ s′ ∧ ≡.refl ∧ r↠τ⋆r′ ∧ s↠τ⋆s′ = x′ ∷ r′ ∧ s′ ∧ ≡.refl
    ∧ x↠τ⋆₁x′ r ◅◅ Star.gmap (_∷_ x′) ↠τ-preempt r↠τ⋆r′ ∧ s↠τ⋆s′
\end{code}
%endif
Again, the proof uses structural induction on the first thread soup
argument; decapitating |x| from the |x ∷ r| in the inductive case---as per
the proof for |↠τ⋆-++|---produces a pair of transitions |x ↠τ⋆₁ x′| and |r
↠τ⋆ r′|. The induction hypothesis delivers the |r ↠τ⋆ r′| needed to
construct the sequence |x ∷ r ↠τ⋆ x′ ∷ r ↠τ⋆ x′ ∷ r′|, which completes the
proof.

A useful corollary of |↠τ⋆-split| allows us to focus our attention on
a single thread, by dissecting its transitions out of a transition sequence
on the entire thread soup:
%format ↠τ⋆-dissect = "\func{{\twoheadrightarrow}\tau^\star\text-dissect}"
%format rˡ = "r^l"
%format rˡ′ = "{r^l}\Prime{}"
%format rʳ = "r^r"
%format rʳ′ = "{r^r}\Prime{}"
\begin{code}
↠τ⋆-dissect : ∀ rˡ rʳ {x r′} → rˡ ++ x ∷ rʳ ↠τ⋆ r′ →
  ∃₂ λ rˡ′ rʳ′ → ∃ λ x′ → r′ ≡ rˡ′ ++ x′ ∷ rʳ′ ×
    rˡ ↠τ⋆ rˡ′ × rʳ ↠τ⋆ rʳ′ × x ↠τ⋆₁ x′
\end{code}
In other words, given a silent transition sequence starting from the thread
soup |rˡ ++ x ∷ rʳ|, there exists |rˡ′|, |rʳ′| and |x′| satisfying |rˡ ↠τ⋆
rˡ′|, |rʳ ↠τ⋆ rʳ′| and |x ↠τ⋆₁ x′| respectively.
%if False
\begin{code}
↠τ⋆-dissect rˡ rʳ rˡxrʳ↠τ⋆r′ with ↠τ⋆-split rˡ _ rˡxrʳ↠τ⋆r′
↠τ⋆-dissect rˡ rʳ rˡxrʳ↠τ⋆r′ | rˡ′ ∧ x′rʳ′ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ′ ∧ xrʳ↠τ⋆x′rʳ′
  with ↠τ⋆-lop xrʳ↠τ⋆x′rʳ′
↠τ⋆-dissect rˡ rʳ rˡxrʳ↠τ⋆r′ | rˡ′ ∧ ._ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ′ ∧ xrʳ↠τ⋆x′rʳ′
  | x′ ∧ rʳ′ ∧ ≡.refl ∧ x↠τ⋆₁x′ ∧ rʳ↠τ⋆rʳ′ = rˡ′ ∧ rʳ′ ∧ x′ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ′ ∧ rʳ↠τ⋆rʳ′ ∧ x↠τ⋆₁x′
\end{code}
%endif

%}}}%

% Decapitating non-silent transitions
%{{{%

%if False
\begin{code}
↠≄τ-lop : ∀ {x s x′∷s′} → (xs↠x′s′ : x ∷ s ↠≄τ x′∷s′) →
  ∃ (λ x′⁺ → x′⁺ ++ s ≡ x′∷s′ × Σ (x ↠≄τ₁ x′⁺) λ x↠₁x′⁺ → ∀ r → ⟦ x↠₁x′⁺ r ⟧ ≡ ⟦ xs↠x′s′ ⟧) ⊎
  ∃ (λ s′ → x ∷ s′ ≡ x′∷s′ × Σ (s ↠≄τ s′) λ s↠s′ → ⟦ s↠s′ ⟧ ≡ ⟦ xs↠x′s′ ⟧)
↠≄τ-lop (._ ∧ α≄τ ∧ ↠-↦ {e} {e′} {t} {s} {α} e↦e′) = inj₁
  ( ⟨ _ ‚ _ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
  ∧ ≡.cong (_∷_ ⟨ _ ‚ _ ⟩) (≡.sym α⁺∷r≡α⁺∷[]++r)
  ∧ (λ r → _ ∧ α≄τ ∧ x∷r↠x′∷α⁺∷[]++r r)
  ∧ λ r → ≡.refl ) where

  α⁺∷r≡α⁺∷[]++r : ∀ {r} → (E⁺ <$> α) ⁺∷ r ≡ ((E⁺ <$> α) ⁺∷ []) ++ r
  α⁺∷r≡α⁺∷[]++r with α
  α⁺∷r≡α⁺∷[]++r | τ = ≡.refl
  α⁺∷r≡α⁺∷[]++r | ⊞ = ≡.refl
  α⁺∷r≡α⁺∷[]++r | ⁺ child = ≡.refl
  α⁺∷r≡α⁺∷[]++r | ∎ m = ≡.refl
  α⁺∷r≡α⁺∷[]++r | … α' = ≡.refl

  x∷r↠x′∷α⁺∷[]++r : ∀ r → _ ∷ r ↠‹ E⁺ <$> α › _ ∷ ((E⁺ <$> α) ⁺∷ []) ++ r
  x∷r↠x′∷α⁺∷[]++r r = ≡.subst
    (λ α⁺∷r → ⟨ e ‚ t ⟩ ∷ r ↠‹ E⁺ <$> α › ⟨ e′ ‚ t ⟩ ∷ α⁺∷r)
    α⁺∷r≡α⁺∷[]++r (↠-↦ e↦e′)

↠≄τ-lop (._ ∧ α≄τ ∧ ↠-↣ {t} {t′} {s} {α} t↣t′) = inj₁
  ( ⟨ _ ⟩ ∷ (M⁺ <$> α) ⁺∷ []
  ∧ ≡.cong (_∷_ ⟨ _ ⟩) (≡.sym α⁺∷r≡α⁺∷[]++r)
  ∧ (λ r → _ ∧ α≄τ ∧ x∷r↠x′∷α⁺∷[]++r r)
  ∧ λ r → ≡.refl ) where
  α⁺∷r≡α⁺∷[]++r : ∀ {r} → (M⁺ <$> α) ⁺∷ r ≡ ((M⁺ <$> α) ⁺∷ []) ++ r
  α⁺∷r≡α⁺∷[]++r with α
  α⁺∷r≡α⁺∷[]++r | τ = ≡.refl
  α⁺∷r≡α⁺∷[]++r | ⊞ = ≡.refl
  α⁺∷r≡α⁺∷[]++r | ⁺ child = ≡.refl
  α⁺∷r≡α⁺∷[]++r | ∎ m = ≡.refl
  α⁺∷r≡α⁺∷[]++r | … α' = ≡.refl

  x∷r↠x′∷α⁺∷[]++r : ∀ r → _ ∷ r ↠‹ M⁺ <$> α › _ ∷ ((M⁺ <$> α) ⁺∷ []) ++ r
  x∷r↠x′∷α⁺∷[]++r r = ≡.subst
    (λ α⁺∷r → ⟨ t ⟩ ∷ r ↠‹ M⁺ <$> α › ⟨ t′ ⟩ ∷ α⁺∷r)
    α⁺∷r≡α⁺∷[]++r (↠-↣ t↣t′)

↠≄τ-lop (._ ∧ α≄τ ∧ ↠-preempt s↠s′) = inj₂ (_ ∧ ≡.refl ∧ (_ ∧ α≄τ ∘ is-… ∧ s↠s′) ∧ ≡.refl)
↠≄τ-lop (.τ ∧ α≄τ ∧ ↠-switch) = ⊥-elim (α≄τ is-τ)
↠≄τ-lop (._ ∧ α≄τ ∧ ↠-done) = inj₁ (⟨⟩ ∷ [] ∧ ≡.refl ∧ (λ r → _ ∧ α≄τ ∧ ↠-done) ∧ λ r → ≡.refl)
\end{code}
%endif

%}}}%

\subsection{Partitioning a Non-Silent Transition}%{{{%

We can also partition the thread soup for a non-silent transition, although
the situation is a little more involved:
%format ↠≄τ-split = "\func{{\twoheadrightarrow}{\not\simeq}\tau\text-split}"
%format rs↠r′s′ = "rs{\twoheadrightarrow}r\Prime\!s\Prime{}"
%format r↠r′ = "r{\twoheadrightarrow}r\Prime{}"
\begin{code}
↠≄τ-split : ∀ r s {r′s′} → (rs↠r′s′ : r ++ s ↠≄τ r′s′) →
  (∃ λ r′ → r′ ++ s ≡ r′s′ × Σ (r ↠≄τ r′)
    λ r↠r′ → ⟦ r↠r′ ⟧ ≡ ⟦ rs↠r′s′ ⟧) ⊎
  (∃ λ s′ → r ++ s′ ≡ r′s′ × Σ (s ↠≄τ s′)
    λ s↠s′ → ⟦ s↠s′ ⟧ ≡ ⟦ rs↠r′s′ ⟧)
\end{code}
Partitioning the thread soup in a non-silent transition has two possible
outcomes, as the active thread responsible for the transition could be in
either one of |r| or |s|. The proof proceeds by structural induction on the
soup |r| as before, by inspecting each of its threads. If found, we
construct and return the transition |r ↠≄τ r′|; otherwise none of the |r|
threads are responsible for the non-silent transition, so by elimination it
must be in |s|, and we can respond with the transition |s ↠≄τ s′|. In both
cases, we construct a proof that the action emitted by the original
|rs↠r′s′| transition is the same as either |⟦ r↠r′ ⟧| or |⟦ s↠s′ ⟧|, as
appropriate.
%if False
\begin{code}
↠≄τ-split [] s s↠s′ = inj₂ (_ ∧ ≡.refl ∧ s↠s′ ∧ ≡.refl)
↠≄τ-split (x ∷ r) s xrs↠x′r′s′ with ↠≄τ-lop xrs↠x′r′s′
↠≄τ-split (x ∷ r) s xrs↠x′r′s′ | inj₁ (x′⁺ ∧ ≡.refl ∧ x↠≄τ₁x′⁺ ∧ ⟦x↠≄τ₁x′⁺⟧≡⟦xrs↠x′r′s′⟧)
  = inj₁ (x′⁺ ++ r ∧ ++.assoc x′⁺ r s ∧ x↠≄τ₁x′⁺ r ∧ ⟦x↠≄τ₁x′⁺⟧≡⟦xrs↠x′r′s′⟧ r) where
      module ++ {A : Set} = Monoid (List.monoid A)
↠≄τ-split (x ∷ r) s xrs↠x′r′s′ | inj₂ (r′s′ ∧ ≡.refl ∧ rs↠r′s′ ∧ ⟦rs↠r′s′⟧≡⟦xrs↠x′r′s′⟧)
  with ↠≄τ-split r s rs↠r′s′
↠≄τ-split (x ∷ r) s xrs↠x′r′s′ | inj₂ (.(r′ ++ s) ∧ ≡.refl ∧ rs↠r′s′ ∧ ⟦rs↠r′s′⟧≡⟦xrs↠x′r′s′⟧)
  | inj₁ (r′ ∧ ≡.refl ∧ r↠r′ ∧ ⟦r↠r′⟧≡⟦rs↠r′s′⟧) with ↠≄τ-preempt {x} r↠r′
↠≄τ-split (x ∷ r) s xrs↠x′r′s′ | inj₂ (.(r′ ++ s) ∧ ≡.refl ∧ rs↠r′s′ ∧ ⟦rs↠r′s′⟧≡⟦xrs↠x′r′s′⟧)
  | inj₁ (r′ ∧ ≡.refl ∧ r↠r′ ∧ ⟦r↠r′⟧≡⟦rs↠r′s′⟧) | xr↠xr′ ∧ ⟦r↠r′⟧≡⟦xr↠xr′⟧
  = inj₁ (x ∷ r′ ∧ ≡.refl ∧ xr↠xr′ ∧ ≡.trans (≡.trans (≡.sym ⟦r↠r′⟧≡⟦xr↠xr′⟧) ⟦r↠r′⟧≡⟦rs↠r′s′⟧) ⟦rs↠r′s′⟧≡⟦xrs↠x′r′s′⟧)
↠≄τ-split (x ∷ r) s xrs↠x′r′s′ | inj₂ (.(r ++ s′) ∧ ≡.refl ∧ rs↠r′s′ ∧ ⟦rs↠r′s′⟧≡⟦xrs↠x′r′s′⟧)
  | inj₂ (s′ ∧ ≡.refl ∧ s↠s′ ∧ ⟦s↠s′⟧≡⟦rs↠r′s′⟧) = inj₂ (s′ ∧ ≡.refl ∧ s↠s′ ∧ ≡.trans ⟦s↠s′⟧≡⟦rs↠r′s′⟧ ⟦rs↠r′s′⟧≡⟦xrs↠x′r′s′⟧)
\end{code}
%endif

%format ↠≄τ-dissect = "\func{{\twoheadrightarrow}{\not\simeq}\tau\text-dissect}"
%format rˡ′ = "r^l{}\Prime{}"
%format rʳ′ = "r^r{}\Prime{}"
%format rˡxrʳ↠r′ = "\mathit{r^l\!xr^r}{\twoheadrightarrow}r\Prime{}"
%format rˡ↠rˡ′ = "r^l{\twoheadrightarrow}r^l{}\Prime{}"
%format rʳ↠rʳ′ = "r^r{\twoheadrightarrow}r^r{}\Prime{}"
In the same way that |↠τ⋆-split| has its |↠τ⋆-dissect| corollary, we can
show the following |↠≄τ-dissect| corollary for |↠≄τ-split|:
\begin{code}
↠≄τ-dissect : ∀ rˡ rʳ {x x′ r′} →
  x ↠τ₁ x′ → (rˡxrʳ↠r′ : rˡ ++ x ∷ rʳ ↠≄τ r′) →
  (∃ λ rˡ′ → r′ ≡ rˡ′ ++ x ∷ rʳ × Σ (rˡ ↠≄τ rˡ′)
    λ rˡ↠rˡ′ → ⟦ rˡ↠rˡ′ ⟧ ≡ ⟦ rˡxrʳ↠r′ ⟧) ⊎
  (∃ λ rʳ′ → r′ ≡ rˡ ++ x ∷ rʳ′ × Σ (rʳ ↠≄τ rʳ′)
    λ rʳ↠rʳ′ → ⟦ rʳ↠rʳ′ ⟧ ≡ ⟦ rˡxrʳ↠r′ ⟧)
\end{code}
Here we are given an additional hypothesis that the thread |x| makes
a silent initial transition, which is unique by our choice of actions.
Therefore the thread responsible for the non-silent transition |rˡxrʳ↠r′|
must reside in either one of |rˡ| or |rʳ|, giving rise to the two
alternatives of either |rˡ ↠≄τ rˡ′| or |rʳ ↠≄τ rʳ′|.
%if False
\begin{code}
↠≄τ-dissect rˡ rʳ x↠τ₁x′ rˡxrʳ↠r′
  with ↠≄τ-split rˡ _ rˡxrʳ↠r′
↠≄τ-dissect rˡ rʳ x↠τ₁x′ rˡxrʳ↠r′
  | inj₁ (rˡ′ ∧ ≡.refl ∧ rˡ↠rˡ′ ∧ ⟦rˡ↠rˡ′⟧≡⟦rˡxrʳ↠r′⟧)
    = inj₁ (rˡ′ ∧ ≡.refl ∧ rˡ↠rˡ′ ∧ ⟦rˡ↠rˡ′⟧≡⟦rˡxrʳ↠r′⟧)
↠≄τ-dissect rˡ rʳ x↠τ₁x′ rˡxrʳ↠r′
  | inj₂ (xrʳ′ ∧ ≡.refl ∧ xrʳ↠xrʳ′ ∧ ⟦xrʳ↠xrʳ′⟧≡⟦rˡxrʳ↠r′⟧)
    with ↠≄τ-lop xrʳ↠xrʳ′
↠≄τ-dissect rˡ rʳ x↠τ₁x′ rˡxrʳ↠r′
  | inj₂ (._ ∧ ≡.refl ∧ xrʳ↠xrʳ′ ∧ ⟦xrʳ↠xrʳ′⟧≡⟦rˡxrʳ↠r′⟧)
    | inj₂ (rʳ′ ∧ ≡.refl ∧ rʳ↠rʳ′ ∧ ⟦rʳ↠rʳ′⟧≡⟦xrʳ↠xrʳ′⟧)
      = inj₂ (rʳ′ ∧ ≡.refl ∧ rʳ↠rʳ′ ∧ ≡.trans ⟦rʳ↠rʳ′⟧≡⟦xrʳ↠xrʳ′⟧ ⟦xrʳ↠xrʳ′⟧≡⟦rˡxrʳ↠r′⟧)
↠≄τ-dissect rˡ rʳ x↠τ₁x′ rˡxrʳ↠r′
  | inj₂ (._ ∧ ≡.refl ∧ xrʳ↠xrʳ′ ∧ ⟦xrʳ↠xrʳ′⟧≡⟦rˡxrʳ↠r′⟧)
    | inj₁ (x′⁺ ∧ ≡.refl ∧ x↠≄τ₁x′⁺ ∧ ⟦x↠≄τ₁x′⁺⟧≡⟦xrʳ↠xrʳ′⟧)
      = ⊥-elim (!x↠x′ (x↠τ₁x′ []) (x↠≄τ₁x′⁺ [])) where

  !x↠x′ : ∀ {x x′ x″} → x ∷ [] ↠τ x′ → x ∷ [] ↠≄τ x″ → ⊥
  !x↠x′ (._ ∧ α≃τ ∧ ↠-↦ e↦e′) x↠≄τx″ = ¬↦τ (E⁺≃τ-inj α≃τ) e↦e′
  !x↠x′ (.τ ∧ α≃τ ∧ ↠-↣ ↣-PUSH) (.τ ∧ β≄τ ∧ ↠-↣ ↣-PUSH) = β≄τ α≃τ
  !x↠x′ (.τ ∧ α≃τ ∧ ↠-↣ ↣-PUSH) (._ ∧ β≄τ ∧ ↠-preempt ())
  !x↠x′ (.⊞ ∧ () ∧ ↠-↣ ↣-ADD) x↠≄τx″
  !x↠x′ (._ ∧ () ∧ ↠-↣ ↣-FORK) x↠≄τx″
  !x↠x′ (._ ∧ α≃τ ∧ ↠-preempt ()) x↠≄τx″
  !x↠x′ (.τ ∧ α≃τ ∧ ↠-switch) (._ ∧ β≄τ ∧ ↠-↦ ())
  !x↠x′ (.τ ∧ α≃τ ∧ ↠-switch) (._ ∧ β≄τ ∧ ↠-preempt ())
  !x↠x′ (.τ ∧ α≃τ ∧ ↠-switch) (.τ ∧ β≄τ ∧ ↠-switch) = β≄τ α≃τ
  !x↠x′ (._ ∧ () ∧ ↠-done) x↠≄τx″
\end{code}
%endif

%}}}%

% uniqueness of  x ↠τ₁ x′
%{{{%

%if False
\begin{code}
↠τ⋆₁-unique : ∀ {x x′ x₀} →
  x ↠τ₁ x′ → x ↠τ⋆₁ x₀ →
  x′ ∷ [] ↠τ⋆ x₀ ∷ [] ⊎ x ≡ x₀
↠τ⋆₁-unique x↠τ₁x′ x↠τ⋆₁x₀ with x↠τ₁x′ [] | x↠τ⋆₁x₀ []
↠τ⋆₁-unique x↠τ₁x′ x↠τ⋆₁x₀ | x↠τx′ | ε = inj₂ ≡.refl
↠τ⋆₁-unique x↠τ₁x′ x↠τ⋆₁x₀ | x↠τx′ | x↠τx″ ◅ x′↠τ⋆x₀ with !x↠τx′ x↠τx′ x↠τx″ where
  !x↠τx′ : ∀ {x x′ x″} → x ∷ [] ↠τ x′ → x ∷ [] ↠τ x″ → x′ ≡ x″
  !x↠τx′ (._ ∧ α≃τ ∧ ↠-↦ e↦e′) x↠τx″ = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) e↦e′)
  !x↠τx′ (.τ ∧ α≃τ ∧ ↠-↣ ↣-PUSH) (.τ ∧ β≃τ ∧ ↠-↣ ↣-PUSH) = ≡.refl
  !x↠τx′ (.τ ∧ α≃τ ∧ ↠-↣ ↣-PUSH) (._ ∧ β≃τ ∧ ↠-preempt ())
  !x↠τx′ (.⊞ ∧ () ∧ ↠-↣ ↣-ADD) x↠τx″
  !x↠τx′ (._ ∧ () ∧ ↠-↣ ↣-FORK) x↠τx″
  !x↠τx′ (._ ∧ α≃τ ∧ ↠-preempt ()) x↠τx″
  !x↠τx′ (.τ ∧ α≃τ ∧ ↠-switch) (._ ∧ β≃τ ∧ ↠-↦ ())
  !x↠τx′ (.τ ∧ α≃τ ∧ ↠-switch) (._ ∧ β≃τ ∧ ↠-preempt ())
  !x↠τx′ (.τ ∧ α≃τ ∧ ↠-switch) (.τ ∧ β≃τ ∧ ↠-switch) = ≡.refl
  !x↠τx′ (._ ∧ () ∧ ↠-done) x↠τx″
↠τ⋆₁-unique x↠τ₁x′ x↠τ⋆₁x₀ | x↠τx′ | x↠τx″ ◅ x′↠τ⋆x₀ | ≡.refl = inj₁ x′↠τ⋆x₀
\end{code}
%endif

%}}}%

\subsection{Dissecting a Visible Transition}\label{sec:fork-dissect}%{{{%

Recall that a visible transition comprises of two sequences of silent
transitions either side of a single non-silent transition. Therefore
combining the previous results allows us to dissect a visible transition in
much the same way:
%format ⤇-dissect = "\func{{\Mapsto}\text-dissect}"
\begin{code}
⤇-dissect : ∀ rˡ rʳ {x x′ r′ α} →
  x ↠τ₁ x′ → rˡ ++ x ∷ rʳ ⤇‹ α › r′ →
  rˡ ++ x′ ∷ rʳ ⤇‹ α › r′ ⊎
  ∃₂ λ rˡ′ rʳ′ → r′ ≡ rˡ′ ++ x ∷ rʳ′ ×
    ((rˡ ⤇‹ α › rˡ′ × rʳ ↠τ⋆ rʳ′) ⊎ (rˡ ↠τ⋆ rˡ′ × rʳ ⤇‹ α › rʳ′))
\end{code}
Given a witness of |x ↠τ₁ x′| and the visible transition |rˡ ++ x ∷ rʳ ⤇‹
α › r′|, there are two possibilities regarding the thread |x|: either |x ↠τ₁
x′| takes place somewhere within the visible transition, so that removing it
results in a witness of |rˡ ++ x′ ∷ rʳ ⤇‹ α › r′|; or that |x| remains
inactive throughout while |rˡ| and |rʳ| make transitions to some |rˡ′| and
|rʳ′| respectively. Depending on which of |rˡ| or |rʳ| the thread
responsible for the non-silent action is found in, we provide witnesses of
either |rˡ ⤇‹ α › rˡ′| and |rʳ ↠τ⋆ rʳ′|, or |rˡ ↠τ⋆ rˡ′| and |rʳ ⤇‹ α › rʳ′|
respectively.

%if False
\begin{code}
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  with ↠τ⋆-dissect rˡ rʳ r↠τ⋆r₀
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  with ↠τ⋆₁-unique x↠τ₁x′ x↠τ⋆₁x₀

-- the easy case -- |x↠τ₁x′| happens before the non-silent transition, so chuck it out and we're done!
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₁ x′↠τ⋆x₀ = inj₁ (⤇-↠ (↠τ⋆-++ rˡ↠τ⋆rˡ₀ (↠τ⋆-++ x′↠τ⋆x₀ rʳ↠τ⋆rʳ₀)) r₀↠≄τr₁ r₁↠τ⋆r′)

-- x doesn't do anything before the main event… so we'll have to dissect that. :-/
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
  with ↠≄τ-dissect rˡ₀ rʳ₀ x↠τ₁x′ r₀↠≄τr₁

-- The two resulting cases are symmetrical. Factor, somehow?

-- dissecting r₀↠≄τr₁: the non-silent thread is to the left of x
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    with ↠τ⋆-dissect rˡ₁ rʳ₀ r₁↠τ⋆r′
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ x″ ∧ ≡.refl ∧ rˡ₁↠τ⋆rˡ′ ∧ rʳ₀↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      with ↠τ⋆₁-unique x↠τ₁x′ x↠τ⋆₁x″

-- uniqueness again: x does something
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ x″ ∧ ≡.refl ∧ rˡ₁↠τ⋆rˡ′ ∧ rʳ₀↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      | inj₁ x′↠τ⋆x″
      with ↠≄τ-append (x″ ∷ rʳ₀) rˡ₀↠≄τrˡ₁
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ x″ ∧ ≡.refl ∧ rˡ₁↠τ⋆rˡ′ ∧ rʳ₀↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
    | inj₁ x′↠τ⋆x″
      | rˡ₀x″rʳ₀↠≄τrˡ₁x″rʳ₀ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦rˡ₀x″rʳ₀↠rˡ₁x″rʳ₀⟧
        rewrite ≡.sym ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧ | ⟦rˡ₀↠rˡ₁⟧≡⟦rˡ₀x″rʳ₀↠rˡ₁x″rʳ₀⟧
      = inj₁ ( ⤇-↠
        (↠τ⋆-++ rˡ↠τ⋆rˡ₀ (↠τ⋆-++ x′↠τ⋆x″ rʳ↠τ⋆rʳ₀))
        rˡ₀x″rʳ₀↠≄τrˡ₁x″rʳ₀
        (↠τ⋆-++ rˡ₁↠τ⋆rˡ′ (↠τ⋆-++ {x″ ∷ []} ε rʳ₀↠τ⋆rʳ′)) )

-- uniqueness again: x does nothing
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ .x ∧ ≡.refl ∧ rˡ₁↠τ⋆rˡ′ ∧ rʳ₀↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      | inj₂ ≡.refl rewrite ≡.sym ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧
      = inj₂ ( rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ inj₁
        (⤇-↠ rˡ↠τ⋆rˡ₀ rˡ₀↠≄τrˡ₁ rˡ₁↠τ⋆rˡ′ ∧ rʳ↠τ⋆rʳ₀ ◅◅ rʳ₀↠τ⋆rʳ′) )

-- dissecting r₀↠≄τr₁: the non-silent thread is to the right of x
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    with ↠τ⋆-dissect rˡ₀ rʳ₁ r₁↠τ⋆r′
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ x″ ∧ ≡.refl ∧ rˡ₀↠τ⋆rˡ′ ∧ rʳ₁↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      with ↠τ⋆₁-unique x↠τ₁x′ x↠τ⋆₁x″

-- uniqueness again: x does something
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ x″ ∧ ≡.refl ∧ rˡ₀↠τ⋆rˡ′ ∧ rʳ₁↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      | inj₁ x′↠τ⋆x″
      with ↠≄τ-preempt {x″} rʳ₀↠≄τrʳ₁
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ x″ ∧ ≡.refl ∧ rˡ₀↠τ⋆rˡ′ ∧ rʳ₁↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      | inj₁ x′↠τ⋆x″
      | x″rʳ₀↠≄τx″rʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦x″rʳ₀↠x″rʳ₁⟧
      with ↠≄τ-prepend rˡ₀ x″rʳ₀↠≄τx″rʳ₁
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ x″ ∧ ≡.refl ∧ rˡ₀↠τ⋆rˡ′ ∧ rʳ₁↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      | inj₁ x′↠τ⋆x″
      | x″rʳ₀↠≄τx″rʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦x″rʳ₀↠x″rʳ₁⟧
      | rˡ₀x″rʳ₀↠≄τrˡ₀x″rʳ₁ ∧ ⟦x″rʳ₀↠x″rʳ₁⟧≡⟦rˡ₀x″rʳ₀↠rˡ₀x″rʳ₁⟧
        rewrite ≡.sym ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧ | ⟦rʳ₀↠rʳ₁⟧≡⟦x″rʳ₀↠x″rʳ₁⟧
          | ⟦x″rʳ₀↠x″rʳ₁⟧≡⟦rˡ₀x″rʳ₀↠rˡ₀x″rʳ₁⟧
      = inj₁ ( ⤇-↠
        (↠τ⋆-++ rˡ↠τ⋆rˡ₀ (↠τ⋆-++ x′↠τ⋆x″ rʳ↠τ⋆rʳ₀))
        rˡ₀x″rʳ₀↠≄τrˡ₀x″rʳ₁
        (↠τ⋆-++ rˡ₀↠τ⋆rˡ′ (↠τ⋆-++ {x″ ∷ []} ε rʳ₁↠τ⋆rʳ′)) )

-- uniqueness again: x does nothing
⤇-dissect rˡ rʳ x↠τ₁x′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ x ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀ ∧ x↠τ⋆₁x₀
  | inj₂ ≡.refl
    | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ .x ∧ ≡.refl ∧ rˡ₀↠τ⋆rˡ′ ∧ rʳ₁↠τ⋆rʳ′ ∧ x↠τ⋆₁x″
      | inj₂ ≡.refl rewrite ≡.sym ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧
      = inj₂ ( rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ inj₂
        (rˡ↠τ⋆rˡ₀ ◅◅ rˡ₀↠τ⋆rˡ′ ∧ ⤇-↠ rʳ↠τ⋆rʳ₀ rʳ₀↠≄τrʳ₁ rʳ₁↠τ⋆rʳ′) )
\end{code}
%endif
The proof---totalling approximately 60 wrapped lines of code---follows
a straightforward method, namely using |↠τ⋆-dissect| and |↠≄τ-dissect| to
tease apart the thread soup, then putting the pieces back together in the
right way, depending on what we find inside.

%}}}%

\subsection{Extracting the Active Thread}\label{sec:fork-extract}

A number of the previous results were concerned with transitions from thread
soups of the form |rˡ ++ x ∷ rʳ|, where |x| makes an initial silent
transition. This final lemma shows that every silent transition |r ↠τ r′| is
in fact of this form. In other words, we can extract from |r ↠τ r′| the
active thread |x| and a witness of its transition |x ↠τ₁ x′|, along with
evidence that other threads in |r| remain unchanged:
%format ↠τ-extract = "\func{{\twoheadrightarrow}\tau\text-extract}"
\begin{code}
↠τ-extract : ∀ {r r′} → r ↠τ r′ → ∃₂ λ rˡ rʳ → ∃₂ λ x x′ →
  r ≡ rˡ ++ x ∷ rʳ × r′ ≡ rˡ ++ x′ ∷ rʳ × x ↠τ₁ x′
\end{code}
%if False
\begin{code}
↠τ-extract (._ ∧ α≃τ ∧ ↠-↦ e↦e′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) e↦e′)
↠τ-extract (.⊞ ∧ () ∧ ↠-↣ ↣-ADD)
↠τ-extract (._ ∧ () ∧ ↠-↣ ↣-FORK)
↠τ-extract (.τ ∧ α≃τ ∧ ↠-↣ ↣-PUSH) = [] ∧ _ ∧ _ ∧ _ ∧ ≡.refl ∧ ≡.refl ∧ λ s → τ ∧ α≃τ ∧ ↠-↣ ↣-PUSH
↠τ-extract (.τ ∧ α≃τ ∧ ↠-switch) = [] ∧ _ ∧ _ ∧ _ ∧ ≡.refl ∧ ≡.refl ∧ λ s → τ ∧ α≃τ ∧ ↠-switch
↠τ-extract (._ ∧ () ∧ ↠-done)
↠τ-extract (._ ∧ is-… α≃τ ∧ ↠-preempt {α = α} s↠s′) with ↠τ-extract (α ∧ α≃τ ∧ s↠s′)
↠τ-extract (._ ∧ is-… α≃τ ∧ ↠-preempt {α = α} s↠s′) | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
  = _ ∷ rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
\end{code}
%endif
The proof proceeds simply by induction on the structure of |r ↠τ r′|.

%format ⤇-append = "\func{{\Mapsto}\text-append}"
%if False
\begin{code}
⤇-append : ∀ sʳ {sˡ sˡ′ α} → sˡ ⤇‹ α › sˡ′ → sˡ ++ sʳ ⤇‹ α › sˡ′ ++ sʳ
⤇-append sʳ {sˡ} {sˡ′} (⤇-↠ sˡ↠τ⋆sˡ₀ sˡ₀↠≄τsˡ₁ sˡ₁↠τ⋆sˡ′) with ↠≄τ-append sʳ sˡ₀↠≄τsˡ₁
⤇-append sʳ {sˡ} {sˡ′} (⤇-↠ sˡ↠τ⋆sˡ₀ sˡ₀↠≄τsˡ₁ sˡ₁↠τ⋆sˡ′) | sˡ₀sʳ↠≄τsˡ₁sʳ ∧ ⟦sˡ₀↠≄τsˡ₁⟧≡⟦sˡ₀sʳ↠≄τsˡ₁sʳ⟧
  = ≡.subst (λ α → sˡ ++ sʳ ⤇‹ α › sˡ′ ++ sʳ) (≡.sym ⟦sˡ₀↠≄τsˡ₁⟧≡⟦sˡ₀sʳ↠≄τsˡ₁sʳ⟧)
    (⤇-↠ (↠τ⋆-++ sˡ↠τ⋆sˡ₀ ε) sˡ₀sʳ↠≄τsˡ₁sʳ (↠τ⋆-++ sˡ₁↠τ⋆sˡ′ ε))
\end{code}
%endif

%format ⤇-prepend = "\func{{\Mapsto}\text-prepend}"
%if False
\begin{code}
⤇-prepend : ∀ sˡ {sʳ sʳ′ α} → sʳ ⤇‹ α › sʳ′ → sˡ ++ sʳ ⤇‹ α › sˡ ++ sʳ′
⤇-prepend sˡ {sʳ} {sʳ′} (⤇-↠ sʳ↠τ⋆sʳ₀ sʳ₀↠≄τsʳ₁ sʳ₁↠τ⋆sʳ′) with ↠≄τ-prepend sˡ sʳ₀↠≄τsʳ₁
⤇-prepend sˡ {sʳ} {sʳ′} (⤇-↠ sʳ↠τ⋆sʳ₀ sʳ₀↠≄τsʳ₁ sʳ₁↠τ⋆sʳ′) | sˡsʳ₀↠≄τsˡsʳ₁ ∧ ⟦sʳ₀↠≄τsʳ₁⟧≡⟦sˡsʳ₀↠≄τsˡsʳ₁⟧
  = ≡.subst (λ α → sˡ ++ sʳ ⤇‹ α › sˡ ++ sʳ′) (≡.sym ⟦sʳ₀↠≄τsʳ₁⟧≡⟦sˡsʳ₀↠≄τsˡsʳ₁⟧)
    (⤇-↠ (↠τ⋆-++ {sˡ} ε sʳ↠τ⋆sʳ₀) sˡsʳ₀↠≄τsˡsʳ₁ (↠τ⋆-++ {sˡ} ε sʳ₁↠τ⋆sʳ′))
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:

