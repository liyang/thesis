%if include /= True
\begin{comment}
%let include = True
%include Fork/Action.lagda
%include Fork/Language.lagda
%include Fork/Combined.lagda
%include Fork/Bisimilarity.lagda
%include Fork/Soup.lagda
%include Fork/ElideTau.lagda
%include Fork/Concat.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import Fork.Action as Action
open import Fork.Language as Language
open import Fork.Combined as Combined
open import Fork.Bisimilarity as Bisimilarity
open import Fork.Soup as Soup
open import Fork.ElideTau as ElideTau
open import Fork.Concat as Concat

module fork where

open RawFunctor Action.rawFunctor
open ≈-Reasoning
\end{code}
%endif

% is bisimilarity substitutive? Don't be silly, of course it isn't.
%     r ≈ s → P r → P s
% but up to visible actions, it is… how do I state this?

\chapter{Compiling Concurrency Correctly}\label{ch:fork}

In the previous chapter, we introduced our methodology of using the notion
of bisimilarity on combined machines for tacking compiler correctness for
a simple non-deterministic language. In this chapter, we shall demonstrate
that this technique is scalable to a concurrent setting, by extending the
language with a simple |fork| primitive that introduces explicit concurrency
into our system.

\input{Fork/Language.lagda}

\input{Fork/Combined.lagda}

\input{Fork/Bisimilarity.lagda}

\input{Fork/Soup.lagda}

\input{Fork/ElideTau.lagda}

\input{Fork/Concat.lagda}

\section{Compiler Correctness}\label{sec:fork-correct}

%format correctness = "\func{correctness}"
%format fork≼FORK = "\func{fork{\preccurlyeq}FORK}"
%format FORK≼fork = "\func{FORK{\preccurlyeq}fork}"
The compiler correctness property for our Fork language is essentially the
same as that of the Zap language, but on singleton thread soups rather than
combined machines:
\begin{code}
correctness : ∀ e c σ → ⟨ e ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ ⟨ compile e c ‚ σ ⟩ ⟩ ∷ []
\end{code}
There is no need to generalise over an arbitrary thread soup, since the
|≈-cong₂| lemma of \S\ref{sec:fork-concat} allows us to concatenate as many
pairs of bisimilar thread soups as is required.

The proof comprises of two parts, each showing one direction of the
bisimulation. Proceeding by case analysis on the visible transition, the
|fork≼FORK| part first shows that |fork e| cannot make a non-silent
transition:
% format s₀↠τ⋆s₁ = "s_0{\twoheadrightarrow}\tau^\star{}s_1"
% format s₁↠≄τs₂ = "s_1{\twoheadrightarrow}{\not\simeq}\tau{}s_2"
% format s₂↠τ⋆s′ = "s_2{\twoheadrightarrow}\tau^\star{}s\Prime{}"
%format s₀↠τ⋆s₁ = "\anonymous{}"
%format s₁↠≄τs₂ = "\anonymous{}"
%format s₂↠τ⋆s′ = "\anonymous{}"
%format s₀↠τ⋆s′ = "s_0{\twoheadrightarrow}\tau^\star{}s\Prime{}"
\savecolumns
\begin{code}
correctness (fork e) c σ = ♯ fork≼FORK & ♯ FORK≼fork where
  fork≼FORK : ⟨ fork e ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ ⟨ FORK (compile e []) ∷ c ‚ σ ⟩ ⟩ ∷ []
  fork≼FORK s′ (⤇-↠ ((._ ∧ () ∧ ↠-↦ ↦-fork) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
  fork≼FORK s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
  fork≼FORK s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
\end{code}
The two |↠-preempt| clauses correspond to the fact that the empty soup |[]|
cannot make any transitions at all. In the case of a non-silent |↦-fork|
transition, the expression side transitions to,
\begin{spec}
⟨ # 0 ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ ⟨ e ‚ ⟨ [] ‚ [] ⟩ ⟩ ∷ []
\end{spec}
while the virtual machine follows by the |↣-FORK| rule:
\restorecolumns
\begin{code}
  fork≼FORK s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ ↦-fork) s₀↠τ⋆s′)
    = ⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩ ∷ ⟨ ⟨ compile e [] ‚ [] ⟩ ⟩ ∷ []
    ∧ ⤇-↠ ε (⁺ _ ∧ (λ ()) ∧ ↠-↣ ↣-FORK) ε
    ∧ ≈′-≈
      (begin
        s′
      ≈⟪ elide-τ⋆ s₀↠τ⋆s′ ⁻¹⟫
        ⟨ # 0 ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ ⟨ e ‚ ⟨ [] ‚ [] ⟩ ⟩ ∷ []
      ≈⟪ ≈-cong₂ (elide-τ (↠τ-switch {[]})) (correctness e [] []) ⟫
        ⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩ ∷ ⟨ ⟨ compile e [] ‚ [] ⟩ ⟩ ∷ []
      ∎)
\end{code}
The two reducts of the original threads are bisimilar by the |elide-τ|
lemma, while bisimilarity of the two spawned threads is obtained from the
induction hypothesis on |e|. Finally, we use the |≈-cong₂| lemma to combine
these results, to give the overall bisimilarity of the two thread soups.

In the opposite direction of |FORK≼fork|, the proof follows the same steps,
with the first clause showing that the |FORK| instruction cannot be silent:
\restorecolumns
\begin{code}
  FORK≼fork : ⟨ ⟨ FORK (compile e []) ∷ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ fork e ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
  FORK≼fork s′ (⤇-↠ ((._ ∧ () ∧ ↠-↣ ↣-FORK) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
  FORK≼fork s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
  FORK≼fork s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
\end{code}
When the virtual machine makes a transition by the |↣-FORK| rule, the
expression follows with |↦-fork|,
\restorecolumns
\begin{code}
  FORK≼fork s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↣ ↣-FORK) s₀↠τ⋆s′)
    = ⟨ # 0 ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ ⟨ e ‚ ⟨ [] ‚ [] ⟩ ⟩ ∷ []
    ∧ ⤇-↠ ε (⁺ _ ∧ (λ ()) ∧ ↠-↦ ↦-fork) ε
    ∧ ≈′-≈
      (begin
        s′
      ≈⟪ elide-τ⋆′ s₀↠τ⋆s′ ⟫
        ⟨ ⟨ c ‚ 0 ∷ σ ⟩ ⟩ ∷ ⟨ ⟨ compile e [] ‚ [] ⟩ ⟩ ∷ []
      ≈⟪ ≈-cong₂ (elide-τ (↠τ-switch {[]})) (correctness e [] []) ⁻¹⟫
        ⟨ # 0 ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ ⟨ e ‚ ⟨ [] ‚ [] ⟩ ⟩ ∷ []
      ∎)
\end{code}
and we obtain the bisimilarity of the two pairs of threads via the |≈-cong₂|
lemma as before. The remaining clauses of |correctness| deal with |# m| and
|a ⊕ b|, following the same steps as that for the Zap language, modulo
cosmetic changes to account for the thread soup. This completes the compiler
correctness proof for the Fork language.

% correctness for # m and a ⊕ b
%{{{%

%if False
\begin{code}
correctness (# m) c σ =
  begin
    ⟨ # m ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
  ≈⟪ elide-τ ↠τ-switch ⟫
    ⟨ ⟨ c ‚ m ∷ σ ⟩ ⟩ ∷ []
  ≈⟪ elide-τ (τ ∧ is-τ ∧ ↠-↣ ↣-PUSH) ⁻¹⟫
    ⟨ ⟨ PUSH m ∷ c ‚ σ ⟩ ⟩ ∷ []
  ≡⟪ ≡.refl ⟫
    ⟨ ⟨ compile (# m) c ‚ σ ⟩ ⟩ ∷ []
  ∎
\end{code}
%endif

%if False
\begin{code}
correctness (a ⊕ b) c σ =
  begin
    ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
  ≈⟪ eval-left a b c σ ⟫
    ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
  ≈⟪ correctness a (compile b (ADD ∷ c)) σ ⟫
    ⟨ ⟨ compile a (compile b (ADD ∷ c)) ‚ σ ⟩ ⟩ ∷ []
  ≡⟪ ≡.refl ⟫
    ⟨ ⟨ compile (a ⊕ b) c ‚ σ ⟩ ⟩ ∷ []
  ∎ where
\end{code}
%endif

%if False
\begin{code}
  eval-right : ∀ m b c σ → ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
  eval-right m b c σ = ♯ m⊕b≼b b & ♯ b≼m⊕b b where
    ⊕≈ADD : ∀ {n} → ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩ ∷ []
    ⊕≈ADD {n} = ♯ ⊕≼ADD & ♯ ADD≼⊕ where
\end{code}
%endif

%if False
\begin{code}
      ⊕≼ADD : ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩ ∷ []
      ⊕≼ADD s′ (⤇-↠ ε (.⊞ ∧ α≄τ ∧ ↠-↦ ↦-⊞) s₀↠τ⋆s′)
        = ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩ ∷ []
        ∧ ⤇-↠ ε (⊞ ∧ (λ ()) ∧ ↠-↣ ↣-ADD) ε
        ∧ ≈′-≈
          (begin
            s′
          ≈⟪ elide-τ⋆ s₀↠τ⋆s′ ⁻¹⟫
            ⟨ # m + n ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
          ≈⟪ elide-τ ↠τ-switch ⟫
            ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩ ∷ []
          ∎)
      ⊕≼ADD s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-L ())) s₀↠τ⋆s′)
      ⊕≼ADD s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-R ())) s₀↠τ⋆s′)
      ⊕≼ADD s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
      ⊕≼ADD s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ e↦e₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
        = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) e↦e₀)
      ⊕≼ADD s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
\end{code}
%endif

%if False
\begin{code}
      ADD≼⊕ : ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩ ∷ [] ≼ ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
      ADD≼⊕ s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↣ ↣-ADD) s₀↠τ⋆s′)
        = ⟨ ⟨ c ‚ m + n ∷ σ ⟩ ⟩ ∷ []
        ∧ ⤇-↠ ε (⊞ ∧ (λ ()) ∧ ↠-↦ ↦-⊞) (↠τ-switch ◅ ε)
        ∧ ≈′-≈ (≈-sym (elide-τ⋆ s₀↠τ⋆s′))
      ADD≼⊕ s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
      ADD≼⊕ s′ (⤇-↠ ((._ ∧ () ∧ ↠-↣ ↣-ADD) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      ADD≼⊕ s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
\end{code}
%endif

%if False
\begin{code}
    case-b≡n : ∀ {n} → ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ # n ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
    case-b≡n {n} =
      begin
        ⟨ # m ⊕ # n ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
      ≈⟪ ⊕≈ADD ⟫
        ⟨ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ⟩ ∷ []
      ≈⟪ elide-τ ↠τ-switch ⁻¹⟫
        ⟨ # n ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
      ∎
\end{code}
%endif

%if False
\begin{code}
    m⊕b≼b : ∀ b → ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
    m⊕b≼b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ e↦e₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) e↦e₀)
    m⊕b≼b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    m⊕b≼b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
    m⊕b≼b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-L ())) s₀↠τ⋆s′)
    m⊕b≼b (# n) s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ ↦-⊞) s₀↠τ⋆s′)
      = ≈→≼ case-b≡n s′ (⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ ↦-⊞) s₀↠τ⋆s′)
    m⊕b≼b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-R {b′ = b₀} {α = α} b↦b₀)) s₀↠τ⋆s′)
      = ⟨ b₀ ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
      ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ b↦b₀) ε
      ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ s₀↠τ⋆s′)) (≈′-cong₂ (≈′-≈ (eval-right m b₀ c σ)) ≈′-refl)
\end{code}
%endif

%if False
\begin{code}
    b≼m⊕b : ∀ b → ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ [] ≼ ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
    b≼m⊕b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ b↦b₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) b↦b₀)
    b≼m⊕b b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    b≼m⊕b (# n) s′ (⤇-↠ ((.τ ∧ is-τ ∧ ↠-switch) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      = ≈→≽ case-b≡n s′ (⤇-↠ ((τ ∧ is-τ ∧ ↠-switch) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    b≼m⊕b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
    b≼m⊕b (# n) s′ (⤇-↠ ε (.τ ∧ α≄τ ∧ ↠-switch) s₀↠τ⋆s′)
      = ≈→≽ case-b≡n s′ (⤇-↠ ε (τ ∧ α≄τ ∧ ↠-switch) s₀↠τ⋆s′)
    b≼m⊕b b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ {e′ = b₀} {α = α} b↦b₀) s₀↠τ⋆s′)
      = ⟨ # m ⊕ b₀ ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
      ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ (↦-R b↦b₀)) ε
      ∧ ≈′-trans (≈′-≈ (≈-sym (elide-τ⋆ s₀↠τ⋆s′))) (≈′-cong₂ (≈′-sym (≈′-≈ (eval-right m b₀ c σ))) ≈′-refl)
\end{code}
%endif

%if False
\begin{code}
  eval-left : ∀ a b c σ → ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
  eval-left a b c σ = ♯ a⊕b≼a a b & ♯ a≼a⊕b a where
    case-a≡m : ∀ {m b} → ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≈ ⟨ # m ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
    case-a≡m {m} {b} =
      begin
        ⟨ # m ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
      ≈⟪ eval-right m b c σ ⟫
        ⟨ b ‚ ⟨ ADD ∷ c ‚ m ∷ σ ⟩ ⟩ ∷ []
      ≈⟪ correctness b (ADD ∷ c) (m ∷ σ) ⟫
        ⟨ ⟨ compile b (ADD ∷ c) ‚ m ∷ σ ⟩ ⟩ ∷ []
      ≈⟪ elide-τ ↠τ-switch ⁻¹⟫
        ⟨ # m ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
      ∎
\end{code}
%endif

%if False
\begin{code}
    a⊕b≼a : ∀ a b → ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ []
    a⊕b≼a a b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ e↦e₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) e↦e₀)
    a⊕b≼a a b s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    a⊕b≼a a b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
    a⊕b≼a (# m) b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-R b↦b₀)) s₀↠τ⋆s′) = ≈→≼ case-a≡m s′ (⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ (↦-R b↦b₀)) s₀↠τ⋆s′)
    a⊕b≼a (# m) (# n) s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ ↦-⊕) s₀↠τ⋆s′) = ≈→≼ case-a≡m s′ (⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ ↦-⊕) s₀↠τ⋆s′)
    a⊕b≼a a b s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ (↦-L {a′ = a₀} {α = α} a↦a₀)) s₀↠τ⋆s′)
      = ⟨ a₀ ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
      ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ a↦a₀) ε
      ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ s₀↠τ⋆s′)) (≈′-cong₂ (≈′-≈ (eval-left a₀ b c σ)) ≈′-refl)
\end{code}
%endif

%if False
\begin{code}
    a≼a⊕b : ∀ a → ⟨ a ‚ ⟨ compile b (ADD ∷ c) ‚ σ ⟩ ⟩ ∷ [] ≼ ⟨ a ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ []
    a≼a⊕b a s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-↦ a↦a₀) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′) = ⊥-elim (¬↦τ (E⁺≃τ-inj α≃τ) a↦a₀)
    a≼a⊕b a s′ (⤇-↠ ((._ ∧ α≃τ ∧ ↠-preempt ()) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    a≼a⊕b (# m) s′ (⤇-↠ ((.τ ∧ α≃τ ∧ ↠-switch) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
      = ≈→≽ case-a≡m s′ (⤇-↠ ((τ ∧ α≃τ ∧ ↠-switch) ◅ s₀↠τ⋆s₁) s₁↠≄τs₂ s₂↠τ⋆s′)
    a≼a⊕b a s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-preempt ()) s₀↠τ⋆s′)
    a≼a⊕b (# m) s′ (⤇-↠ ε (.τ ∧ α≄τ ∧ ↠-switch) s₀↠τ⋆s′)
      = ≈→≽ case-a≡m s′ (⤇-↠ ε (τ ∧ α≄τ ∧ ↠-switch) s₀↠τ⋆s′)
    a≼a⊕b a s′ (⤇-↠ ε (._ ∧ α≄τ ∧ ↠-↦ {e′ = a₀} {α = α} a↦a₀) s₀↠τ⋆s′)
      = ⟨ a₀ ⊕ b ‚ ⟨ c ‚ σ ⟩ ⟩ ∷ (E⁺ <$> α) ⁺∷ []
      ∧ ⤇-↠ ε (_ ∧ α≄τ ∧ ↠-↦ (↦-L a↦a₀)) ε
      ∧ ≈′-trans (≈′-≈ (elide-τ⋆′ s₀↠τ⋆s′)) (≈′-cong₂ (≈′-sym (≈′-≈ (eval-left a₀ b c σ))) ≈′-refl)
\end{code}
%endif

%}}}%

\section{Conclusion}

%In the previous chapter, we introduced our methodology of using the notion
%of bisimilarity on combined machines for tacking compiler correctness for
%a simple non-deterministic language. In this chapter, we shall demonstrate
%that this technique is scalable, by extending the language with a simple
%|fork| primitive in order to introduce explicit concurrency into our system.

We have demonstrated that our previously introduced technique of showing
bisimilarity between combined machines does indeed scale to the explicitly
concurrent Fork language, modelled as a simple `thread soup' of combined
machines. The |elide-τ| lemma was updated for this context using our arsenal
of thread soup lemmas, while the result that soup concatenation preserves
bisimilarity meant that we could phrase our compiler correctness statement
on singleton thread soups. As a result, we were able to reuse most of the
correctness proof for the Zap language, with only the |fork e| case
requiring further attention.

% vim: ft=tex fo-=m fo-=M:

