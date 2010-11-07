%if include /= True
\begin{comment}
%let include = True
%include Fork/Language.lagda
%include Fork/Combined.lagda
%include Fork/Soup.lagda
%include Fork/Bisimilarity.lagda
%include Fork/ElideTau.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import Fork.Combined as Combined
open import Fork.Soup as Soup
open import Fork.Bisimilarity as Bisimilarity
open import Fork.ElideTau as ElideTau

module Fork.Concat where
\end{code}
%endif

\section{Soup Concatenation Preserves Bisimilarity}\label{sec:fork-concat}

With the introduction of explicit concurrency in this Fork language, another
important lemma used in our compiler correctness proof concerns the result
of combining two pairs of bisimilar thread soups. That is, given |rˡ ≈ sˡ|
and |rʳ ≈ sʳ|, concatenating the soups pairwise results in a pair of
bisimilar soups, |rˡ ++ rʳ ≈ sˡ ++ sʳ|.

Intuitively, one can appeal to the following reasoning to see why this is
true; without loss of generality, we need only consider |rˡ ++ rʳ ≼ sˡ ++
sʳ| as the other direction can be obtained by symmetry. We must show that
whatever visible transition |rˡ ++ rʳ| makes, |sˡ ++ sʳ| is able to follow
with the same action. If non-silent transition is due to |rˡ|, then the |sˡ|
half of |sˡ ++ sʳ| can match it by |rˡ ≈ sˡ|, and vice versa for |rʳ|. Any
silent transitions can be bridged using the |elide-τ⋆| lemma.

% ≼-cong₂ : ∀ {rˡ rʳ sˡ sʳ} → rˡ ≈ sˡ → rʳ ≈ sʳ → rˡ ++ rʳ ≼ sˡ ++ sʳ
%format ≼-cong₂ = "\func{{\preccurlyeq}\text-cong_2}"
%format r↠τ⋆r₀ = "r{\twoheadrightarrow}\tau^\star{}r_0"
%format r₀↠≄τr₁ = "r_0{\twoheadrightarrow}{\not\simeq}\tau{}r_1"
%format r₁↠τ⋆r′ = "r_1{\twoheadrightarrow}\tau^\star{}r\Prime{}"
%format rˡ≈sˡ = "r^l{\approx}s^l"
%format rʳ≈sʳ = "r^r{\approx}s^r"
%format rˡ₀ = "r^l_0"
%format rˡ₁ = "r^l_1"
%format rʳ₀ = "r^r_0"
%format rʳ₁ = "r^r_1"
%format rˡ↠τ⋆rˡ₀ = "r^l{\twoheadrightarrow}\tau^\star{}r^l_0"
%format rʳ↠τ⋆rʳ₀ = "r^r{\twoheadrightarrow}\tau^\star{}r^r_0"
Let us now formalise the above argument. We are given |r′| and the three
transition sequences |r↠τ⋆r₀|, |r₀↠≄τr₁| and |r₁↠τ⋆r′| comprising |r ⤇‹
α › r′|. By |r|, we actually mean |rˡ ++ rʳ|; therefore we can use
|↠τ⋆-split| to partition |r↠τ⋆r₀| into two sequences |rˡ↠τ⋆rˡ₀| and
|rʳ↠τ⋆rʳ₀|, which refines |r₀| to |rˡ₀ ++ rʳ₀|:
\begin{code}
≼-cong₂ : _++_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≼_
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ r′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  with ↠τ⋆-split rˡ rʳ r↠τ⋆r₀
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ r′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀
  with ↠≄τ-split rˡ₀ rʳ₀ r₀↠≄τr₁
\end{code}
%format rʳ↠τ⋆rʳ₀ = "r^r{\twoheadrightarrow}\tau^\star{}r^r_0"
%format rˡ₀↠≄τrˡ₁ = "r^l_0{\twoheadrightarrow}{\not\simeq}\tau{}r^l_1"
%format ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧ = "[\![r^l_0{\twoheadrightarrow}\tau{}r^l_1]\!]{\equiv}[\![r_0{\twoheadrightarrow}\tau{}r_1]\!]"
%format sˡ′ = "s^l{}\Prime{}"
%format sˡ⤇sˡ′ = "s^l{\Mapsto}s^l{}\Prime{}"
%format rˡ′≈′sˡ′ = "r^l{}\Prime{\approx}\Prime{}s^l{}\Prime{}"
%format rʳ′≈sʳ = "r^r{}\Prime{\approx}s^r"
%format rʳ₀↠τ⋆rʳ′ = "r^r_0{\twoheadrightarrow}\tau^\star{}r^r{}\Prime{}"
Carrying on in the same vein, we use |↠≄τ-split| on |r₀↠≄τr₁| to locate
which side of |rˡ₀ ++ rʳ₀| the non-silent transition comes from. The proofs
for both cases are symmetrical, so let us consider just the left instance:
|↠≄τ-split| returns a witness |rˡ₀↠≄τrˡ₁|, and refines |r₁| to |rˡ₁ ++ rʳ₀|:
\begin{code}
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ r′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀
  | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    with ↠τ⋆-split rˡ₁ rʳ₀ r₁↠τ⋆r′
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ ._ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀
  | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ rˡ₁↠τ⋆rˡ′ ∧ rʳ₀↠τ⋆rʳ′
    with ≈→≼ rˡ≈sˡ rˡ′ (⤇-↠ rˡ↠τ⋆rˡ₀ rˡ₀↠≄τrˡ₁ rˡ₁↠τ⋆rˡ′)
\end{code}
Partitioning |r₁↠τ⋆r′| along the two sides of |r₁| then gives us the
witnesses |rˡ₁↠τ⋆rˡ′| and |rʳ₀↠τ⋆rʳ′|; the |r′| argument is refined to |rˡ′
++ rʳ′|. The transitions |rˡ↠τ⋆rˡ₀|, |rˡ₀↠≄τrˡ₁| and |rˡ₁↠τ⋆rˡ′| are just
what we need to build a witness of |rˡ ⤇‹ α › rˡ′|. When this is passed to
the |rˡ ≼ sˡ| component of |rˡ≈sˡ|, we receive back a matching transition
|sˡ ⤇‹ α › sˡ′| and a proof |rˡ′≈′sˡ′|:
\begin{code}
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ ._ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀
  | inj₁ (rˡ₁ ∧ ≡.refl ∧ rˡ₀↠≄τrˡ₁ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ rˡ₁↠τ⋆rˡ′ ∧ rʳ₀↠τ⋆rʳ′
    | sˡ′ ∧ sˡ⤇sˡ′ ∧ rˡ′≈′sˡ′ rewrite ⟦rˡ₀↠rˡ₁⟧≡⟦r₀↠r₁⟧
      = sˡ′ ++ sʳ ∧ ⤇-append sʳ sˡ⤇sˡ′
      ∧ ≈′-cong₂ rˡ′≈′sˡ′ (≈′-≈ ( ≈-trans
        (elide-τ⋆′ (rʳ↠τ⋆rʳ₀ ◅◅ rʳ₀↠τ⋆rʳ′)) rʳ≈sʳ ))
\end{code}
Finally, constructing a witness of |sˡ ++ sʳ ⤇‹ α › sˡ′ ++ sʳ| from the
above pieces satisfies one half of the goal; the other half of |rˡ′ ++ rʳ′
≈ sˡ′ ++ sʳ| is obtained coinductively, making use of |elide-τ⋆′| and
transitivity of |_≈_| in the process.

%if False
%format rʳ₀↠≄τrʳ₁ = "r^r_0{\twoheadrightarrow}{\not\simeq}\tau{}r^r_1"
%format ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧ = "[\![r^r_0{\twoheadrightarrow}\tau{}r^r_1]\!]{\equiv}[\![r_0{\twoheadrightarrow}\tau{}r_1]\!]"
%format rˡ₀↠τ⋆rˡ′ = "r^l_0{\twoheadrightarrow}\tau^\star{}r^l{}\Prime{}"
%format rʳ₁↠τ⋆rʳ′ = "r^r_1{\twoheadrightarrow}\tau^\star{}r^r{}\Prime{}"
%format sʳ′ = "s^r{}\Prime{}"
%format sʳ⤇sʳ′ = "s^r{\Mapsto}s^r{}\Prime{}"
%format rʳ′≈′sʳ′ = "r^r{}\Prime{\approx}\Prime{}s^r{}\Prime{}"
\begin{code}
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ r′ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀
  | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    with ↠τ⋆-split rˡ₀ rʳ₁ r₁↠τ⋆r′
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ ._ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀
  | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ rˡ₀↠τ⋆rˡ′ ∧ rʳ₁↠τ⋆rʳ′
    with ≈→≼ rʳ≈sʳ rʳ′ (⤇-↠ rʳ↠τ⋆rʳ₀ rʳ₀↠≄τrʳ₁ rʳ₁↠τ⋆rʳ′)
≼-cong₂ {rˡ} {sˡ} {rʳ} {sʳ} rˡ≈sˡ rʳ≈sʳ ._ (⤇-↠ r↠τ⋆r₀ r₀↠≄τr₁ r₁↠τ⋆r′)
  | rˡ₀ ∧ rʳ₀ ∧ ≡.refl ∧ rˡ↠τ⋆rˡ₀ ∧ rʳ↠τ⋆rʳ₀
  | inj₂ (rʳ₁ ∧ ≡.refl ∧ rʳ₀↠≄τrʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧)
    | rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ rˡ₀↠τ⋆rˡ′ ∧ rʳ₁↠τ⋆rʳ′
    | sʳ′ ∧ sʳ⤇sʳ′ ∧ rʳ′≈′sʳ′ rewrite ⟦rʳ₀↠rʳ₁⟧≡⟦r₀↠r₁⟧
      = sˡ ++ sʳ′ ∧ ⤇-prepend sˡ sʳ⤇sʳ′
      ∧ ≈′-cong₂ (≈′-≈ (≈-trans (elide-τ⋆′ (rˡ↠τ⋆rˡ₀ ◅◅ rˡ₀↠τ⋆rˡ′)) rˡ≈sˡ)) rʳ′≈′sʳ′
\end{code}
%endif

The full result that soup contatenation preserves bisimilarity simply
requires two symmetric invocations of |≼-cong₂|:
% ≈-cong₂ : ∀ {rˡ rʳ sˡ sʳ} → rˡ ≈ sˡ → rʳ ≈ sʳ → rˡ ++ rʳ ≈ sˡ ++ sʳ
%format ≈-cong₂ = "\func{{\approx}\text-cong_2}"
\begin{code}
≈-cong₂ : _++_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
≈-cong₂ rˡ≈sˡ rʳ≈sʳ
  =  ♯ ≼-cong₂         rˡ≈sˡ          rʳ≈sʳ
  &  ♯ ≼-cong₂ (≈-sym  rˡ≈sˡ) (≈-sym  rʳ≈sʳ)
\end{code}
This makes |_≈_| a congruence relation on the monoid $(|List Combined|,
|++|, |[]|)$.

We can now fulfill our obligation (\S\ref{sec:fork-bisimilarity}) of
providing an interpretor for the syntax of |_≈′_|, as follows:
%format ≈′→≈ = "\func{{\approx}\Prime{\rightarrow}{\approx}}"
%format r≈s = "r{\approx}s"
%format rˡ≈′sˡ = "r^l{\approx}\Prime\!s^l"
%format rʳ≈′sʳ = "r^r{\approx}\Prime\!s^r"
%format r≈′s = "r{\approx}\Prime\!s"
%format s≈′t = "s{\approx}\Prime\!t"
\begin{code}
≈′→≈ : _≈′_ ⇒ _≈_
≈′→≈ (≈′-≈ r≈s)                = r≈s
≈′→≈ (≈′-sym r≈′s)             = ≈-sym (≈′→≈ r≈′s)
≈′→≈ (≈′-trans r≈′s s≈′t)      = ≈-trans (≈′→≈ r≈′s) (≈′→≈ s≈′t)
≈′→≈ (≈′-cong₂ rˡ≈′sˡ rʳ≈′sʳ)  = ≈-cong₂ (≈′→≈ rˡ≈′sˡ) (≈′→≈ rʳ≈′sʳ)
\end{code}

% vim: ft=tex fo-=m fo-=M:

