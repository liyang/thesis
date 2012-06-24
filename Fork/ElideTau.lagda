%if include /= True
\begin{comment}
%let include = True
%include Fork/Action.lagda
%include Fork/Language.lagda
%include Fork/Combined.lagda
%include Fork/Soup.lagda
%include Fork/Bisimilarity.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import Fork.Action as Action
open import Fork.Language as Language
open import Fork.Combined as Combined
open import Fork.Soup as Soup
open import Fork.Bisimilarity as Bisimilarity

module Fork.ElideTau where
\end{code}
%endif

%format elide-τ = "\func{elide\text-\tau}"
\section{The |elide-τ| Lemma}

Given the arsenal assembled in the previous section, the proof of the
|elide-τ| lemma is relatively straightforward:
%format r↠τs = "r{\twoheadrightarrow}\tau{}s"
%format s≼r = "\func{s{\preccurlyeq}r}"
%format r≼s = "\func{r{\preccurlyeq}s}"
%format s↠⋆s₀ = "s{\twoheadrightarrow}^\star{}s_0"
%format s₀↠s₁ = "s_0{\twoheadrightarrow}s_1"
%format s₁↠⋆s′ = "s_1{\twoheadrightarrow}^\star{}s\Prime{}"
\savecolumns
\begin{code}
elide-τ : _↠τ_ ⇒ _≈_
elide-τ {r} {s} r↠τs = ♯ r≼s r↠τs & ♯ s≼r where
  s≼r : s ≼ r
  s≼r s′ (⤇-↠ s↠⋆s₀ s₀↠s₁ s₁↠⋆s′)
    = s′ ∧ ⤇-↠ (r↠τs ◅ s↠⋆s₀) s₀↠s₁ s₁↠⋆s′ ∧ ≈′-refl
\end{code}
For |s≼r| the proof is trivial: whatever |s| does, |r| can always match it
by first making the given |r↠τs| transition, after which it can follow |s|
exactly.

%format r⤇r′ = "r{\Mapsto}r\Prime{}"
In the other direction, we begin by extracting (\S\ref{sec:fork-extract})
the active thread |x| from |r↠τs|. This refines |r| to |rˡ ++ x ∷ rʳ|, which
allows us to dissect (\S\ref{sec:fork-dissect}) |r⤇r′| using |x| as the
pivot:
\restorecolumns
\begin{code}
  r≼s : ∀ {r s} → r ↠τ s → r ≼ s
  r≼s r↠τs r′ r⤇r′
    with ↠τ-extract r↠τs
  r≼s r↠τs r′ r⤇r′
    | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
      with ⤇-dissect rˡ rʳ x↠τ₁x′ r⤇r′
\end{code}
In the instance where |r⤇r′| happens to already include the |x↠τ₁x′|
transition, the proof is trivial:
%format s⤇r′ = "s{\Mapsto}r\Prime{}"
\restorecolumns
\begin{code}
  r≼s r↠τs r′ r⤇r′
    | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
      | inj₁ s⤇r′ = r′ ∧ s⤇r′ ∧ ≈′-refl
\end{code}
Here, |⤇-dissect| provides the witness |s⤇r′| showing that |s| can
transition to |r′| too, with |r′ ≈′ r′| given by reflexivity of |_≈′_|.

Otherwise |r⤇r′| has yet to make the |x↠τ₁x′| transition. Two alternatives
arise, as the non-silent transition could have been on either side of |x|.
Without loss of generalisation suppose this is on the left, in which case
|⤇-dissect| refines |r′| to |rˡ′ ++ x ∷ rʳ′|, and delivers witnesses of |rˡ
⤇‹ α › rˡ′| and |rʳ ↠τ⋆ rʳ′|:
%format rˡ↠τ⋆rˡ₀ = "r^l{\twoheadrightarrow}\tau^\star{}r^l_0"
%format rˡ₀↠rˡ₁ = "r^l_0{\twoheadrightarrow}r^l_1"
%format rˡ₁↠τ⋆rˡ′ = "r^l_1{\twoheadrightarrow}\tau^\star{}r^l{}\Prime{}"
%format rʳ↠τ⋆rʳ′ = "r^r{\twoheadrightarrow}\tau^\star{}r^r{}\Prime{}"
%format rˡ₀x′rʳ↠rˡ₁x′rʳ = "r^l_0x\Prime{}r^r{\twoheadrightarrow}r^l_1x\Prime{}r^r"
%format ⟦rˡ₀↠rˡ₁⟧≡⟦rˡ₀x′rʳ↠rˡ₁x′rʳ⟧ = "[\![r^l_0{\twoheadrightarrow}r^l_1]\!]{\equiv}[\![r^l_0x\Prime{}r^r{\twoheadrightarrow}r^l_1x\Prime{}r^r]\!]"
\restorecolumns
\begin{code}
  r≼s r↠τs ._ r⤇r′
    | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
      | inj₂ ( rˡ′ ∧ rʳ′ ∧ ≡.refl
        ∧ inj₁ (⤇-↠ rˡ↠τ⋆rˡ₀ rˡ₀↠rˡ₁ rˡ₁↠τ⋆rˡ′ ∧ rʳ↠τ⋆rʳ′) )
      with ↠≄τ-append (x′ ∷ rʳ) rˡ₀↠rˡ₁
  r≼s r↠τs ._ r⤇r′
      | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
      | inj₂ ( rˡ′ ∧ rʳ′ ∧ ≡.refl
        ∧ inj₁ (⤇-↠ rˡ↠τ⋆rˡ₀ rˡ₀↠rˡ₁ rˡ₁↠τ⋆rˡ′ ∧ rʳ↠τ⋆rʳ′) )
      | rˡ₀x′rʳ↠rˡ₁x′rʳ ∧ ⟦rˡ₀↠rˡ₁⟧≡⟦rˡ₀x′rʳ↠rˡ₁x′rʳ⟧
        rewrite ⟦rˡ₀↠rˡ₁⟧≡⟦rˡ₀x′rʳ↠rˡ₁x′rʳ⟧
      = rˡ′ ++ x′ ∷ rʳ′
      ∧ ⤇-↠ (↠τ⋆-++ rˡ↠τ⋆rˡ₀ (ε {x = x′ ∷ rʳ})) rˡ₀x′rʳ↠rˡ₁x′rʳ
          (↠τ⋆-++ rˡ₁↠τ⋆rˡ′ (ε {x = x′ ∷ rʳ}) ◅◅
            ↠τ⋆-++ (ε {x = rˡ′}) (↠τ⋆-++ (ε {x = x′ ∷ []}) rʳ↠τ⋆rʳ′))
      ∧ ≈′-≈ (elide-τ (↠τ-prepend rˡ′ (x↠τ₁x′ rʳ′)))
\end{code}
Note that the earlier |↠τ-extract| had established that |s| is in fact equal
to |rˡ ++ x′ ∷ rʳ|. Therefore, we can construct a visible transition from
|s|,
\begin{spec}
rˡ ++ x′ ∷ rʳ ⤇‹ α › rˡ′ ++ x′ ∷ rʳ′
\end{spec}
by reconstituting the aforementioned |rˡ ⤇‹ α › rˡ′| and |rʳ ↠τ⋆ rʳ′|. The
final bisimilarity component of the proof is obtained by coinduction on:
\begin{spec}
rˡ′ ++ x ∷ rʳ′ ↠τ rˡ′ ++ x′ ∷ rʳ′
\end{spec}

\noindent For the case where the non-silent transition is to the right of
|x|, the proof follows the same approach.
%if False
\restorecolumns
\begin{code}
  r≼s r↠τs ._ r⤇r′
    | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
      | inj₂ (rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ inj₂ (rˡ↠τ⋆rˡ′ ∧ ⤇-↠ rʳ↠τ⋆rʳ₀ rʳ₀↠rʳ₁ rʳ₁↠τ⋆rʳ′))
      with ↠≄τ-prepend (x′ ∷ []) rʳ₀↠rʳ₁
  r≼s r↠τs ._ r⤇r′
    | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
      | inj₂ (rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ inj₂ (rˡ↠τ⋆rˡ′ ∧ ⤇-↠ rʳ↠τ⋆rʳ₀ rʳ₀↠rʳ₁ rʳ₁↠τ⋆rʳ′))
      | x′rʳ₀↠x′rʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦x′rʳ₀↠x′rʳ₁⟧
      with ↠≄τ-prepend rˡ x′rʳ₀↠x′rʳ₁
  r≼s r↠τs ._ r⤇r′
    | rˡ ∧ rʳ ∧ x ∧ x′ ∧ ≡.refl ∧ ≡.refl ∧ x↠τ₁x′
      | inj₂ (rˡ′ ∧ rʳ′ ∧ ≡.refl ∧ inj₂ (rˡ↠τ⋆rˡ′ ∧ ⤇-↠ rʳ↠τ⋆rʳ₀ rʳ₀↠rʳ₁ rʳ₁↠τ⋆rʳ′))
      | x′rʳ₀↠x′rʳ₁ ∧ ⟦rʳ₀↠rʳ₁⟧≡⟦x′rʳ₀↠x′rʳ₁⟧
      | rˡx′rʳ₀↠rˡx′rʳ₁ ∧ ⟦x′rʳ₀↠x′rʳ₁⟧≡⟦rˡx′rʳ₀↠rˡx′rʳ₁⟧
        rewrite ⟦rʳ₀↠rʳ₁⟧≡⟦x′rʳ₀↠x′rʳ₁⟧ | ⟦x′rʳ₀↠x′rʳ₁⟧≡⟦rˡx′rʳ₀↠rˡx′rʳ₁⟧
      = rˡ′ ++ x′ ∷ rʳ′
      ∧ ⤇-↠ (↠τ⋆-++ (ε {x = rˡ}) (↠τ⋆-++ (ε {x = x′ ∷ []}) rʳ↠τ⋆rʳ₀)) rˡx′rʳ₀↠rˡx′rʳ₁
        (↠τ⋆-++ (ε {x = rˡ}) (↠τ⋆-++ (ε {x = x′ ∷ []}) rʳ₁↠τ⋆rʳ′)
          ◅◅ ↠τ⋆-++ rˡ↠τ⋆rˡ′ (ε {x = x′ ∷ rʳ′}))
      ∧ ≈′-≈ (elide-τ (↠τ-prepend rˡ′ (x↠τ₁x′ rʳ′)))
\end{code}
%endif

Using the transitivity and reflexivity of |_≈_| we can generalise |elide-τ|
to silent transition sequences, as well as a symmetric variant:
%format elide-τ⋆ = "\func{elide\text-\tau^\star}"
%format elide-τ⋆′ = "\func{elide\text-\tau^\star{}\Prime{}}"
\begin{code}
elide-τ⋆ : _↠τ⋆_ ⇒ _≈_
elide-τ⋆ = Star.fold _≈_ ≈-trans ≈-refl ∘ Star.map elide-τ

elide-τ⋆′ : _↠τ⋆_ ⇒ flip _≈_
elide-τ⋆′ = ≈-sym ∘ elide-τ⋆
\end{code}

% vim: ft=tex fo-=m fo-=M:

