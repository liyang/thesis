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
module Lemmas where

open import Common
open import Language
open import Combined
\end{code}
%endif

%-- No progress.
%format #↦̸ = "\func{\texttt\#{\not\mapsto}}"
\begin{code}
#↦̸ : ∀ {α h m x′} →
  α ▹ h , # m ↦ x′ → ⊥
#↦̸ ()
\end{code}

%format #↣̸ = "\func{\texttt\#{\not\rightarrowtail}}"
\begin{code}
#↣̸ : ∀ {α h t m x′} →
  α ▹ h , t , # m ↣ x′ → ⊥
#↣̸ ()
\end{code}

%format #↠̸ = "\func{\texttt\#{\not\twoheadrightarrow}}"
\begin{code}
#↠̸ : ∀ {α h c m x′} →
  α ▹ h , c , # m ↠ x′ → ⊥
#↠̸ (↠-↦ e↦e′) = #↦̸ e↦e′
#↠̸ (↠-↣ e↣e′) = #↣̸ e↣e′
\end{code}

%format #⤇̸ = "\func{\texttt\#{\not\Mapsto}}"
%format e↠e′ = "\Varid{e{\twoheadrightarrow}e\Prime}"
%format e′↠⋆e″ = "\Varid{e\Prime{\twoheadrightarrow^\star}e\PPrime}"
\begin{code}
#⤇̸ : ∀ {α h c m x′} →
  α ▹ h , c , # m ⤇ x′ → ⊥
#⤇̸ (⤇: α≢τ ε e↠e′) = #↠̸ e↠e′
#⤇̸ (⤇: α≢τ (e↠e′ ◅ e′↠⋆e″) e″↠e‴) = #↠̸ e↠e′
\end{code}

%-- transactions always finish after visible transition
%format ↣→t′≡○ = "\func{{\rightarrowtail}{\rightarrow}t\Prime{\equiv}\circ}"
\begin{code}
↣→t′≡○ : ∀ {α h t e h′ t′ e′} →
  α ≢ τ →
  α ▹ h , t , e ↣ h′ , t′ , e′ →
  t′ ≡ ○
↣→t′≡○ α≢τ ↣-ℕ = ≡.refl
↣→t′≡○ α≢τ (↣-R m b↣b′) = ↣→t′≡○ α≢τ b↣b′
↣→t′≡○ α≢τ (↣-L b a↣a′) = ↣→t′≡○ α≢τ a↣a′
↣→t′≡○ α≢τ ↣-begin = ⊥-elim (α≢τ ≡.refl)
↣→t′≡○ α≢τ (↣-step e↣e′) = ⊥-elim (α≢τ ≡.refl)
↣→t′≡○ α≢τ (↣-mutate h′) = ⊥-elim (α≢τ ≡.refl)
↣→t′≡○ α≢τ (↣-abort ¬cons) = ⊥-elim (α≢τ ≡.refl)
↣→t′≡○ α≢τ (↣-commit cons) = ≡.refl
\end{code}

%format ↠→t′≡○ = "\func{{\twoheadrightarrow}{\rightarrow}t\Prime{\equiv}\circ}"
\begin{code}
↠→t′≡○ : ∀ {α h t e h′ t′ e′} →
  α ≢ τ →
  α ▹ h , ↣: t , e ↠ h′ , ↣: t′ , e′ →
  t′ ≡ ○
↠→t′≡○ α≢τ (↠-↣ e↣e′) = ↣→t′≡○ α≢τ e↣e′
\end{code}

%format ↠⋆/↦-L = "\func{{\twoheadrightarrow^\star}/{\mapsto}\text-{\oplus}L}"
\begin{code}
↠⋆/↦-L : ∀ {α h a b x′ x″} →
  α ≢ τ →
  h , ↦: , a ⊕ b ↠⋆ x′ →
  α ▹ x′ ↠ x″ →
  ∃ ( λ m → a ≡ # m ) ⊎
  ∃₄ ( λ h′ a′ h″ a″ →
    x′ ≡ h′ , ↦: , a′ ⊕ b ×
    x″ ≡ h″ , ↦: , a″ ⊕ b ×
    h , ↦: , a ↠⋆ h′ , ↦: , a′ ×
    α ▹ h′ , ↦: , a′ ↠ h″ , ↦: , a″ )
↠⋆/↦-L α≢τ ε (↠-↦ ↦-ℕ) = inl (_ , ≡.refl)
↠⋆/↦-L α≢τ ε (↠-↦ (↦-R m b↦b′)) = inl (m , ≡.refl)
↠⋆/↦-L α≢τ ε (↠-↦ (↦-L b a↦a′)) = inr (_ , _ , _ , _ , ≡.refl , ≡.refl , ε , ↠-↦ a↦a′)
↠⋆/↦-L α≢τ (↠-↦ (↦-R m b↦b′) ◅ e′↠⋆e″) e″↠e‴ = inl (m , ≡.refl)
↠⋆/↦-L α≢τ (↠-↦ (↦-L b a↦a′) ◅ e′↠⋆e″) e″↠e‴ with ↠⋆/↦-L α≢τ e′↠⋆e″ e″↠e‴
↠⋆/↦-L α≢τ (↠-↦ (↦-L b ()) ◅ e′↠⋆e″) e″↠e‴ | inl (m , ≡.refl)
... | inr (h″ , a″ , h‴ , a‴ , ≡.refl , ≡.refl , a′↠⋆a″ , a″↠a‴) = 
      inr (h″ , a″ , h‴ , a‴ , ≡.refl , ≡.refl , ↠-↦ a↦a′ ◅ a′↠⋆a″ , a″↠a‴)
\end{code}

%format ↠⋆/↣-L = "\func{{\twoheadrightarrow^\star}/{\rightarrowtail}\text-{\oplus}L}"
\begin{code}
↠⋆/↣-L : ∀ {α h t a b x′ x″} →
  α ≢ τ →
  h , ↣: t , a ⊕ b ↠⋆ x′ →
  α ▹ x′ ↠ x″ →
  ∃ ( λ m → a ≡ # m ) ⊎
  ∃₃ ( λ h′ t′ a′ → ∃₂ λ h″ a″ →
    x′ ≡ h′ , ↣: t′ , a′ ⊕ b ×
    x″ ≡ h″ , ↣: ○  , a″ ⊕ b ×
    h , ↣: t , a ↠⋆ h′ , ↣: t′ , a′ ×
    α ▹ h′ , ↣: t′ , a′ ↠ h″ , ↣: ○ , a″ )
↠⋆/↣-L α≢τ ε (↠-↣ ↣-ℕ) = inl (_ , ≡.refl)
↠⋆/↣-L α≢τ ε (↠-↣ (↣-R m b↣b′)) = inl (m , ≡.refl)
↠⋆/↣-L α≢τ ε (↠-↣ (↣-L b a↣a′)) with ↣→t′≡○ α≢τ a↣a′
... | ≡.refl = inr (_ , _ , _ , _ , _ , ≡.refl , ≡.refl , ε , ↠-↣ a↣a′)
↠⋆/↣-L α≢τ (↠-↣ (↣-R m b↣b′) ◅ e′↠⋆e″) e″↠e‴ = inl (m , ≡.refl)
↠⋆/↣-L α≢τ (↠-↣ (↣-L b a↣a′) ◅ e′↠⋆e″) e″↠e‴ with ↠⋆/↣-L α≢τ e′↠⋆e″ e″↠e‴
↠⋆/↣-L α≢τ (↠-↣ (↣-L b ()) ◅ e′↠⋆e″) e″↠e‴ | inl (m , ≡.refl)
... | inr (h″ , t″ , a″ , h‴ , a‴ , ≡.refl , ≡.refl , a′↠⋆a″ , a″↠a‴) =
      inr (h″ , t″ , a″ , h‴ , a‴ , ≡.refl , ≡.refl , ↠-↣ a↣a′ ◅ a′↠⋆a″ , a″↠a‴)
\end{code}

%format ↠⋆/↦-R = "\func{{\twoheadrightarrow^\star}/{\mapsto}\text-{\oplus}R}"
\begin{code}
↠⋆/↦-R : ∀ {α h m b x′ x″} →
  α ≢ τ →
  h , ↦: , # m ⊕ b ↠⋆ x′ →
  α ▹ x′ ↠ x″ →
  ∃ ( λ n →
    b ≡ # n ×
    α ≡ ⊞ ×
    x′ ≡ h , ↦: , # m ⊕ # n ×
    x″ ≡ h , ↦: , # (m + n) ) ⊎
  ∃₄ ( λ h′ b′ h″ b″ →
    x′ ≡ h′ , ↦: , # m ⊕ b′ ×
    x″ ≡ h″ , ↦: , # m ⊕ b″ ×
    h , ↦: , b ↠⋆ h′ , ↦: , b′ ×
    α ▹ h′ , ↦: , b′ ↠ h″ , ↦: , b″ )
↠⋆/↦-R α≢τ ε (↠-↦ ↦-ℕ) = inl (_ , ≡.refl , ≡.refl , ≡.refl , ≡.refl)
↠⋆/↦-R α≢τ ε (↠-↦ (↦-R m b↦b′)) = inr (_ , _ , _ , _ , ≡.refl , ≡.refl , ε , ↠-↦ b↦b′)
↠⋆/↦-R α≢τ ε (↠-↦ (↦-L b a↦a′)) = ⊥-elim (#↦̸ a↦a′)
↠⋆/↦-R α≢τ (↠-↦ (↦-L b a↦a′) ◅ c′↠⋆c″) c″↠c‴ = ⊥-elim (#↦̸ a↦a′)
↠⋆/↦-R α≢τ (↠-↦ (↦-R m b↦b′) ◅ c′↠⋆c″) c″↠c‴ with ↠⋆/↦-R α≢τ c′↠⋆c″ c″↠c‴
↠⋆/↦-R α≢τ (↠-↦ (↦-R m ()) ◅ c′↠⋆c″) c″↠c‴
    | inl (n , ≡.refl , ≡.refl , ≡.refl , ≡.refl)
... | inr (h″ , b″ , h‴ , b‴ , ≡.refl , ≡.refl , b′↠⋆b″ , b″↠b‴) =
      inr (h″ , b″ , h‴ , b‴ , ≡.refl , ≡.refl , ↠-↦ b↦b′ ◅ b′↠⋆b″ , b″↠b‴)
\end{code}

%format ↠⋆/↣-R = "\func{{\twoheadrightarrow^\star}/{\rightarrowtail}\text-{\oplus}R}"
\begin{code}
↠⋆/↣-R : ∀ {α h t m b x′ x″} →
  α ≢ τ →
  h , ↣: t , # m ⊕ b ↠⋆ x′ →
  α ▹ x′ ↠ x″ →
  ∃ ( λ n →
    b ≡ # n ×
    α ≡ ⊞ ×
    x′ ≡ h , ↣: t , # m ⊕ # n ×
    x″ ≡ h , ↣: t , # (m + n) ) ⊎
  ∃₃ ( λ h′ t′ b′ → ∃₂ λ h″ b″ →
    x′ ≡ h′ , ↣: t′ , # m ⊕ b′ ×
    x″ ≡ h″ , ↣: ○  , # m ⊕ b″ ×
    h , ↣: t , b ↠⋆ h′ , ↣: t′ , b′ ×
    α ▹ h′ , ↣: t′ , b′ ↠ h″ , ↣: ○ , b″ )
↠⋆/↣-R α≢τ ε (↠-↣ ↣-ℕ) = inl (_ , ≡.refl , ≡.refl , ≡.refl , ≡.refl)
↠⋆/↣-R α≢τ ε (↠-↣ (↣-R m b↣b′)) with ↣→t′≡○ α≢τ b↣b′
... | ≡.refl = inr (_ , _ , _ , _ , _ , ≡.refl , ≡.refl , ε , ↠-↣ b↣b′)
↠⋆/↣-R α≢τ ε (↠-↣ (↣-L b a↣a′)) = ⊥-elim (#↣̸ a↣a′)
↠⋆/↣-R α≢τ (↠-↣ (↣-L b a↣a′) ◅ e′↠⋆e″) e″↠e‴ = ⊥-elim (#↣̸ a↣a′)
↠⋆/↣-R α≢τ (↠-↣ (↣-R m b↣b′) ◅ e′↠⋆e″) e″↠e‴ with ↠⋆/↣-R α≢τ e′↠⋆e″ e″↠e‴
↠⋆/↣-R α≢τ (↠-↣ (↣-R m ()) ◅ e′↠⋆e″) e″↠e‴
    | inl (n , ≡.refl , ≡.refl , ≡.refl , ≡.refl)
... | inr (h″ , t″ , b″ , h‴ , b‴ , ≡.refl , ≡.refl , b′↠⋆b″ , b″↠b‴) =
      inr (h″ , t″ , b″ , h‴ , b‴ , ≡.refl , ≡.refl , ↠-↣ b↣b′ ◅ b′↠⋆b″ , b″↠b‴)
\end{code}

%format ↠∘↦-L = "\func{{\twoheadrightarrow}{\circ}{\mapsto}\text-{\oplus}L}"
\begin{code}
↠∘↦-L : ∀ b {α h a h′ c′ a′} →
  α ▹ h , ↦: , a ↠ h′ , c′ , a′ →
  c′ ≡ ↦: ×
  α ▹ h , ↦: , a ⊕ b ↠ h′ , ↦: , a′ ⊕ b
↠∘↦-L b (↠-↦ a↦a′) = ≡.refl , ↠-↦ (↦-L b a↦a′)
\end{code}

%format ↠⋆∘↦-L = "\func{{\twoheadrightarrow^\star}{\circ}{\mapsto}\text-{\oplus}L}"
\begin{code}
↠⋆∘↦-L : ∀ b {h a h′ c′ a′} →
  h , ↦: , a ↠⋆ h′ , c′ , a′ →
  c′ ≡ ↦: ×
  h , ↦: , a ⊕ b ↠⋆ h′ , ↦: , a′ ⊕ b
↠⋆∘↦-L b ε = ≡.refl , ε
↠⋆∘↦-L b (↠-↦ a↦a′ ◅ a′↠⋆a″) with ↠⋆∘↦-L b a′↠⋆a″
... | ≡.refl , a′⊕b↠⋆a″⊕b = ≡.refl , ↠-↦ (↦-L b a↦a′) ◅ a′⊕b↠⋆a″⊕b
\end{code}

%format ⤇∘↦-L = "\func{{\Mapsto}{\circ}{\mapsto}\text-{\oplus}L}"
\begin{code}
⤇∘↦-L : ∀ b {α h a h′ c′ a′} →
  α ▹ h , ↦: , a ⤇ h′ , c′ , a′ →
  c′ ≡ ↦: ×
  α ▹ h , ↦: , a ⊕ b ⤇ h′ , ↦: , a′ ⊕ b
⤇∘↦-L b (⤇: α≢τ a↠⋆a′ a′↠a″) with ↠⋆∘↦-L b a↠⋆a′
... | ≡.refl , a⊕b↠⋆a′⊕b with ↠∘↦-L b a′↠a″
...   | ≡.refl , a′⊕b↠a″⊕b = ≡.refl , ⤇: α≢τ a⊕b↠⋆a′⊕b a′⊕b↠a″⊕b
\end{code}

%format ↠∘↣-L = "\func{{\twoheadrightarrow}{\circ}{\rightarrowtail}\text-{\oplus}L}"
\begin{code}
↠∘↣-L : ∀ b {α h t a h′ c′ a′} →
  α ▹ h , ↣: t , a ↠ h′ , c′ , a′ →
  ∃ λ t′ →
  c′ ≡ ↣: t′ ×
  α ▹ h , ↣: t , a ⊕ b ↠ h′ , ↣: t′ , a′ ⊕ b
↠∘↣-L b (↠-↣ a↣a′) = _ , ≡.refl , ↠-↣ (↣-L b a↣a′)
\end{code}

%format ↠⋆∘↣-L = "\func{{\twoheadrightarrow^\star}{\circ}{\rightarrowtail}\text-{\oplus}L}"
\begin{code}
↠⋆∘↣-L : ∀ b {h t a h′ c′ a′} →
  h , ↣: t , a ↠⋆ h′ , c′ , a′ →
  ∃ λ t′ →
  c′ ≡ ↣: t′ ×
  h , ↣: t , a ⊕ b ↠⋆ h′ , ↣: t′ , a′ ⊕ b
↠⋆∘↣-L b ε = _ , ≡.refl , ε
↠⋆∘↣-L b (↠-↣ a↣a′ ◅ a′↠⋆a″) with ↠⋆∘↣-L b a′↠⋆a″
... | t″ , ≡.refl , a′⊕b↠⋆a″⊕b = t″ , ≡.refl , ↠-↣ (↣-L b a↣a′) ◅ a′⊕b↠⋆a″⊕b
\end{code}

%format ⤇∘↣-L = "\func{{\Mapsto}{\circ}{\rightarrowtail}\text-{\oplus}L}"
\begin{code}
⤇∘↣-L : ∀ b {α h t a h′ c′ a′} →
  α ▹ h , ↣: t , a ⤇ h′ , c′ , a′ →
  c′ ≡ ↣: ○ ×
  α ▹ h , ↣: t , a ⊕ b ⤇ h′ , ↣: ○ , a′ ⊕ b
⤇∘↣-L b (⤇: α≢τ a↠⋆a′ a′↠a″) with ↠⋆∘↣-L b a↠⋆a′
... | t′ , ≡.refl , a⊕b↠⋆a′⊕b with ↠∘↣-L b a′↠a″
...   | t″ , ≡.refl , a′⊕b↠a″⊕b rewrite ↠→t′≡○ α≢τ a′↠a″ = ≡.refl , ⤇: α≢τ a⊕b↠⋆a′⊕b a′⊕b↠a″⊕b
\end{code}

%format ↠∘↦-R = "\func{{\twoheadrightarrow}{\circ}{\mapsto}\text-{\oplus}R}"
\begin{code}
↠∘↦-R : ∀ m {α h b h′ c′ b′} →
  α ▹ h , ↦: , b ↠ h′ , c′ , b′ →
  c′ ≡ ↦: ×
  α ▹ h , ↦: , # m ⊕ b ↠ h′ , ↦: , # m ⊕ b′
↠∘↦-R m (↠-↦ b↦b′) = ≡.refl , ↠-↦ (↦-R m b↦b′)
\end{code}

%format ↠⋆∘↦-R = "\func{{\twoheadrightarrow^\star}{\circ}{\mapsto}\text-{\oplus}R}"
\begin{code}
↠⋆∘↦-R : ∀ m {h b h′ c′ b′} →
  h , ↦: , b ↠⋆ h′ , c′ , b′ →
  c′ ≡ ↦: ×
  h , ↦: , # m ⊕ b ↠⋆ h′ , ↦: , # m ⊕ b′
↠⋆∘↦-R m ε = ≡.refl , ε
↠⋆∘↦-R m (↠-↦ b↦b′ ◅ b′↠⋆b″) with ↠⋆∘↦-R m b′↠⋆b″
... | ≡.refl , m⊕b′↠⋆m⊕b″ = ≡.refl , ↠-↦ (↦-R m b↦b′) ◅ m⊕b′↠⋆m⊕b″
\end{code}

%format ⤇∘↦-R = "\func{{\Mapsto}{\circ}{\mapsto}\text-{\oplus}R}"
\begin{code}
⤇∘↦-R : ∀ m {α h b h′ c′ b′} →
  α ▹ h , ↦: , b ⤇ h′ , c′ , b′ →
  c′ ≡ ↦: ×
  α ▹ h , ↦: , # m ⊕ b ⤇ h′ , ↦: , # m ⊕ b′
⤇∘↦-R m (⤇: α≢τ b↠⋆b′ b′↠b″) with ↠⋆∘↦-R m b↠⋆b′
... | ≡.refl , m⊕b↠⋆m⊕b′ with ↠∘↦-R m b′↠b″
...   | ≡.refl , m⊕b′↠m⊕b″ = ≡.refl , ⤇: α≢τ m⊕b↠⋆m⊕b′ m⊕b′↠m⊕b″
\end{code}

%format ↠∘↣-R = "\func{{\twoheadrightarrow}{\circ}{\rightarrowtail}\text-{\oplus}R}"
\begin{code}
↠∘↣-R : ∀ m {α h t b h′ c′ b′} →
  α ▹ h , ↣: t , b ↠ h′ , c′ , b′ →
  ∃ λ t′ →
  c′ ≡ ↣: t′ ×
  α ▹ h , ↣: t , # m ⊕ b ↠ h′ , ↣: t′ , # m ⊕ b′
↠∘↣-R m (↠-↣ b↣b′) = _ , ≡.refl , ↠-↣ (↣-R m b↣b′)
\end{code}

%format ↠⋆∘↣-R = "\func{{\twoheadrightarrow^\star}{\circ}{\rightarrowtail}\text-{\oplus}R}"
\begin{code}
↠⋆∘↣-R : ∀ m {h t b h′ c′ b′} →
  h , ↣: t , b ↠⋆ h′ , c′ , b′ →
  ∃ λ t′ →
  c′ ≡ ↣: t′ ×
  h , ↣: t , # m ⊕ b ↠⋆ h′ , ↣: t′ , # m ⊕ b′
↠⋆∘↣-R m ε = _ , ≡.refl , ε
↠⋆∘↣-R m (↠-↣ b↣b′ ◅ b′↠⋆b″) with ↠⋆∘↣-R m b′↠⋆b″
... | t″ , ≡.refl , m⊕b′↠⋆m⊕b″ = t″ , ≡.refl , ↠-↣ (↣-R m b↣b′) ◅ m⊕b′↠⋆m⊕b″
\end{code}

%format ⤇∘↣-R = "\func{{\Mapsto}{\circ}{\rightarrowtail}\text-{\oplus}R}"
\begin{code}
⤇∘↣-R : ∀ m {α h t b h′ c′ b′} →
  α ▹ h , ↣: t , b ⤇ h′ , c′ , b′ →
  c′ ≡ ↣: ○ ×
  α ▹ h , ↣: t , # m ⊕ b ⤇ h′ , ↣: ○ , # m ⊕ b′
⤇∘↣-R m (⤇: α≢τ b↠⋆b′ b′↠b″) with ↠⋆∘↣-R m b↠⋆b′
... | t′ , ≡.refl , m⊕b↠⋆m⊕b′ with ↠∘↣-R m b′↠b″
...   | t″ , ≡.refl , m⊕b′↠m⊕b″ rewrite ↠→t′≡○ α≢τ b′↠b″ = ≡.refl , ⤇: α≢τ m⊕b↠⋆m⊕b′ m⊕b′↠m⊕b″
\end{code}

% vim: ft=tex fo-=m fo-=M:

