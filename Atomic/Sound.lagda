%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
%include Atomic/Combined.lagda
%include Atomic/Transaction.lagda
\end{comment}
%endif

%if False
\begin{code}
module Sound where

open import Common
open import Heap
open import Logs
open import Language
open import Combined
open import Transaction
\end{code}
%endif

\subsection{Soundness}

%if False
\begin{code}
infix 3 H⊢_↣′_ H⊢_↣′⋆_
\end{code}
%endif

%format ↣′-swap = "\func{{\rightarrowtail\Prime}\text-swap}"
%format cons′-v-h«v» = "\Varid{cons\Prime\text-v\text-h_v}"
%format ↣′-read-l-v = "\Varid{{\rightarrowtail\Prime}\text-read\text-l\text-v}"
\begin{code}
↣′-swap : ∀ {h h′ l e l′ e′} → Consistent h′ l′ →
  h ⊢ l , e ↣′ l′ , e′ → h′ ⊢ l , e ↣′ l′ , e′
↣′-swap cons′ ↣′-ℕ = ↣′-ℕ
↣′-swap cons′ (↣′-R m b↣b′) = ↣′-R m (↣′-swap cons′ b↣b′)
↣′-swap cons′ (↣′-L b a↣a′) = ↣′-L b (↣′-swap cons′ a↣a′)
↣′-swap cons′ (↣′-writeE e↣e′) = ↣′-writeE (↣′-swap cons′ e↣e′)
↣′-swap cons′ ↣′-writeℕ = ↣′-writeℕ
↣′-swap {h} {h′} cons′ (↣′-read l v)
     with cons′ v (h « v ») | ↣′-read {h = h′} l v
...  |  cons′-v-h«v» | ↣′-read-l-v with Logs.ω l « v »
...     |  ● m = ↣′-read-l-v
...     |  ○ with Logs.ρ l « v »
...        | ● m = ↣′-read-l-v
...        | ○  rewrite Vec.lookup∘update v (Logs.ρ l) (● (h « v »))
                | cons′-v-h«v» ≡.refl = ↣′-read-l-v
\end{code}

%-- sequence of ↣′ transitions with different heaps
%format H⊢_↣′_ = "\type{H{\vdash}\anonymous{\rightarrowtail\Prime}\anonymous}"
%format H⊢_↣′⋆_ = "\type{H{\vdash}\anonymous{\rightarrowtail\Prime^\star}\anonymous}"
%format H⊢ = "\prefix{\type{H{\vdash}}}"
\begin{code}
H⊢_↣′_ : Rel (Logs × Expression′)
H⊢ x ↣′ x′ = Σ Heap (λ h → h ⊢ x ↣′ x′)

H⊢_↣′⋆_ : Rel (Logs × Expression′)
H⊢_↣′⋆_ = Star H⊢_↣′_
\end{code}

%format ↣′⋆-swap = "\func{{\rightarrowtail\Prime^\star}\text-swap}"
%format e′↣⋆e″ = "\Varid{e\Prime{\rightarrowtail^\star}\!e\PPrime}"
%{
%format P = "\type{P}"
%format f = "\func{f}"
\begin{code}
↣′⋆-swap : ∀ {h′ l e l′ e′} → Consistent h′ l′ →
  H⊢ l , e ↣′⋆ l′ , e′ → h′ ⊢ l , e ↣′⋆ l′ , e′
↣′⋆-swap {h′} cons = fst ∘ Star.gfold id P f (ε , cons) where
  P : Logs × Expression′ → Logs × Expression′ → Set
  P (l , e) (l′ , e′) = h′ ⊢ l , e ↣′⋆ l′ , e′ × Consistent h′ l
  f : ∀ {x x′ x″} → H⊢ x ↣′ x′ → P x′ x″ → P x x″
  f (h , e↣e′) (e′↣⋆e″ , cons′)
    = ↣′-swap cons′ e↣e′ ◅ e′↣⋆e″ , ↣′-Consistent′ e↣e′ cons′
\end{code}
%}

%if False
\begin{code}
private
\end{code}
%endif

%format ↣-extract′ = "\func{{\rightarrowtail}\text-extract\Prime}"
%format r↣′⋆e = "\Varid{r{\rightarrowtail\Prime^\star}\!e}"
%format e′↠⋆e″ = "\Varid{e\Prime{\twoheadrightarrow^\star_\tau}e\PPrime}"
%format e″↠e‴ = "\Varid{e\PPrime{\twoheadrightarrow}e\PPPrime}"
\begin{code}
  ↣-extract′ : ∀ {α h r l e h′ c′ e′ h″ c″ e″} →
    H⊢ ∅ , r ↣′⋆ l , e →
    α ≢ τ → h , ↣: ● (r , l) , atomic e  ↠⋆  h′ , c′ , e′ →
    α ▹  h′ , c′ , e′  ↠  h″ , c″ , e″ →
    ∃₂ λ l′ m → α , h″ , c″ , e″ ≡ ☢ , Update h′ l′ , ↣: ○ , # m ×
    Consistent h′ l′ × H⊢ ∅ , r ↣′⋆ l′ , # m
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-step e↣e′)) = ⊥-elim (α≢τ ≡.refl)
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-mutate h′)) = ⊥-elim (α≢τ ≡.refl)
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-abort ¬cons)) = ⊥-elim (α≢τ ≡.refl)
  ↣-extract′ r↣′⋆e α≢τ ε (↠-↣ (↣-commit cons)) =
    _ , _ , ≡.refl , cons , r↣′⋆e
  ↣-extract′ r↣′⋆e α≢τ (↠-↣ (↣-step e↣e′)   ◅ e′↠⋆e″) e″↠e‴ =
    ↣-extract′ (r↣′⋆e ◅◅ (_ , e↣e′) ◅ ε) α≢τ e′↠⋆e″ e″↠e‴
  ↣-extract′ r↣′⋆e α≢τ (↠-↣ (↣-mutate h′)   ◅ e′↠⋆e″) e″↠e‴ =
    ↣-extract′ r↣′⋆e α≢τ e′↠⋆e″ e″↠e‴
  ↣-extract′ r↣′⋆e α≢τ (↠-↣ (↣-abort ¬cons) ◅ e′↠⋆e″) e″↠e‴ =
    ↣-extract′ ε α≢τ e′↠⋆e″ e″↠e‴
\end{code}

%format ↣-extract = "\func{{\rightarrowtail}\text-extract}"
\begin{code}
↣-extract : ∀ {α h r h″ c″ e″} →
  α ▹ h , ↣: ○ , atomic r ⤇ h″ , c″ , e″ →
  ∃₃ λ h′ l′ m → α , h″ , c″ , e″ ≡ ☢ , Update h′ l′ , ↣: ○ , # m ×
  Consistent h′ l′ × H⊢ ∅ , r ↣′⋆ l′ , # m
↣-extract (⤇: α≢τ ε (↠-↣ ↣-begin)) = ⊥-elim (α≢τ ≡.refl)
↣-extract (⤇: α≢τ (↠-↣ ↣-begin ◅ e↠⋆e′) e′↠e″) =
  _ , ↣-extract′ ε α≢τ e↠⋆e′ e′↠e″
\end{code}

%format ↣′→↦′ = "\func{{\rightarrowtail\Prime}{\rightarrow}{\mapsto\Prime}}"
%format ↦′-read-h-v = "\Varid{{\rightarrowtail\Prime}\text-read\text-v}"
\begin{code}
↣′→↦′ : ∀ {h l e l′ e′ h₀} →
            Equivalent h₀ l h    →  h₀ ⊢ l , e ↣′ l′ , e′ →
  ∃ λ h′ →  Equivalent h₀ l′ h′  ×  h , e ↦′ h′ , e′
↣′→↦′ equiv ↣′-ℕ = _ , equiv , ↦′-ℕ
↣′→↦′ equiv (↣′-R m b↣b′) =
  Σ.map id (Σ.map id (↦′-R m)) (↣′→↦′ equiv b↣b′)
↣′→↦′ equiv (↣′-L b a↣a′) =
  Σ.map id (Σ.map id (↦′-L b)) (↣′→↦′ equiv a↣a′)
↣′→↦′ equiv (↣′-writeE e↣e′) =
  Σ.map id (Σ.map id ↦′-writeE) (↣′→↦′ equiv e↣e′)
↣′→↦′ equiv ↣′-writeℕ = _ , Write-Equivalent equiv , ↦′-writeℕ
↣′→↦′ {h} equiv (↣′-read l v) with equiv v | ↦′-read h v
... |  equiv-v | ↦′-read-h-v with Logs.ω l « v »
...    |  ● m rewrite equiv-v = _ , equiv , ↦′-read-h-v
...    |  ○ with Logs.ρ l « v » | ≡.inspect (_«_» (Logs.ρ l)) v
...       |  ● m | _ rewrite equiv-v = _ , equiv , ↦′-read-h-v
...       |  ○ | ‹ ρ«v»≡○ › rewrite ≡.sym equiv-v = _
             , Read-Equivalent ρ«v»≡○ equiv , ↦′-read-h-v
\end{code}

%format ↣′⋆→↦′⋆ = "\func{{\rightarrowtail\Prime^\star}{\rightarrow}{\mapsto\Prime^\star}}"
%format e′↦⋆e″ = "\Varid{e\Prime{\mapsto^\star}\!e\PPrime}"
%format cons″ = "\Varid{cons\PPrime}"
%format equiv′ = "\Varid{equiv\Prime}"
%format equiv″ = "\Varid{equiv\PPrime}"
\begin{code}
↣′⋆→↦′⋆ : ∀ {h l e l′ e′ h₀} →
            Equivalent h₀ l h    →  h₀ ⊢ l , e ↣′⋆ l′ , e′ →
  ∃ λ h′ →  Equivalent h₀ l′ h′  ×  h , e ↦′⋆ h′ , e′
↣′⋆→↦′⋆ equiv ε = _ , equiv , ε
↣′⋆→↦′⋆ equiv (e↣e′ ◅ e′↣⋆e″) with ↣′→↦′ equiv e↣e′
... |  h′ , equiv′ , e↦e′ with ↣′⋆→↦′⋆ equiv′ e′↣⋆e″
...    | h″ , equiv″ , e′↦⋆e″ = h″ , equiv″ , e↦e′ ◅ e′↦⋆e″
\end{code}

% vim: ft=tex fo-=m fo-=M:

