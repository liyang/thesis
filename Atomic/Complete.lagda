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
module Complete where

open import Common
open import Heap
open import Logs
open import Language
open import Combined
open import Transaction
\end{code}
%endif

\subsection{Completeness}

%-- Zero or more ↦-mutate rules followed by ↦-atomic.
%format ↦-extract = "\func{{\mapsto}\text-extract}"
%format e↦′⋆m = "\Varid{e{\mapsto\Prime^\star}m}"
%format h₁≟h₀ = "\Varid{h_1{\stackrel?=}h_0}"
\begin{code}
↦-extract : ∀ {α h e h″ c″ e″} →
  α ▹ h , ↦: , atomic e ⤇ h″ , c″ , e″ →
  ∃₂ λ h₀ m → α , c″ , e″ ≡ ☢ , ↦: , # m ×
  Dec (h ≡ h₀) × h₀ , e ↦′⋆ h″ , # m
↦-extract (⤇: α≢τ ε (↠-↦ (↦-mutate h₁))) = ⊥-elim (α≢τ ≡.refl)
↦-extract (⤇: α≢τ ε (↠-↦ (↦-atomic e↦′⋆m))) =
  _ , _ , ≡.refl , yes ≡.refl , e↦′⋆m
↦-extract (⤇: α≢τ (↠-↦ (↦-mutate h₁) ◅ e↠⋆e′) e′↠e″)
     with ↦-extract (⤇: α≢τ e↠⋆e′ e′↠e″)
...  |  h₀ , m , ≡.refl , h₁≟h₀ , e↦⋆m =
        h₀ , m , ≡.refl , _ ≟Heap h₀ , e↦⋆m
\end{code}

%format ↦′→↣′ = "\func{{\mapsto\Prime}{\rightarrow}{\rightarrowtail\Prime}}"
%format ↣′-read-l-v = "\Varid{{\rightarrowtail\Prime}\text-read\text-l\text-v}"
\begin{code}
↦′→↣′ : ∀ {l h₀ h e h′ e′} →
            Consistent h₀ l   →  Equivalent h₀ l h    →  h , e  ↦′  h′ , e′ →
  ∃ λ l′ →  Consistent h₀ l′  ×  Equivalent h₀ l′ h′  ×  h₀ ⊢  l , e  ↣′  l′ , e′
↦′→↣′ cons equiv ↦′-ℕ = _ , cons , equiv , ↣′-ℕ
↦′→↣′ cons equiv (↦′-R m b↦b′) =
  Σ.map id (Σ.map id (Σ.map id (↣′-R m))) (↦′→↣′ cons equiv b↦b′)
↦′→↣′ cons equiv (↦′-L b a↦a′) =
  Σ.map id (Σ.map id (Σ.map id (↣′-L b))) (↦′→↣′ cons equiv a↦a′)
↦′→↣′ cons equiv (↦′-writeE e↦e′) =
  Σ.map id (Σ.map id (Σ.map id ↣′-writeE)) (↦′→↣′ cons equiv e↦e′)
↦′→↣′ cons equiv ↦′-writeℕ = , cons , Write-Equivalent equiv , ↣′-writeℕ
↦′→↣′ {l} cons equiv (↦′-read h₀ v) with equiv v | ↣′-read l v
... |  equiv-v | ↣′-read-l-v with Logs.ω l « v »
...    |  ● m rewrite equiv-v = , cons , equiv , ↣′-read-l-v
...    |  ○  with Logs.ρ l « v » | ≡.inspect (_«_» (Logs.ρ l)) v
...       |  ● m  | _ rewrite equiv-v = , cons , equiv , ↣′-read-l-v
...       |  ○    | ‹ ρ«v»≡○ › rewrite ≡.sym equiv-v = _
             , Read-Consistent l v cons
             , Read-Equivalent ρ«v»≡○ equiv , ↣′-read-l-v
\end{code}

%format ↦′⋆→↣′⋆ = "\func{{\mapsto\Prime^\star}{\rightarrow}{\rightarrowtail\Prime^\star}}"
%format e′↦⋆e″ = "\Varid{e\Prime{\mapsto^\star}e\PPrime}"
%format e′↣⋆e″ = "\Varid{e\Prime{\rightarrowtail^\star}e\PPrime}"
%format cons″ = "\Varid{cons\PPrime}"
%format equiv′ = "\Varid{equiv\Prime}"
%format equiv″ = "\Varid{equiv\PPrime}"
\begin{code}
↦′⋆→↣′⋆ : ∀ {h₀ l h e h′ e′} →
            Consistent h₀ l   →  Equivalent h₀ l h    →  h , e  ↦′⋆  h′ , e′ →
  ∃ λ l′ →  Consistent h₀ l′  ×  Equivalent h₀ l′ h′  ×  h₀ ⊢ l , e  ↣′⋆ l′ , e′
↦′⋆→↣′⋆ cons equiv ε = _ , cons , equiv , ε
↦′⋆→↣′⋆ cons equiv (e↦e′ ◅ e′↦⋆e″) with ↦′→↣′ cons equiv e↦e′
... |  l′ , cons′ , equiv′ , e↣e′ with ↦′⋆→↣′⋆ cons′ equiv′ e′↦⋆e″
...    | l″ , cons″ , equiv″ , e′↣⋆e″ = l″ , cons″ , equiv″ , e↣e′ ◅ e′↣⋆e″
\end{code}

% vim: ft=tex fo-=m fo-=M:

