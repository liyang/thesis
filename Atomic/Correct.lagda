%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
%include Atomic/Combined.lagda
%include Atomic/Bisimilar.lagda
%include Atomic/Transaction.lagda
%include Atomic/Complete.lagda
%include Atomic/Sound.lagda
%include Atomic/Lemmas.lagda
\end{comment}
%endif

%if False
\begin{code}
module Correct where

open import Common
open import Heap
open import Logs
open import Language
open import Combined
open import Bisimilar
open import Transaction
open import Complete
open import Sound
open import Lemmas
\end{code}
%endif

\section{Bisimilarity of Semantics}

%format #⊢↦≈↣ = "\func{\texttt\#{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
\begin{code}
#⊢↦≈↣ : ∀ {h m} → h , # m ⊢ ↦: ≈ ↣: ○
#⊢↦≈↣ = ♯ (⊥-elim ∘ #⤇̸) & ♯ (⊥-elim ∘ #⤇̸)
\end{code}

lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit
amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor
sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum

%format m⊕n⊢↦≈↣ = "\func{m{\oplus}n{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format ↦≼↣ = "\func{{\mapsto}{\succcurlyeq}{\rightarrowtail}}"
%format ↣≼↦ = "\func{{\rightarrowtail}{\succcurlyeq}{\mapsto}}"
\savecolumns
\begin{code}
m⊕n⊢↦≈↣ : ∀ {h m n} → h , # m ⊕ # n ⊢ ↦: ≈ ↣: ○
m⊕n⊢↦≈↣ {h} {m} {n} = ♯ ↦≼↣ & ♯ ↣≼↦ where
  ↦≼↣ : h , # m ⊕ # n ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ ε (↠-↦ ↦-ℕ)) =
    _ , ⤇: α≢τ ε (↠-↣ ↣-ℕ) , #⊢↦≈↣
  ↦≼↣ (⤇: α≢τ ε (↠-↦ (↦-R ._ b↦b′))) = ⊥-elim (#↦̸ b↦b′)
  ↦≼↣ (⤇: α≢τ ε (↠-↦ (↦-L ._ a↦a′))) = ⊥-elim (#↦̸ a↦a′)
  ↦≼↣ (⤇: α≢τ (↠-↦ (↦-R ._ b↦b′) ◅ _) _) = ⊥-elim (#↦̸ b↦b′)
  ↦≼↣ (⤇: α≢τ (↠-↦ (↦-L ._ a↦a′) ◅ _) _) = ⊥-elim (#↦̸ a↦a′)
\end{code}

\restorecolumns
\begin{code}
  ↣≼↦ : h , # m ⊕ # n ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ ε (↠-↣ ↣-ℕ)) =
    _ , ⤇: α≢τ ε (↠-↦ ↦-ℕ) , ≈-sym #⊢↦≈↣
  ↣≼↦ (⤇: α≢τ ε (↠-↣ (↣-R ._ b↣b′))) = ⊥-elim (#↣̸ b↣b′)
  ↣≼↦ (⤇: α≢τ ε (↠-↣ (↣-L ._ a↣a′))) = ⊥-elim (#↣̸ a↣a′)
  ↣≼↦ (⤇: α≢τ (↠-↣ (↣-R ._ b↣b′) ◅ _) _) = ⊥-elim (#↣̸ b↣b′)
  ↣≼↦ (⤇: α≢τ (↠-↣ (↣-L ._ a↣a′) ◅ _) _) = ⊥-elim (#↣̸ a↣a′)
\end{code}

%format eval-right = "\func{eval\text-right}"
%format b⊢↦≈↣ = "\Varid{b{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format b″⊢↦≈↣ = "\Varid{b\PPrime{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format b″⊢↣≈↦ = "\Varid{b\PPrime{\vdash}{\rightarrowtail}{\approx}{\mapsto}}"
\savecolumns
\begin{code}
eval-right : ∀ {h m b} →
  h , b ⊢ ↦: ≈ ↣: ○ → h , # m ⊕ b ⊢ ↦: ≈ ↣: ○
eval-right {h} {m} {b} b⊢↦≈↣ = ♯ ↦≼↣ & ♯ ↣≼↦ where
\end{code}

lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit
amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor
sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum

%format b≡n = "\Varid{b{\equiv}n}"
%format b↠⋆b′ = "\Varid{b{\twoheadrightarrow^\star_\tau}b\Prime}"
%format b′↠b″ = "\Varid{b\Prime{\twoheadrightarrow}b\PPrime}"
%format b⤇b″ = "\Varid{b{\Mapsto}b\PPrime}"
%format c″≡↣ = "\Varid{c\PPrime{\equiv}{\rightarrowtail}}"
%format c″≡↦ = "\Varid{c\PPrime{\equiv}{\mapsto}}"
%format m⊕b⤇m⊕b″ = "\Varid{m{\oplus}b{\Mapsto}m{\oplus}b\PPrime}"
\restorecolumns
\begin{code}
  ↦≼↣ : h , # m ⊕ b ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↦-R α≢τ e↠⋆e′ e′↠e″
  ... |  inl (n , b≡n , ≡.refl , ≡.refl , ≡.refl) rewrite b≡n =
         ♭ (≈→≼ m⊕n⊢↦≈↣) (⤇: α≢τ ε (↠-↦ ↦-ℕ))
  ... |  inr (h′ , b′ , h″ , b″ , ≡.refl , ≡.refl , b↠⋆b′ , b′↠b″)
         with ♭ (≈→≼ b⊢↦≈↣) (⤇: α≢τ b↠⋆b′ b′↠b″)
  ...    |  c″ , b⤇b″ , b″⊢↦≈↣ with ⤇∘↣-R m b⤇b″
  ...       |  c″≡↣ , m⊕b⤇m⊕b″ rewrite c″≡↣ =
               _ , m⊕b⤇m⊕b″ , eval-right b″⊢↦≈↣
\end{code}

lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit
amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor
sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum

%format ↦≈↣ = "\func{{\mapsto}{\approx}{\rightarrowtail}}"
%format ↣≈↦ = "\func{{\rightarrowtail}{\approx}{\mapsto}}"
\restorecolumns
\begin{code}
  ↣≼↦ : h , # m ⊕ b ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↣-R α≢τ e↠⋆e′ e′↠e″
  ... |  inl (n , b≡n , ≡.refl , ≡.refl , ≡.refl) rewrite b≡n =
         ♭ (≈→≽ m⊕n⊢↦≈↣) (⤇: α≢τ ε (↠-↣ ↣-ℕ))
  ... |  inr (h′ , t′ , b′ , h″ , b″ , ≡.refl , ≡.refl , b↠⋆b′ , b′↠b″)
         with ♭ (≈→≽ b⊢↦≈↣) (⤇: α≢τ b↠⋆b′ b′↠b″)
  ...    |  c″ , b⤇b″ , b″⊢↣≈↦ with ⤇∘↦-R m b⤇b″
  ...       |  c″≡↦ , m⊕b⤇m⊕b″ rewrite c″≡↦ =
               _ , m⊕b⤇m⊕b″ , ↣≈↦ where
    ↦≈↣ = eval-right (≈-sym b″⊢↣≈↦)
    ↣≈↦ = ≈→≽ ↦≈↣ & ≈→≼ ↦≈↣
\end{code}

lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit
amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor
sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum

%format eval-left = "\func{eval\text-left}"
%format a⊢↦≈↣ = "\Varid{a{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format a″⊢↦≈↣ = "\Varid{a\PPrime{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
%format ∀b⊢↦≈↣ = "\Varid{{\forall}b{\vdash}{\mapsto}{\approx}{\rightarrowtail}}"
\savecolumns
\begin{code}
eval-left : ∀ {h a b} →
  h , a ⊢ ↦: ≈ ↣: ○ → (∀ h′ → h′ , b ⊢ ↦: ≈ ↣: ○) →
  h , a ⊕ b ⊢ ↦: ≈ ↣: ○
eval-left {h} {a} {b} a⊢↦≈↣ ∀b⊢↦≈↣ = ♯ ↦≼↣ & ♯ ↣≼↦ where
\end{code}

%format a≡m = "\Varid{a{\equiv}m}"
%format a↠⋆a′ = "\Varid{a{\twoheadrightarrow^\star_\tau}a\Prime}"
%format a′↠a″ = "\Varid{a\Prime{\twoheadrightarrow}a\PPrime}"
%format a⤇a″ = "\Varid{a{\Mapsto}a\PPrime}"
%format a⊕b⤇a″⊕b = "\Varid{a{\oplus}b{\Mapsto}a\PPrime{\oplus}b}"
\restorecolumns
\begin{code}
  ↦≼↣ : h , a ⊕ b ⊢ ↦: ≼ ↣: ○
  ↦≼↣ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↦-L α≢τ e↠⋆e′ e′↠e″
  ... |  inl (m , a≡m) rewrite a≡m =
         ♭ (≈→≼ (eval-right (∀b⊢↦≈↣ h))) (⤇: α≢τ e↠⋆e′ e′↠e″)
  ... |  inr (h′ , a′ , h″ , a″ , ≡.refl , ≡.refl , a↠⋆a′ , a′↠a″)
         with ♭ (≈→≼ a⊢↦≈↣) (⤇: α≢τ a↠⋆a′ a′↠a″)
  ...    |  c″ , a⤇a″ , a″⊢↦≈↣ with ⤇∘↣-L b a⤇a″
  ...       |  c″≡↣ , a⊕b⤇a″⊕b rewrite c″≡↣ =
               _ , a⊕b⤇a″⊕b , eval-left a″⊢↦≈↣ ∀b⊢↦≈↣
\end{code}

\restorecolumns
\begin{code}
  ↣≼↦ : h , a ⊕ b ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ (⤇: α≢τ e↠⋆e′ e′↠e″) with ↠⋆/↣-L α≢τ e↠⋆e′ e′↠e″
  ... |  inl (m , a≡m) rewrite a≡m =
         ♭ (≈→≽ (eval-right (∀b⊢↦≈↣ h))) (⤇: α≢τ e↠⋆e′ e′↠e″)
  ... |  inr (h′ , t′ , a′ , h″ , a″ , ≡.refl , ≡.refl , a↠⋆a′ , a′↠a″)
         with ♭ (≈→≽ a⊢↦≈↣) (⤇: α≢τ a↠⋆a′ a′↠a″)
  ...    |  c″ , a⤇a″ , a″⊢↣≈↦ with ⤇∘↦-L b a⤇a″
  ...       |  c″≡↦ , a⊕b⤇a″⊕b rewrite c″≡↦ =
               _ , a⊕b⤇a″⊕b , ↣≈↦ where
    ↦≈↣ = eval-left (≈-sym a″⊢↣≈↦) ∀b⊢↦≈↣
    ↣≈↦ = ≈→≽ ↦≈↣ & ≈→≼ ↦≈↣
\end{code}

%format transaction = "\func{transaction}"
%format mutate? = "\func{mutate?}"
%format e⤇m = "\func{e{\Mapsto}m}"
%format e⤇e″ = "\Varid{e{\Mapsto}e\PPrime}"
%format h≟h₀ = "\Varid{h{\stackrel?=}h_0}"
%format e↣′⋆m = "\Varid{e{\rightarrowtail\Prime^\star}m}"
\restorecolumns
\begin{code}
transaction : ∀ {h e} → h , atomic e ⊢ ↦: ≈ ↣: ○
transaction {h} {e} = ♯ ↦≼↣ & ♯ ↣≼↦ where
  ↦≼↣ : h , atomic e ⊢ ↦: ≼ ↣: ○
  ↦≼↣ e⤇e″ with ↦-extract e⤇e″
  ... |  h₀ , m , ≡.refl , h≟h₀ , e↦′⋆m
         with ↦′⋆→↣′⋆ ∅-Consistent ∅-Equivalent e↦′⋆m
  ...    |  l′ , cons′ , equiv′ , e↣′⋆m rewrite ≡.sym (Commit cons′ equiv′) =
            _ , e⤇m , #⊢↦≈↣ where
\end{code}

lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit
amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor
sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum

%format h≡h₀ = "\Varid{h{\equiv}h_0}"
%format h≢h₀ = "\Varid{h{\not\equiv}h_0}"
\restorecolumns
\begin{code}
    mutate? : ∀ {h₀} → Dec (h ≡ h₀) →
      h  , ↣: ● (e , ∅) , atomic e ↠⋆ h₀ , ↣: ● (e , ∅) , atomic e
    mutate? (yes h≡h₀) rewrite h≡h₀ = ε
    mutate? (no h≢h₀) = ↠-↣ (↣-mutate _) ◅ ε
\end{code}

lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit
amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum dolor
sit amet lorem ipsum dolor sit amet lorem ipsum dolor sit amet lorem ipsum

%{
%format e↣⋆m = "\func{e{\rightarrowtail^\star}m}"
\restorecolumns
\begin{code}
    e↣⋆m : h₀ , ↣: ● (e , ∅) , atomic e ↠⋆ h₀ , ↣: ● (e , l′) , atomic (# m)
    e↣⋆m = Star.gmap _ (↠-↣ ∘ ↣-step) e↣′⋆m

    e⤇m : ☢ ▹ h , ↣: ○ , atomic e ⤇ Update h₀ l′ , ↣: ○ , # m
    e⤇m = ⤇: (λ ()) (↠-↣ ↣-begin ◅ mutate? h≟h₀ ◅◅ e↣⋆m)
      (↠-↣ (↣-commit cons′))
\end{code}
%}

\restorecolumns
\begin{code}
  ↣≼↦ : h , atomic e ⊢ ↣: ○ ≼ ↦:
  ↣≼↦ e⤇e″ with ↣-extract e⤇e″
  ... |  h′ , l′ , m , ≡.refl , cons , e↣⋆m
         with ↣′⋆→↦′⋆ ∅-Consistent ∅-Equivalent (↣′⋆-swap cons e↣⋆m)
  ...    |  h″ , _ , equiv , e↦′⋆m rewrite ≡.sym (Commit cons equiv) =
            _ , e⤇m , ≈-sym #⊢↦≈↣ where
\end{code}

\restorecolumns
\begin{code}
    mutate? : ∀ {h₀} → Dec (h ≡ h₀) →
      h , ↦: , atomic e ↠⋆ h₀ , ↦: , atomic e
    mutate? (yes ≡.refl) = ε
    mutate? (no h≢h₀) = ↠-↦ (↦-mutate {!!}) ◅ ε
\end{code}

\restorecolumns
\begin{code}
    e⤇m : ☢ ▹ h , ↦: , atomic e ⤇ Update h′ l′ , ↦: , # m
    e⤇m = ⤇: (λ ()) (mutate? (h ≟Heap _)) (↠-↦ (↦-atomic e↦′⋆m))
\end{code}

%format correct = "\func{correct}"
\begin{code}
correct : ∀ h e → h , e ⊢ ↦: ≈ ↣: ○
correct h (# m) = #⊢↦≈↣
correct h (a ⊕ b) = eval-left (correct h a) (λ h′ → correct h′ b)
correct h (atomic e) = transaction
\end{code}

% vim: ft=tex fo-=m fo-=M:

