%include local.fmt
%include agda.fmt

%{{{%
%if False
\begin{code}
module agda where

open import Data.Empty
open import Data.Sum
import Data.Product as Σ
open Σ renaming (_,_ to _&_)
import Data.Star as Star
open Star

open import Data.Nat

open import Function

open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≢_; _with-≡_)
\end{code}
%endif
%}}}%

\chapter{Machine-Assisted Proofs in Agda}

\begin{itemize}
\item intro to Agda
\item replay previous proofs
\end{itemize}

\section{Integers and Addition}

The language in question:
%{{{%
%if False
\begin{code}
infixl 4 _⊕_
infix 5 #_
\end{code}
%endif
%format #_ = "\cons{\texttt{\#}\anonymous}"
%format # = "\prefix{\cons{\texttt{\#}}}"
%format _⊕_ = "\cons{\anonymous{\oplus}\anonymous}"
%format ⊕ = "\infix{\cons{\oplus}}"
%format Expression = "\type{Expression}"
\begin{code}
data Expression : Set where
  #_   : (m : ℕ)             → Expression
  _⊕_  : (a b : Expression)  → Expression
\end{code}
%}}}%

\section{Denotational}

As a function:
%{{{%
%format ⟦_⟧ = "\func{[\![\anonymous]\!]}"
%format ⟦ = "\prefix{\func{[\![}}"
%format ⟧ = "\postfix{\func{]\!]}}"
\begin{code}
⟦_⟧ : Expression → ℕ
⟦ # m ⟧    = m
⟦ a ⊕ b ⟧  = ⟦ a ⟧ + ⟦ b ⟧
\end{code}
%}}}%

\section{Big-Step Semantics}

Functions are more straightforward, but does not generalise to non-deterministic semantics.

As a relation:
%{{{%
%if False
\begin{code}
infix 4 _⇓_
\end{code}
%endif
%format _⇓_ = "\type{\anonymous{\Downarrow}\anonymous}"
%format ⇓ = "\infix{\type{{\Downarrow}}}"
%format ⇓-ℕ = "\cons{{\Downarrow}\text-\mathbb{N}}"
%format ⇓-⊕ = "\cons{{\Downarrow}\text-\oplus}"
\begin{code}
data _⇓_ : Expression → ℕ → Set where
  ⇓-ℕ  : ∀ {m} → # m ⇓ m
  ⇓-⊕  : ∀ {a b m n} → a ⇓ m → b ⇓ n → a ⊕ b ⇓ m + n
\end{code}
%}}}%

\section{Small-Step Semantics}

As a function:
%{{{%
%if False
\begin{code}
-- ⊕≡e⇒∄m≡e : ∀ {a b e} → a ⊕ b ≡ e → ∄ λ m → # m ≡ e
-- ⊕≡e⇒∄m≡e ≡.refl (n & ())

-- step : (e : Expression) → {_ : ∄ λ m → # m ≡ e} → Expression
-- step (# m) {¬m} = ⊥-elim (¬m (m & ≡.refl))
-- step (a ⊕ b) with ≡.inspect a
-- step (a ⊕ b) | (_ ⊕ _) with-≡ ⊕≡a = step a {⊕≡e⇒∄m≡e ⊕≡a} ⊕ b
-- step (a ⊕ b) | (# m) with-≡ m≡a with ≡.inspect b
-- step (a ⊕ b) | (# m) with-≡ m≡a | (_ ⊕ _) with-≡ ⊕≡b = a ⊕ step b {⊕≡e⇒∄m≡e ⊕≡b}
-- step (a ⊕ b) | (# m) with-≡ m≡a | (# n) with-≡ n≡b = # m + n
\end{code}
%endif
%format step = "\func{step}"
%format a′ = "a\Prime{}"
%format b′ = "b\Prime{}"
\begin{code}
step : (e : Expression) → ℕ ⊎ Expression
step (# m) = inj₁ m
step (a ⊕ b)  with step a
step (a ⊕ b)  | inj₁ m  with step b
step (a ⊕ b)  | inj₁ m  | inj₁ n   = inj₂ (# (m + n))
step (a ⊕ b)  | inj₁ m  | inj₂ b′  = inj₂ (a ⊕ b′)
step (a ⊕ b)  | inj₂ a′ = inj₂ (a′ ⊕ b)
\end{code}
%}}}%

As a relation:
%{{{%
%if False
\begin{code}
infix 3 _↦_ _↦⋆_ _↦⋆#_
\end{code}
%endif
%format _↦_ = "\type{\anonymous{\mapsto}\anonymous}"
%format ↦ = "\type{{\mapsto}}"
%format _↦⋆_ = "\type{\anonymous{\mapsto}^\star\anonymous}"
%format ↦⋆ = "\type{{\mapsto}^\star}"
%format _↦⋆#_ = "\type{\anonymous{\mapsto}^\star\;" # "\anonymous}"
%format ↦⋆# = "\type{{\mapsto}^\star}\;" #
%format ↦-ℕ = "\cons{{\mapsto}\text-\mathbb{N}}"
%format ↦-L = "\cons{{\mapsto}\text-L}"
%format ↦-R = "\cons{{\mapsto}\text-R}"
\begin{code}
data _↦_ : Rel Expression _ where
  ↦-ℕ  : ∀ {m n}       →           #  m  ⊕ # n  ↦ # (m + n)
  ↦-L  : ∀ {a a′ b  }  → a ↦ a′ →     a  ⊕ b    ↦    a′  ⊕ b
  ↦-R  : ∀ {m b  b′ }  → b ↦ b′ →  #  m  ⊕ b    ↦ #  m   ⊕ b′

_↦⋆_ : Rel Expression _
_↦⋆_ = Star _↦_

_↦⋆#_ : REL Expression ℕ _
e ↦⋆# m = e ↦⋆ # m
\end{code}
%}}}%

\section{Equivalence Proof and Techniques}

%{{{%
%format denotation→big = "\func{denot{\rightarrow}big}"
\begin{code}
denotation→big : ∀ {e m} → ⟦ e ⟧ ≡ m → e ⇓ m
denotation→big {# m}    ≡.refl = ⇓-ℕ
denotation→big {a ⊕ b}  ≡.refl = ⇓-⊕ (denotation→big ≡.refl) (denotation→big ≡.refl)
\end{code}

%format big→denotation = "\func{big{\rightarrow}denot}"
%format a⇓m = "a{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"
\begin{code}
big→denotation : ∀ {e m} → e ⇓ m → ⟦ e ⟧ ≡ m
big→denotation ⇓-ℕ = ≡.refl
big→denotation (⇓-⊕ a⇓m b⇓n) with big→denotation a⇓m | big→denotation b⇓n
big→denotation (⇓-⊕ a⇓m b⇓n) | ≡.refl | ≡.refl = ≡.refl
\end{code}

%format big→small = "\func{big{\rightarrow}small}"
%format a⇓m = "a{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"
\begin{code}
big→small : ∀ {e : Expression} {m : ℕ} → e ⇓ m → e ↦⋆# m
big→small ⇓-ℕ = ε
big→small (⇓-⊕ {a} {b} {m} {n} a⇓m b⇓n) =
  gmap (λ a′ →    a′  ⊕ b)   ↦-L (big→small a⇓m) ◅◅
  gmap (λ b′ → #  m   ⊕ b′)  ↦-R (big→small b⇓n) ◅◅
  ↦-ℕ ◅ ε
\end{code}

%format small→big = "\func{small{\rightarrow}big}"
%format e′ = "e\Prime{}"
%format e↦e′ = "e{\mapsto}e\Prime{}"
%format e′↦⋆m = "e\Prime{}{\mapsto}^\star{}m"
%format sound = "\func{sound}"
%format a↦a′ = "a{\mapsto}a\Prime{}"
%format b↦b′ = "b{\mapsto}b\Prime{}"
%format a′⇓m = "a\Prime{\Downarrow}m"
%format b⇓n = "b{\Downarrow}n"
%format b′⇓n = "b\Prime{\Downarrow}n"
\begin{code}
small→big : ∀ {e m} → e ↦⋆# m → e ⇓ m
small→big ε = ⇓-ℕ
small→big (e↦e′ ◅ e′↦⋆m) = sound e↦e′ (small→big e′↦⋆m) where
  sound : ∀ {e e′ m} → e ↦ e′ → e′ ⇓ m → e ⇓ m
  sound ↦-ℕ         ⇓-ℕ             = ⇓-⊕ ⇓-ℕ ⇓-ℕ
  sound (↦-L a↦a′)  (⇓-⊕ a′⇓m b⇓n)  = ⇓-⊕ (sound a↦a′ a′⇓m) b⇓n
  sound (↦-R b↦b′)  (⇓-⊕ ⇓-ℕ b′⇓n)  = ⇓-⊕ ⇓-ℕ (sound b↦b′ b′⇓n)
\end{code}
%}}}%

\section{Stack Machines and Their Semantics}

%{{{%
%if False
\begin{code}
open import Data.List

data Instruction : Set where
  PUSH : ℕ → Instruction
  ADD : Instruction

data Machine : Set where
  ⟨_,_⟩ : List Instruction → List ℕ → Machine
\end{code}

\begin{code}
infix 3 _↣_
data _↣_ : Rel Machine _ where
  ↣-PUSH : ∀ {m c σ} → ⟨ PUSH m ∷ c , σ ⟩ ↣ ⟨ c , m ∷ σ ⟩
  ↣-ADD : ∀ {m n c σ} → ⟨ ADD ∷ c , n ∷ m ∷ σ ⟩ ↣ ⟨ c , m + n ∷ σ ⟩

infix 3 _↣⋆_
_↣⋆_ : Rel Machine _
_↣⋆_ = Star _↣_
\end{code}
%endif
%}}}%

%{{{%
%if False
\begin{code}
compile : Expression → List Instruction → List Instruction
compile (# m) c = PUSH m ∷ c
compile (a ⊕ b) c = compile a (compile b (ADD ∷ c))
\end{code}
%endif
%}}}%

%{{{%
%if False
\begin{code}
infix 3 _↣⋆#_
_↣⋆#_ : REL Expression ℕ _
e ↣⋆# m = ∀ {c σ} → ⟨ compile e c , σ ⟩ ↣⋆ ⟨ c , m ∷ σ ⟩

-- big→machine : ∀ {e m} → e ⇓ m → e ↣⋆# m
-- big→machine ⇓-ℕ = ↣-PUSH ◅ ε
-- big→machine (⇓-⊕ a⇓m b⇓n) = big→machine a⇓m ◅◅ big→machine b⇓n ◅◅ ↣-ADD ◅ ε

-- small→machine : ∀ {e m} → e ↦⋆# m → e ↣⋆# m
-- small→machine = big→machine ∘ small→big
\end{code}
%endif
%}}}%

%{{{%
%if False
\begin{code}
-- machine≡small : ∀ e {m m′} → e ↣⋆# m → e ↦⋆# m′ → m ≡ m′
-- machine≡small (# m) ∀cσ∶e↣⋆m (() ◅ _)
-- machine≡small (# m) ∀cσ∶e↣⋆m ε with ∀cσ∶e↣⋆m {[]} {[]}
-- machine≡small (# m) ∀cσ∶e↣⋆m ε | ↣-PUSH ◅ ε = ≡.refl
-- machine≡small (# m) ∀cσ∶e↣⋆m ε | ↣-PUSH ◅ () ◅ _
-- machine≡small (a ⊕ b) ∀cσ∶e↣⋆m e↦⋆m′ = {!!}
\end{code}
%endif
%}}}%

%{{{%
%if False
%\begin{code}
-- ∀ {i c σ σ′} → 


import Data.List.Properties as ListProp

-- x≢x∷xs : ∀ {A : Set} {x : A} {xs : List A} → xs ≢ x ∷ xs
-- x≢x∷xs xs≡x∷xs with left-identity-unique [ _ ] xs≡x∷xs
-- x≢x∷xs xs≡x∷xs | ()

x∷xs≢xs : ∀ {A : Set} {x : A} {xs : List A} → x ∷ xs ≢ xs
x∷xs≢xs {xs = []} ()
x∷xs≢xs {xs = x′ ∷ xs′} x∷xs≡xs = x∷xs≢xs (proj₂ (ListProp.∷-injective x∷xs≡xs))

-- foo : ∀ {c σ c′ σ′} → ⟨ c , σ ⟩ ↣ ⟨ c′ , σ′ ⟩ → c′ ≢ c
-- foo ↣-PUSH = x≢x∷xs
-- foo ↣-ADD = x≢x∷xs

open import Data.Empty

-- boo : ∀ {A : Set} {i j k : A} {T : Rel A _} {x : T i j} {xs : Star T j k} →
--   x ◅ xs ≇ xs
-- boo {xs = ε} ()
-- boo {xs = x′ ◅ xs} foo = boo (proj₂ (◅-injective foo))

-- moo : ∀ {A : Set} {i j k : A} {T : Rel A _} {jTk : T j k} {xs : Star T i j} → xs ◅◅ jTk ◅ ε ≇ (_ : ε)
-- moo {xs = ε} ()
-- moo {xs = x ◅ xs} ()

-- moo : ∀ {xs tr} → xs ◅◅ tr ◅ ε ≇ ε
-- moo cow = {!!}

-- bar : ∀ {c σ} → (tr : ⟨ c , σ ⟩ ↣⋆ ⟨ c , σ ⟩) → tr ≡ ε
-- bar ε = ≡.refl
-- bar (x ◅ xs) = {!!}

-- bar ε = inj₁ ≡.refl
-- bar (↣-PUSH ◅ xs) = {!!}
-- bar (↣-ADD ◅ xs) with bar (xs ◅◅ ↣-ADD ◅ ε)
-- bar (↣-ADD ◅ xs) | inj₁ cow = {!!}
-- bar (↣-ADD ◅ xs) | inj₂ cow = inj₂ cow

◅-view : ∀ {A : Set} {T : Rel A _} {i k : A} → i ≢ k → (s : Star T i k) →
  ∃ λ j → Σ (T i j) λ iTj → Σ (Star T j k) λ jT⋆k → s ≡ iTj ◅ jT⋆k
◅-view i≢k ε = ⊥-elim (i≢k ≡.refl)
◅-view i≢k (x ◅ xs) = _ & x & xs & ≡.refl

↣-wf : ∀ {c σ u} → ⟨ c , σ ⟩ ↣ u →
  ∃ λ i → ∃ λ c′ → ∃ λ σ′ →
    c ≡ i ∷ c′ × u ≡ ⟨ c′ , σ′ ⟩
↣-wf ↣-PUSH = PUSH _ & _ & _ & ≡.refl & ≡.refl
↣-wf ↣-ADD = ADD & _ & _ & ≡.refl & ≡.refl

-- infix 3 _>∷_ _>∷⋆_
-- data _>∷_ {A : Set} : List A → List A → Set where
--   +∷ : ∀ {x xs} → x ∷ xs >∷ xs

-- _>∷⋆_ : ∀ {A : Set} → List A → List A → Set
-- _>∷⋆_ = Star _>∷_

-- >∷-injective : ∀ {A} {x y : A} {xs ys} → x ∷ xs >∷ y ∷ ys → xs ≡ y ∷ ys × xs >∷ ys
-- >∷-injective +∷ = ≡.refl & +∷

-- code : Machine → List Instruction
-- code ⟨ c , _ ⟩ = c

-- f : _↣_ =[ code ]⇒ _>∷_
-- f ↣-PUSH = +∷
-- f ↣-ADD = +∷

-- g : _↣⋆_ =[ code ]⇒ _>∷⋆_
-- g = gmap code f

-- cow : ∀ {A} {xs : List A} → xs >∷ xs → ⊥
-- cow {A} {[]} ()
-- cow {xs = x′ ∷ xs} foo = cow (proj₂ (>∷-injective foo))

-- elim : ∀ {A} {c c′ : List A} → c >∷⋆ c′ → c ≡ c′
-- elim ε = ≡.refl
-- elim (x ◅ xs) = {!!}

-- elim foo ε = cow foo
-- elim foo (x ◅ xs) = elim x (xs ◅◅ foo ◅ ε)

⟨,⟩-injective : ∀ {c σ c′ σ′} → ⟨ c , σ ⟩ ≡ ⟨ c′ , σ′ ⟩ → c ≡ c′ × σ ≡ σ′
⟨,⟩-injective ≡.refl = ≡.refl & ≡.refl


-- wat : ∀ {c i σ σ′} → ⟨ c , σ ⟩ ≢ ⟨ i ∷ c , σ′ ⟩
-- wat {[]} ()
-- wat {x ∷ xs} foo with proj₁ (⟨,⟩-injective foo)
-- wat {x ∷ xs} foo | c≡i∷c = x≢x∷xs c≡i∷c

-- -- no : ∀ {c σ c′ σ′} → ⟨ c , σ ⟩ ↣⋆ ⟨ c′ ++ c , σ′ ⟩ → ⊥
-- -- no foo = {!!}

-- absurd : ∀ {c σ i σ′} → ⟨ c , σ ⟩ ↣⋆ ⟨ i ∷ c , σ′ ⟩ → ⊥
-- absurd cow with ◅-view wat cow
-- absurd ._ | u & c↣u & u↣⋆ic & ≡.refl with ↣-wf c↣u
-- absurd ._ | ._ & c↣u & u↣⋆ic & ≡.refl | j & c′ & σ′ & ≡.refl & ≡.refl = {!!}

-- -- ↣⋆→≡ : ∀ {c σ σ″} → ⟨ c , σ ⟩ ↣⋆ ⟨ c , σ″ ⟩ → σ ≡ σ″
-- -- ↣⋆→≡ ε = ≡.refl
-- -- ↣⋆→≡ (↣-PUSH ◅ xs) = proj₂ (∷-injective (↣⋆→≡ (xs ◅◅ ↣-PUSH ◅ ε)))
-- -- ↣⋆→≡ (↣-ADD ◅ xs) = {!xs ◅◅ ↣-ADD ◅ ε!}

-- -- with ↣-wf x
-- -- ↣⋆→≡ (x ◅ xs) | i & c′ & σ′ & ≡.refl & ≡.refl = {!!}

-- -- ⊥-elim (absurd xs)


c↣⋆c→σ≡σ : ∀ {c σ σ′} → ⟨ c , σ ⟩ ↣⋆ ⟨ c , σ′ ⟩ → σ ≡ σ′
c↣⋆c→σ≡σ ε = ≡.refl
c↣⋆c→σ≡σ (x ◅ xs) with ↣-wf x
c↣⋆c→σ≡σ (x ◅ xs) | i & c′ & σ′ & ≡.refl & ≡.refl = {!!}

ys++xs≢xs : ∀ {A : Set} {xs} (ys : List A) → ys ≢ [] → ys ++ xs ≢ xs
ys++xs≢xs ys ¬ys = ¬ys ∘ ListProp.left-identity-unique ys ∘ ≡.sym

∷≢[] : ∀ {A : Set} {x : A} {xs} → x ∷ xs ≢ []
∷≢[] ()

-- x₀₁₂∷xs≢xs [] ()
-- x₀₁₂∷xs≢xs (x ∷ xs) eq = {!!}

recon : ∀ e {m} {c′ σ′} → ⟨ compile e c′ , σ′ ⟩ ↣⋆ ⟨ c′ , m ∷ σ′ ⟩ → e ↣⋆# m
recon (# n) e↣⋆m with ◅-view (ys++xs≢xs [ _ ] ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) e↣⋆m
recon (# n) ._ | ._ & ↣-PUSH & n↣⋆m & ≡.refl with c↣⋆c→σ≡σ n↣⋆m
recon (# n) ._ | ._ & ↣-PUSH & n↣⋆m & ≡.refl | ≡.refl = ↣-PUSH ◅ ε

recon (# m ⊕ # n) m⊕n↣⋆m+n with ◅-view (ys++xs≢xs (_ ∷ _ ∷ _ ∷ []) ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) m⊕n↣⋆m+n
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & foo & ≡.refl with ◅-view (ys++xs≢xs (_ ∷ _ ∷ []) ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) foo
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-PUSH & foo & ≡.refl with ◅-view (ys++xs≢xs (_ ∷ []) ∷≢[] ∘ proj₁ ∘ ⟨,⟩-injective) foo
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-ADD & foo & ≡.refl with c↣⋆c→σ≡σ foo
recon (# m ⊕ # n) ._ | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-PUSH & ._ & ≡.refl | ._ & ↣-ADD & foo & ≡.refl | ≡.refl = ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ ε

recon (# m ⊕ (b₀ ⊕ b₁)) cow = {!!}
recon ((a₀ ⊕ a₁) ⊕ b) cow = {!!}

-- -- foo : ∀ {m n e} → # m ⊕ e ↣⋆# m + n → e ↣⋆# n
-- -- foo cow {c} {σ} with cow {[]} {[]}
-- -- foo cow {c} {σ} | ↣-PUSH ◅ xs = {!!}

-- -- decomp-⊕ : ∀ a b m+n → a ⊕ b ↣⋆# m+n → ∃₂ λ m n → a ↣⋆# m × b ↣⋆# n × m + n ≡ m+n
-- -- decomp-⊕ (# m) (# n) m+n a⊕b↣⋆m+n with a⊕b↣⋆m+n {[]} {[]}
-- -- decomp-⊕ (# m) (# n) m+n a⊕b↣⋆m+n | ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ () ◅ _
-- -- decomp-⊕ (# m) (# n) .(m + n) a⊕b↣⋆m+n | ↣-PUSH ◅ ↣-PUSH ◅ ↣-ADD ◅ ε = m & n & (λ {c} {σ} → ↣-PUSH ◅ ε) & (λ {c} {σ} → ↣-PUSH ◅ ε) & ≡.refl
-- -- decomp-⊕ (# m) (b₀ ⊕ b₁) m+n a⊕b↣⋆m+n with a⊕b↣⋆m+n {[]} {[]}
-- -- decomp-⊕ (# m) (b₀ ⊕ b₁) m+n a⊕b↣⋆m+n | foo with decomp-⊕ b₀ b₁ {!!} {!!}
-- -- decomp-⊕ (# m) (b₀ ⊕ b₁) m+n a⊕b↣⋆m+n | ↣-PUSH ◅ xs | cow = {!!}
-- -- decomp-⊕ (a₀ ⊕ a₁) b m+n a⊕b↣⋆m+n = {!!}

-- -- ⟨ PUSH m ∷ compile (b₀ ⊕ b₁) (ADD ∷ c) , σ ⟩ ↣⋆ ⟨ c , m+n ∷ σ ⟩  →  ⟨ compile (b₀ ⊕ b₁) c , σ ⟩ ↣⋆ ⟨ c , m+n - m ∷ σ ⟩

-- -- decomp : ∀ e c σ → ∃ λ m → ⟨ compile e c , σ ⟩ ↣⋆ ⟨ c , m ∷ σ ⟩
-- -- decomp (# m) c σ = m & ↣-PUSH ◅ ε
-- -- decomp (a ⊕ b) c σ with decomp a (compile b (ADD ∷ c)) σ
-- -- decomp (a ⊕ b) c σ | m & a↣⋆m with decomp b (ADD ∷ c) (m ∷ σ)
-- -- decomp (a ⊕ b) c σ | m & a↣⋆m | n & b↣⋆n = m + n & a↣⋆m ◅◅ b↣⋆n ◅◅ ↣-ADD ◅ ε

machine→small : ∀ e {m} → e ↣⋆# m → e ↦⋆# m
machine→small e ∀cσ∶e↣⋆m with ∀cσ∶e↣⋆m {[]} {[]}
machine→small (# m) ∀cσ∶e↣⋆m | ↣-PUSH ◅ ε = ε
machine→small (# m) ∀cσ∶e↣⋆m | ↣-PUSH ◅ () ◅ _
machine→small (a ⊕ b) ∀cσ:a⊕b↣⋆m | a⊕b↣⋆m = {!!}


-- --   gmap (λ a′ → a′ ⊕ b) ↦-L (machine→small a {!cow!}) ◅◅
-- --   gmap (λ b′ → # _ ⊕ b′) ↦-R (machine→small b {!!}) ◅◅ ↦-ℕ ◅ ε where
-- --   cow : ∀ c σ → {!!}
-- --   cow c σ = ∀cσ:e↣⋆m {compile a (compile b (ADD ∷ c))} {σ}
-- --   cow : ∀ a m → a ↣⋆# m
-- --   cow a m {c} {σ} with decomp a (compile b c) σ
-- --   cow a m {c} {σ} | m′ & a↣⋆m = {!!}

-- -- foo : ∀ {a m b n} → a ⊕ b ↣⋆# m + n → a ↣⋆# m × b ↣⋆# n
-- -- foo abmn = {!!}

-- -- machine→big : ∀ e m → e ↣⋆# m → e ⇓ m
-- -- machine→big (# m′) m ∀cσ∶e↣⋆m with ∀cσ∶e↣⋆m {[]} {[]}
-- -- machine→big (# m′) m ∀cσ∶e↣⋆m | ↣-PUSH ◅ () ◅ _
-- -- machine→big (# m) .m ∀cσ∶e↣⋆m | ↣-PUSH ◅ ε = ⇓-ℕ
-- -- machine→big (a ⊕ b) m ∀cσ∶e↣⋆m = {!!}

-- -- with decomp a (compile ) | decomp b
-- -- machine→small (a ⊕ b) ∀cσ:e↣⋆m | x ◅ xs | foo | bar = {!!}

-- -- machine→small : ∀ {e m} → ⟨ compile e [] , [] ⟩ ↣⋆ ⟨ [] , m ∷ [] ⟩ → e ↦⋆# m
-- -- machine→small {# m} .{m} (↣-PUSH ◅ ε) = ε
-- -- machine→small {# m} (↣-PUSH ◅ () ◅ _)
-- -- machine→small {a ⊕ b} (a↣a′ ◅ a′↣⋆m) = {!!}
%\end{code}
%endif
%}}}%


% vim: ft=tex:

