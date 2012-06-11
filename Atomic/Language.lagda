module Language where

open import Common
open import Heap public


-- Expressions for IO and STM

infix 7 #_
infix 6 _⊕_
data Expression′ : Set where
  #_ : (m : ℕ) → Expression′
  _⊕_ : (a b : Expression′) → Expression′
  read : (v : Variable) → Expression′
  write : (v : Variable) (e : Expression′) → Expression′

data Expression : Set where
  #_ : (m : ℕ) → Expression
  _⊕_ : (a b : Expression) → Expression
  atomic : (e : Expression′) → Expression


-- Combined Expressions; choice of big or small-step semantics

Transaction : Set
Transaction = Maybe (Expression′ × Logs)

infix 7 ↣:_
data Combined : Set where
  ↦: : Combined
  ↣:_ : (t : Transaction) → Combined

data Action : Set where
  τ : Action
  ⊞ : Action
  ☢ : Action

infix 3 _↦′_
data _↦′_ : Rel (Heap × Expression′) where
  ↦′-ℕ : ∀ {h m n} →
    h , # m ⊕ # n  ↦′  h , # (m + n)
  ↦′-R : ∀ {h h′ b b′} m →
    (b↦b′ : h ,       b  ↦′  h′ ,       b′)  →
            h , # m ⊕ b  ↦′  h′ , # m ⊕ b′
  ↦′-L : ∀ {h h′ a a′} b →
    (a↦a′ : h , a      ↦′  h′ , a′)  →
            h , a ⊕ b  ↦′  h′ , a′ ⊕ b

  ↦′-read : ∀ {h} v →
    h , read v  ↦′  h , # Vec.lookup v h
  ↦′-writeE : ∀ {h e h′ e′ v} →
    (e↦e′ : h ,         e  ↦′  h′ ,         e′)  →
            h , write v e  ↦′  h′ , write v e′
  ↦′-writeℕ : ∀ {h v m} →
    h , write v (# m)  ↦′  h [ v ]≔ m , # m

infix 3 _↦′⋆_
_↦′⋆_ : Rel (Heap × Expression′)
_↦′⋆_ = Star _↦′_

infix 3 _⊢_↦_
data _⊢_↦_ : Action → Rel (Heap × Expression) where
  ↦-ℕ : ∀ {h m n} →
    ⊞ ⊢ h , # m ⊕ # n  ↦  h , # (m + n)
  ↦-R : ∀ {α h h′ b b′} m →
    (b↦b′ : α ⊢  h ,       b  ↦  h′ ,       b′)  →
            α ⊢  h , # m ⊕ b  ↦  h′ , # m ⊕ b′
  ↦-L : ∀ {α h h′ a a′} b →
    (a↦a′ : α ⊢  h , a      ↦  h′ , a′)  →
            α ⊢  h , a ⊕ b  ↦  h′ , a′ ⊕ b

  ↦-mutate : ∀ h′ {h e} →
    τ ⊢ h , atomic e  ↦  h′ , atomic e
  ↦-atomic : ∀ {h e h′ m} →
    (e↦⋆# : h ,        e  ↦′⋆  h′ , # m)  →
       ☢ ⊢  h , atomic e  ↦    h′ , # m

infix 3 _⊢_↣′_
data _⊢_↣′_ (h : Heap) : Rel (Logs × Expression′) where
  ↣′-ℕ : ∀ {l m n} →
    h ⊢  l , # m ⊕ # n  ↣′  l , # (m + n)
  ↣′-R : ∀ {l b l′ b′} m →
    (b↣b′ : h ⊢  l ,       b  ↣′  l′ ,       b′)  →
            h ⊢  l , # m ⊕ b  ↣′  l′ , # m ⊕ b′
  ↣′-L : ∀ {l a l′ a′} b →
    (a↣a′ : h ⊢  l , a      ↣′  l′ , a′)  →
            h ⊢  l , a ⊕ b  ↣′  l′ , a′ ⊕ b

  ↣′-read : ∀ l v → let l′m = Read h l v in
    h ⊢  l , read v  ↣′  fst l′m , # snd l′m
  ↣′-writeE : ∀ {l e l′ e′ v} →
    (e↣e′ : h ⊢  l ,         e  ↣′  l′ ,         e′)  →
            h ⊢  l , write v e  ↣′  l′ , write v e′
  ↣′-writeℕ : ∀ {l v m} →
    h ⊢  l , write v (# m)  ↣′  Write l v m , # m

-- ↣′ preserves consistency
↣′-Consistent : ∀ {h l e l′ e′} →
  h ⊢  l , e  ↣′  l′ , e′ →
  Consistent h l ⇔ Consistent h l′
↣′-Consistent ↣′-ℕ = Equivalence.id
↣′-Consistent (↣′-R m b↣b′) = ↣′-Consistent b↣b′
↣′-Consistent (↣′-L b a↣a′) = ↣′-Consistent a↣a′
↣′-Consistent (↣′-read l v) = Read-Consistent′ l v
↣′-Consistent (↣′-writeE e↣e′) = ↣′-Consistent e↣e′
↣′-Consistent ↣′-writeℕ = Equivalence.id

-- sequence of ↣′ transitions with the same heap
infix 3 _⊢_↣′⋆_
_⊢_↣′⋆_ : Heap → Rel (Logs × Expression′)
h ⊢ l , e ↣′⋆ l′ , e′ = Star (_⊢_↣′_ h) (l , e) (l′ , e′)

↣′⋆-Consistent : ∀ {h l′ e′ l e} →
  h  ⊢ l , e ↣′⋆ l′ , e′ →
  Consistent h l ⇔ Consistent h l′
↣′⋆-Consistent {h} {l′} {e′} = ⋆.gfold (Consistent h ∘ fst) _⇔_
  (λ e↣′e′ l⇔l′ → l⇔l′ ⟨∘⟩ ↣′-Consistent e↣′e′) {k = l′ , e′} Equivalence.id

infix 3 _⊢_↣_
data _⊢_↣_ : Action → Rel (Heap × Transaction × Expression) where
  ↣-ℕ : ∀ {h m n} →
    ⊞ ⊢  h , ○ , # m ⊕ # n  ↣  h , ○ , # (m + n)
  ↣-R : ∀ {α h t b h′ t′ b′} m →
    (b↣b′ : α ⊢  h , t ,       b  ↣  h′ , t′ ,       b′)  →
            α ⊢  h , t , # m ⊕ b  ↣  h′ , t′ , # m ⊕ b′
  ↣-L : ∀ {α h t a h′ t′ a′} b →
    (a↣a′ : α ⊢  h , t , a      ↣  h′ , t′ , a′)  →
            α ⊢  h , t , a ⊕ b  ↣  h′ , t′ , a′ ⊕ b

  ↣-begin : ∀ {h e} →
    τ ⊢  h , ○ , atomic e  ↣  h , ● (e , ∅) , atomic e
  ↣-step : ∀ {h R l e l′ e′} →
    (e↣e′ : h ⊢  l , e  ↣′  l′ , e′)  →
    τ ⊢ h , ● (R , l) , atomic e  ↣  h , ● (R , l′) , atomic e′
  ↣-mutate : ∀ h′ {h t e} →
    τ ⊢ h , ● t , atomic e  ↣  h′ , ● t , atomic e
  ↣-abort : ∀ {h R l m} → (¬cons : ¬ Consistent h l) →
    τ ⊢  h , ● (R , l) , atomic (# m)  ↣  h , ● (R , ∅) , atomic R
  ↣-commit : ∀ {h R l m} → (cons : Consistent h l) →
    ☢ ⊢  h , ● (R , l) , atomic (# m)  ↣  Update h l , ○ , # m

infix 3 _⊢_↠_
data _⊢_↠_ (α : Action) : Rel (Heap × Combined × Expression) where
  ↠-↦ : ∀ {h e h′ e′} →
    (e↦e′ : α ⊢  h ,      e  ↦  h′ ,      e′)  →
            α ⊢  h , ↦: , e  ↠  h′ , ↦: , e′
  ↠-↣ : ∀ {h t e h′ t′ e′} →
    (e↣e′ : α ⊢  h ,    t , e  ↣  h′ ,    t′ , e′)  →
            α ⊢  h , ↣: t , e  ↠  h′ , ↣: t′ , e′

infix 3 _↠⋆_
_↠⋆_ : Rel (Heap × Combined × Expression)
_↠⋆_ = Star (_⊢_↠_ τ)

infix 3 _⊢_⤇_
record _⊢_⤇_ (α : Action) (x x″ : Heap × Combined × Expression) : Set where
  constructor ⤇:
  field
    {h′} : Heap
    {c′} : Combined
    {e′} : Expression
    α≢τ : α ≢ τ
    e↠⋆e′ : x ↠⋆ h′ , c′ , e′
    e′↠e″ : α ⊢ h′ , c′ , e′ ↠ x″
