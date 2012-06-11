%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Transaction.lagda
\end{comment}
%endif

%if False
\begin{code}
module Language where

open import Common
open import Heap
open import Logs
open import Transaction
\end{code}
%endif

%if False
\begin{code}
infix 7 #_
infix 6 _⊕_
\end{code}
%endif

\section{The Atomic Language}

\subsection{Syntax}

%format #_ = "\cons{\texttt{\#}\anonymous}"
%format # = "\cons{\texttt{\#}}"
%format _⊕_ = "\cons{\anonymous{\oplus}\anonymous}"
%format ⊕ = "\infix{\cons{\oplus}}"
%format read = "\cons{read}"
%format write = "\cons{write}"
%format fork = "\cons{fork}"
%format atomic = "\cons{atomic}"
%format Expression = "\type{Expression}"
%format Expression′ = "\type{Expression\Prime}"
%{
%format Tran = "\type{Tran}"
%format Proc = "\type{Proc}"
For the Atomic language, we migrate to a two-level syntax in a similar
manner to the |Tran| and |Proc| types of chapter \ref{ch:model}. On the
transaction level, we extend our base language of natural numbers and
addition with the |read| and |write| keywords for manipulating transactional
variables,
%}
\begin{code}
data Expression′ : Set where
  #_     : (m : ℕ) → Expression′
  _⊕_    : (a b : Expression′) → Expression′
  read   : (v : Variable) → Expression′
  write  : (v : Variable) (e : Expression′) → Expression′
\end{code}
while the `IO' level is extended with an |atomic| keyword that runs
a transaction of type |Expression′|\footnote{Throughout this chapter,
I adopt the convention of using a $\type{\Prime}$ to identify types that are
associated with the transaction level of the Atomic language.}:
\savecolumns
\begin{code}
data Expression : Set where
  #_ : (m : ℕ) → Expression
  _⊕_ : (a b : Expression) → Expression
  atomic : (e : Expression′) → Expression
\end{code}

\noindent Conspicuously missing is the presence of the |fork| construct
dealt with in the last chapter, and as originally modelled in chapter
\ref{ch:model}:
\restorecolumns
\begin{spec}
  fork : (e : Expression) → Expression
\end{spec}
As it turned out, the presence of threads made the proof unmanageable, so
I've instead taken a more simplified approach. Rather than go via a compiler
and virtual machine, we instead compare two semantics for the same language:
one with a stop-the-world rule for |atomic| versus another with log-based
transactions.

\input{Atomic/Heap.lagda.tex}

\subsection{Stop-the-World Semantics}

%if False
\begin{code}
infix 3 _↦′_
\end{code}
%endif

%format _↦′_ = "\type{\anonymous{\mapsto}\Prime\!\anonymous}"
%format ↦′ = "\infix{\type{{\mapsto}\Prime}}"
%format ↦′-ℕ = "\cons{{\mapsto}\Prime\text-{\oplus}\mathbb{N}}"
%format ↦′-L = "\cons{{\mapsto}\Prime\text-{\oplus}L}"
%format ↦′-R = "\cons{{\mapsto}\Prime\text-{\oplus}R}"
%format ↦′-read = "\cons{{\mapsto}\Prime\text-read}"
%format ↦′-writeE = "\cons{{\mapsto}\Prime\text-write_E}"
%format ↦′-writeℕ = "\cons{{\mapsto}\Prime\text-write_{\mathbb{N}}}"
%format a↦a′ = "a{\mapsto}a\Prime{}"
%format b↦b′ = "b{\mapsto}b\Prime{}"
%format e↦e′ = "e{\mapsto}e\Prime{}"
Now we have enough machinery to describe the high-level stop-the-world
semantics for the Atomic language. Due to the two-level stratification of
the language, this involves two separate transitions for |Expression′| and
|Expression|. The first of these is |_↦′_|, defined on the transaction level
between pairs of |Heap|s and |Expression′|s. We begin with the familiar
rules for left-biased addition:
\savecolumns
\begin{code}
data _↦′_ : Rel (Heap × Expression′) where
  ↦′-ℕ : ∀ {h m n} →
    h , # m ⊕ # n  ↦′  h , # (m + n)
  ↦′-L : ∀ {h h′ a a′} b →
    (a↦a′ :  h , a      ↦′  h′ , a′)  →
             h , a ⊕ b  ↦′  h′ , a′ ⊕ b
  ↦′-R : ∀ {h h′ b b′} m →
    (b↦b′ :  h ,        b  ↦′  h′ ,        b′)  →
             h , # m ⊕  b  ↦′  h′ , # m ⊕  b′

  ↦′-read : ∀ {h} v →
    h , read v  ↦′  h , # Vec.lookup v h
  ↦′-writeℕ : ∀ {h v m} →
    h , write v (# m) ↦′ h « v »≔ m , # m
  ↦′-writeE : ∀ {h e h′ e′ v} →
    (e↦e′ :  h ,          e  ↦′  h′ ,          e′)  →
             h , write v  e  ↦′  h′ , write v  e′
\end{code}
Here the |↦′-read| and |↦′-writeℕ| rules refer directly to the heap, while
|↦′-writeE| effects the reduction of the sub-expression argument to |write|.
%if False
\begin{code}
infix 3 _↦′⋆_
\end{code}
%endif
%format _↦′⋆_ = "\type{\anonymous{\mapsto}^\star\anonymous}"
%format ↦′⋆ = "\infix{\type{{\mapsto}^\star}}"
We write |_↦′⋆_| for the reflexive, transitive closure of |_↦′_|, defined
using the |Star| type:
\begin{code}
_↦′⋆_ : Rel (Heap × Expression′)
_↦′⋆_ = Star _↦′_
\end{code}

\noindent On the `IO' level, transitions are labelled with a choice of
actions,
%format Action = "\type{Action}"
%format τ = "\cons{\tau}"
%format ⊞ = "\cons{\boxplus}"
%format ☢ = "\cons{\text\Radioactivity}"
\begin{code}
data Action : Set where
  τ {-"\;"-} ⊞ {-"\;"-} ☢ : Action
\end{code}
where |τ| is the silent action, |⊞| corresponds to the addition operation,
and |☢| indicates the successful completion of a transaction.

%if False
\begin{code}
infix 3 _▹_↦_
\end{code}
%endif

%format _▹_↦_ = "\type{\anonymous{\triangleright}\anonymous{\mapsto}\anonymous}"
%format ▹ = "\infix{\type{\triangleright}}"
%format ↦ = "\infix{\type{\mapsto}}"
%format ↦-ℕ = "\cons{{\mapsto}\text-{\oplus}\mathbb{N}}"
%format ↦-L = "\cons{{\mapsto}\text-{\oplus}L}"
%format ↦-R = "\cons{{\mapsto}\text-{\oplus}R}"
%format ↦-atomic = "\cons{{\mapsto}\text-atomic}"
%format ↦-mutate = "\cons{{\mapsto}\text-mutate}"
%format e↦⋆m = "e{\mapsto}^{\star}m"
The labelled transition is defined as follows, with the first three rules
corresponding to the familiar left-biased addition:
\savecolumns
\begin{code}
data _▹_↦_ : Action → Rel (Heap × Expression) where
  ↦-ℕ : ∀ {h m n} →
    ⊞ ▹ h , # m ⊕ # n  ↦  h , # (m + n)
  ↦-R : ∀ {α h h′ b b′} m →
    (b↦b′ :   α ▹ h ,        b ↦ h′ ,        b′)  →
              α ▹ h , # m ⊕  b ↦ h′ , # m ⊕  b′
  ↦-L : ∀ {α h h′ a a′} b →
    (a↦a′ :   α ▹ h , a      ↦ h′ , a′)  →
              α ▹ h , a ⊕ b  ↦ h′ , a′ ⊕ b
\end{code}
The |↦-atomic| rule implements a stop-the-world semantics for |atomic|
blocks by taking a reduction sequence |e↦⋆m| on the transaction level, and
encapsulating it in a single step:
\restorecolumns
\begin{code}
  ↦-atomic : ∀ {h e h′ m} →
    (e↦⋆m :  h ,         e ↦′⋆  h′ , # m)  →
        ☢ ▹  h , atomic  e ↦    h′ , # m
  ↦-mutate : ∀ h′ {h e} →
    τ ▹ h , atomic e  ↦  h′ , atomic e
\end{code}
Since there are no explicit threads in the Atomic language, we introduce
a silent |↦-mutate| rule to allow the heap to change at any time. It is
limited to contexts where the expression is of the form |atomic e|, but this
is purely to avoid complicating unrelated parts of the proof. We shall later
examine how a corresponding rule in the log-based semantics allows the heap
to mutate during a transaction.


\subsection{Transaction Logs}

\input{Atomic/Logs.lagda.tex}

%if False
\begin{code}
TState : Set
TState = Maybe (Expression′ × Logs)
\end{code}
%endif

\subsection{Log-based Semantics}

%if False
\begin{code}
infix 3 _⊢_↣′_
\end{code}
%endif

%if False
\begin{code}
data _⊢_↣′_ (h : Heap) : Rel (Logs × Expression′) where
  ↣′-ℕ : ∀ {l m n} →
    h ⊢  l , # m ⊕ # n  ↣′  l , # (m + n)
  ↣′-R : ∀ {l b l′ b′} m →
    (b↣b′ : h ⊢  l ,       b  ↣′  l′ ,       b′)  →
            h ⊢  l , # m ⊕ b  ↣′  l′ , # m ⊕ b′
  ↣′-L : ∀ {l a l′ a′} b →
    (a↣a′ : h ⊢  l , a      ↣′  l′ , a′)  →
            h ⊢  l , a ⊕ b  ↣′  l′ , a′ ⊕ b
\end{code}
%endif

%if False
\begin{code}
  ↣′-read : ∀ l v → let l′m = Read h l v in
    h ⊢  l , read v  ↣′  fst l′m , # snd l′m
  ↣′-writeℕ : ∀ {l v m} →
    h ⊢  l , write v (# m)  ↣′  Write l v m , # m
  ↣′-writeE : ∀ {l e l′ e′ v} →
    (e↣e′ : h ⊢  l ,         e  ↣′  l′ ,         e′)  →
            h ⊢  l , write v e  ↣′  l′ , write v e′
\end{code}
%endif

%if False
\begin{code}
-- sequence of ↣′ transitions with the same heap
infix 3 _⊢_↣′⋆_
_⊢_↣′⋆_ : Heap → Rel (Logs × Expression′)
h ⊢ l , e ↣′⋆ l′ , e′ = Star (_⊢_↣′_ h) (l , e) (l′ , e′)
\end{code}
%endif

%if False
\begin{code}
infix 3 _▹_↣_
data _▹_↣_ : Action → Rel (Heap × TState × Expression) where
  ↣-ℕ : ∀ {h m n} →
    ⊞ ▹  h , ○ , # m ⊕ # n  ↣  h , ○ , # (m + n)
  ↣-R : ∀ {α h t b h′ t′ b′} m →
    (b↣b′ : α ▹  h , t ,       b  ↣  h′ , t′ ,       b′)  →
            α ▹  h , t , # m ⊕ b  ↣  h′ , t′ , # m ⊕ b′
  ↣-L : ∀ {α h t a h′ t′ a′} b →
    (a↣a′ : α ▹  h , t , a      ↣  h′ , t′ , a′)  →
            α ▹  h , t , a ⊕ b  ↣  h′ , t′ , a′ ⊕ b
\end{code}
%endif

%if False
\begin{code}
  ↣-begin : ∀ {h e} →
    τ ▹  h , ○ , atomic e  ↣  h , ● (e , ∅) , atomic e
  ↣-step : ∀ {h R l e l′ e′} →
    (e↣e′ : h ⊢  l , e  ↣′  l′ , e′)  →
    τ ▹ h , ● (R , l) , atomic e  ↣  h , ● (R , l′) , atomic e′
  ↣-mutate : ∀ h′ {h t e} →
    τ ▹ h , ● t , atomic e  ↣  h′ , ● t , atomic e
  ↣-abort : ∀ {h R l m} → (¬cons : ¬ Consistent h l) →
    τ ▹  h , ● (R , l) , atomic (# m)  ↣  h , ● (R , ∅) , atomic R
  ↣-commit : ∀ {h R l m} → (cons : Consistent h l) →
    ☢ ▹  h , ● (R , l) , atomic (# m)  ↣  Update h l , ○ , # m
\end{code}
%endif

\subsection{Properties?}

\input{Atomic/Transaction.lagda.tex}

%if False
\begin{code}
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
\end{code}
%endif

%if False
\begin{code}
↣′⋆-Consistent : ∀ {h l′ e′ l e} →
  h  ⊢ l , e ↣′⋆ l′ , e′ →
  Consistent h l ⇔ Consistent h l′
↣′⋆-Consistent {h} {l′} {e′} = Star.gfold (Consistent h ∘ fst) _⇔_
  (λ e↣′e′ l⇔l′ → l⇔l′ ⟨∘⟩ ↣′-Consistent e↣′e′) {k = l′ , e′} Equivalence.id
\end{code}
%endif

\subsection{Combined}

%if False
\begin{code}
infix 7 ↣:_
\end{code}
%endif

%if False
\begin{code}
-- Combined Expressions; choice of big or small-step semantics
data Combined : Set where
  ↦: : Combined
  ↣:_ : (t : TState) → Combined
\end{code}
%endif

%if False
\begin{code}
infix 3 _▹_↠_
\end{code}
%endif

%if False
\begin{code}
data _▹_↠_ (α : Action) : Rel (Heap × Combined × Expression) where
  ↠-↦ : ∀ {h e h′ e′} →
    (e↦e′ : α ▹  h ,      e  ↦  h′ ,      e′)  →
            α ▹  h , ↦: , e  ↠  h′ , ↦: , e′
  ↠-↣ : ∀ {h t e h′ t′ e′} →
    (e↣e′ : α ▹  h ,    t , e  ↣  h′ ,    t′ , e′)  →
            α ▹  h , ↣: t , e  ↠  h′ , ↣: t′ , e′
\end{code}
%endif

%if False
\begin{code}
infix 3 _↠⋆_
_↠⋆_ : Rel (Heap × Combined × Expression)
_↠⋆_ = Star (_▹_↠_ τ)
\end{code}
%endif

%if False
\begin{code}
infix 3 _▹_⤇_
\end{code}
%endif

%if False
\begin{code}
record _▹_⤇_ (α : Action) (x x″ : Heap × Combined × Expression) : Set where
  constructor ⤇:
  field
    {h′} : Heap
    {c′} : Combined
    {e′} : Expression
    α≢τ : α ≢ τ
    e↠⋆e′ : x ↠⋆ h′ , c′ , e′
    e′↠e″ : α ▹ h′ , c′ , e′ ↠ x″
\end{code}
%endif

% vim: ft=tex fo-=m fo-=M:
