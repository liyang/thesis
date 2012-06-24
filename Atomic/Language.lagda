%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
\end{comment}
%endif

%if False
\begin{code}
module Language where

open import Common
open import Heap
open import Logs
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

\noindent Note that we have not included the |fork| construct that spawns
additional threads as we did in chapters \ref{ch:model} and \ref{ch:fork}:
\restorecolumns
\begin{spec}
  fork : (e : Expression) → Expression
\end{spec}
The reason for this is that the presence of fork turned out to significantly
complicate the formal reasoning process, so we investigated a simpler
approach. First we replace concurrency with a `mutate' rule that can change
the heap at any time during a transaction, which simulates the worst
possible concurrent environment, in a similar manner to the worst-case
interrupt rule of \cite{hutton07-interruptions}. Secondly we replace the
compiler and virtual machine with a direct log-based transactional semantics
for the source language, which makes the proof more manageable.

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

  ↦′-read : ∀ h v →
    h , read v  ↦′  h , # h « v »
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
and |☢| indicates the successful completion of a transaction. These simple
observable actions make it possible to define a notion of bisimilarity for
the stop-the-world and log-based semantics, where there need not be
a one-to-one correspondence of transition rules on each side.

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
a silent |↦-mutate| rule to allow the heap to change at any time, which
reflects the idea that a concurrent thread may modify the heap while the
current thread is running. The above rule implements the worst possible case
in which the heap |h| can be replaced by a completely different heap |h′|.
For simplicity, note that |↦-mutate| is limited to contexts where the
expression is of the form |atomic e|, as this is the only construct that
interacts with the heap. We shall later examine how a corresponding rule in
the log-based semantics allows the heap to mutate during a transaction.


\input{Atomic/Logs.lagda.tex}


\subsection{Log-Based Semantics}

%if False
\begin{code}
infix 3 _⊢_↣′_
infix 3 _⊢_↣′⋆_
\end{code}
%endif

%format _⊢_↣′_ = "\type{\anonymous{\vdash}\anonymous{\rightarrowtail}\Prime\anonymous}"
%format ⊢ = "\infix{\type{\vdash}}"
%format ↣′ = "\infix{\type{\rightarrowtail\Prime}}"
%format ↣′-ℕ = "\cons{{\rightarrowtail}\Prime\text-{\oplus}\mathbb{N}}"
%format ↣′-L = "\cons{{\rightarrowtail}\Prime\text-{\oplus}L}"
%format ↣′-R = "\cons{{\rightarrowtail}\Prime\text-{\oplus}R}"
%format ↣′-read = "\cons{{\rightarrowtail}\Prime\text-read}"
%format ↣′-writeE = "\cons{{\rightarrowtail}\Prime\text-write_E}"
%format ↣′-writeℕ = "\cons{{\rightarrowtail}\Prime\text-write_{\mathbb{N}}}"
%format a↣a′ = "a{\rightarrowtail}a\Prime{}"
%format b↣b′ = "b{\rightarrowtail}b\Prime{}"
%format e↣e′ = "e{\rightarrowtail}e\Prime{}"
%format l′m = "l\Prime{}m"
The log-base semantics makes transitions between pairs of |Logs| and
|Expression′| rather than operating directly on a |Heap|. We can still read
from the heap, but it is never modified by the following rules. The first
three rules corresponding to left-biased addition should look familiar:
\savecolumns
\begin{code}
data _⊢_↣′_ {-"\;"-} (h : Heap) : Rel (Logs × Expression′) where
  ↣′-ℕ : ∀ {l m n} →
    h ⊢  l , # m ⊕ # n  ↣′  l , # (m + n)
  ↣′-R : ∀ {l b l′ b′} m →
    (b↣b′ :  h ⊢ l ,        b ↣′ l′ ,        b′)  →
             h ⊢ l , # m ⊕  b ↣′ l′ , # m ⊕  b′
  ↣′-L : ∀ {l a l′ a′} b →
    (a↣a′ :  h ⊢ l , a       ↣′ l′ , a′)  →
             h ⊢ l , a ⊕ b   ↣′ l′ , a′ ⊕ b
\end{code}
The |↣′-read| rule reduces a |read v| expression to the value of |v| using
the |Read| function defined in the previous section, potentially also
resulting in a new log:
\restorecolumns
\begin{code}
  ↣′-read : ∀ l v → let l′m = Read h l v in
    h ⊢ l , read v ↣′ fst l′m , # snd l′m
  ↣′-writeℕ : ∀ {l v m} →
    h ⊢ l , write v (# m) ↣′ Write l v m , # m
  ↣′-writeE : ∀ {l e l′ e′ v} →
    (e↣e′ :  h ⊢ l ,          e ↣′ l′ ,          e′)  →
             h ⊢ l , write v  e ↣′ l′ , write v  e′
\end{code}
The |↣′-writeℕ| rule updates the write log via the |Write| helper when the
expression argument to |write| is just a number, while |↣′-writeE| effects
the reduction of |e| in the same manner as the stop-the-world semantics.

%format _⊢_↣′⋆_ = "\type{\anonymous{\vdash}\anonymous{\rightarrowtail}\Prime^\star\anonymous}"
%format ↣′⋆ = "\infix{\type{\rightarrowtail\Prime^\star}}"
We write |_⊢_↣′⋆_| for the reflexive, transitive closure of |_⊢_↣′_| under
the same heap, again defined using the |Star| type:
\begin{code}
_⊢_↣′⋆_ : Heap → Rel (Logs × Expression′)
_⊢_↣′⋆_ h = Star (_⊢_↣′_ h)
\end{code}

%format TState = "\type{TState}"
%format _▹_↣_ = "\type{\anonymous{\triangleright}\anonymous{\rightarrowtail}\anonymous}"
%format ↣ = "\infix{\type{\rightarrowtail}}"
%format ↣-ℕ = "\cons{{\rightarrowtail}\text-{\oplus}\mathbb{N}}"
%format ↣-L = "\cons{{\rightarrowtail}\text-{\oplus}L}"
%format ↣-R = "\cons{{\rightarrowtail}\text-{\oplus}R}"
%format ↣-begin = "\cons{{\rightarrowtail}\text-begin}"
%format ↣-step = "\cons{{\rightarrowtail}\text-step}"
%format ↣-mutate = "\cons{{\rightarrowtail}\text-mutate}"
%format ↣-abort = "\cons{{\rightarrowtail}\text-abort}"
%format ↣-commit = "\cons{{\rightarrowtail}\text-commit}"
%format ¬cons = "\Varid{\lnot{}cons}"
\noindent For the `IO' level of this log-based semantics, we define
a transition |_▹_↣_| between triples of heaps, transaction states and
expressions, labelled with the same |Action|s we used earlier. During
a running transaction, the state comprises of the original expression and
the transaction |Logs|; otherwise it is empty:
\begin{code}
TState : Set
TState = Maybe (Expression′ × Logs)
\end{code}
%if False
\begin{code}
infix 3 _▹_↣_
\end{code}
%endif
The rules for addition are identical to those of |_▹_↦_|:
\savecolumns
\begin{code}
data _▹_↣_ : Action → Rel (Heap × TState × Expression) where
  ↣-ℕ : ∀ {h m n} →
    ⊞  ▹ h , ○ , # m ⊕ # n ↣ h , ○ , # (m + n)
  ↣-R : ∀ {α h t b h′ t′ b′} m →
    (b↣b′ :  α ▹ h , t ,        b ↣ h′ , t′ ,        b′)  →
             α ▹ h , t , # m ⊕  b ↣ h′ , t′ , # m ⊕  b′
  ↣-L : ∀ {α h t a h′ t′ a′} b →
    (a↣a′ :  α ▹ h , t , a       ↣ h′ , t′ , a′)  →
             α ▹ h , t , a ⊕ b   ↣ h′ , t′ , a′ ⊕ b
\end{code}
Next we move on to the transaction rules: when the expression to be reduced
is of the form |atomic e| and we have yet to enter the transaction, the
|↣-begin| rule sets up the restart expression to |e| and initialises the
transaction logs to |∅|:
\restorecolumns
\begin{code}
  ↣-begin : ∀ {h e} →
    τ  ▹ h , ○ , atomic e ↣ h , ● (e , ∅) , atomic e
\end{code}
The second |↣-step| rule allows us to make a single |_⊢_↣′_| transition on
the transaction level; note that the heap |h| does not change:
\restorecolumns
\begin{code}
  ↣-step : ∀ {h r l e l′ e′} →
    (e↣e′ : h ⊢ l , e ↣′ l′ , e′)  →
    τ  ▹ h , ● (r , l) , atomic e ↣ h , ● (r , l′) , atomic e′
\end{code}
While the Atomic language does not contain explicit parallelism, we can
model interference using a |↣-mutate| rule that changes to an arbitrary heap
|h′| at any time during a transaction:
\restorecolumns
\begin{code}
  ↣-mutate : ∀ h′ {h t e} →
    τ  ▹ h , ● t , atomic e ↣ h′ , ● t , atomic e
\end{code}
Finally we come to the |↣-abort| and |↣-commit| rules, one of which applies
when the transactional expression has reduced down to a number:
\restorecolumns
\begin{code}
  ↣-abort : ∀ {h r l m} (¬cons : ¬ Consistent h l) →
    τ  ▹ h , ● (r , l) , atomic (# m) ↣ h , ● (r , ∅) , atomic r
  ↣-commit : ∀ {h r l m} (cons : Consistent h l) →
    ☢  ▹ h , ● (r , l) , atomic (# m) ↣ Update h l , ○ , # m
\end{code}
Both rules carry proof of the consistency or otherwise of the log |l| with
respect to |h|. While this is not technically necessary and we could make do
with a single rule---as consistency is decidable---having two rules labelled
with distinct |Actions| makes later proofs easier to work with.

In any case if we do have consistency, we commit the transaction by applying
the write log to the heap using the |Update| function, setting the
transaction state to |○|, and reducing |atomic (# m)| to |# m|. Otherwise
the |↣-abort| rule applies, and we silently restart the transaction by
resetting the transaction state and the expression.

% vim: ft=tex fo-=m fo-=M:

