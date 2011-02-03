%if include /= True
\begin{comment}
%let include = True
%include Verified/Bisimilarity.lagda
%include Verified/Heap.lagda
%include Verified/Action.lagda
%include Verified/Commit.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Verified.Language where

open import Verified.Heap as Heap
open import Verified.Action as Action
open import Verified.Commit as Commit
\end{code}
%endif

\section{The Atomic Language}

%format LTS = "\func{LTS}"
%if False
\begin{code}
infixl 5 _⊕_
infix 5 #_
\end{code}
%endif

\subsection{Syntax and Virtual Machine}

%format #_ = "\cons{\texttt{\#}\anonymous}"
%format # = "\cons{\texttt{\#}}"
%format _⊕_ = "\cons{\anonymous{\oplus}\anonymous}"
%format ⊕ = "\infix{\cons{\oplus}}"
%format fork = "\cons{fork}"
%format atomic = "\cons{atomic}"
%format read = "\cons{read}"
%format write = "\cons{write}"
%format Expression = "\type{Expression}"
%format Context = "\type{Context}"
%format STM = "\cons{STM}"
%format IO = "\cons{IO}"
%{
%format Tran = "\type{Tran}"
%format Proc = "\type{Proc}"
For the Atomic language, we extend our previously used language of natural
numbers and addition to a two-level syntax, corresponding to the |Tran| and
|Proc| types of chapter \ref{ch:model}:
%}
\begin{code}
data Context : Set where
  STM : Context
  IO : Context

data Expression : Context → Set where
  #_ : ∀ {k} (m : ℕ) → Expression k
  _⊕_ : ∀ {k} (a b : Expression k) → Expression k

  fork : (e : Expression IO) → Expression IO
  atomic : (e : Expression STM) → Expression IO

  read : (v : Variable) → Expression STM
  write : (v : Variable) (e : Expression STM) → Expression STM
\end{code}
The |Expression| type is indexed with a |Context| corresponding the two
levels of the language, with addition and natural numbers being common to
both. We retain the |fork| construct from the previous chapter, adding the
|atomic| keyword for running transactions, along with the |read| and |write|
primitives for manipulating transactional variables.

%format Instruction = "\type{Instruction}"
%format PUSH = "\cons{PUSH}"
%format ADD = "\cons{ADD}"
%format FORK = "\cons{FORK}"
%format BEGIN = "\cons{BEGIN}"
%format COMMIT = "\cons{COMMIT}"
%format READ = "\cons{READ}"
%format WRITE = "\cons{WRITE}"
Accordingly, the virtual machine gains the |BEGIN|, |COMMIT|, |READ| and
|WRITE| instructions to match the capabilities of the expression language,
\begin{code}
data Instruction : Set where
  PUSH : (m : ℕ) → Instruction
  ADD : Instruction
  FORK : (c : List Instruction) → Instruction
  BEGIN COMMIT : Instruction
  READ WRITE : (v : Variable) → Instruction
\end{code}
while the compiler is extended with clauses handling |atomic|, |read| and
|write|:
%format compile = "\func{compile}"
\begin{code}
compile : ∀ {k} → Expression k → List Instruction → List Instruction
compile (# m) c = PUSH m ∷ c
compile (a ⊕ b) c = compile a (compile b (ADD ∷ c))
compile (fork e) c = FORK (compile e []) ∷ c
compile (atomic e) c = BEGIN ∷ compile e (COMMIT ∷ c)
compile (read v) c = READ v ∷ c
compile (write v e) c = compile e (WRITE v ∷ c)
\end{code}
The compiled code comprising a transaction are bracketed with a pair of
|BEGIN| and |COMMIT| instructions, as shown in the |atomic| clause. The
|READ| instruction pushes the value of the transactional variable |v| onto
the stack, while |WRITE| updates it with the topmost value of the stack.

As per chapter \ref{ch:model}, each virtual machine thread consists of---as
well as the usual code sequence |c| and stack |σ|---three additional
components:
%format Machine = "\type{Machine}"
%format ⟨_‚_‚_‚_‚_⟩ = "\cons{\langle\anonymous,\!\anonymous,\!\anonymous,\!\anonymous,\!\anonymous\rangle}"
%format ‚ = "\infix{\cons{,}}"
%format ⟨ = "\prefix{\cons{\langle}}"
%format ⟩ = "\postfix{\cons{\rangle}}"
\begin{spec}
data Machine : Set where
  ⟨_‚_‚_‚_‚_⟩ : (c : List Instruction) (σ : List ℕ)
    (γ : List Instruction) (ρ ω : Log) → Machine
\end{spec}
The |γ| field gives the code to rerun if a transaction fails to commit,
while |ρ| and |ω| hold the read and write transaction logs.

%if False
\begin{code}
record Machine : Set where
  constructor ⟨_‚_‚_‚_‚_⟩
  field
    c : List Instruction
    σ : List ℕ
    γ : List Instruction
    ρ ω : Log
\end{code}
%endif

\input{Verified/Heap.lagda}

\input{Verified/Action.lagda}

\subsection{Expression Semantics}

%format _‣_↦‹_›_ = "\type{\anonymous{\triangleright}\anonymous{\mapsto}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ‣ = "\infix{\type{{\triangleright}}}"
%format ↦‹ = "\infix{\type{{\mapsto}\texttt{<}}}"
%format › = "\infix{\type{\texttt{>}}}"
%format STM‣_↦⋆_ = "\func{STM{\triangleright}\anonymous{\mapsto}^\star\anonymous}"
%format STM‣ = "\prefix{\func{STM{\triangleright}}}"
%format ↦⋆ = "\infix{\func{{\mapsto}^\star}}"
%format ↦ = "\infix{\func{{\mapsto}}}"
%format rwLog = "\func{rwLog}"
%format ↦-⊞ = "\cons{{\mapsto}\text-\boxplus}"
%format ↦-R = "\cons{{\mapsto}\text-R}"
%format ↦-L = "\cons{{\mapsto}\text-L}"
%format ↦-fork = "\cons{{\mapsto}\text-fork}"
%format ↦-atomic = "\cons{{\mapsto}\text-atomic}"
%format ↦-read = "\cons{{\mapsto}\text-read}"
%format ↦-writeE = "\cons{{\mapsto}\text-write_E}"
%format ↦-writeℕ = "\cons{{\mapsto}\text-write_{\mathbb{N}}}"
%format a↦a′ = "a{\mapsto}a\Prime{}"
%format b↦b′ = "b{\mapsto}b\Prime{}"
%format e↦⋆m = "e{\mapsto}^\star{}m"
%format e↦e′ = "e{\mapsto}e\Prime{}"
Finally, we can given the semantics for expressions and virtual machines.
Due to the two-level stratification of our source language, the |_‣_↦‹_›_|
relation is additionally indexed by its context. We begin with the familiar
rules for left-biased addition:
%if False
\begin{code}
-- infix 1 _‣_↦‹_›_ STM‣_↦_ STM‣_↦⋆_
infix 3 _‣_↦‹_›_ STM‣_↦_ STM‣_↦⋆_
mutual
\end{code}
%endif
\savecolumns
\begin{code}
  data _‣_↦‹_›_ : (k : Context) →
    LTS (Action (Expression k)) (Heap × Expression k) where
    ↦-⊞ : ∀ {k m n h} →
      k ‣ h ∧ # m ⊕ # n ↦‹ τ › h ∧ # (m + n)
    ↦-R : ∀ {k m b b′ α h h′} (b↦b′ : k ‣ h ∧ b ↦‹ α › h′ ∧ b′) →
      k ‣ h ∧ # m ⊕ b ↦‹ α › h′ ∧ # m ⊕ b′
    ↦-L : ∀ {k a a′ b α h h′} (a↦a′ : k ‣ h ∧ a ↦‹ α › h′ ∧ a′) →
      k ‣ h ∧ a ⊕ b ↦‹ α › h′ ∧ a′ ⊕ b
\end{code}
The |↦-fork| rule is only usable in an |IO| context, but is otherwise
identical to that of the Fork language. The new |↦-atomic| rule implements
a stop-the-world semantics for |atomic| blocks,
\restorecolumns
\begin{code}
    ↦-fork : ∀ {e h} →
      IO ‣ h ∧ fork e ↦‹ ⁺ e › h ∧ # 0
    ↦-atomic : ∀ {m e h h′} → (e↦⋆m : STM‣ h ∧ e ↦⋆ h′ ∧ # m) →
      let ρ∧ω = rwLog e↦⋆m (newLog ∧ newLog) in
      IO ‣ h ∧ atomic e ↦‹ ☢ ρ∧ω › h′ ∧ # m
\end{code}
by taking a reduction sequence |e↦⋆m| and encapsulating it in a single step,
where |STM‣_↦⋆_| is a synonym for the reflexive transitive closure of
a single step in the |STM| context. It emits the |☢_| action, embedding
a pair of read and write logs, computed with the help of the |rwLog|
function, which we will examine shortly. Within transactions however, the
applicable rules make no mention of any logs:
\restorecolumns
\begin{code}
    ↦-read : ∀ {v h} →
      STM ‣ h ∧ read v ↦‹ τ › h ∧ # h « v »
    ↦-writeℕ : ∀ {v m h} →
      STM ‣ h ∧ write v (# m) ↦‹ τ › h « v »≔ m ∧ # m
    ↦-writeE : ∀ {e e′ v h h′} →
      (e↦e′ : STM ‣ h ∧ e ↦‹ τ › h′ ∧ e′) →
      STM ‣ h ∧ write v e ↦‹ τ › h′ ∧ write v e′
\end{code}
Here the |↦-read| and |↦-writeℕ| rules refer directly to the heap, while
|↦-writeE| effects the reduction of the sub-expression argument to |write|.

%if False
% STM transitions are all silent!
The |STM‣_↦⋆_| synonym used in the |↦-atomic| rule is defined as follows,
\restorecolumns
\begin{code}
  STM‣_↦_ : Rel (Heap × Expression STM) Level.zero
  STM‣ x ↦ y = STM ‣ x ↦‹ τ › y

  STM‣_↦⋆_ : Rel (Heap × Expression STM) Level.zero
  STM‣_↦⋆_ = Star STM‣_↦_
\end{code}
by taking the reflexive transitive closure of a single step in the |STM|
context.
%endif

\subsubsection{Reconstructing the Transaction Logs}

Even though the above transactional semantics do not make use of any logs,
they do serve as a useful summary of the side-effects of the transaction on
the heap, which is why we chose to embed pairs of read and write logs in
|☢_| actions. The |↦-atomic| rule thus uses |rwLog| to reconstruct a pair of
read and write logs from a sequence of |STM| transitions. Let us first give
an auxiliary definition that classifies each transition as either a read or
a write:
%format STM→rw = "\func{STM\text-r{\uplus}w}"
\restorecolumns
\begin{code}
  STM→rw : ∀ {h h′ e e′ α} →
    STM ‣ h ∧ e ↦‹ α › h′ ∧ e′ → Maybe (Variable × (Heap ⊎ ℕ))
  STM→rw ↦-⊞                 = nothing
  STM→rw (↦-R b↦b′)          = STM→rw b↦b′
  STM→rw (↦-L a↦a′)          = STM→rw a↦a′
  STM→rw (↦-writeE e↦e′)     = STM→rw e↦e′
  STM→rw (↦-read {v} {h})    = just (v ∧ inj₁ h)
  STM→rw (↦-writeℕ {v} {m})  = just (v ∧ inj₂ m)
\end{code}
In the former case we return the heap from which the value is read, while in
the latter case we return the newly-written value. The |rwLog| function is
written in an accumulator-passing style to allow for easy composition and
reasoning later, and proceeds through the sequence one step at a time:
% WTF didn't I write this as a Star.fold? Too scared to change it in case it
% messes up later proofs. :(
%format e′↦⋆e″ = "e\Prime{\mapsto}^\star{}e\PPrime{}"
\restorecolumns
\begin{code}
  rwLog : ∀ {e e″} → STM‣ e ↦⋆ e″ → Log × Log → Log × Log
  rwLog ε ρ∧ω = ρ∧ω
\end{code}
For an empty sequence, we simply give back the pair of read and write logs
unmodified. Otherwise, we inspect the result of |STM→rw| on the first
transition; if it corresponds to neither a read or a write, we leave the
logs alone and recurse on the remainder of the sequence:
\restorecolumns
\begin{code}
  rwLog (e↦e′ ◅ e′↦⋆e″) ρ∧ω
    with STM→rw e↦e′
  rwLog (e↦e′ ◅ e′↦⋆e″) ρ∧ω
    | nothing = rwLog e′↦⋆e″ ρ∧ω
  rwLog (e↦e′ ◅ e′↦⋆e″) (ρ ∧ ω)
    | just (v ∧ inj₂ m) = rwLog e′↦⋆e″ (ρ ∧ ω « v »≔ just m)
\end{code}
For transitions involving a write, we obtain the corresponding variable |v|
and its new value |m|, and update the write log accordingly. For reads,
we simply invoke the |update-rLog| function defined previously to obtain the
new read log:
\begin{code}
  rwLog (e↦e′ ◅ e′↦⋆e″) (ρ ∧ ω)
    | just (v ∧ inj₁ h) = rwLog e′↦⋆e″ (update-rLog h ρ ω v ∧ ω)
\end{code}

%format ↦⋆-R = "\func{{\mapsto}^\star\text-R}"
%format ↦⋆-L = "\func{{\mapsto}^\star\text-L}"
%format ↦⋆-writeE = "\func{{\mapsto}^\star\text-write_E}"
%if False
\begin{code}
↦⋆-R : ∀ m {h b h′ b′} → STM‣ h ∧ b ↦⋆ h′ ∧ b′ → STM‣ h ∧ # m ⊕ b ↦⋆ h′ ∧ # m ⊕ b′
↦⋆-R m b↦⋆b′ = Star.gmap (Σ.map id (λ b′ → # m ⊕ b′)) ↦-R b↦⋆b′

↦⋆-L : ∀ {h a h′ a′} b → STM‣ h ∧ a ↦⋆ h′ ∧ a′ → STM‣ h ∧ a ⊕ b ↦⋆ h′ ∧ a′ ⊕ b
↦⋆-L b a↦⋆a′ = Star.gmap (Σ.map id (λ a′ → a′ ⊕ b)) ↦-L a↦⋆a′

↦⋆-writeE : ∀ v {h e h′ e′} → STM‣ h ∧ e ↦⋆ h′ ∧ e′ → STM‣ h ∧ write v e ↦⋆ h′ ∧ write v e′
↦⋆-writeE v e↦⋆e′ = Star.gmap (Σ.map id (write v)) ↦-writeE e↦⋆e′
\end{code}
%endif

\subsection{Virtual Machine Semantics}

%format _↣‹_›_ = "\type{\anonymous{\rightarrowtail}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↣‹ = "\infix{\type{{\rightarrowtail}\texttt{<}}}"
%format ↣-PUSH = "\cons{{\rightarrowtail}\text-PUSH}"
%format ↣-ADD = "\cons{{\rightarrowtail}\text-ADD}"
%format ↣-FORK = "\cons{{\rightarrowtail}\text-FORK}"
%format ↣-BEGIN = "\cons{{\rightarrowtail}\text-BEGIN}"
%format ↣-READ = "\cons{{\rightarrowtail}\text-READ}"
%format ↣-WRITE = "\cons{{\rightarrowtail}\text-WRITE}"
%format ↣-COMMIT = "\cons{{\rightarrowtail}\text-COMMIT}"
The semantics for the virtual machines inherits essentially the same rules
from the Fork language given in \S\ref{sec:fork-semantics}, additionally
passing along |h|, |γ|, |ρ| and |ω| unchanged:
%if False
\begin{code}
infix 4 _↣‹_›_ _↣_ _↣⋆_ _↣τ_ _↣≄τ_ _↣τ⋆_
\end{code}
%endif
\savecolumns
\begin{code}
data _↣‹_›_ : LTS (Action Machine) (Heap × Machine) where
  ↣-PUSH : ∀ {m c σ γ ρ ω h} →
    h ∧ ⟨ PUSH m ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣‹ τ ›
      h ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩
  ↣-ADD : ∀ {m n c σ γ ρ ω h} →
    h ∧ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣‹ τ ›
      h ∧ ⟨ c ‚ m + n ∷ σ ‚ γ ‚ ρ ‚ ω ⟩
  ↣-FORK : ∀ {c c′ σ  γ ρ ω h} → let
    t = ⟨ c′ ‚ [] ‚ [] ‚ newLog ‚ newLog ⟩ in
    h ∧ ⟨ FORK c′ ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣‹ ⁺ t ›
      h ∧ ⟨ c ‚ 0 ∷ σ ‚ γ ‚ ρ ‚ ω ⟩
\end{code}
Furthermore, each new instruction for our virtual machine also comes with
a corresponding reduction rule. The first of the four is |↣-BEGIN|, which
clears both transaction logs and sets the restart field to the start of the
transaction:
\restorecolumns
\begin{code}
  ↣-BEGIN : ∀ {c σ ρ ω h} →
    h ∧ ⟨ BEGIN ∷ c ‚ σ ‚ [] ‚ ρ ‚ ω ⟩ ↣‹ τ ›
      h ∧ ⟨ c ‚ σ ‚ c ‚ newLog ‚ newLog ⟩
\end{code}
Next, |↣-READ| pushes the value of the variable |v| onto the stack
using |lookupTVar|, while updating the read log with |update-rLog|, both of
were defined in \S\ref{sec:verified-heap}:
\restorecolumns
\begin{code}
  ↣-READ : ∀ {v c σ γ ρ ω h} →
    h ∧ ⟨ READ v ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣‹ τ ›
      h ∧ ⟨ c ‚ lookupTVar h ρ ω v ∷ σ ‚ γ ‚ update-rLog h ρ ω v ‚ ω ⟩
  ↣-WRITE : ∀ {v m c σ γ ρ ω h} →
    h ∧ ⟨ WRITE v ∷ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣‹ τ ›
      h ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω « v »≔ just m ⟩
\end{code}
The |↣-WRITE| rule on the other hand simply updates the write log entry for
|v| to the topmost value on the stack, leaving everything else the same.

\input{Verified/Commit.lagda}

% we may need to split this up into ↣-COMMIT and ↣-RETRY

Finally, the transition rule for the |COMMIT| instruction includes a premise
witnessing the consistency of |ρ| with |h|---or otherwise---and proceeds
using the above definitions:
\restorecolumns
\begin{code}
  ↣-COMMIT : ∀ {c m σ γ ρ ω h} → (p : Dec (Consistent h ρ)) → let
      h′  = if ⌊ p ⌋    then update h ω  else h
      t′  = if ⌊ p ⌋    then  ⟨ c   ‚ m ∷  σ ‚ []  ‚ newLog ‚ newLog ⟩
                        else  ⟨ γ   ‚      σ ‚ γ   ‚ newLog ‚ newLog ⟩
      α   = if ⌊ p ⌋    then ☢ (ρ ∧ ω)   else τ in
    h ∧ ⟨ COMMIT ∷ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣‹ α › h′ ∧ t′
\end{code}
There are two possible outcomes: depending on the truthiness of |p|, we
either commit the changes recorded in |ω| to the heap using |update| and
emit an |☢_| action, or silently discard the result |m| and restart the
transaction by resetting the instruction sequence to |γ|.

%format ↣τ = "\infix{\func{{\rightarrowtail}\tau}}"
%format ↣≄τ = "\infix{\func{{\rightarrowtail}{\not\simeq}\tau}}"
%format ↣τ⋆ = "\infix{\func{{\rightarrowtail}\tau^\star}}"
%format ↣τ-PUSH = "\func{{\rightarrowtail}\tau\text-PUSH}"
%format ↣τ-ADD = "\func{{\rightarrowtail}\tau\text-ADD}"
%format ↣τ-READ = "\func{{\rightarrowtail}\tau\text-READ}"
%format ↣τ-WRITE = "\func{{\rightarrowtail}\tau\text-WRITE}"
%if False
\begin{code}
_↣_ : Rel (Heap × Machine) Level.zero
x ↣ y = ∃ λ α → x ↣‹ α › y

_↣⋆_ : Rel (Heap × Machine) Level.zero
_↣⋆_ = Star _↣_

_↣τ_ : Rel (Heap × Machine) Level.zero
x ↣τ y = ∃ λ α → α ≃τ × x ↣‹ α › y

_↣≄τ_ : Rel (Heap × Machine) Level.zero
x ↣≄τ y = ∃ λ α → α ≄τ × x ↣‹ α › y

_↣τ⋆_ : Rel (Heap × Machine) Level.zero
_↣τ⋆_ = Star _↣τ_



↣τ-PUSH : ∀ {m c σ γ ρ ω h} →
  h ∧ ⟨ PUSH m ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ h ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩
↣τ-PUSH = τ ∧ is-τ ∧ ↣-PUSH

↣τ-ADD : ∀ {m n c σ γ ρ ω h} →
  h ∧ ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ h ∧ ⟨ c ‚ m + n ∷ σ ‚ γ ‚ ρ ‚ ω ⟩
↣τ-ADD = τ ∧ is-τ ∧ ↣-ADD

↣τ-READ : ∀ {v c σ γ ρ ω h} →
  h ∧ ⟨ READ v ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ h ∧ ⟨ c ‚ lookupTVar h ρ ω v ∷ σ ‚ γ ‚ update-rLog h ρ ω v ‚ ω ⟩
↣τ-READ = τ ∧ is-τ ∧ ↣-READ

↣τ-WRITE : ∀ {v m c σ γ ρ ω h} →
    h ∧ ⟨ WRITE v ∷ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ↣τ h ∧ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω « v »≔ just m ⟩
↣τ-WRITE = τ ∧ is-τ ∧ ↣-WRITE
\end{code}
%endif

\section{Combined Machines and Bisimilarity}

%format Combined = "\type{Combined}"
%format ⟨_‚_⟩ = "\cons{\langle\anonymous{,}\anonymous\rangle}"
%format ⟨_⟩ = "\cons{\langle\anonymous\rangle}"
%format ⟨⟩ = "\cons{\langle\rangle}"
The definition of a combined machine remains unchanged, with the
constructors |⟨_‚_⟩|, |⟨_⟩| and |⟨⟩| corresponding to the three phases of
execution:
\begin{code}
data Combined : Set where
  ⟨_‚_⟩ : (e : Expression IO) (t : Machine) → Combined
  ⟨_⟩ : (t : Machine) → Combined
  ⟨⟩ : Combined
\end{code}

%format E⁺ = "\func{E^{\texttt+}}"
%format M⁺ = "\func{M^{\texttt+}}"
%if False
\begin{code}
E⁺ : Expression IO → Combined
E⁺ e = ⟨ e ‚ ⟨ [] ‚ [] ‚ [] ‚ newLog ‚ newLog ⟩ ⟩

M⁺ : Machine → Combined
M⁺ = ⟨_⟩
\end{code}
%endif

%if False
\begin{code}
-- prepend child to soup if appropriate (was: soupCon / soupÇon)
infixr 5 _⁺∷_
_⁺∷_ : Action Combined → List Combined → List Combined
⁺ child ⁺∷ s = child ∷ s
τ ⁺∷ s = s
∎ m ⁺∷ s = s
… α ⁺∷ s = s
☢ ρ∧ω ⁺∷ s = s

open RawFunctor Action.rawFunctor

E⁺≃τ-inj : ∀ {α} → E⁺ <$> α ≃τ → α ≃τ
E⁺≃τ-inj {τ} α≃τ = is-τ
E⁺≃τ-inj {⁺ x} ()
E⁺≃τ-inj {∎ m} ()
E⁺≃τ-inj {… α} (is-… α≃τ) = is-… (E⁺≃τ-inj α≃τ)
E⁺≃τ-inj {☢ ρ∧ω} ()

M⁺≃τ-inj : ∀ {α} → M⁺ <$> α ≃τ → α ≃τ
M⁺≃τ-inj {τ} is-τ = is-τ
M⁺≃τ-inj {⁺ x} ()
M⁺≃τ-inj {∎ m} ()
M⁺≃τ-inj {… α} (is-… α′≃τ) = is-… (M⁺≃τ-inj α′≃τ)
M⁺≃τ-inj {☢ ρ∧ω} ()

M⁺≃τ : ∀ {α} → α ≃τ → M⁺ <$> α ≃τ
M⁺≃τ is-τ = is-τ
M⁺≃τ (is-… α≃τ) = is-… (M⁺≃τ α≃τ)

τ⁺∷s≡s : ∀ {α} → α ≃τ → ∀ s → α ⁺∷ s ≡ s
τ⁺∷s≡s is-τ s = ≡.refl
τ⁺∷s≡s (is-… α≃τ) s = ≡.refl

infix 4 _↠‹_›_
\end{code}
%endif

\noindent The semantics of combined machine thread soups---aside from the
introduction of heaps and contexts for the expression language---is
otherwise identical to that of the Fork language
(\S\ref{sec:fork-combined}):
%format _↠‹_›_ = "\type{\anonymous{\twoheadrightarrow}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↠‹ = "\infix{\type{{\twoheadrightarrow}\texttt{<}}}"
%format ↠-↦ = "\cons{{\twoheadrightarrow}\text-{\mapsto}}"
%format ↠-↣ = "\cons{{\twoheadrightarrow}\text-{\rightarrowtail}}"
%format ↠-done = "\cons{{\twoheadrightarrow}\text-done}"
%format ↠-switch = "\cons{{\twoheadrightarrow}\text-switch}"
%format ↠-preempt = "\cons{{\twoheadrightarrow}\text-preempt}"
%format e↦e′ = "e{\mapsto}e\Prime{}"
%format t↣t′ = "t{\rightarrowtail}t\Prime{}"
%format s↠s′ = "s{\twoheadrightarrow}s\Prime{}"
\begin{code}
data _↠‹_›_ : LTS (Action Combined) (Heap × List Combined) where
  ↠-↦ : ∀ {h h′ e e′ t s α} →
    (e↦e′ : IO ‣ h ∧ e ↦‹ α › h′ ∧ e′) → let α′ = E⁺ <$> α in
      h ∧ ⟨ e ‚ t ⟩ ∷ s ↠‹ α′ › h′ ∧ ⟨ e′ ‚ t ⟩ ∷ α′ ⁺∷ s
  ↠-↣ : ∀ {h h′ t t′ s α} →
    (t↣t′ : h ∧ t ↣‹ α › h′ ∧ t′) → let α′ = M⁺ <$> α in
      h ∧ ⟨ t ⟩ ∷ s ↠‹ α′ › h′ ∧ ⟨ t′ ⟩ ∷ (α′ ⁺∷ s)
  ↠-done : ∀ {h m γ ρ ω s} →
    h ∧ ⟨ ⟨ [] ‚ m ∷ [] ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ s ↠‹ ∎ m › h ∧ ⟨⟩ ∷ s
  ↠-switch : ∀ {h m c σ γ ρ ω s} →
    h ∧ ⟨ # m ‚ ⟨ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ s ↠‹ τ ›
      h ∧ ⟨ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ s
  ↠-preempt : ∀ {h h′ x s s′ α} → (s↠s′ : h ∧ s ↠‹ α › h′ ∧ s′) →
    h ∧ x ∷ s ↠‹ … α › h′ ∧ x ∷ s′
\end{code}
%format _↠τ_ = "\func{\anonymous{\twoheadrightarrow}\tau\anonymous}"
%format ↠τ = "\infix{\func{{\twoheadrightarrow}\tau}}"
%format _↠τ⋆_ = "\func{\anonymous{\twoheadrightarrow}\tau^\star\anonymous}"
%format ↠τ⋆ = "\infix{\func{{\twoheadrightarrow}\tau^\star}}"
%format _↠≄τ_ = "\func{\anonymous{\twoheadrightarrow}{\not\simeq}\tau\anonymous}"
%format ↠≄τ = "\infix{\func{{\twoheadrightarrow}{\not\simeq}\tau}}"
%if False
\begin{code}
infix 4 _↠τ_ _↠τ⋆_ _↠≄τ_
_↠τ_ : ∀ r s → Set
r ↠τ s = ∃ λ α → α ≃τ × r ↠‹ α › s

_↠τ⋆_ : ∀ r s → Set
_↠τ⋆_ = Star _↠τ_

_↠≄τ_ : ∀ r s → Set
r ↠≄τ s = ∃ λ α → α ≄τ × r ↠‹ α › s
\end{code}
%endif

%format _↠τ₁_ = "\func{\anonymous{\twoheadrightarrow}\tau_1\anonymous}"
%format ↠τ₁ = "\infix{\func{{\twoheadrightarrow}\tau_1}}"
%format _↠τ⋆₁_ = "\func{\anonymous{\twoheadrightarrow}\tau^\star_1\anonymous}"
%format ↠τ⋆₁ = "\infix{\func{{\twoheadrightarrow}\tau^\star_1}}"
%format _↠≄τ₁_ = "\func{\anonymous{\twoheadrightarrow}{\not\simeq}\tau_1\anonymous}"
%format ↠≄τ₁ = "\infix{\func{{\twoheadrightarrow}{\not\simeq}\tau_1}}"
% format x′⁺ = "x\Prime^{\texttt+}"
%format _◅₁_ = "\func{\anonymous{\lhd}_1\anonymous}"
%format ◅₁ = "\infix{\func{{\lhd}_1}}"
% format x↠τ₁x′ = "x{\twoheadrightarrow}\tau_1x\Prime{}"
% format x′↠τ⋆₁y = "x\Prime{\twoheadrightarrow}\tau^\star_1y"
%if False
\begin{code}
infix 4 _↠τ₁_ _↠τ⋆₁_ _↠≄τ₁_
_↠τ₁_ : ∀ x y → Set
x ↠τ₁ y = ∀ h s → h ∧ x ∷ s ↠τ h ∧ y ∷ s

_↠τ⋆₁_ : ∀ x y → Set
x ↠τ⋆₁ y = ∀ h s → h ∧ x ∷ s ↠τ⋆ h ∧ y ∷ s

_↠≄τ₁_ : ∀ x x′⁺ → Set
x ↠≄τ₁ x′⁺ = ∀ h s → h ∧ x ∷ s ↠≄τ h ∧ x′⁺ ++ s

infixr 5 _◅₁_
_◅₁_ : ∀ {x x′ y} → x ↠τ₁ x′ → x′ ↠τ⋆₁ y → x ↠τ⋆₁ y
x↠τ₁x′ ◅₁ x′↠τ⋆₁y = λ h s → x↠τ₁x′ h s ◅ x′↠τ⋆₁y h s
\end{code}
%endif

%format visible = "\func{visible}"
%format ⟦_⟧ = "\func{[\![\anonymous]\!]}"
%format ⟦ = "\prefix{\func{[\![}}"
%format ⟧ = "\postfix{\func{]\!]}}"
%if False
\begin{code}
visible : ∀ {α : Action Combined} → α ≄τ → Action ⊤
visible {τ} α≄τ = ⊥-elim (α≄τ is-τ)
visible {⁺ x} α≄τ = ⁺ tt
visible {∎ m} α≄τ = ∎ m
visible {☢ ρ∧ω} α≄τ = ☢ ρ∧ω
visible {… α} …α≄τ = visible (…α≄τ ∘ is-…)

⟦_⟧ : ∀ {s s′} → s ↠≄τ s′ → Action ⊤
⟦_⟧ (α ∧ α≄τ ∧ s↠s′) = visible α≄τ
\end{code}
%endif

%format ↠τ-switch = "\func{{\twoheadrightarrow}\tau\text-switch}"
%if False
\begin{code}
↠τ-switch : ∀ {m c σ γ ρ ω h s} → h ∧ ⟨ # m ‚ ⟨ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ s ↠τ h ∧ ⟨ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ s
↠τ-switch = τ ∧ is-τ ∧ ↠-switch
↠τ-PUSH : ∀ {m c σ γ ρ ω h s} → h ∧ ⟨ ⟨ PUSH m ∷ c ‚ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ s ↠τ h ∧ ⟨ ⟨ c ‚ m ∷ σ ‚ γ ‚ ρ ‚ ω ⟩ ⟩ ∷ s
↠τ-PUSH = τ ∧ is-τ ∧ ↠-↣ ↣-PUSH
\end{code}
%endif

%format _⤇‹_›_ = "\type{\anonymous{\Mapsto}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ⤇‹ = "\infix{\type{{\Mapsto}\texttt{<}}}"
%format ⤇-↠ = "\cons{{\Mapsto}\text-{\twoheadrightarrow}}"
%format s↠τ⋆s₀ = "s{\twoheadrightarrow}\tau^\star{}s_0"
%format s₀↠≄τs₁ = "s_0{\twoheadrightarrow}{\not\simeq}\tau{}s_0"
%format s₁↠τ⋆s′ = "s_1{\twoheadrightarrow}\tau^\star{}s\Prime{}"
%if False
\begin{code}
infix 4 _⤇‹_›_
data _⤇‹_›_ : LTS (Action ⊤) (Heap × List Combined) where
  ⤇-↠ : ∀ {s s₀ s₁ s′} (s↠τ⋆s₀ : s ↠τ⋆ s₀) (s₀↠≄τs₁ : s₀ ↠≄τ s₁) (s₁↠τ⋆s′ : s₁ ↠τ⋆ s′) → s ⤇‹ ⟦ s₀↠≄τs₁ ⟧ › s′
\end{code}
%endif
\noindent We may define silent (|_↠τ_|), non-silent (|_↠≄τ_|) and visible
(|_⤇‹_›_|) transitions in the usual way. The exact same definition of
bisimilarity (and all associated lemmas) from the Fork language suffices for
this chapter, requiring only a change of type to |_≈_ : Rel (Heap × List
Combined)|.

% vim: ft=tex fo-=m fo-=M:

