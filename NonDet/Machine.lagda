%if include /= True
\begin{comment}
%let include = True
%include NonDet/Language.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import NonDet.Language

module NonDet.Machine where
\end{code}
%endif

\section{Compiler, Virtual Machine and its
Semantics}\label{sec:nondet-machine}

The virtual machine for this language has a simple stack-based design, with
the same two instructions as we had in the previous chapter:
%format Instruction = "\type{Instruction}"
%format PUSH = "\cons{PUSH}"
%format ADD = "\cons{ADD}"
\begin{code}
data Instruction : Set where
  PUSH : (m : ℕ) → Instruction
  ADD : Instruction
\end{code}
A program comprises a list of such instructions. The compiler for our
expression language is the same as the previous chapter, and is repeated
below. In order to make our proofs more straightforward, we take a code
continuation as an additional argument~\cite{hutton07-haskell}, which
corresponds to writing the compiler in an accumulator-passing style:
%format compile = "\func{compile}"
\begin{code}
compile : Expression → List Instruction → List Instruction
compile (# m) c = PUSH m ∷ c
compile (a ⊕ b) c = compile a (compile b (ADD ∷ c))
\end{code}
To execute a program |c : List Instruction|, we pair it with a stack |σ
: List ℕ|. This is precisely how we represent the state of a virtual
machine:
%format Machine = "\type{Machine}"
%format ⟨_‚_⟩ = "\cons{\langle\anonymous,\!\anonymous\rangle}"
%format ‚ = "\infix{\cons{,}}"
%format ⟨ = "\prefix{\cons{\langle}}"
%format ⟩ = "\postfix{\cons{\rangle}}"
\begin{code}
data Machine : Set where
  ⟨_‚_⟩ : (c : List Instruction) (σ : List ℕ) → Machine
\end{code}

%format _↣‹_›_ = "\type{\anonymous{\rightarrowtail}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↣‹ = "\type{{\rightarrowtail}\texttt{<}}"
%format ↣-PUSH = "\cons{{\rightarrowtail}\text-PUSH}"
%format ↣-ADD = "\cons{{\rightarrowtail}\text-ADD}"
%format ↣-ZAP = "\cons{{\rightarrowtail}\text-ZAP}"
%if False
\begin{code}
infix 3 _↣‹_›_
\end{code}
%endif
Finally, we specify the operational semantics of the virtual machine through
the |_↣‹_›_| relation:
\begin{code}
data _↣‹_›_ : LTS Label Machine where
  ↣-PUSH : ∀ {c σ m} → ⟨ PUSH m ∷ c ‚ σ ⟩ ↣‹ τ › ⟨ c ‚ m ∷ σ ⟩
  ↣-ADD : ∀ {c σ m n} →
    ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ↣‹ ! ⊞  › ⟨ c ‚ m + n  ∷ σ ⟩
  ↣-ZAP : ∀ {c σ m n} →
    ⟨ ADD ∷ c ‚ n ∷ m ∷ σ ⟩ ↣‹ ! ↯  › ⟨ c ‚ 0      ∷ σ ⟩
\end{code}
That is, the |PUSH| instruction takes a numeric argument |m| and pushes it
onto the stack |σ|, with a silent label |τ|. In turn, the |ADD| instruction
replaces the top two numbers on the stack with either their sum, or
zero---labelled respectively with |⊞| or |↯|---in correspondence with the
|↣-ADD| and |↣-ZAP| rules.

% vim: ft=tex fo-=m fo-=M:

