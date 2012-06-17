%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
\end{comment}
%endif

%if False
\begin{code}
module Heap where

open import Common
\end{code}
%endif

\subsection{Heaps and Variables}

%format ∣Heap∣ = "\func{{|}Heap{|}}"
Recall that previously in chapter \ref{ch:model}, we modelled the heap as
a total map from a fixed set of variable names to their values, initialised
to zero. In Agda, we can realise this using the indexed |Vec| type
(\S\ref{sec:agda-dependent}) from the standard library. As our proof is to
be independent of the heap size---rather than parametrising the entire proof
by it---we simply postulate a number |∣Heap∣|,
\begin{code}
postulate ∣Heap∣ : ℕ
\end{code}
%format Heap = "\type{Heap}"
with the |Heap| type defined as follows:
\begin{code}
Heap : Set
Heap = Vec ℕ ∣Heap∣
\end{code}

%if False
\begin{code}
infix 5 _≟Heap_
\end{code}
%endif

%format _≟Heap_ = "\func{\anonymous{\stackrel?=_{Heap}}\anonymous}"
%format ≟Heap = "\infix{\func{\stackrel?=_{Heap}}}"
%if False
\begin{code}
_≟Heap_ : ∀ (h h′ : Heap) → Dec (h ≡ h′)
h ≟Heap h′ = Dec.map Vec.Pointwise-≡ (Vec.Pointwise.decidable _≟ℕ_ h h′)
\end{code}
%endif

%format Variable = "\type{Variable}"
\noindent Correspondingly, a |Variable| is just a synonym for the finite set
(\S\ref{sec:agda-dependent}) with |∣Heap∣| distinct elements:
\begin{code}
Variable : Set
Variable = Fin ∣Heap∣
\end{code}

% vim: ft=tex fo-=m fo-=M:

