%if include /= True
\begin{comment}
%let include = True
%include Verified/Heap.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Verified.Commit where

open import Verified.Heap as Heap
\end{code}
%endif

\subsubsection{Committing Log-Based Transactions}\label{sec:verified-commit}

%format Consistent = "\func{Consistent}"
On reaching the end of a transaction we either commit or roll back,
depending on whether the values of the variables gleaned from the heap
during the transaction are consistent with their corresponding values at the
end. That is, all values recorded in the read log must match those currently
in the heap for corresponding variables. The following predicate allows us
to state this succinctly:
\def\ConsistentSig#1{|REL Heap Log|}
\restorecolumns
\begin{code}
Consistent : {-"\ConsistentSig{"-}∀ {N} → REL (Heap′ N) (Log′ N) Level.zero{-"}"-}
Consistent h ρ = ∀ v {n} → ρ « v » ≡ just n → h « v » ≡ n
\end{code}
A read log |ρ| is consistent with the heap |h| precisely when all non-empty
entries in |ρ| have the same values as the corresponding entries in |h|.
Note that a transactional variable that is written to before being read from
will not have a corresponding entry in |ρ|; this is acceptable since its
original value in the heap could not possibly have influenced the behaviour
of the transaction.

%format isConsistent = "\func{isConsistent}"
%format ¬p = "{\lnot}p"
%format ρ«v»≡n = "\rho\text[v\text]{\equiv}n"
%format m≢n = "m{\not\equiv}n"
%{
%format p′ = "p\Prime{}"
The |Dec P| type corresponds to the decidability of some proposition |P|. It
has two constructors |yes| and |no|, carrying the appropriate evidence in
either case:
\begin{spec}
data Dec (P : Set) : Set where
  yes  : ( p  :    P) → Dec P
  no   : (¬p  : ¬  P) → Dec P
\end{spec}
An element of |Dec P| is strictly more informative than a boolean value.
Using this, we implement a decision procedure for whether a given heap and
read log are indeed consistent; that is, consistency is a decidable
property. In the base case, there are no variable names (in |Fin zero|), so
the proof is a trivial |λ ()|:
\def\isConsistentSig#1{|(h : Heap) (ρ : Log) → Dec (Consistent h ρ)|}
\restorecolumns
\begin{code}
isConsistent : {-"\isConsistentSig{"-}∀ {N} → (h : Heap′ N) (ρ : Log′ N) → Dec (Consistent h ρ){-"}"-}
isConsistent []         []             = yes (λ ())
isConsistent (m ∷ h)    (n ∷ ρ)        with isConsistent h ρ
isConsistent (m ∷ h)    (n ∷ ρ)        | no ¬p  = no (λ p → ¬p (p ∘ suc))
\end{code}
The code above then proceeds by structural induction: if the tails |h| and
|ρ| are not consistent, we can adapt |¬p| to show the inconsistency between
|m ∷ h| and |n ∷ ρ| too.

Next, we inspect the head of the read log: for an empty entry of |nothing|,
we can construct a proof |p′| from |p : Consistent h ρ|, where the |zero|
case is eliminated by the impossibility of |nothing ≡ just n|:
\restorecolumns
\begin{code}
isConsistent (m ∷ h)    (nothing ∷ ρ)  | yes p  = yes p′ where
  p′ : Consistent (m ∷ h) (nothing ∷ ρ)
  p′ zero     ()
  p′ (suc v)  ρ«v»≡n   = p v ρ«v»≡n
\end{code}
Otherwise, we use |_≟ℕ_| to compare the |m| in the heap versus the |n|
recorded in the read log for equality, and build the appropriate response in
either case:
\restorecolumns
\begin{code}
isConsistent (m ∷ h)    (just n ∷ ρ)   | yes p with m ≟ℕ n
isConsistent (m ∷ h)    (just .m ∷ ρ)  | yes p | yes ≡.refl = yes p′ where
  p′ : Consistent (m ∷ h) (just m ∷ ρ)
  p′ zero     ≡.refl   = ≡.refl
  p′ (suc v)  ρ«v»≡n   = p v ρ«v»≡n
isConsistent (m ∷ h)    (just n ∷ ρ)   | yes _ | no m≢n
  = no (λ p → m≢n (p zero ≡.refl))
\end{code}
%}

%format update = "\func{apply\text-h\omega}"
\noindent Once we have ascertained the consistency of the read log
with respect to the heap, then we may commit the changes recorded in the
write log with the following |update| function:
\def\updateSig#1{|Heap → Log → Heap|}
\restorecolumns
\begin{code}
update : {-"\updateSig{"-}∀ {N} → Heap′ N → Log′ N → Heap′ N{-"}"-}
update []       []              = []
update (m ∷ h)  (nothing  ∷ ω)  = m  ∷ update h ω
update (m ∷ h)  (just n   ∷ ω)  = n  ∷ update h ω
\end{code}

% vim: ft=tex fo-=m fo-=M:

