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

module Verified.Action where

open import Verified.Heap
\end{code}
%endif

\subsection{Choice of Actions}

%format Action = "\type{Action}"
%format ⊞ = "\cons{\boxplus}"
%format ∎_ = "\cons{\square\anonymous}"
%format ∎ = "\cons{\square}"
%format τ = "\cons{\tau}"
%format ⁺_ = "\cons{^\texttt{+}\anonymous}"
%format ⁺ = "\cons{^\texttt{+}}"
%format …_ = "\cons{...\anonymous}"
%format … = "\cons{...}"
%format ☢_ = "\cons{\text\Radioactivity\anonymous}"
%format ☢ = "\cons{\text\Radioactivity}"
%format ρ∧ω = "\rho{\wedge}\omega"
%if False
\begin{code}
infix 6 ⁺_ ∎_ …_ ☢_
\end{code}
%endif
As the addition operation is no longer non-deterministic, we may remove the
|⊞| action with only minor consequences. For transactions however, we extend
the set of actions with |☢_|, carrying with it a pair of read and write
transaction logs:
\begin{code}
data Action (L : Set) : Set where
  τ   : Action L
  ⁺_  : (x : L) → Action L
  ∎_  : (m : ℕ) → Action L
  …_  : (α : Action L) → Action L
  ☢_  : (ρ∧ω : Log × Log) → Action L
\end{code}

%if False
\begin{code}
private
  fmap : ∀ {L L′ : Set} → (L → L′) → Action L → Action L′
  fmap f τ = τ
  fmap f (… α) = … fmap f α
  fmap f (⁺ child) = ⁺ f child
  fmap f (∎ m) = ∎ m
  fmap f (☢ ρ∧ω) = ☢ ρ∧ω

rawFunctor : RawFunctor Action
rawFunctor = record { _<$>_ = fmap }
\end{code}
%endif

%format _≃τ = "\type{\anonymous{\simeq}\tau}"
%format ≃τ = "\postfix{\type{{\simeq}\tau}}"
%format is-τ = "\cons{is\text-\tau}"
%format is-… = "\cons{is\text-...}"
%format _≄τ = "\func{\anonymous{\not\simeq}\tau}"
%format ≄τ = "\postfix{\func{{\not\simeq}\tau}}"
%if False
\begin{code}
infix 3 _≃τ _≄τ
\end{code}
%endif
\noindent The silent and non-silent predicates on actions are defined in the
same way as we did for the Fork language:
\begin{code}
data _≃τ {l} : Action l -> Set where
  is-τ : τ ≃τ
  is-… : ∀ {α} → α ≃τ → (… α) ≃τ

_≄τ : ∀ {l} → Action l → Set
α ≄τ = ¬ α ≃τ
\end{code}
The proposition |α ≃τ| is inhabited precisely when |α| is considered silent,
with |α ≄τ| interpreted as its logical negation.

% vim: ft=tex fo-=m fo-=M:

