%if include /= True
\begin{comment}
%let include = True
%include Fork/Language.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

module Fork.Action where
\end{code}
%endif

\subsection{Actions}

%format Action = "\type{Action}"
%format ⊞ = "\cons{\boxplus}"
%format ∎_ = "\cons{\square\anonymous}"
%format ∎ = "\cons{\square}"
%format τ = "\cons{\tau}"
%format ⁺_ = "\cons{^\texttt{+}\anonymous}"
%format ⁺ = "\cons{^\texttt{+}}"
%format …_ = "\cons{...\anonymous}"
%format … = "\cons{...}"
We extend the set of actions by |⁺ e|, to indicate the spawning of a new
thread |e|, and the action |… α| to indicate preemption of the foremost
thread:
%if False
\begin{code}
infix 6 ∎_ ⁺_ …_
\end{code}
%endif
\begin{code}
data Action (L : Set) : Set where
  τ : Action L
  ⊞ : Action L
  ∎_ : (m : ℕ) → Action L
  ⁺_ : (x : L) → Action L
  …_ : (α : Action L) → Action L
\end{code}
The above definition of |Action| is parametrised over the type of spawned
threads, either |Expression|s or |Machine|s. As we now have explicit
concurrency in the language, we no longer require the `zap' action or its
associated semantics.

%if False
\begin{code}
rawFunctor : RawFunctor Action
rawFunctor = record { _<$>_ = fmap } where
  fmap : ∀ {L L′ : Set} → (L → L′) → Action L → Action L′
  fmap f τ = τ
  fmap f ⊞ = ⊞
  fmap f (∎ m) = ∎ m
  fmap f (⁺ x) = ⁺ f x
  fmap f (… α) = … fmap f α
\end{code}
%endif

With the Zap language, a |τ| label sufficed to identify silent actions,
because its semantics does not diverge at points where silent transitions
occurred. With the Fork language, we have a `soup' of concurrent threads, of
which more than one may be able to make a silent transition at any given
point. Previously we mandated that distinct choices in the reduction path
must be labelled with distinct actions: in this case, we have folded the |τ|
label into the definition of |Action|, such that e.g.~both |τ| and |… τ| are
considered to be silent, yet they remain distinct.

This choice does complicate matters somewhat: in the two-level definition of
labels and actions in the Zap language, we could simply pattern match
a `label' with |τ| to determine if a transition was silent; in the same way,
we know \emph{a priori} that `actions' cannot be silent. With the Fork
language, we must use a more elaborate scheme:
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
\begin{code}
data _≃τ {l} : Action l → Set where
  is-τ  :                    τ   ≃τ
  is-…  : ∀ {α} → α ≃τ → (…  α)  ≃τ
\end{code}
The above type functions as a predicate on |Action|s: |α ≃τ| is inhabited
precisely when |α| is considered silent. Conversely, the negation of |_≃τ|
serves the same r\^ole for non-silent actions, defined as follows:
\begin{code}
_≄τ : ∀ {l} → Action l → Set
α ≄τ = ¬ α ≃τ
\end{code}

%format α≃τ = "\alpha{\simeq}\tau"
%format α≄τ = "\alpha{\not\simeq}\tau"
%format …α≄τ = "{...}\alpha{\not\simeq}\tau"

% vim: ft=tex fo-=m fo-=M:

