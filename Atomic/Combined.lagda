%if False
\begin{code}
module Combined where

open import Common
open import Heap
open import Language
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

