%if include /= True
\begin{comment}
%let include = True
%include Atomic/Common.lagda
%include Atomic/Heap.lagda
%include Atomic/Logs.lagda
%include Atomic/Language.lagda
\end{comment}
%endif

%if False
\begin{code}
module Combined where

open import Common
open import Heap
open import Language
\end{code}
%endif

\subsection{Combined Semantics}

%if False
\begin{code}
infix 7 ↣:_
infix 3 _▹_↠_ _↠⋆_
\end{code}
%endif

%format Combined = "\type{Combined}"
%format ↦: = "\cons{{\mapsto}{:}}"
%format ↣:_ = "\cons{{\rightarrowtail}{:}\anonymous}"
%format ↣: = "\cons{{\rightarrowtail}{:}}"
In a similar spirit to the combined machines of previous chapters, let us
define a |Combined| type that allows us to select which of our two semantics
to use to interpret some given expression:
\begin{code}
data Combined : Set where
  ↦: : Combined
  ↣:_ : (t : TState) → Combined
\end{code}
The |↦:| constructor indicates that the associated expression should be
interpreted according to the stop-the-world semantics, while |↣:_| implies
the log-based semantics. The latter is also used to carry around the
transaction state.
%format _▹_↠_ = "\type{\anonymous{\triangleright}\anonymous{\twoheadrightarrow}\anonymous}"
%format ↠ = "\infix{\type{\twoheadrightarrow}}"
%format ↠-↦ = "\cons{{\twoheadrightarrow}\text-{\mapsto}}"
%format ↠-↣ = "\cons{{\twoheadrightarrow}\text-{\rightarrowtail}}"
%format _↠⋆_ = "\type{\anonymous{\twoheadrightarrow^\star_\tau}\anonymous}"
%format ↠⋆ = "\infix{\type{\twoheadrightarrow^\star_\tau}}"
How this works can be seen in the definition of |_▹_↠_| below:
\begin{code}
data _▹_↠_ (α : Action) : Rel (Heap × Combined × Expression) where
  ↠-↦ : ∀ {h e h′ e′} →
    (e↦e′ :  α ▹ h ,       e ↦ h′ ,       e′)  →
             α ▹ h , ↦: ,  e ↠ h′ , ↦: ,  e′
  ↠-↣ : ∀ {h t e h′ t′ e′} →
    (e↣e′ :  α ▹ h ,     t , e ↣ h′ ,      t′ , e′)  →
             α ▹ h , ↣:  t , e ↠ h′ , ↣:   t′ , e′
\end{code}
This combined transition is essentially a disjoint union of |_▹_↦_| and
|_▹_↣_|. We will write |_↠⋆_| for an arbitrary sequence of silent |τ|
transitions:
\begin{code}
_↠⋆_ : Rel (Heap × Combined × Expression)
_↠⋆_ = Star (_▹_↠_ τ)
\end{code}

%if False
\begin{code}
infix 3 _▹_⤇_
\end{code}
%endif

%format _▹_⤇_ = "\type{\anonymous{\triangleright}\anonymous{\Mapsto}\anonymous}"
%format ⤇ = "\type{\Mapsto}"
%format ⤇: = "\cons{{\Mapsto}{:}}"
%format α≢τ = "\Varid{\alpha{\not\equiv}\tau}"
%format e↠⋆e′ = "\Varid{e{\twoheadrightarrow^\star_\tau}e\Prime}"
%format e′↠e″ = "\Varid{e\Prime{\twoheadrightarrow}e\PPrime}"
%{
%format α≢τ = "\name{\alpha{\not\equiv}\tau}"
%format e↠⋆e′ = "\name{e{\twoheadrightarrow^\star_\tau}e\Prime}"
%format e′↠e″ = "\name{e\Prime{\twoheadrightarrow}e\PPrime}"
Finally, let us define a visible transition as a sequence of silent |τ|
transitions followed by a single non-|τ| transition:
\begin{code}
record _▹_⤇_ (α : Action) (x x″ : Heap × Combined × Expression) : Set where
  constructor ⤇:
  field
    {h′}  : Heap
    {c′}  : Combined
    {e′}  : Expression
    α≢τ    : α ≢ τ
    e↠⋆e′  : x ↠⋆ h′ , c′ , e′
    e′↠e″  : α ▹ h′ , c′ , e′ ↠ x″
\end{code}
%}
The visible transition above is basically the same idea as that of the Fork
and Zap languages of the previous two chapters, but without a second
sequence of |τ|-transitions after the main |e′↠e″| transition.

% vim: ft=tex fo-=m fo-=M:

