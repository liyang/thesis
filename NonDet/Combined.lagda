%if include /= True
\begin{comment}
%let include = True
%include NonDet/Language.lagda
%include NonDet/Machine.lagda
%include NonDet/justification.lagda
\end{comment}
%endif

%if False
\begin{code}
import Level
open import Common

open import NonDet.Language
open import NonDet.Machine

module NonDet.Combined where
\end{code}
%endif

\section{Combined Machine and its Semantics}\label{sec:nondet-combined}

In this section, we introduce our key idea of a `combined machine', which we
arrive at by considering the small-step analogue of the compiler correctness
statement for big-step deterministic languages. The advantage of the
combined machine is that it lifts source expressions and target virtual
machine states into the same domain, which avoids the need for an
intermediate process calculus~\cite{wand95-parallel} and allows us to
directly establish a bisimulation between the source and target languages.

Our approach to non-deterministic compiler correctness is illustrated below,
%format injS = "\func{inj_S}"
%format injT = "\func{inj_T}"
%format ≈ = "\mathrel{\approx}"
\[\xymatrix@@C=6ex@@R=8ex{
	\text{Source}
		\PATH `ul^ur,[] []
			*!(2.05,2.1):(-0.05,-1)\dir{>}
		\xyar[rr]^{|compile|}
		\xyar[dr]_{|injS|}
	&&\text{Target}
		\PATH `dr^dl,[] []
			*!(-2,2.125):(-1,.14)\dir{>}
		\xyar[dl]^{|injT|}
\\
	&\text{Combined\;|/ ≈|}
		\PATH `dl^ul,[] []
			*!(-2.125,2):(.14,-1)\dir{>}
}\]
making use of such a combined machine, where the lifting by |injS| and
|injT| are trivial enough to be `obviously correct'. Rather than considering
final results, we consider combined machines up to a suitable notion of
bisimilarity.

%format Combined = "\type{Combined}"
%format ⟨_⟩ = "\cons{\langle\anonymous\rangle}"
%format ⟨⟩ = "\cons{\langle\rangle}"
In the case of our Zap language, a combined machine |x : Combined| has three
distinct phases of execution,
\begin{code}
data Combined : Set where
  ⟨_‚_⟩ : (e : Expression) (t : Machine) → Combined
  ⟨_⟩ : (t : Machine) → Combined
  ⟨⟩ : Combined
\end{code}
whose semantics is defined by the following transition relation:
%if False
\begin{code}
infix 3 _↠‹_›_
\end{code}
%endif
%format _↠‹_›_ = "\type{\anonymous{\twoheadrightarrow}\texttt{<}\anonymous\texttt{>}\anonymous}"
%format ↠‹ = "\type{{\twoheadrightarrow}\texttt{<}}"
%format ↠-↦ = "\cons{{\twoheadrightarrow}\text-{\mapsto}}"
%format ↠-↣ = "\cons{{\twoheadrightarrow}\text-{\rightarrowtail}}"
%format ↠-switch = "\cons{{\twoheadrightarrow}\text-switch}"
%format ↠-done = "\cons{{\twoheadrightarrow}\text-done}"
%format e↦e′ = "e{\mapsto}e\Prime{}"
%format t↣t′ = "t{\rightarrowtail}t\Prime{}"
\begin{code}
data _↠‹_›_ : LTS Label Combined where
  ↠-↦  : ∀ {e e′ t Λ}  (e↦e′ : e  ↦‹  Λ  › e′)  → ⟨ e  ‚ t ⟩  ↠‹ Λ › ⟨ e′ ‚ t ⟩
  ↠-↣  : ∀ {t t′ Λ}    (t↣t′ : t  ↣‹  Λ  › t′)  →      ⟨ t ⟩  ↠‹ Λ › ⟨ t′ ⟩
  ↠-switch  : ∀ {m c σ} →  ⟨ # m ‚ ⟨ c ‚ σ ⟩ ⟩   ↠‹ τ ›      ⟨ ⟨ c ‚ m ∷ σ ⟩ ⟩
  ↠-done    : ∀ {m} →      ⟨ ⟨ [] ‚ m ∷ [] ⟩ ⟩   ↠‹ ! ∎ m ›  ⟨⟩
\end{code}
The first constructor |⟨_‚_⟩| of |Combined| pairs an expression with
a virtual machine continuation. In this initial phase, a combined machine |⟨
e ‚ ⟨ c ‚ σ ⟩ ⟩| can be understood as the small-step analogue of the right
side of the |det-correct| statement---|exec (eval a ∷ σ) c|---which begins
by effecting the reduction of |a|. The applicable reductions are exactly
those of the |Expression| language, inherited via the |↠-↦| rule above.

When the expression |a| eventually reduces to a value |m|, the |↠-switch|
rule pushes |m| onto the stack |σ|, switching the combined machine to its
second phase of execution, corresponding to the |⟨_⟩| constructor. This can
be thought of as the small-step analogue of pushing the result |m ≡ eval a|
onto the stack, again following the right side of |det-correct|, namely
|exec (m ∷ σ) c|.

The second |Combined| constructor |⟨_⟩| lifts a virtual machine into
a combined machine, which then effects the reduction of the former via the
|↠-↣| rule. This corresponds to the small-step analogue of |exec σ c|, which
matches the left side of |det-correct|, and also the right side after the
evaluation of the embedded expression has completed.

Lastly, the |↠-done| rule embeds the computed result in a |∎| action, and
terminates with the empty |⟨⟩| state. This construction allows us to compare
final result values using the existing bisimulation machinery.

%The idea is that |<< a , t >>| follows exactly the transitions that |a| can
%make---via the |->>-||->| rule---until no further steps are possible.
%Since the expression must be a numeric value at this point, the |->>-switch|
%rule can now bridge the expression and virtual machine worlds by
%transferring the value onto the top of the machine continuation stack. The
%resulting state then follows |_>-><_>_| via the |->>->->| rule until all
%instructions are exhausted. Finally the |->>-done| rule emits a |Done|
%action, revealing the result.

% vim: ft=tex fo-=m fo-=M:

