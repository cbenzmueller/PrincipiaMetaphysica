(*<*)
theory FreeFOL 
imports Main 
begin
(*
% %------------------------------------------------------------
% \section{Introduction}

% %------------------------------------------------------------
% \section{Functionality??}
% \begin{itemize}
% \item Describe the functionality of the software.
% \item Address  wide audience (not just experts on the particular area).
% \item Use carefully chosen  simple(toy) examples, screen shots, etc.
% \end{itemize}
  
% %------------------------------------------------------------
% \section{Application??}
% \begin{itemize}
% \item Show important/non-trivial applications of the software.
% \item Address wide audience (not just experts on the particular area).
% \item Use carefully chosen  non-trivial  examples, screen shots, etc.
% \end{itemize}

% %------------------------------------------------------------
% \section{Underlying theory??}
% \begin{itemize}
% \item Explain briefly/informally the main theories/algorithms underlying the software.
% \item Address wide audience (not just experts on the particular area).
% \item If helps, use carefully chosen  simple  examples, diagrams, etc.
% \end{itemize}

% %------------------------------------------------------------
% \section{Technical contribution??}
% \begin{itemize}
% \item Discuss main technical challenges that had to be overcome, 
%       while developing the software.
% \item Address experts on the particular area.
% \item If helps, use carefully chosen  simple  examples, diagrams, etc.
% \end{itemize}

% %------------------------------------------------------------
% \begin{thebibliography}{4}
% \bibitem{...} .... 
% \end{thebibliography}
% \end{document}
*)
(*>*)
section \<open>Introduction\<close>
text \<open>Partiality and undefinedness are core concepts in various areas of mathematics.
Modern mathematical proof assistants and theorem proving systems are often based on traditional 
classical or intuitionistic logics and provide rather inadequate support 
for these challenge concepts.  
Free logic @{cite "sep-logic-free,scott67:_exist"}, in contrast, 
offers a theoretically and practically appealing solution. Unfortunately, however, 
we are not aware of any implemented and available theorem proving system for free logic.
 
In this extended abstract we show how free logic can be ``implemented'' in any 
theorem proving system for classical higher-order logic (HOL) @{cite "B5"}. The proposed solution 
employs a semantic embedding of free (or inclusive logic) in HOL. We 
present an exemplary implementation of this idea in the mathematical proof assistant 
Isabelle/HOL @{cite "NPW02"}. Various state-of-the-art first-order and higher-order automated 
theorem provers and model
finders are integrated (modulo suitable logic translations) with Isabelle via the Sledgehammer 
tool @{cite "Sledgehammer"}, so that our 
solution can be utilized, via Isabelle as foreground system, with a whole range of other background 
reasoners. As a result we obtain an elegant and powerful implementation
of an interactive and automated theorem proving (and model finding) system for free logic. 
  
To demonstrate the practical relevance of our new system, we report on first experiments in 
category theory. In these experiments, theorem provers were able 
to detect a (presumably unknown) redundancy in the foundational axiom system of the 
category theory textbook by Freyd and Scedrov @{cite "FreydScedrov90"}.
\<close>

section \<open>Free Logic\<close>
text \<open>
Terms in classical logic denote, without exceptions, entities in a
non-empty domain of (existing) objects \<open>\<^bold>D\<close>, and it are these objects of
\<open>\<^bold>D\<close> the universal and existential quantifiers do range over.
Unfortunately, however, these conditions may render classical logic
unsuited for handling mathematically relevant issues such as
undefinedness and partiality. For example in category theory
composition of maps is not always defined. 
\<close>

(* Motivated by problems and shortcomings in the handling of improper descriptions in the works of 
Russel, Frege and Hilbert-Bernays, the second author has proposed an alternative solution 
in his 1967 paper \emph{Existence and Description in Formal Logic} @{cite "scott67:_exist"}. *)

text \<open>
Free logic (and inclusive logic) has been proposed as an alternative
to remedy these shortcomings. It distinguishes between a raw domain of
possibly non-existing objects \<open>\<^bold>D\<close> and a particular subdomain \<open>\<^bold>E\<close> of \<open>\<^bold>D\<close>,
containing only the ``existing'' entities. Free variables range over \<open>\<^bold>D\<close>
and quantified variables only over \<open>\<^bold>E\<close>. Each term denotes in \<open>\<^bold>D\<close> but not
necessarily in \<open>\<^bold>E\<close>. The particular notion of free logic as exploited below has been
introduced by Scott @{cite "scott67:_exist"}. A graphical 
illustration of this notion of free logic is presented in Fig.~\ref{fig1}.

\begin{figure}
\centering
\scalebox{.8}{
\newcommand\firstellipse{(2,-5) ellipse (6cm and 4cm)}
\newcommand\secondellipse{(0,-5.3) ellipse (3.5cm and 2.5cm)}1
\begin{tikzpicture}
  \begin{scope}[fill opacity=1]
    \fill[gray!40] \firstellipse;
    \fill[gray!10] \secondellipse;
  \end{scope}
  \begin{scope}[very thick,font=\large]
    \draw \firstellipse node[font=\normalsize\bfseries] at (-.5,-5) {\underline{\textbf{E}: existing objects}};
    \draw \firstellipse node[font=\small] at (-.5,-5.5) {values of bound variables};
    \draw \secondellipse node[font=\normalsize\bfseries] at (4.3,-2.5) {\underline{\textbf{D}: raw objects}};
    \draw \secondellipse node[font=\small] at (4.3,-3) {values of free variables};
  \end{scope}
  \node[font=\normalsize\bfseries] at (6,-5) {$\star$};
  \node[font=\normalsize\bfseries] at (6,-5.3) {undefined};
\end{tikzpicture}
}
\caption{Illustration of the Semantical Domains of Free Logic \label{fig1}}
\end{figure}
\<close>

section \<open>Implementing Free Logic in Isabell/HOL\<close>
text \<open>
We start out with introducing a type i of individuals. The domain of objects associated with this 
this type will serve as the domain of raw objects \<open>\<^bold>D\<close>, cf. Fig~\ref{fig1}. Moreover, we 
introduce an existence predicate \<open>\<^bold>E\<close> on type i. As mentioned, \<open>\<^bold>E\<close> 
characterises the subset of existing objects in \<open>\<^bold>D\<close>. Next, we declare a special constant symbol 
star \<open>\<^bold>\<star>\<close>, which is intended to denote a distinguished ``non-existing'' element of \<open>\<^bold>D\<close>. 
\<close>

typedecl i   \<comment> "the type for indiviuals" 
consts fExistence:: "i\<Rightarrow>bool" ("\<^bold>E")    \<comment> "Existence predicate"
consts fStar:: "i" ("\<^bold>\<star>")   \<comment> "Distinguished symbol for undefinedness"

text \<open>
We postulate that \<open>\<^bold>\<star>\<close> is a ``non-existing'' object in \<open>D\<close>. 
\<close>

(* axiomatization where nonEmpty: "\<exists>x. \<^bold>E(x)" *)

axiomatization where fStarAxiom: "\<not>\<^bold>E(\<^bold>\<star>)"

text \<open>The two primitive logical connective we introduce for free logic are negation (\<open>\<^bold>\<not>\<close>) 
and implication (\<open>\<^bold>\<rightarrow>\<close>). 
They are identified with negation (\<open>\<not>\<close>) and implication (\<open>\<longrightarrow>\<close>) in the 
underlying Isabelle/HOL logic. The internal names in Isabelle/HOL of the new logical connectives  
are  \<open>fNot\<close> and \<open>fImplies\<close> (the prefix \<open>f\<close> stands for ``free'');
\<open>\<^bold>\<not>\<close> and the infix operator \<open>\<^bold>\<rightarrow>\<close> are introduced as syntactical sugar.\footnote{The
numbers in \<open>\<^bold>(infixr \<^bold>\<rightarrow> 49)\<close> and \<open>(binder \<^bold>\<forall> [8] 9)\<close> (see below) specify structural
priorities and thus  help to avoid brackets in formula representations.}  
\<close>
abbreviation fNot:: "bool\<Rightarrow>bool" ("\<^bold>\<not>")          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr "\<^bold>\<rightarrow>" 49)   
 where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 


text \<open>
The main challenge is to appropriately define free logic universal quantification (\<open>\<^bold>\<forall>\<close>) 
and free logic definite description (\<open>\<^bold>I\<close>).
Again, we are interested to relate these logical operators to the respective operators 
\<open>\<forall>\<close> and \<open>THE\<close> in the  Isabelle/HOL logic. Different to the trivial 
maps for \<open>\<^bold>\<not>\<close> and \<open>\<^bold>\<rightarrow>\<close> from above, their 
mappings are relativized in the sense that the existence predicate \<open>\<^bold>E\<close> is utilized as 
guard in their definitions.

The definition of the free logic universal quantifier \<open>\<^bold>\<forall>\<close> thus becomes:
\<close>
abbreviation fForall:: "(i\<Rightarrow>bool)\<Rightarrow>bool" ("\<^bold>\<forall>")                 
 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. \<^bold>E(x)\<longrightarrow>\<Phi>(x)"   
text \<open>
Apparently, this definitions restricts the set of objects the \<open>\<^bold>\<forall>\<close>-operator is ranging over to the
set of existing objects \<open>\<^bold>E\<close>. Note that this set can be empty (if desired, we may of course
simply postulate that the domain \<open>\<^bold>E\<close> is non-empty: \<open>\<exists>x. \<^bold>E(x)\<close>).

The Isabelle framework supports the introduction of syntactic sugar for binding notations.
Here we make use of this option to introduce binding notation for \<open>\<^bold>\<forall>\<close>. 
With the definition below we can now use the more familiar notation \<open>\<^bold>\<forall>x. \<phi>(x)\<close> 
instead of writing \<open>\<^bold>\<forall>(\<lambda>x. \<phi>(x))\<close> or \<open>\<^bold>\<forall>\<phi>\<close>.
\<close>
abbreviation fForallBinder:: "(i\<Rightarrow>bool)\<Rightarrow>bool" (binder "\<^bold>\<forall>" [8] 9) 
 where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"

text \<open>
Definite description \<open>\<^bold>I\<close> in free logic works as follows: Given an unary set $\Phi=\{a\}$, 
with $a$ being an ``existing'' element in \<open>\<^bold>E\<close>, \<open>\<^bold>I\<close> returns  the single element $a$ of $\Phi$. 
In all other cases, that is, if $\Phi$ is not unary or $a$ is not an element of \<open>\<^bold>E\<close>, 
\<open>\<^bold>I\<Phi>\<close> returns the distinguished ``non-existing'' object denoted by \<open>\<^bold>\<star>\<close>. With the 
help of Isabelle/HOL's definite description operator \<open>THE\<close>, \<open>\<^bold>I\<close> can thus 
be defined as follows:
\<close>
abbreviation fThat:: "(i\<Rightarrow>bool)\<Rightarrow>i" ("\<^bold>I") 
 where "\<^bold>I\<Phi> \<equiv> if \<exists>x. \<^bold>E(x) \<and> \<Phi>(x) \<and> (\<forall>y. (\<^bold>E(y) \<and> \<Phi>(y)) \<longrightarrow> (y = x)) 
              then THE x. \<^bold>E(x) \<and> \<Phi>(x) 
              else \<^bold>\<star>"

text \<open> 
Analogous to above we introduce binder notation for \<open>\<^bold>I\<close>, so that 
we can write \<open>\<^bold>Ix. \<phi>(x)\<close> instead of \<open>\<^bold>I(\<lambda>x. \<phi>(x))\<close> or \<open>\<^bold>I\<phi>\<close>.
\<close>
abbreviation fThatBinder:: "(i\<Rightarrow>bool)\<Rightarrow>i"  (binder "\<^bold>I" [8] 9) 
 where "\<^bold>Ix. \<phi>(x) \<equiv> \<^bold>I(\<phi>)"

text \<open> 
Further logical connectives of free can now be defined in the usual way (and for \<open>\<^bold>\<exists>\<close> we 
again introduce binder notation).
\<close>
abbreviation fOr (infixr "\<^bold>\<or>" 51) where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 52) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 50) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation fEquals (infixr "\<^bold>=" 56) where "x\<^bold>=y \<equiv> x=y"
abbreviation fExists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"


section \<open>Functionality Tests\<close> 
text \<open>
We exemplarily investigate some example proof problems from Scott's paper @{cite "scott67:_exist"}, pp. 183-184, 
where a free logic with a  single relation symbol 
\<open>\<^bold>r\<close> is discussed.
\<close>
consts r:: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "\<^bold>r" 70)   

text \<open>
The implication \<open>x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x\<close>, where \<open>x\<close> is a free variable, is valid 
independently whether \<open>x\<close> is defined (i.e. ``exists'') or not. In Isabelle/HOL this 
quickly confirmed by 
the simplification procedure simp.
\<close>
lemma "x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x" by simp  

text \<open>
However, as intended, the formula \<open>\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y\<close> is not valid, since set of existing
objects \<open>\<^bold>E\<close> could be empty.  Nitpick quickly presents a respective countermodel.
\<close>
lemma "\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y" nitpick [user_axioms] oops
text \<open>
Consequently, also the implication \<open>(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)\<close> has a countermodel,
where \<open>\<^bold>E\<close> is empty. 
\<close>
lemma "(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" nitpick [user_axioms]  oops
text \<open>
If we rule out that \<open>\<^bold>E\<close> is empty, e.g. with additional condition \<open>\<^bold>(\<^bold>\<exists>y. y \<^bold>= y)\<close> 
in the antecedent of the above formula, then we obtain a valid implication. Isabelle trivially 
proves this with procedure simp.
\<close>
lemma "((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> (\<^bold>\<exists>y. y \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" by simp
text \<open>
We analyse some further statements (respectively statement instances) from Scott's paper
@{cite "scott67:_exist"}, p. 185. Because of space restrictions we do not further comment these 
statements here. Altogether they provide further evidence that our implementation of free logic in fact 
obeys the intended properties.
\<close>
lemma S1: "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<Psi>(x)))" by auto
lemma S2: "\<^bold>\<forall>y. \<^bold>\<exists>x. x \<^bold>= y" by auto
lemma S3: "\<alpha> \<^bold>= \<alpha>" by auto
lemma S4: "(\<Phi>(\<alpha>) \<^bold>\<and> (\<alpha> \<^bold>= \<beta>)) \<^bold>\<rightarrow> \<Phi>(\<beta>)" by auto
lemma UI_1: "((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<and> (\<^bold>\<exists>x. x \<^bold>= \<alpha>)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" by auto
lemma UI_2: "(\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" nitpick [user_axioms] oops \<comment> "Countermodel by Nitpick"
lemma UI_cor1: "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y))" by auto
lemma UI_cor2: "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<^bold>\<not>(x \<^bold>= y)) \<^bold>\<rightarrow> \<^bold>\<not>(y \<^bold>= y))" by auto
lemma UI_cor3: "\<^bold>\<forall>y.((y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<exists>x. x \<^bold>= y))" by auto
lemma UI_cor4: "(\<^bold>\<forall>y. y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<forall>y.\<^bold>\<exists>x. x \<^bold>= y)" by simp
lemma Existence: "(\<^bold>\<exists>x. x \<^bold>= \<alpha>) \<longrightarrow> \<^bold>E(\<alpha>)" by simp (* ... to say that (\<^bold>\<exists>x. x = \<alpha>) is true means that the value of \<alpha> exists (properly) *)
lemma I1: "\<^bold>\<forall>y. ((y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))))" by (smt fStarAxiom the_equality)
abbreviation Star ("\<Otimes>") where "\<Otimes> \<equiv> \<^bold>Iy. \<^bold>\<not> (y \<^bold>= y)"
lemma StarTest: "\<Otimes> = \<^bold>\<star>" by simp
lemma I2: "\<^bold>\<not>(\<^bold>\<exists>y. y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<rightarrow>  (\<Otimes> \<^bold>= (\<^bold>Ix. \<Phi>(x)))" by (metis (no_types, lifting) the_equality)
lemma ExtI: "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<leftrightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>Ix. \<Phi>(x)) \<^bold>= (\<^bold>Ix. \<Psi>(x)))" by (smt the1_equality)
lemma I3: "(\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)" nitpick [user_axioms] oops \<comment> "Countermodel by Nitpick"
(*<*)
lemma Russel:     
 "((\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)) 
  \<^bold>\<rightarrow> 
  ((\<alpha> \<^bold>r (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<exists>y.((\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))) \<^bold>\<and> (\<alpha> \<^bold>r y))))"
 nitpick [user_axioms] oops
lemma "\<^bold>\<not>(\<^bold>\<exists>x. (x \<^bold>= (\<^bold>Iy. \<^bold>\<not> (y \<^bold>= y))))" using fStarAxiom by auto
lemma "(\<^bold>\<exists>x. x \<^bold>= a) \<^bold>\<rightarrow>  \<^bold>E(a)" by simp
consts ca::i cb::i 
axiomatization where ax1: "\<^bold>E(ca) \<^bold>\<and> \<^bold>E(cb) \<^bold>\<and> \<^bold>\<not> (ca \<^bold>= cb) \<^bold>\<and> \<^bold>\<not> (ca \<^bold>= \<Otimes>) \<^bold>\<and> \<^bold>\<not> (cb \<^bold>= \<Otimes>)"
lemma test2: "\<Otimes> \<^bold>= (\<^bold>I (\<lambda>x. x  \<^bold>= ca \<^bold>\<or> x \<^bold>= cb))" by (metis ax1)
(*<*)
end
(*>*)