(*<*)
theory AxiomaticCategoryTheory imports Main
begin 
declare [[ smt_solver = cvc4 ]]
(*
declare [[ smt_timeout = 200 ]]
declare [[ z3_options = "-memory:1500" ]]
*)
(*>*)

text{*
\begin{abstract}
Starting from a generalization of the standard axioms for a monoid we present a stepwise development 
of various, mutually equivalent foundational axiom systems for category theory. 
Our axiom sets have been formalized in the Isabelle/HOL interactive proof assistant, and this
formalization utilizes a semantically correct embedding of free logic 
in classical higher-order logic. The modeling and formal analysis of our axiom sets has been 
significantly supported  by series of experiments with automated reasoning tools integrated 
with Isabelle/HOL. We also address the relation of our axiom systems to alternative proposals 
from the literature, including an axiom set proposed by Freyd and Scedrov for which we reveal 
a technical issue (when encoded in free logic): either all operations, e.g. morphism composition, are total or 
their axiom system is inconsistent. The repair for this problem is quite straightforward, however. 
\end{abstract}
*}

section {* Introduction *}

text {* 
We present a stepwise development of axiom systems for category theory by generalizing 
the standard axioms for a monoid to a partial composition operation. Our purpose is not to make or
claim any contribution to category theory but rather to show how formalizations involving the kind 
of logic required (free logic) can be validated within modern proof assistants. 

A total of eight different axiom systems is studied. The systems I-VI are shown to 
be equivalent. The axiom system VII slightly modifies axiom system VI to obtain (modulo 
notational transformation) the set of axioms as proposed by  Freyd and Scedrov in their textbook
 ``Categories, Allegories'' @{cite "FreydScedrov90"}, published in 1990; 
see also Subsection \ref{subsec:FreydNotation} where we present their original system.
While the axiom systems I-VI are shown to be  consistent, a constricted inconsistency result is 
obtained for system VII (when encoded in free logic where free variables range over all 
objects): We can prove @{text "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<rightarrow> False"}, where @{text "E"} is the existence predicate. Read this as: If there 
are undefined objects, e.g. the value of an undefined composition @{text "x\<cdot>y"}, then we have falsity.
By contraposition, all objects (and thus all compositions) must exist. But when we assume the latter,
then the axiom system VII essentially reduces categories to monoids.
We note that axiom system V, which avoids this problem, corresponds to a set of axioms proposed 
by Scott @{cite "Scott79"} in the 1970s. The problem can also be avoided by restricting the variables 
in axiom system VII to range only over existing objects and by postulating strictness conditions. 
This gives us axiom system VIII.

Our exploration has been significantly supported by series of experiments in which automated reasoning tools 
have been called from within the proof assistant Isabelle/HOL @{cite "Isabelle"} via the Sledgehammer 
tool @{cite "Sledgehammer"}. Moreover, we have obtained very useful feedback at various stages 
from the model finder Nitpick @{cite "Nitpick"} saving us from making several mistakes.

At the conceptual level this paper exemplifies a new style of explorative mathematics which rests 
on a significant amount of human-machine interaction with integrated interactive-auto\-ma\-ted 
theorem proving technology. The experiments we have conducted are such that the required 
reasoning is often too tedious and time-consuming for humans to be carried out repeatedly with 
highest level of precision. It is here where cycles of formalization and experimentation efforts in 
Isabelle/HOL provided  significant support. Moreover, the technical inconsistency issue for
axiom system VII was discovered by automated theorem provers, which further emphasises the added 
value of automated theorem proving in this area. 

To enable our experiments we have exploited an embedding of free logic @{cite "Scott67"} 
in classical higher-order logic, which we have recently presented in a related paper @{cite "C57"}.


We also want to emphasize that this paper has been written entirely within the Isabelle 
framework by utilizing the Isabelle ``build'' tool; cf. @{cite "IsabelleManual2016"}, Section~2. 
It is thus an example of a formally verified mathematical document, where the PDF document as 
presented here has been generated directly from the verified source files mentioned above.
We also note that once the proofs have been mechanically checked, they are generally easy 
to find by hand using paper and pencil.

*}


section {* Embedding of Free Logic in HOL *}

text {* Free logic models partial functions as total functions over a ``raw domain'' @{text "D"}. 
A subset @{text "E"} of @{text "D"} is used to characterize the subdomain of ``existing'' objects; cf.
@{cite "Scott67"} for further details.

The experiments presented in the subsequent sections exploit our embedding of free logic 
in HOL @{cite "C57"}. This embedding is trivial for the standard Boolean connectives. The interesting
aspect is that free logic quantifiers are guarded in the embedding by an explicit existence 
predicate @{text "E"} (associated with the subdomain @{text "E"} of @{text "D"}), so 
that quantified variables range only over existing objects, while free 
variables and arbitrary terms may also denote undefined/non-existing objects outside of @{text "E"}. 
This way we obtain an 
elegant treatment of partiality resp. undefinednes as required in category theory. In our related 
paper @{cite "C57"} we also show how definite description can be appropriately modeled in this
approach. However, the definite description is not required for purposes of this paper, so we omit it.
Note that the connectives and quantifiers of free logic are displayed below in bold-face fonts. Normal, 
non-bold-face connectives and quantifiers in contrast belong to the meta-logic HOL. The prefix ``f'',
e.g. in @{text "fNot"}, stands for ``free''. 
*}

typedecl i -- {* Type for individuals *}
consts fExistence:: "i\<Rightarrow>bool" ("E") --{* Existence/definedness predicate in free logic *}

abbreviation fNot ("\<^bold>\<not>") --{* Free negation *}                          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies (infixr "\<^bold>\<rightarrow>" 13) --{* Free implication *}        
 where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
abbreviation fIdentity (infixr "\<^bold>=" 13) --{* Free identity *}        
 where "l \<^bold>= r \<equiv> l = r"
abbreviation fForall ("\<^bold>\<forall>") --{* Free universal quantification guarded by existence 
                                predicate @{text "E"}*}                  
 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E x \<longrightarrow> \<Phi> x"   
abbreviation fForallBinder (binder "\<^bold>\<forall>" [8] 9) --{* Binder notation *} 
 where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"

text {* Further free logic connectives can now be defined as usual. *}

abbreviation fOr (infixr "\<^bold>\<or>" 11)                                 
 where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 12)                                
 where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"    
abbreviation fImplied (infixr "\<^bold>\<leftarrow>" 13)       
 where "\<phi> \<^bold>\<leftarrow> \<psi> \<equiv> \<psi> \<^bold>\<rightarrow> \<phi>" 
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 15)                             
 where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"  
abbreviation fExists ("\<^bold>\<exists>")                                       
 where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     
 where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"

text {* In this framework partial and total functions are modelled as follows: 
A function @{text "f"} is total if and only if for all @{text "x"} we have @{text "E x \<^bold>\<rightarrow> E(f x)"}. 
For partial functions @{text "f"} we may have some @{text "x"} such that @{text "E x"} but not
 @{text "E(f x)"}. A function @{text "f"} is strict  if  and only if for all @{text "x"} 
we have @{text "E(f x) \<^bold>\<rightarrow> E x"}.
*} 

section {* Preliminaries *}

text {* Morphisms in the category are objects of type @{text "i"}. We introduce three partial functions, 
@{text "dom"} (domain), @{text "cod"} (codomain), and @{text "\<cdot>"} (morphism composition). 
Partiality of composition is handled exactly as expected: we generally may have 
non-existing compositions @{text "x\<cdot>y"} (i.e.~@{text "\<^bold>\<not>(E(x\<cdot>y))"}) for some existing  
morphisms @{text "x"} and @{text "y"} (i.e.~@{text "E x"} and @{text "E y"}).
 *}


consts 
 domain:: "i\<Rightarrow>i" ("dom _" [108] 109) 
 codomain:: "i\<Rightarrow>i" ("cod _" [110] 111) 
 composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

text {* For composition @{text "\<cdot>"} we assume set-theoretical composition here (i.e., functional 
composition from right to left). This means that
\[@{text "(cod x)\<cdot>(x\<cdot>(dom x)) \<cong> x"}\] and that \[@{text "(x\<cdot>y)a \<cong> x(y a)"}\quad \text{when}\quad
@{text "dom x \<simeq> cod y"}\] 
The equality symbol @{text "\<cong>"} denotes Kleene equality and it
is defined as follows (where @{text "="} is identity on all objects, existing or non-existing, 
of type @{text "i"}): *}

abbreviation KlEq (infixr "\<cong>" 56) -- {* Kleene equality *}
 where "x \<cong> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<^bold>= y"  

text {* 
Reasoning tools in Isabelle quickly confirm that @{text "\<cong>"} is an equivalence relation. 
But existing identity @{text "\<simeq>"}, in contrast, is only symmetric and transitive, and lacks 
reflexivity. It is defined as:
*}

abbreviation ExId (infixr "\<simeq>" 56) -- {* Existing identity *}  
 where "x \<simeq> y \<equiv> E x \<^bold>\<and> E y \<^bold>\<and> x \<^bold>= y"

text {* We have: *}

lemma "x \<cong> x \<^bold>\<and> (x \<cong> y \<^bold>\<rightarrow> y \<cong> x) \<^bold>\<and> ((x \<cong> y \<^bold>\<and> y \<cong> z) \<^bold>\<rightarrow> x \<cong> z)" 
  by blast
lemma "x \<simeq> x" -- {* This does not hold; Nitpick finds a countermodel.\footnote{The keyword
  ``oops'' in Isabelle/HOL indicates a failed/incomplete proof attempt; the respective (invalid) conjecture is 
  then not made available for further use. The simplest countermodel for the conjecture given
  here consists of single, non-existing element. } *}
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops  
lemma " (x \<simeq> y \<^bold>\<rightarrow> y \<simeq> x) \<^bold>\<and> ((x \<simeq> y \<^bold>\<and> y \<simeq> z) \<^bold>\<rightarrow> x \<simeq> z)" 
  by blast
lemma "x \<simeq> y \<^bold>\<rightarrow> x \<cong> y" 
  by simp
lemma "x \<simeq> y \<^bold>\<leftarrow> x \<cong> y" -- {* Nitpick finds a countermodel *}
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 

text {* 
Next, we define the identity morphism predicate @{text "I"} as follows: 
*}

abbreviation I where "I i \<equiv> (\<^bold>\<forall>x. E(i\<cdot>x) \<^bold>\<rightarrow> i\<cdot>x \<cong> x) \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>i) \<^bold>\<rightarrow> x\<cdot>i \<cong> x)"

text {* This definition was suggested by an exercise in @{cite "FreydScedrov90"} on p.~4.
In earlier experiments we used a longer definition which can be proved equivalent on the basis
of the other axioms. For monoids, where composition is total, @{text "I i"} means @{text "i"} is
a two-sided identity — and such are unique. For categories the property is much weaker.
*}
 
section {* Axiom Set I *}

text {*  Axiom Set I is our most basic axiom set for category theory generalizing the 
axioms for a monoid to a partial composition operation. Remember that a monoid is an 
algebraic structure $(S,\circ)$, where $\circ$ is a binary operator on set $S$, 
satisfying the following properties:

\begin{tabular}{ll}
Closure: & $ \forall a,b \in S.\ a \circ b \in S$ \\
Associativity: & $\forall a,b,c \in S.\ a \circ (b \circ c) = (a \circ b) \circ c$ \\
Identity: & $\exists id_S \in S. \forall a\in S.\ id_S\circ a = a = a \circ id_S$
\end{tabular}

That is, a monoid is a semigroup with a two-sided identity element.

Our first axiom set for category theory employs a partial, strict binary 
composition operation @{text "\<cdot>"}, and the existence of left and right identity elements is 
addressed in the last two axioms. The notions of @{text "dom"} (Domain) and @{text "cod"} (Codomain)
abstract from their common meaning in the context of sets. In category theory we
work with just a single type of objects (the type @{text "i"} of morphisms) and therefore 
identity morphisms are employed to suitably characterize their meanings. 
*}

(*<*)
context -- {* Axiom Set I *}
assumes 
(*>*)
 S\<^sub>i: --{*\makebox[2cm][l]{Strictness:}*} "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
 E\<^sub>i: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
 A\<^sub>i: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i: --{*\makebox[2cm][l]{Codomain:}*} "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y" and
 D\<^sub>i: --{*\makebox[2cm][l]{Domain:}*} "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x" 
(*<*) 
begin
(*>*)

(*
abbreviation Dom where 
  "Dom \<equiv> SOME j. (\<forall>x. (E(x) \<^bold>\<rightarrow> (I(j(x)) \<^bold>\<and> x\<cdot>(j(x)) \<cong> x)))"
*)

text {* Nitpick confirms that this axiom set is consistent. *}
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  

text {* Even if we assume there are non-existing objects we get consistency (which is e.g. not the
case for Axiom Set VII below). *}  
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  -- {* Nitpick finds a model\footnote{To display the models or countermodels from Nitpick in the Isabelle/HOL system interface 
simply put the mouse on the expression "nitpick".}  *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 

text {* We may also assume an existing and a non-existing object and still get consistency. *}  
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 

text {* The left-to-right direction of existence axiom @{text "E\<^sub>i"} is implied. *}
  lemma E\<^sub>iImplied: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    by (metis A\<^sub>i C\<^sub>i S\<^sub>i)

text {* We can prove that the @{text "i"} in axiom @{text "C\<^sub>i"} is unique. The proofs can be 
   found automatically by Sledgehammer.\footnote{In our initial experiments proof reconstruction of the
   external ATP proofs failed in Isabelle/HOL. The SMT reasoner Z3 @{cite "Z3"}, which is employed
   in the @{text "smt"} tactic by default, was too weak. Therefore we first introduced further lemmata, 
   which helped. 
   However, an alternative way out, which we discovered later, has been to replace Z3 by CVC4 @{cite "CVC4"} 
   in Isabelle's @{text "smt"} 
   tactic (this can be done by stating ``@{text "declare [[ smt_solver = cvc4]]"}'' in the source document).
   In the latest version of the proof document we now suitably switch between the two SMT solvers to obtain best results.} *}
(* lemma L1i: "E y \<^bold>\<rightarrow> (\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<forall>j. E j \<^bold>\<rightarrow> ((I j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j)))" 
    by (smt A\<^sub>i C\<^sub>i S\<^sub>i) 
  lemma L2i: "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<forall>j. E j \<^bold>\<rightarrow> ((I j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j))" 
    using C\<^sub>i L1i by blast  *)
  lemma UC\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<^bold>\<forall>j.(I j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j)" 
    by (smt A\<^sub>i C\<^sub>i S\<^sub>i)  

 text {* Analogously, the provers quickly show that @{text "j"} in axiom @{text "D"} is unique. *}
  lemma UD\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x \<^bold>\<and> (\<^bold>\<forall>i.(I i \<^bold>\<and> x\<cdot>i \<cong> x) \<^bold>\<rightarrow> j \<cong> i)"  
    by (smt A\<^sub>i D\<^sub>i S\<^sub>i) 

 text {* However, the @{text "i"} and @{text "j"} need not be equal. Using the Skolem 
   function symbols @{text "C"} and @{text "D"} this can be encoded in
   our formalization as follows: *}
 lemma "(\<exists>C D. (\<^bold>\<forall>y. I (C y) \<^bold>\<and> (C y)\<cdot>y \<cong> y) \<^bold>\<and> (\<^bold>\<forall>x. I (D x) \<^bold>\<and> x\<cdot>(D x) \<cong> x) \<^bold>\<and> \<^bold>\<not>(D \<^bold>= C))"
   nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops  -- {* Nitpick finds a model. *}
 text {* Nitpick finds a model for cardinality @{text "i = 2"}. This model consists of two non-existing
   objects @{text "i\<^sub>1"} and @{text "i\<^sub>2"}. @{text "C"} maps both @{text "i\<^sub>1"} and @{text "i\<^sub>2"} to
   @{text "i\<^sub>2"}. @{text "D"} maps @{text "i\<^sub>1"} to @{text "i\<^sub>2"}, and vice versa. The composition 
   @{text "i\<^sub>2\<cdot>i\<^sub>2"}
   is mapped to @{text "i\<^sub>2"}. All other composition pairs are mapped to @{text "i\<^sub>1"}.
   *}
(* Skolem constants:
    Cod = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>2, i\<^sub>2 := i\<^sub>2)
    Dom = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>2, i\<^sub>2 := i\<^sub>1)
  Constants:
    op \<cdot> = (\<lambda>x. _)((i\<^sub>1, i\<^sub>1) := i\<^sub>1, (i\<^sub>1, i\<^sub>2) := i\<^sub>1, (i\<^sub>2, i\<^sub>1) := i\<^sub>1, (i\<^sub>2, i\<^sub>2) := i\<^sub>2)
    E = (\<lambda>x. _)(i\<^sub>1 := False, i\<^sub>2 := False) *)
 text {* Even if we require at least one existing object Nitpick still finds a model: *}
 lemma "(\<exists>x. E x) \<^bold>\<and> (\<exists>C D. (\<^bold>\<forall>y. I (C y) \<^bold>\<and> (C y)\<cdot>y \<cong> y) \<^bold>\<and> (\<^bold>\<forall>x. I (D x) \<^bold>\<and> x\<cdot>(D x) \<cong> x) \<^bold>\<and> \<^bold>\<not>(D \<^bold>= C))"
   nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops  -- {* Nitpick finds a model. *}
 text {* Again the model is of cardinality @{text "i = 2"}, but now we have a non-existing @{text "i\<^sub>1"} and 
  and an existing @{text "i\<^sub>2"}. Composition @{text "\<cdot>"} and @{text "C"} are as above, but 
  @{text "D"} is now identity on all objects.  *}
(* 
  Nitpick found a model for card i = 2:
  Skolem constants:
  Skolem constants:
    C = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>2, i\<^sub>2 := i\<^sub>2)
    D = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>1, i\<^sub>2 := i\<^sub>2)
    x = i\<^sub>2
  Constants:
    op \<cdot> = (\<lambda>x. _)((i\<^sub>1, i\<^sub>1) := i\<^sub>1, (i\<^sub>1, i\<^sub>2) := i\<^sub>1, (i\<^sub>2, i\<^sub>1) := i\<^sub>1, (i\<^sub>2, i\<^sub>2) := i\<^sub>2)
    E = (\<lambda>x. _)(i\<^sub>1 := False, i\<^sub>2 := True)
*)
(*<*)
end
(*>*)



section {* Axiom Set II *}

text {* Axiom Set II is developed from Axiom Set I by Skolemization of @{text "i"} and @{text "j"} 
 in axioms @{text "C\<^sub>i"} and @{text "D\<^sub>i"}. We can argue semantically that every model of Axiom Set I has such 
 functions. Hence, we get a conservative extension of Axiom Set I. This could be done for any 
 theory with an ``@{text "\<forall>x.\<exists>i."}''-axiom. The strictness axiom @{text "S"} is extended, 
 so that strictness is now also postulated for the new Skolem functions @{text "dom"} 
 and @{text "cod"}. Note: the values of Skolem functions outside E can just be given by 
the identity function.
 *}

(*<*)
context -- {* Axiom Set II *}
assumes 
(*>*)
 S\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Strictness:}*} "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
 A\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Codomain:}*} "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
 D\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Domain:}*} "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
(*<*)
begin  
(*>*)

text {* As above, we first check for consistency. *}
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 

text {* The left-to-right direction of existence axiom @{text "E\<^sub>i\<^sub>i"} is implied. *}
  lemma E\<^sub>i\<^sub>iImplied: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    by (metis A\<^sub>i\<^sub>i C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)

text {* Axioms @{text "C\<^sub>i\<^sub>i"} and @{text "D\<^sub>i\<^sub>i"}, together with @{text "S\<^sub>i\<^sub>i"}, show that
@{text "dom"} and @{text "cod"} are total functions -- as intended. *}
lemma domTotal: "E x \<^bold>\<rightarrow> E(dom x)" 
  by (metis D\<^sub>i\<^sub>i S\<^sub>i\<^sub>i) 
lemma codTotal: "E x \<^bold>\<rightarrow> E(cod x)" 
  by (metis C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)  

text {* Axiom Set II implies Axiom Set I.\footnote{Axiom Set I also implies Axiom Set II. This can 
be shown by semantical means on the meta-level. We have also attempted to prove this equivalence 
within Isabelle/HOL, but so far without final success. However, we succeed to 
prove that the following holds: @{text "\<exists>Cod Dom. 
              ((\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y))) \<^bold>\<and> 
               (\<forall>x y. E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))) \<^bold>\<and> 
               (\<forall>x y z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z) \<^bold>\<and> 
               (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and>
               (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x)
              )"}. Note that the inclusion of strictness of @{text "Cod"} and @{text "Dom"} is still missing.} *}
  lemma S\<^sub>iFromII: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)"  
    using S\<^sub>i\<^sub>i by blast
  lemma E\<^sub>iFromII: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    using E\<^sub>i\<^sub>i by blast
  lemma A\<^sub>iFromII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i by blast
  lemma C\<^sub>iFromII: "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y" 
    by (metis C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
  lemma D\<^sub>iFromII: "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x" 
    by (metis D\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
(*<*)
end
(*>*)

section {* Axiom Set III *}

text {*  In Axiom Set III the existence  axiom  @{text "E"} is simplified by taking advantage of 
  the two new Skolem functions @{text "dom"} and @{text "cod"}. *}

(*<*)
context -- {* Axiom Set III *}
assumes
(*>*) 
 S\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Strictness:}*} "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
 A\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Codomain:}*} "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
 D\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Domain:}*} "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
(*<*)
begin
(*>*)
  
text {* The obligatory consistency check is positive. *}
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops   

text {* The left-to-right direction of existence axiom @{text "E\<^sub>i\<^sub>i\<^sub>i"} is implied. *}
  lemma E\<^sub>i\<^sub>i\<^sub>iImplied: "E(x\<cdot>y) \<^bold>\<rightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" 
    by (metis (full_types) A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)

text {* Moreover, Axiom Set II is implied. *}
  lemma S\<^sub>i\<^sub>iFromIII: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>i\<^sub>i by blast
  lemma E\<^sub>i\<^sub>iFromIII: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    by (metis A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i E\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
  lemma A\<^sub>i\<^sub>iFromIII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i\<^sub>i by blast
  lemma C\<^sub>i\<^sub>iFromIII: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" 
    using C\<^sub>i\<^sub>i\<^sub>i by auto
  lemma D\<^sub>i\<^sub>iFromIII: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
    using D\<^sub>i\<^sub>i\<^sub>i by auto
(*<*)
end
(*>*)

text {* A side remark on the experiments: All proofs above and all proofs in the rest of this paper 
 have been obtained fully automatically with the Sledgehammer tool in Isabelle/HOL. This
 tool interfaces to prominent first-order automated theorem provers such as CVC4 @{cite "CVC4"}, 
 Z3 @{cite "Z3"}, E @{cite "E"} and Spass @{cite "Spass"}. 
 Remotely, also provers such as Vampire @{cite "Vampire"}, or the higher-order provers 
 Satallax @{cite "Satallax"} and LEO-II @{cite "LEO"} 
 can be reached. For example, to prove lemma @{text "E\<^sub>i\<^sub>i\<^sub>iFromII"} we have called Sledgehammer on all 
 postulated axioms of the theory: @{text "sledgehammer (S\<^sub>i\<^sub>i E\<^sub>i\<^sub>i A\<^sub>i\<^sub>i C\<^sub>i\<^sub>i D\<^sub>i\<^sub>i)"}.  
 The provers then, via Sledgehammer, suggested to call trusted/verified tools in Isabelle/HOL
 with the exactly required dependencies they detected. In lemma @{text "E\<^sub>i\<^sub>i\<^sub>iFromII"}, for 
 example, all  axioms from Axiom Set II are required. With the provided dependency information 
 the trusted tools in Isabelle/HOL were then able to reconstruct the external proofs on their own.
 This way we obtain a verified Isabelle/HOL document in which all the proofs have nevertheless been contributed
 by automated theorem provers. *}

text {* Axiom Set II also implies Axiom Set III. Hence, both theories are
 equivalent. The only interesting case is lemma @{text "E\<^sub>i\<^sub>i\<^sub>iFromII"}, the other cases are 
 trivial. *}

(*<*)
context -- {* Axiom Set II *}
assumes
 S\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Strictness:}*} "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
 A\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Codomain:}*} "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
 D\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Domain:}*} "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
begin
(*>*)  

  lemma S\<^sub>i\<^sub>i\<^sub>iFromII: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>i by blast
  lemma E\<^sub>i\<^sub>i\<^sub>iFromII: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> (E(cod y)))" 
    by (metis C\<^sub>i\<^sub>i D\<^sub>i\<^sub>i E\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
  lemma A\<^sub>i\<^sub>i\<^sub>iFromII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i by blast
  lemma C\<^sub>i\<^sub>i\<^sub>iFromII: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" 
    using C\<^sub>i\<^sub>i by auto
  lemma D\<^sub>i\<^sub>i\<^sub>iFromII: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
    using D\<^sub>i\<^sub>i by auto
(*<*)
end
(*>*)


section {* Axiom Set IV *}

text {* Axiom Set IV simplifies the axioms @{text "C\<^sub>i\<^sub>i\<^sub>i"} and  @{text "D\<^sub>i\<^sub>i\<^sub>i"}. However, as it turned 
 out, these simplifications also require the existence axiom @{text "E\<^sub>i\<^sub>i\<^sub>i"} to be strengthened into
 an equivalence. *}

(*<*)
context -- {* Axiom Set IV *}
assumes
(*>*)
 S\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Strictness:}*} "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
 A\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Codomain:}*} "(cod y)\<cdot>y \<cong> y" and
 D\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Domain:}*} "x\<cdot>(dom x) \<cong> x" 
(*<*)
begin
(*>*)

text {* The obligatory consistency check is again positive. *}
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 

text {* The Axiom Set III is implied. The only interesting cases are 
 lemmata @{text "C\<^sub>i\<^sub>i\<^sub>iFromIV"} and @{text "D\<^sub>i\<^sub>i\<^sub>iFromIV"}. Note that the strengthened 
 axiom @{text "E\<^sub>i\<^sub>v"} is used here. *}
  lemma S\<^sub>i\<^sub>i\<^sub>iFromIV: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>v by blast
  lemma E\<^sub>i\<^sub>i\<^sub>iFromIV: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> (E(cod y)))" 
    using E\<^sub>i\<^sub>v by blast
  lemma A\<^sub>i\<^sub>i\<^sub>iFromIV: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>v by blast
  lemma C\<^sub>i\<^sub>i\<^sub>iFromIV: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" 
    by (metis C\<^sub>i\<^sub>v D\<^sub>i\<^sub>v E\<^sub>i\<^sub>v)
  lemma D\<^sub>i\<^sub>i\<^sub>iFromIV: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)"
    by (metis C\<^sub>i\<^sub>v D\<^sub>i\<^sub>v E\<^sub>i\<^sub>v)
(*<*)
end
(*>*)

text {* Vice versa, Axiom Set III implies Axiom Set IV. Hence, both theories are
 equivalent. The interesting cases are lemmata @{text "E\<^sub>i\<^sub>vFromIII"}, @{text "C\<^sub>i\<^sub>vFromIII"}
 and @{text "D\<^sub>i\<^sub>vFromIII"}. *}

(*<*)
context -- {* Axiom Set III *}
assumes
 S\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Strictness:}*} "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
 A\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Codomain:}*} "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
 D\<^sub>i\<^sub>i\<^sub>i: --{*\makebox[2cm][l]{Domain:}*} "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
begin
(*>*)  

  lemma S\<^sub>i\<^sub>vFromIII: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>i\<^sub>i by blast
  lemma E\<^sub>i\<^sub>vFromIII: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" 
    by (metis (full_types) A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i E\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
  lemma A\<^sub>i\<^sub>vFromIII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i\<^sub>i by blast
  lemma C\<^sub>i\<^sub>vFromIII: "(cod y)\<cdot>y \<cong> y" 
    using C\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i by blast
  lemma D\<^sub>i\<^sub>vFromIII: "x\<cdot>(dom x) \<cong> x" 
    using D\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i by blast
(*<*)
end
(*>*)


section {* Axiom Set V *}

text {* Axiom Set V has been proposed by Scott @{cite "Scott79"} in the 1970s. This set of
 axioms is equivalent to the axiom set presented by Freyd and Scedrov in their textbook
 ``Categories, Allegories'' @{cite "FreydScedrov90"} when encoded in free logic, corrected/adapted and further simplified. 
 Their axiom set is technically flawed when encoded in our given context. This issue has been detected by automated theorem provers
 with the same technical infrastructure as employed so far. See the subsequent section  
 for more details. 
 We have modified the axioms of @{cite "FreydScedrov90"} by replacing the original Kleene 
 equality @{text "\<cong>"} in axiom S3 by the
 non-reflexive, existing identity @{text "\<simeq>"}. Note that the modified axiom @{text "S3"} is equivalent to @{text "E\<^sub>i\<^sub>v"};
 see the mutual proofs below.  
*}

(*<*)
context -- {* Axiom Set V (Freyd and Scedrov when corrected and simplified) *}
assumes 
(*>*)
 S1: --{*\makebox[2cm][l]{Strictness:}*} "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: --{*\makebox[2cm][l]{Strictness:}*} "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 S4: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: --{*\makebox[2cm][l]{Codomain:}*} "(cod y)\<cdot>y \<cong> y" and
 S6: --{*\makebox[2cm][l]{Domain:}*} "x\<cdot>(dom x) \<cong> x"
(*<*)
begin
(*>*)

text {* The obligatory consistency check is again positive. *}
  lemma True -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 

text {* The Axiom Set IV is implied. The only interesting cases are 
 lemmata @{text "S\<^sub>i\<^sub>vFromV"} and @{text "E\<^sub>i\<^sub>vFromV"}.*}
  lemma S\<^sub>i\<^sub>vFromV: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"   
    using S1 S2 S3 by blast
  lemma E\<^sub>i\<^sub>vFromV: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" 
    using S3 by metis
  lemma A\<^sub>i\<^sub>vFromV: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using S4 by blast
  lemma C\<^sub>i\<^sub>vFromV: "(cod y)\<cdot>y \<cong> y" 
    using S5 by blast
  lemma D\<^sub>i\<^sub>vFromV: "x\<cdot>(dom x) \<cong> x" 
    using S6 by blast
(*<*)
end
(*>*)


text {* Vice versa, Axiom Set IV implies Axiom Set V. Hence, both theories are
 equivalent. *}

(*<*)
context -- {* Axiom Set IV *}
assumes
 S\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Strictness:}*} "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
 A\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Codomain:}*} "(cod y)\<cdot>y \<cong> y" and
 D\<^sub>i\<^sub>v: --{*\makebox[2cm][l]{Domain:}*} "x\<cdot>(dom x) \<cong> x" 
begin
(*>*)
  lemma S1FromV:  "E(dom x) \<^bold>\<rightarrow> E x" 
    using S\<^sub>i\<^sub>v by blast
  lemma S2FromV:  "E(cod y) \<^bold>\<rightarrow> E y" 
    using S\<^sub>i\<^sub>v by blast
  lemma S3FromV:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    using E\<^sub>i\<^sub>v by metis
  lemma S4FromV:  "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>v by blast
  lemma S5FromV:  "(cod y)\<cdot>y \<cong> y" 
    using C\<^sub>i\<^sub>v by blast
  lemma S6FromV:  "x\<cdot>(dom x) \<cong> x" 
    using D\<^sub>i\<^sub>v by blast
(*<*)
end
(*>*)

section {* Axiom Sets VI and VII *}

text {* The axiom set of Freyd and Scedrov from their textbook
 ``Categories, Allegories'' @{cite "FreydScedrov90"} becomes inconsistent in our free logic setting if we assume 
  non-existing objects of type @{text "i"}, respectively, if we assume that the operations are 
  non-total.  Freyd and Scedrov employ a different notation for 
  @{text "dom x"} and @{text "cod x"}. They denote these operations by @{text "\<box>x"} 
  and @{text "x\<box>"}. Moreover, they employ diagrammatic composition @{text "(f\<cdot>g) x \<cong> g(f x)"} 
  (functional composition from left to right) instead of the set-theoretic 
  definition @{text "(f\<cdot>g) x \<cong> f(g x)"} (functional composition from right to left) used so far.
 
  We leave it to the reader to verify that their axiom system corresponds to the 
  axiom system given below modulo an appropriate conversion of notation.\footnote{A recipe for 
  this translation is as follows: (i) replace all @{text "x\<cdot>y"} by @{text "y\<cdot>x"}, 
(ii) rename the variables to get them again in alphabetical order,
(iii) replace @{text "\<phi>\<box>"} by @{text "cod \<phi>"} and @{text "\<box>\<phi>"}  by @{text "dom \<phi>"}, and finally
(iv) replace @{text "cod y \<cong> dom x"} (resp. @{text "cod y \<simeq> dom x"}) 
   by @{text "dom x \<cong> cod y"} (resp. @{text "dom x \<simeq> cod y"}).}
  In Subsection 9.2 we will also analyze their axiom system using their original notation.


  A main difference in the system by Freyd and Scedrov to our Axiom Set V from above concerns
  axiom @{text "S3"}. Namely, instead of the non-reflexive @{text "\<simeq>"}, they use Kleene 
  equality @{text "\<cong>"}, cf. definition 1.11 on page 3 of @{cite "FreydScedrov90"}.\footnote{Def. 1.11 in Freyd 
  Scedrov: ``The ordinary equality sign @{text "="} [i.e., our @{text "\<cong>"}] will be used in the
  symmetric sense, to wit: if either side is defined then so is the other and they are equal. \ldots''} 
  The difference seems minor, but in our free logic setting it has the effect to cause the mentioned
  constricted inconsistency issue. This could perhaps be an oversight, or it could indicate
  that Freyd and Scedrov actually mean the Axiom Set VIII below (where the variables in the axioms range 
  over defined objects only). However, in Axiom Set VIII we had to (re-)introduce explicit 
  strictness conditions to ensure equivalence to the Axiom Set V by Scott.
*}

subsection {* Axiom Set VI *}

(*<*)
context -- {* Axiom Set VI *}
assumes
(*>*)
  A1: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 A2a: "cod(dom x) \<cong> dom x" and  
 A2b: "dom(cod y) \<cong> cod y" and  
 A3a: "x\<cdot>(dom x) \<cong> x" and 
 A3b: "(cod y)\<cdot>y \<cong> y" and 
 A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
(*<*)
begin
(*>*)

text {* The obligatory consistency checks are again positive. 
 But note that this only holds when we use @{text "\<simeq>"} instead of  @{text "\<cong>"} in  @{text "A1"}. *}
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 

text {* Axiom Set VI implies Axiom Set V. *}
  lemma S1FromVI: "E(dom x) \<^bold>\<rightarrow> E x" 
    by (metis A1 A2a A3a)
  lemma S2FromVI: "E(cod y) \<^bold>\<rightarrow> E y" 
    using A1 A2b A3b by metis
  lemma S3FromVI: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    by (metis A1)
  lemma S4FromVI: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A5 by blast
  lemma S5FromVI: "x\<cdot>(dom x) \<cong> x" 
    using A3a by blast
  lemma S6FromVI: "(cod y)\<cdot>y \<cong> y" 
    using A3b by blast

text {* Note, too, that Axiom Set VI is redundant. For example, axioms @{text "A4a"} and @{text "A4b"} are
  implied from the others. This kind of flaw in presenting axioms in our view is a more serious oversight.
  The automated theorem provers can quickly reveal such redundancies. *}
  lemma A4aRedundant: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" 
    using A1 A2a A3a A5 by metis
  lemma A4bRedundant: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))"  
    using A1 A2b A3b A5 by metis
text {* Our attempts to further reduce the axioms set @{text "(A1 A2a A2b A3a A3b A5)"}  were not successful.
Alternatively, we can e.g. keep @{text "A4a"} and @{text "A4b"} and show that axioms @{text "A2a"} 
and @{text "A2b"} are implied. *}
(*<*)declare [[ smt_solver = z3]](*>*) 
  lemma A2aRedundant: "cod(dom x) \<cong> dom x" 
    using A1 A3a A3b A4a A4b by smt
  lemma A2bRedundant: "dom(cod y) \<cong> cod y" 
    using  A1 A3a A3b A4a A4b by smt 
text {* Again, attempts to further reduce the set @{text "(A1 A3a A3b A4a A4b A5)"} were not successful.
   Other reduced sets of axioms we identified in experiments are @{text "(A1 A2a A3a A3b A4b A5)"} and
    @{text "(A1 A2b A3a A3b A4a A5)"}. Attempts to remove axioms @{text "A1"}, @{text "A3a"}, 
    @{text "A3b"}, and @{text "A5"} from Axiom Set VI failed. Nitpick shows that they are independent. 

   However, when assuming strictness of @{text "dom"} and @{text "cod"}, the axioms @{text "A2a"}, 
   @{text "A2b"}, @{text "A4a"} and @{text "A4b"} are all implied. Hence, under this 
   assumptions, the reasoning tools quickly identify @{text "(A1 A3a A3b A5)"} as a minimal axiom 
   set, which then exactly matches the Axiom Set V from above.\footnote{This minimal set of axioms 
   is also mentioned by Freyd in @{cite "Freyd16"} and attributed to Martin Knopman. However, the proof
   sketch presented there seems to fail when the adapted version of A1 (with @{text "\<simeq>"}) is employed.}
*}
(*<*)
end
(*>*) 
text {* Axiom Set V implies Axiom Set VI. Hence, both theories are equivalent. *}
(*<*)
context -- {* Axiom Set V (Freyd and Scedrov) when adapted/corrected and simplified)  *}
assumes
 S1: --{*\makebox[2cm][l]{Strictness:}*} "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: --{*\makebox[2cm][l]{Strictness:}*} "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and 
 S4: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: --{*\makebox[2cm][l]{Domain:}*} "x\<cdot>(dom x) \<cong> x" and
 S6: --{*\makebox[2cm][l]{Codomain:}*} "(cod y)\<cdot>y \<cong> y" 
begin
(*>*)
  lemma  A1FromV: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    using S3 by blast
  lemma A2aFromV: "cod(dom x) \<cong> dom x"  
    by (metis S1 S2 S3 S5)
  lemma A2bFromV: "dom(cod y) \<cong> cod y"  
    using S1 S2 S3 S6 by metis
  lemma A3aFromV: "x\<cdot>(dom x) \<cong> x" 
    using S5 by blast
  lemma A3bFromV: "(cod y)\<cdot>y \<cong> y" 
    using S6 by blast
  lemma A4aFromV: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)"
    by (metis S1 S3 S4 S5 S6)
  lemma A4bFromV: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" 
    by (metis S2 S3 S4 S5 S6)
  lemma  A5FromV: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using S4 by blast
(*<*)
end
(*>*)


subsection {* Axiom Set VII *}

text {* We now study the constricted inconsistency in Axiom Set VI when replacing  @{text "\<simeq>"}  
 in  @{text "A1"} by  @{text "\<cong>"}. We call this Axiom Set VII. This set corresponds
 modulo representational transformation to the axioms as presented by Freyd and Scedrov. Remember, however,
 that the free variables are ranging here over all objects, defined or undefined. Below, when we study
 Axiom Set VIII, we will restrict the variables to range only over existing objects.  *}

(*<*)
context -- {* Axiom Set VII (Freyd and Scedrov in our notation) *}
assumes
(*>*)
  A1: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
 A2a: "cod(dom x) \<cong> dom x " and  
 A2b: "dom(cod y) \<cong> cod y" and  
 A3a: "x\<cdot>(dom x) \<cong> x" and 
 A3b: "(cod y)\<cdot>y \<cong> y" and 
 A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
(*<*)
begin
(*>*)

text {* A model can still be constructed if we do not make assumptions about non-existing
  objects. In fact, the model presented by Nitpick consists of a single, existing morphism.  *}
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops -- {* Nitpick finds a model *}

text {* However, one can see directly that axiom  @{text "A1"} is problematic as written:
If  @{text "x"} and  @{text "y"} are undefined, then (presumably)  @{text "dom x"} and 
@{text "cod y"} are undefined as well, and by the definition of Kleene equality,
 @{text "dom x \<cong> cod y"}. @{text "A1"} stipulates that @{text "x\<cdot>y"}  
should be defined in this case, which appears unintended.

We shall see that the consequences of this version of the axiom are
even stronger. It implies that \emph{all} objects are defined,
that is, composition (as well as @{text "dom"} and @{text "cod"}) become total operations.
The theory described by these axioms ``collapses'' to the theory of
monoids. (If all objects are defined, then one can conclude from @{text "A1"} that 
@{text "dom x \<cong> dom y"} (resp.~@{text "dom x \<cong> cod y"} and @{text "cod x \<cong> cod y"}), 
and according to 1.14 of @{cite "FreydScedrov90"}, 
the category reduces to a monoid provided that it is not empty.) *}
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick does *not* find a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = none] oops

text {* In fact, the automated theorem provers quickly prove falsity when assuming a 
 non-existing object of type @{text "i"}. The provers identify the axioms @{text "A1"}, @{text "A2a"}
 and @{text "A3a"} to cause the problem under this assumption.*}
  lemma InconsistencyAutomaticVII: "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<rightarrow> False" 
    by (metis A1 A2a A3a)

   text {* Hence, all morphisms must be defined in theory of Axiom Set VII, or in other 
      words, all operations must be total. *}
  lemma "\<forall>x. E x" using InconsistencyAutomaticVII by auto

text {* The constricted inconsistency proof can be turned into an interactive mathematical argument: *}

  lemma InconsistencyInteractiveVII: 
    assumes NEx: "\<exists>x. \<^bold>\<not>(E x)" shows False 
  proof -
    -- {* Let @{text "a"} be an undefined object *}
   obtain a where 1: "\<^bold>\<not>(E a)" using NEx by auto
    -- {* We instantiate axiom @{text "A3a"} with @{text "a"}. *}
   have 2: "a\<cdot>(dom a) \<cong> a" using A3a by blast  
    -- {* By unfolding the definition of @{text "\<cong>"} we get from 1 that
        @{text "a\<cdot>(dom a)"} is not defined. This is 
        easy to see, since if @{text "a\<cdot>(dom a)"} were defined, we also had that @{text "a"} is 
        defined, which is not the case by assumption.*}
   have 3: "\<^bold>\<not>(E(a\<cdot>(dom a)))" using 1 2 by metis
    -- {* We instantiate axiom @{text "A1"} with @{text "a"} and @{text "dom a"}. *}
   have 4: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<cong> cod(dom a)" using A1 by blast
    -- {* We instantiate axiom @{text "A2a"} with @{text "a"}. *}
   have 5: "cod(dom a) \<cong> dom a" using A2a by blast 
    -- {* We use 5 (and symmetry and transitivity of @{text "\<cong>"}) to rewrite the 
         right-hand of the equivalence 4 into @{text "dom a \<cong> dom a"}. *} 
   have 6: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<cong> dom a" using 4 5 by auto
    -- {* By reflexivity of @{text "\<cong>"} we get that @{text "a\<cdot>(dom a)"} must be defined. *}
   have 7: "E(a\<cdot>(dom a))" using 6 by blast
    -- {* We have shown in 7 that @{text "a\<cdot>(dom a)"} is defined, and in 3 
         that it is undefined. Contradiction. *}
   then show ?thesis using 7 3 by blast
  qed
(*<*)
end
(*>*)


text {* We present the constricted inconsistency argument once again, but this time in the original
  notation of Freyd and Scedrov. *}

consts  
   source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
   target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
   compositionF:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<^bold>\<cdot>" 110)

(*<*)
context -- {* Axiom Set VI (Freyd and Scedrov) in their notation *}   
assumes           
(*>*)

  A1: "E(x\<^bold>\<cdot>y) \<^bold>\<leftrightarrow> (x\<box> \<cong> \<box>y)" and 
 A2a: "((\<box>x)\<box>) \<cong> \<box>x" and 
 A2b: "\<box>(x\<box>) \<cong> \<box>x" and 
 A3a: "(\<box>x)\<^bold>\<cdot>x \<cong> x" and 
 A3b: "x\<^bold>\<cdot>(x\<box>) \<cong> x" and 
 A4a: "\<box>(x\<^bold>\<cdot>y) \<cong> \<box>(x\<^bold>\<cdot>(\<box>y))" and 
 A4b: "(x\<^bold>\<cdot>y)\<box> \<cong> ((x\<box>)\<^bold>\<cdot>y)\<box>" and 
  A5: "x\<^bold>\<cdot>(y\<^bold>\<cdot>z) \<cong> (x\<^bold>\<cdot>y)\<^bold>\<cdot>z"
(*<*)
begin
(*>*)

text {* \label{subsec:FreydNotation} Again, the automated theorem provers via Sledgehammer 
       find the constricted inconsistency very quickly and they identify the  exact dependencies. *}

lemma InconsistencyAutomatic: "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<rightarrow> False" 
  by (metis A1 A2a A3a)

text {* The following alternative interactive proof is slightly shorter than the one 
        presented above. *}
  lemma InconsistencyInteractive: assumes NEx: "\<exists>x. \<^bold>\<not>(E x)" shows False 
  proof -
    -- {* Let @{text "a"} be an undefined object *}
   obtain a where 1: "\<^bold>\<not>(E a)" using assms by auto
    -- {* We instantiate axiom @{text "A3a"} with @{text "a"}. *}
   have 2: "(\<box>a)\<^bold>\<cdot>a \<cong> a" using A3a by blast
    -- {* By unfolding the definition of @{text "\<cong>"} we get from 1 that @{text "(\<box>a)\<^bold>\<cdot>a"} is 
         not defined. This is 
         easy to see, since if @{text "(\<box>a)\<^bold>\<cdot>a"} were defined, we also had that  @{text "a"} is 
         defined, which is not the case by assumption. *}
   have 3: "\<^bold>\<not>(E((\<box>a)\<^bold>\<cdot>a))" using 1 2 by metis
    -- {* We instantiate axiom @{text "A1"} with @{text "\<box>a"} and @{text "a"}. *}
   have 4: "E((\<box>a)\<^bold>\<cdot>a) \<^bold>\<leftrightarrow> (\<box>a)\<box> \<cong> \<box>a" using A1 by blast
    -- {* We instantiate axiom @{text "A2a"} with @{text "a"}. *}
   have 5: "(\<box>a)\<box> \<cong> \<box>a" using A2a by blast 
    -- {* From 4 and 5 we obtain @{text "\<^bold>(E((\<box>a)\<^bold>\<cdot>a))"} by propositional logic. *} 
   have 6: "E((\<box>a)\<^bold>\<cdot>a)" using 4 5 by blast 
    -- {* We have @{text "\<^bold>\<not>(E((\<box>a)\<^bold>\<cdot>a))"} and @{text "E((\<box>a)\<^bold>\<cdot>a)"}, hence Falsity. *}
   then show ?thesis using 6 3 by blast
  qed

text {* Obviously Axiom Set VII is also redundant, and we have previously reported 
on respective redundancies @{cite "C57"}. However, this was before the discovery of the above 
constricted inconsistency issue, which tells us that the system (in our setting) can even be reduced 
to @{text "A1"}, @{text "A2a"} and @{text "A3a"} (when we additionally assume @{text "NEx"}). *}
(*<*)
end
(*>*)

section {* Axiom Set VIII *}

text {* We study the axiom system by Freyd and Scedrov once again. However, this time we restrict 
the free variables in their system to range over existing objects only. By employing the free logic 
universal quantifier @{text "\<^bold>\<forall>"} we thus modify Axiom Set VII as follows:*}   
(*<*)
context -- {* Axiom Set VII (Freyd and Scedrov) in our notation *}
assumes
(*>*)
  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
 B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " and  
 B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" and  
 B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" and 
 B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" and 
 B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
(*<*)
begin
(*>*)
text {* Now, the two consistency checks succeed. *}
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 

text {* However, this axiom set is obviously weaker than our Axiom Set V. In fact, none of 
the @{text "V"}-axioms are implied: *}

  lemma S1: "E(dom x) \<^bold>\<rightarrow> E x"  -- {* Nitpick finds a countermodel *}  
    nitpick [user_axioms, show_all, format = 2] oops 
  lemma S2: "E(cod y) \<^bold>\<rightarrow> E y"  -- {* Nitpick finds a countermodel *}  
    nitpick [user_axioms, show_all, format = 2] oops 
  lemma S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y"   -- {* Nitpick finds a countermodel *} 
    nitpick [user_axioms, show_all, format = 2] oops 
  lemma S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"   -- {* Nitpick finds a countermodel *} 
    nitpick [user_axioms, show_all, format = 2] oops 
  lemma S5: "x\<cdot>(dom x) \<cong> x"   -- {* Nitpick finds a countermodel *} 
    nitpick [user_axioms, show_all, format = 2] oops 
  lemma S6: "(cod y)\<cdot>y \<cong> y"   -- {* Nitpick finds a countermodel *} 
    nitpick [user_axioms, show_all, format = 2] oops 
(*<*)
end
(*>*)

text {* The situation changes when we explicitly postulate strictness of @{text "dom"},
@{text "cod"} and @{text "\<cdot>"}. We thus obtain our Axiom Set VIII: *}
(*<*)
context -- {* Axiom Set VIII. *}
assumes
(*>*)
 B0a: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
 B0b: "E(dom x) \<^bold>\<rightarrow> E x" and
 B0c: "E(cod x) \<^bold>\<rightarrow> E x" and
  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
 B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " and  
 B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" and  
 B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" and 
 B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" and 
 B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
(*<*)
begin
(*>*)
text {* Again, the two consistency checks succeed *}
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  -- {* Nitpick finds a model *} 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 


text {* Now Axiom Set V is implied. *}
  lemma S1FromVIII: "E(dom x) \<^bold>\<rightarrow> E x"  using B0b by blast
  lemma S2FromVIII: "E(cod y) \<^bold>\<rightarrow> E y"  using B0c by blast 
  lemma S3FromVIII: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" by (metis B0a B0b B0c B1 B3a)
  lemma S4FromVIII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" by (meson B0a B5) 
  lemma S5FromVIII: "x\<cdot>(dom x) \<cong> x" using B0a B3a by blast  
  lemma S6FromVIII: "(cod y)\<cdot>y \<cong> y" using B0a B3b by blast
(*<*)
end
(*>*)

text {* Vive versa, Axiom Set V implies Axiom Set VIII. Hence, both theories are equivalent. *}

(*<*)
context -- {* Axiom Set V (Freyd and Scedrov) when adapted/corrected and simplified)  *}
assumes
(*>*)
 S1: --{*\makebox[2cm][l]{Strictness:}*} "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: --{*\makebox[2cm][l]{Strictness:}*} "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and 
 S4: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: --{*\makebox[2cm][l]{Domain:}*} "x\<cdot>(dom x) \<cong> x" and
 S6: --{*\makebox[2cm][l]{Codomain:}*} "(cod y)\<cdot>y \<cong> y" 

(*<*)
begin
(*>*)

  lemma B0a: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using S1 S2 S3 by blast
  lemma B0b: "E(dom x) \<^bold>\<rightarrow> E x" using S1 by blast
  lemma B0c: "E(cod x) \<^bold>\<rightarrow> E x" using S2 by blast
  lemma  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" by (metis S3 S5)
  lemma B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " by (metis S3 S5)
  lemma B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" by (metis S3 S6)  
  lemma B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" using S5 by auto
  lemma B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" using S6 by blast
  lemma B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" by (metis S1 S3 S4 S5)
  lemma B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" by (metis S2 S3 S4 S6)
  lemma  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using S4 by blast
(*<*)
end
(*>*)

text {* Axiom Set VIII is redundant (as expected from previous observations).
The theorem provers quickly confirm that axioms @{text "B2a, B2b, B4a, B4b"} are implied. *}

(*<*)
context -- {* Axiom Set VII (Freyd and Scedrov) in our notation *}
assumes
(*>*)
 B0a: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
 B0b: "E(dom x) \<^bold>\<rightarrow> E x" and
 B0c: "E(cod x) \<^bold>\<rightarrow> E x" and
  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
 B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" and 
 B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" and 
  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  

(*<*)
begin
(*>*)

  lemma B2aRedundant: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " by (metis B0a B1 B3a) 
  lemma B2bRedundant: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" by (metis B0a B1 B3b) 
  lemma B4aRedundant: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" by (metis B0a B0b B1 B3a B5) 
  lemma B4bRedundant: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" by (metis B0a B0c B1 B3b B5) 
(*<*)
end
(*>*)

text {* Again, note the relation and similarity of the reduced Axiom Set VIII to Axiom Set V by Scott, 
which we prefer, since it avoids a mixed use of free and bound variables in the encoding and 
since it is smaller. *}


paragraph {* Acknowledgements *}
text {* We thank G\"unter Rote and Lutz Schr\"oder for their valuable comments to earlier drafts of this paper. *}

(*
section {* Observations during Experiments *}

text {*
\begin{itemize}
 \item ATPs often found proofs which couldn't be verified in Isabelle
 \item In many cases we had to remove certain axioms from ATP proof attempts in order to be successful:
   e.g. Asssociativity.
 \item Individual ATPs, in particular Z3, often gave false feedback, 
   like "The generated roblem is unprovable" while other provers contradicted this claim.
 \item The strongest FOF ATP seemes to be CVC4 in our experiments
 \item Suggested reconstruction with smt often did run into a timeout: \\
    SMT: Solver "z3": Timed out (setting the configuration option "smt_timeout" might help)
 \item Z3 often runs into an error: "z3": A prover error occurred:
exception Option raised (line 82 of "General/basics.ML")
 \item Suggested reconstruction with smt often did run into error.
 \item Spass often reported: "An internal error occurred"
 \item In some case only LEO-II did find proofs.
 \item ATPs sometimes timeout on very trivial problems, e.g. proving the quantified version of 
   E\<^sub>i from Axiom Set I.
 \item The strengths of ATPs are surprisingly complementary. They all contributed.
 \item Nitpick's results could be better supported in the interface.
\end{itemize}
*}



section {* Conclusion *}
text {* todo *}      


context -- {* Axiom Set I *}
assumes 
 S\<^sub>i: --{*\makebox[2cm][l]{Strictness:}*} "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)"  and
 E\<^sub>i: --{*\makebox[2cm][l]{Existence:}*} "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
 A\<^sub>i: --{*\makebox[2cm][l]{Associativity:}*} "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i: --{*\makebox[2cm][l]{Codomain:}*} "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y" and
 D\<^sub>i: --{*\makebox[2cm][l]{Domain:}*} "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x" 
 
begin
(*>*)
 lemma S\<^sub>i': "\<forall>x y. E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using S\<^sub>i by blast
 lemma E\<^sub>i': "\<forall>x y. E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" using E\<^sub>i by blast
 lemma A\<^sub>i': "\<forall>x y z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A\<^sub>i by blast
 lemma COD: "(\<exists>Cod. (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y))" by (metis C\<^sub>i)
(* lemma COD_T1: "(\<exists>Cod. (\<forall>x. \<^bold>\<not>(E x) \<^bold>\<rightarrow> (Cod x) = x))" by auto
 lemma COD_T2: "\<exists>Cod. ((\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and> (\<forall>x. \<^bold>\<not>(E x) \<^bold>\<rightarrow> (Cod x) = x) \<^bold>\<and> (\<exists>x. E x))" 
    nitpick [satisfy,user_axioms, show_all] *)
 lemma DOM: "(\<exists>Dom. (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x) )" by (metis D\<^sub>i) 
 lemma L: "(\<exists>Cod Dom. 
              ((\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y))) \<^bold>\<and> 
               (\<forall>x y. E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))) \<^bold>\<and> 
               (\<forall>x y z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z) \<^bold>\<and> 
               (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and>
               (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x)
              ))" 
     using A\<^sub>i' COD DOM E\<^sub>i' S\<^sub>i' by blast
(*
 lemma L': "(Dom = (\<lambda>x. x) \<^bold>\<and> Cod = (\<lambda> x. x) \<^bold>\<rightarrow> 
              ((\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y))) \<^bold>\<and> 
               (\<forall>x y. E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))) \<^bold>\<and> 
               (\<forall>x y z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z) \<^bold>\<and> 
               (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and>
               (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x)
              ))" 
   sledgehammer ( A\<^sub>i' COD DOM E\<^sub>i' S\<^sub>i' )
   using A\<^sub>i' COD DOM E\<^sub>i' S\<^sub>i' by blast
*)

  lemma L1i': "E y \<^bold>\<rightarrow> (\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<forall>j. E j \<^bold>\<rightarrow> ((I j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j)))" 
    by (smt A\<^sub>i C\<^sub>i S\<^sub>i) 
  lemma L2i': "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<forall>j. E j \<^bold>\<rightarrow> ((I j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j))" 
    using C\<^sub>i L1i' by blast  
  lemma UC\<^sub>i': "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<^bold>\<forall>j.(I j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j)"  
    using L2i' by blast 

 text {* Analogously, the provers quickly shor that @{text "j"} in axiom @{text "D"} is unique. 
  Again, lemmata are need to succeed with proof reconstruction and verification. *}
  lemma L3i': "E(x) \<^bold>\<rightarrow> (\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x \<^bold>\<and> (\<forall>i. E i \<^bold>\<rightarrow> ((I i \<^bold>\<and> x\<cdot>i \<cong> x) \<^bold>\<rightarrow> j \<cong> i)))" 
    by (smt A\<^sub>i D\<^sub>i S\<^sub>i) 
  lemma L4i': "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x \<^bold>\<and> (\<forall>i. E i \<^bold>\<rightarrow> ((I i \<^bold>\<and> x\<cdot>i \<cong> x) \<^bold>\<rightarrow> j \<cong> i))" 
    using  C\<^sub>i L3i' by blast  
  lemma UD\<^sub>i': "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x \<^bold>\<and> (\<^bold>\<forall>i.(I i \<^bold>\<and> x\<cdot>i \<cong> x) \<^bold>\<rightarrow> j \<cong> i)"  
    using L4i' by blast  

 lemma SCod: "(\<exists>Cod. (\<forall>x. (E(Cod x) \<^bold>\<rightarrow> E x)))" 
  by auto

 lemma CODT1: "(\<exists>Cod. (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y \<^bold>\<and> E(Cod y) \<^bold>\<and> E y))" by (metis C\<^sub>i) 
 lemma DOMT1: "(\<exists>Dom. (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x \<^bold>\<and> E(Dom x) \<^bold>\<and> E x) )" by (metis D\<^sub>i) 
 

 lemma COD': "(\<exists>Cod. (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y \<^bold>\<and> (\<forall>x. (E(Cod x) \<^bold>\<rightarrow> E x))))" 
    sledgehammer [remote_leo2 remote_satallax, timeout = 100] (CODT1 S\<^sub>i')
    sledgehammer (CODT1 S\<^sub>i')
    sledgehammer [remote_leo2 remote_satallax, timeout = 100] (COD SCod UC\<^sub>i')
    sledgehammer (COD SCod UC\<^sub>i')
    using DOM nitpick


   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (S\<^sub>i' E\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (S\<^sub>i' E\<^sub>i' A\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (C\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (C\<^sub>i UC\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 100] (S\<^sub>i' E\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 100] (S\<^sub>i' E\<^sub>i' A\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 100] (C\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 100] (C\<^sub>i UC\<^sub>i)
   nitpick 
   sorry

 lemma COD'': "(\<exists>Cod. (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and> 
                      (\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(Cod x) \<^bold>\<rightarrow> E x))
              )" 
   using COD' S\<^sub>i' by blast

 lemma DOM': "(\<exists>Dom. (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x) \<^bold>\<and> (\<forall>x. (E(Dom x) \<^bold>\<rightarrow> E x)))" 
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (S\<^sub>i' E\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (S\<^sub>i' E\<^sub>i' A\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (S\<^sub>i' E\<^sub>i' A\<^sub>i' C\<^sub>i D\<^sub>i UD\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 600] (D\<^sub>i UD\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 60] (S\<^sub>i' E\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 60] (S\<^sub>i' E\<^sub>i' A\<^sub>i' C\<^sub>i D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 60] (D\<^sub>i)
   sledgehammer [remote_leo2 remote_satallax, timeout = 60] (D\<^sub>i UD\<^sub>i)
   nitpick 
   sorry
 lemma DOM'': "(\<exists>Dom. (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x) \<^bold>\<and> 
                      (\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(Dom x) \<^bold>\<rightarrow> E x))
              )" 
   using DOM' S\<^sub>i' by blast
 lemma CODDOM: "(\<exists>Cod Dom. 
                 (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and> 
                 (\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(Cod x) \<^bold>\<rightarrow> E x)) 
                 \<^bold>\<and>
                 (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x) \<^bold>\<and> 
                 (\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(Dom x) \<^bold>\<rightarrow> E x))
                )"
   using COD'' DOM'' by blast
 lemma CODDOM': 
               "(\<exists>Cod Dom. 
                 (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and> 
                 (\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y))) \<^bold>\<and> (\<forall>x. (E(Cod x) \<^bold>\<rightarrow> E x)) 
                 \<^bold>\<and>
                 (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x) \<^bold>\<and> 
                 (\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y))) \<^bold>\<and> (\<forall>x. (E(Dom x) \<^bold>\<rightarrow> E x))
                )"
   sledgehammer (CODDOM)
   using CODDOM by blast


  lemma CODDOM''': "(\<exists>Cod Dom. 
                      (\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y))) \<^bold>\<and> 
                      (\<forall>x. E(Cod x) \<^bold>\<rightarrow> E x) \<^bold>\<and> 
                      (\<forall>x. E(Dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and>
                      (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and> 
                      (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x)                       
              )" 
   sledgehammer (CODDOM')
   using CODDOM' by blast


         


 lemma L'': "(\<exists>Cod Dom. 
              ((\<forall>x y. (E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(Cod x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(Dom x) \<^bold>\<rightarrow> E x)) \<^bold>\<and> 
               (\<forall>x y. E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))) \<^bold>\<and> 
               (\<forall>x y z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z) \<^bold>\<and> 
               (\<^bold>\<forall>y. I (Cod y) \<^bold>\<and> (Cod y)\<cdot>y \<cong> y) \<^bold>\<and>
               (\<^bold>\<forall>x. I (Dom x) \<^bold>\<and> x\<cdot>(Dom x) \<cong> x)
              ))" 
   using A\<^sub>i' CODDOM''' E\<^sub>i' by blast 
end 


(*<*)
context -- {* Axiom Set VI (Freyd and Scedrov in their notation *}   
assumes           
(*>*)

 A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (x\<box> \<simeq> \<box>y)" and 
 A2a: "((\<box>x)\<box>) \<cong> \<box>x" and 
 A2b: "\<box>(x\<box>) \<cong> \<box>x" and 
 A3a: "(\<box>x)\<cdot>x \<cong> x" and 
 A3b: "x\<cdot>(x\<box>) \<cong> x" and 
 A4a: "\<box>(x\<cdot>y) \<cong> \<box>(x\<cdot>(\<box>y))" and 
 A4b: "(x\<cdot>y)\<box> \<cong> ((x\<box>)\<cdot>y)\<box>" and 
 A5:  "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"
(*<*)
begin
(*>*)
end
*)


(*<*)
end
(*>*)


