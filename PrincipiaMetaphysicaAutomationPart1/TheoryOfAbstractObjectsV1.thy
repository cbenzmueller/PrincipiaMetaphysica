(**) 
theory TheoryOfAbstractObjectsV1
imports Main

begin
(**)

section {* Introduction *}
 text {* 
 We present a formalisation and partial automation of an initial part of the (third authors)
 Principia Metaphysica \cite{zalta:_princ_metap} in Isabelle/HOL \cite{Isabelle}.  

 The Principia Metaphysica, which is based on and extends the Theory of Abstract 
 Objects \cite{zalta83:_abstr_objec}, 
 employs a modal relational type theory as logical foundation. Arguments
 defending this choice against a modal functional type theory 
 have been presented before \cite{zalta11:_relat_versus_funct_found_logic}.
 In a nutshell, the situation is this: functional type theory comes with strong 
 comprehension principles, which, in the context of the Theory of Abstract Objects, 
 have paradoxical implications. When starting off with a relational foundation, however, 
 weaker comprehension principles are provided, and these obstacles can be avoided.

 Isabelle/HOL is a proof assistant based on a functional type theory, 
 more precisely, Church's theory of types \cite{Church40}. Recently, it has been shown 
 that Church's type theory can be elegantly utilized as a meta-logic to encode and 
 automate various quantified non-classical logics, including modal functional type 
 theory \cite{J23,C40}. This work has subsequently been employed in a case study in
 computational metaphysics, in which different variants of Kurt Gödel's ontological 
 argument \cite{ECAI} were verified (respectively, falsified). 
 

 The motivating research questions for the work presented below include:
 \begin{itemize} 
 \item Can functional type theory, despite the problems as pointed by Zalta and Oppenheimer, 
  be utilized to encode the Theory of Abstract Objects when following the embeddings approach?
 \item How elegant and user-friendly is the resulting formalization? In other
  words, to what extend can Isabelle's  user interface be facilitated to hide 
  unpleasant technicalities of the (extended) embedding from the user?
 \item How far can automation be pushed in the approach? How much user interaction can
  be avoided in the formalization of the (first part) of the Principia Metaphysica? 
 \item Can the consistency of the theory be validated with the available automated 
  reasoning tools?
 \item Can the reasoners eventually even contribute some new knowledge? 
 \ldots
 \end{itemize}
 *}

 text {* The encoding of modal functional type theory in functional type theory as explored in 
 previous work \cite{J23,C40} is simple: modal logic formulas are identified with certain functional 
 type theory formulas of predicate type @{text "io"}. Possible worlds are explicitly represented by 
 terms of type  @{text "i"}. A modal logic @{text "\<phi>"} formula holds for a world @{text "w"} if and 
 only if the application @{text "\<phi> w"} evaluates to true. The definition of the propositional modal logic 
 connectives is then straightforward and it simply realizes the standard translation as a set of equations 
 in functional type theory. The approach has been successfully extended for quantifiers. A crucial 
 aspect thereby is that in simple type theory quantifiers can be treated
 as ordinary logical connectives. No extra binding mechanism is needed since the already existing 
 lambda binding mechanism can be elegantly utilized. 
  
 The challenge in this work is to appropriately 'restrict' this embedding for modal relational type theory.
  \begin{figure}[t]
 \includegraphics[height=5.5cm]{ModalRelationalTypeTheory.png}\includegraphics[height=4.5cm]{ModalRelationalTypeTheory2.png}
 \caption{Grammar of Modal Relational Type Theory. \label{mmrt}
 Note that two kinds of (complex) formulas are introduced: ones that may have encoding subformulas and ones that don’t.
 The latter are designated as propositional formulas, the former ones simply as formulas. }
 \end{figure}


 To achieve this  we provide means to explicitly represents and maintain information and constraints on the 
 syntactical structure of modal relational type theory, in particular, we provide means to distinguish 
 between propositional formulas, formulas, terms and erreneous (disallowed) formations. 
 This clearly creates some technical overhead. However, we exploit facilities in Isabelle/HOL's user 
 interface, and other means, to hide most of these technicalities from the user in applications. 
   
 *}


section {* Preliminaries *}
 text {* 
 We start out with some type declarations and type abbreviations. 
 Our formalism explicitly encodes Kripke style semantics. Hence, we introduce a 
 distinguished type @{text "i"} to represent the set of possible worlds. 
 Consequently, terms of this type denote possible worlds. 
 Moreover, modal logic formulas are associated in our approach with
 predicates (resp. sets) on possible worlds. Hence, modal logic formulas have
 type @{text "(i \<Rightarrow> bool)"}. To make our representation in the remainder more concise
 we abbreviate this type as @{text "io"}.
 *}

typedecl i
type_synonym io = "(i \<Rightarrow> bool)" 

 text {*
 Entities in the abstract theory of types are represented in our formalism by the
 type @{text "e"}. We call this the raw type of entities resp. objects. Later 
 on we will introduce means to distinguish between abstract and ordinary entities.    
 *}

typedecl e

 text {*
 To explicitly model the syntactical restrictions of modal relational type theory we introduce a 
 datatype @{text "'a opt"} based on four constructors:
 @{text "ERR 'a"} (identifies erroneous term constructions), @{text "P 'a"} (identifies 
 propositional formulas), @{text "F 'a"} (identifies  formulas), and @{text "T 'a"} (identifies 
 terms, such as lambda abstractions). The embeddings approach will be suitably adapted below so that 
 for each language expression (in the embedded modal relational type theory) the respective datatype 
 is identified and appropriately propagated. The encapsulated expressions (the polymorphic type @{text "'a"} 
 will be instantiated below) realize the actual modeling of the logic embedding analogous 
 to previous work for modal functional type theory.  
 *}

datatype 'a opt = ERR 'a | P 'a | F 'a | T 'a 

 text {* Some language constructs in the theory of abstract types, e.g. the actuality operator  
 @{text "\<A>"} (for "it is actually the case that"), refer to a (fixed) given world. To model such a 
 global world reference we introduce a
 constant symbol (name) @{text "cw"} of world type @{text "i"}. Moreover, for technical reasons, 
 which will be clarified below, we introduce further (dummy) constant symbols for various domains. Since
 we assume that all domains are non-empty, introducing these constant symbols is obviously not harmful. 
 *}

consts cw :: i 
consts de::"e" dio::"io" da::'a

section {* Embedding of Modal Relational Type Theory *}

 text {* The language constructs of modal relational type theory are introduced step by step. 
 *}

 text {* The actuality operator @{text "\<A>"} when applied to a formula or propositional formula 
 @{text "\<phi>"} evaluates @{text "\<phi>"} wrt the fixed given world @{text "cw"}. 
 The compound expression @{text "\<A> \<phi>"} inherits its syntactical category  (@{text "Form"} or
 @{text "PropForm"}) from @{text "\<phi>"}. If the syntactical catagory of  @{text "\<phi>"} is 
 @{text "Error"} or @{text "Term"}, then the syntactical catagory of @{text "\<A> \<phi>"} 
 is @{text "Error"} and a dummy entity of appropriate type is returned. This illustrates the very 
 idea of our explicit structure and constraints and this scheme will repeated below
 for all the other language constructs of modal relational type theory. 
 *}

abbreviation \<A>::"io opt \<Rightarrow> io opt" where "\<A> \<phi> \<equiv> case \<phi> of 
    F \<psi> \<Rightarrow> F(\<lambda>w. \<psi> cw) | P \<psi> \<Rightarrow> P(\<lambda>w. \<psi> cw) | _ \<Rightarrow> ERR dio"

 text {* The Principia Metaphysica distinguishes between encoding and exemplifying, ... say more ...

 Encoding @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} is noted here as @{text "\<kappa>\<^sub>1\<cdot>\<Pi>\<^sup>1"}. 
 Encoding yields formulas and never propositional formulas. In the embedding encoding 
 is identified with predicate application.
 *}


abbreviation Enc::"e opt\<Rightarrow>(e\<Rightarrow>io) opt\<Rightarrow>io opt"(**)("_\<cdot>_")(**) where "x\<cdot>\<Phi> \<equiv> case (x,\<Phi>) of 
    (T y,T Q) \<Rightarrow> F (\<lambda>w.(Q y) w) | _ \<Rightarrow> ERR dio"

 text {* Exemplifying formulas @{text "\<Pi>\<^sup>1\<kappa>\<^sub>1"} are noted here as @{text "\<Pi>\<^sup>1\<bullet>\<kappa>\<^sub>1"}.  
 Exemplification yields propositional formulas and never formulas. In the embedding exemplification 
 is identified with predicate application, just as encoding.
 *}

abbreviation Exe1::"(e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>io opt"(**)("_\<bullet>_")(**) where "\<Phi>\<bullet>x \<equiv> case (\<Phi>,x) of 
    (T Q,T y) \<Rightarrow> P (\<lambda>w.(Q y) w) | _ \<Rightarrow> ERR dio"

 text {* The Principia Metaphysica supports $n$-ary exemplification constructions. For pragmatical 
 reasons we consider here the cases only for $n\leq 3$.
 *}  

abbreviation Exe2::"(e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt"(**)("_\<bullet>_,_")(**) where "\<Phi>\<bullet>x1,x2 \<equiv> case (\<Phi>,x1,x2) of 
    (T Q,T y1,T y2) \<Rightarrow> P(\<lambda>w.(Q y1 y2) w) | _ \<Rightarrow> ERR dio"
abbreviation Exe3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt"(**)("_\<bullet>_,_,_") (**) where "\<Phi>\<bullet>x1,x2,x3 \<equiv> case (\<Phi>,x1,x2,x3) of 
    (T Q,T y1,T y2,T y3) \<Rightarrow> P (\<lambda>w.(Q y1 y2 y3) w) | _ \<Rightarrow> ERR dio"

 text {* Formations with negation and implication are supported for both, formulas  and propositional
 formulas, and their embeddings are straightforward.
 *}  

abbreviation negation::"io opt\<Rightarrow>io opt"(**)("\<^bold>\<not>")(**) where "\<^bold>\<not> \<phi> \<equiv> case \<phi> of 
    F \<psi> \<Rightarrow> F (\<lambda>w.\<not>(\<psi> w)) | P \<psi> \<Rightarrow> P(\<lambda>w.\<not>(\<psi> w)) | _ \<Rightarrow> ERR dio"  
abbreviation implication::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(**)(infixl "\<^bold>\<rightarrow>" 51)(**) where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (F \<alpha>,F \<beta>) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | (P \<alpha>,P \<beta>) \<Rightarrow> P(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | _ \<Rightarrow> ERR dio"  

 text {* Also universal quantification @{text "\<forall>(\<lambda>x.\<phi>)"} is supported for formulas  and propositional
 formulas. Following previous work the embedding maps @{text "\<forall>(\<lambda>x.\<phi>)"} to @{text "(\<lambda>w.\<forall>x.\<phi>xw)"}. *}

abbreviation universalQuantification::"('a\<Rightarrow>io opt)\<Rightarrow>io opt"(**)("\<^bold>\<forall>")(**) where "\<^bold>\<forall> \<Phi> \<equiv> case (\<Phi> da) of
    F \<phi> \<Rightarrow> F(\<lambda>w.\<forall>x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> w) | P \<phi> \<Rightarrow> P(\<lambda>w.\<forall>x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> w) | _ \<Rightarrow> ERR dio"

 text {* The modal box operator @{text "\<box>"} .... *}

abbreviation box::"io opt\<Rightarrow>io opt"(**)("\<^bold>\<box>")(**) where "\<^bold>\<box>\<phi> \<equiv> case \<phi> of 
    F \<psi> \<Rightarrow> F(\<lambda>w.\<forall>v. \<psi> v) | P \<psi> \<Rightarrow> P(\<lambda>w.\<forall>v. \<psi> v) | _ \<Rightarrow> ERR dio"  

 text {* n-ary lambda abstraction @{text "\<lambda>\<^sup>0,\<lambda>\<^sup>1,\<lambda>\<^sup>2,\<lambda>\<^sup>3,..."}, for $n\geq 0$, is supported in the Principia
 Metaphysica only for propositional formulas. ... say more about @{text "\<lambda>\<^sup>0"} ... Their embedding is 
 straightforward: @{text "\<lambda>\<^sup>0"} is mapped to identity and {text "\<lambda>\<^sup>1,\<lambda>\<^sup>2,\<lambda>\<^sup>3,..."} are mapped to n-ary
 lambda abstractions, that is, @{text "\<lambda>\<^sup>2(\<lambda>xy.\<phi>)"} is e.g. mapped to @{text "(\<lambda>xy.\<phi>)"}.
 For pragmatical reasons we restrict ourselves here to the cases where $n\leq 0$. 
 *}

abbreviation lambda0::"io opt\<Rightarrow>io opt"(**)("\<lambda>\<^sup>0_")(**) where "\<lambda>\<^sup>0\<phi> \<equiv> case \<phi> of 
    P \<psi> \<Rightarrow> P \<psi> | _ \<Rightarrow> ERR dio"  
abbreviation lambda1::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt"(**)("\<lambda>\<^sup>1_")(**) where "\<lambda>\<^sup>1\<Phi> \<equiv> case (\<Phi> de) of
    P \<phi> \<Rightarrow> T (\<lambda>x. case (\<Phi> x) of P \<phi> \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR (\<lambda>x. dio)"
abbreviation lambda2::"(e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>io) opt"(**)("\<lambda>\<^sup>2_")(**) where "\<lambda>\<^sup>2\<Phi> \<equiv> case (\<Phi> de de) of
    P \<phi> \<Rightarrow> T (\<lambda>x y. case (\<Phi> x y) of P \<phi> \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR (\<lambda>x y. dio)"
abbreviation lambda3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt"(**)("\<lambda>\<^sup>3_")(**) where "\<lambda>\<^sup>3\<Phi> \<equiv> case (\<Phi> de de de) of
    P \<phi> \<Rightarrow> T (\<lambda>x y z. case (\<Phi> x y z) of P \<phi> \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR (\<lambda>x y z. dio)"

 text {* That ...
 *}

abbreviation definiteDescription::"(e\<Rightarrow>io opt)\<Rightarrow>e opt"(**)("\<epsilon>")(**)  where "\<epsilon> \<Phi> \<equiv> case (\<Phi> de) of
    P \<phi> \<Rightarrow> T (THE x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> cw) | _ \<Rightarrow> ERR de"
text {* that operator; that @{text "(\<lambda>x.\<phi>)"} returns Term @{text "(THE x. \<phi> x cw)"}, that is the inbuilt THE 
operator is used and evaluation is wrt to the current world cw; moreover, application of that 
is allowed if @{text "(\<Phi> sRE)"} is a PropForm, otherwise Error is passed on for some someRawEntity *}



section {* Further logical connectives *}

abbreviation conjunction::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(**)(infixl "\<^bold>\<and>" 53)(**) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<phi>\<^bold>\<rightarrow>\<^bold>\<not>\<psi>)"
abbreviation disjunction::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(**)(infixl "\<^bold>\<or>" 52)(**) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<^bold>\<not>\<phi>\<^bold>\<rightarrow>\<psi>"
abbreviation equivalence::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(**)(infixl "\<^bold>\<equiv>" 52)(**) where "\<phi>\<^bold>\<equiv>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"
abbreviation diamond::"io opt\<Rightarrow>io opt"(**)("\<^bold>\<diamond>")(**) where "\<^bold>\<diamond>\<phi> \<equiv> \<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not> \<phi>))"
abbreviation existentialQuantification::"('a\<Rightarrow>io opt)\<Rightarrow>io opt"(**)("\<^bold>\<exists>")(**) where "\<^bold>\<exists>\<Phi> \<equiv> case (\<Phi> da) of
    P \<phi> \<Rightarrow> P(\<lambda>w.\<exists>x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> w) | F \<phi> \<Rightarrow> F(\<lambda>w. \<exists>x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> w) | _ \<Rightarrow> ERR dio"

(* abbreviation z_true::"io opt"(**)("\<top>\<^sup>z")(**) where "\<top>\<^sup>z \<equiv> todo; not entirely clear yet " *)
(* abbreviation z_false::"io opt"(**)("\<bottom>\<^sup>z")(**) where "\<bottom>\<^sup>z \<equiv> todo; not entirely clear yet " *)


section {* Some shortcuts for the constructors *}

abbreviation mkPropForm::"io\<Rightarrow>io opt" ("_\<^sup>P" 110)  where "\<phi>\<^sup>P \<equiv> P \<phi>" 
abbreviation mkForm::"io\<Rightarrow>io opt" ("_\<^sup>F" 110)  where "\<phi>\<^sup>F \<equiv> F \<phi>" 
abbreviation mkTerm::"'a\<Rightarrow>'a opt" ("_\<^sup>T" 110)  where "\<phi>\<^sup>T \<equiv> T \<phi>" 


 text {* Three Valued Meta-Logic *}

datatype mf = tt ("\<top>") | ff ("\<bottom>") | err ("*")

(*
abbreviation meta_not::"mf \<Rightarrow> mf" (**)("\<not>\<^sup>m")(**) 
  where "\<not>\<^sup>m \<phi>  \<equiv> case \<phi> of 
    error \<Rightarrow> error | tt \<Rightarrow> ff | ff \<Rightarrow> tt"  
text {* Not operator *}

abbreviation meta_implies::"mf \<Rightarrow> mf \<Rightarrow>mf" (**)(infixr "\<longrightarrow>\<^sup>m" 51)(**) 
  where "\<phi> \<longrightarrow>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (tt,ff) \<Rightarrow> ff | _ \<Rightarrow> tt"  
text {* Implies operator *}

abbreviation meta_or::"mf \<Rightarrow> mf \<Rightarrow>mf" (**)(infixr "\<or>\<^sup>m" 51)(**) 
  where "\<phi> \<or>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (ff,ff) \<Rightarrow> ff | _ \<Rightarrow> tt"  
text {* Or operator *}

abbreviation meta_and::"mf \<Rightarrow> mf \<Rightarrow>mf" (**)(infixr "\<and>\<^sup>m" 51)(**) 
  where "\<phi> \<and>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (tt,tt) \<Rightarrow> tt | _ \<Rightarrow> ff"  
text {* And operator *}

abbreviation meta_equiv::"mf \<Rightarrow> mf \<Rightarrow>mf" (**)(infixr "\<longleftrightarrow>\<^sup>m" 51)(**) 
  where "\<phi> \<longleftrightarrow>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (tt,tt) \<Rightarrow> tt | (ff,ff) \<Rightarrow> tt | _ \<Rightarrow> ff"  
text {* Equivalence operator *}

*)



(**) no_syntax "_list" :: "args\<Rightarrow>e list" ("[(_)]") (**) 
abbreviation valid :: "io opt\<Rightarrow>mf" (**)("[_]")(**) where "[\<phi>] \<equiv> case \<phi> of 
    P \<psi> \<Rightarrow> if \<forall>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | F \<psi> \<Rightarrow> if \<forall>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"
abbreviation satisfiable :: "io opt\<Rightarrow>mf" (**)("[_]\<^sup>s\<^sup>a\<^sup>t")(**) where "[\<phi>]\<^sup>s\<^sup>a\<^sup>t \<equiv> case \<phi> of 
    P \<psi> \<Rightarrow> if \<exists>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | F \<psi> \<Rightarrow> if \<exists>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"
abbreviation countersatisfiable :: "io opt\<Rightarrow>mf" (**)("[_]\<^sup>c\<^sup>s\<^sup>a\<^sup>t")(**) where "[\<phi>]\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  case \<phi> of 
    P \<psi> \<Rightarrow> if \<exists>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | F \<psi> \<Rightarrow> if \<exists>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"
abbreviation invalid :: "io opt\<Rightarrow>mf" (**)("[_]\<^sup>i\<^sup>n\<^sup>v")(**) where "[\<phi>]\<^sup>i\<^sup>n\<^sup>v \<equiv> case \<phi> of 
    P \<psi> \<Rightarrow> if \<forall>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | F \<psi> \<Rightarrow> if \<forall>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"


section {* Some Basic Tests *}


subsection {* Verifying Modal Logic Principles *}

text {* Necessitation holds *}
lemma necessitation_PropForm: "[\<phi>\<^sup>P] = \<top> \<longrightarrow> [\<^bold>\<box>(\<phi>\<^sup>P)] = \<top>" apply simp done
lemma necessitation_Form:     "[\<phi>\<^sup>F] = \<top> \<longrightarrow> [\<^bold>\<box>(\<phi>\<^sup>F)] = \<top>" apply simp done

text {* Modal Collapse does not hold *}
lemma modalCollapse_PropForm: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>P)] = \<top>" apply simp nitpick oops
lemma modalCollapse_Form:     "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>F)] = \<top>" apply simp nitpick oops


subsection {* S5 Principles *}

lemma axiom_T_P: "[\<^bold>\<box>(\<phi>\<^sup>P) \<^bold>\<rightarrow> (\<phi>\<^sup>P)] = \<top>" apply simp done
lemma axiom_T_F: "[\<^bold>\<box>(\<phi>\<^sup>F) \<^bold>\<rightarrow> (\<phi>\<^sup>F)] = \<top>" apply simp done

lemma axiom_B_P: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>P))] = \<top>" apply simp done
lemma axiom_B_F: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>F))] = \<top>" apply simp done

lemma axiom_4_P: "[\<^bold>\<box>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>P)] = \<top>" apply simp by auto
lemma axiom_4_F: "[\<^bold>\<box>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>F)] = \<top>" apply simp by auto

lemma axiom_D_P: "[\<^bold>\<box>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<box>(\<phi>\<^sup>P))] = \<top>" apply simp done
lemma axiom_D_F: "[\<^bold>\<box>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<box>(\<phi>\<^sup>F))] = \<top>" apply simp done

lemma axiom_5_P: "[\<^bold>\<diamond>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>P))] = \<top>" apply simp done
lemma axiom_5_F: "[\<^bold>\<diamond>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>F))] = \<top>" apply simp done

lemma test_A_P: "[\<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>P)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>P)] = \<top>" apply simp done
lemma test_A_F: "[\<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>F)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>F)] = \<top>" apply simp done

lemma test_B_P: "[\<^bold>\<diamond>(\<^bold>\<box>(\<phi>\<^sup>P)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>P)] = \<top>" apply simp by auto
lemma test_B_F: "[\<^bold>\<diamond>(\<^bold>\<box>(\<phi>\<^sup>F)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>F)] = \<top>" apply simp by auto

lemma test_C_P: "[\<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>P)) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>P)] = \<top>" apply simp nitpick oops
lemma test_C_F: "[\<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>F)) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>F)] = \<top>" apply simp nitpick oops

lemma test_D_P: "[\<^bold>\<diamond>(\<^bold>\<box>(\<phi>\<^sup>P)) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>P)] = \<top>" apply simp done
lemma test_D_F: "[\<^bold>\<diamond>(\<^bold>\<box>(\<phi>\<^sup>F)) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>F)] = \<top>" apply simp done


subsection {* Validity, Satisfiabilty, Countersatisfiability and Invalidity *}
lemma  "[\<phi>\<^sup>P] = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
lemma  "[\<phi>\<^sup>P]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done
lemma  "[\<phi>\<^sup>F] = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
lemma  "[\<phi>\<^sup>F]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done

text {* For Terms we have *}
lemma  "[\<phi>\<^sup>T] = *" apply simp done
lemma  "[\<phi>\<^sup>T]\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
lemma  "[\<phi>\<^sup>T]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
lemma  "[\<phi>\<^sup>T]\<^sup>i\<^sup>n\<^sup>v = *" apply simp done



subsection {* Example signature; entities and relations *}

consts a_0 :: "e" abbreviation a  where "a \<equiv> (a_0\<^sup>T)"
consts b_0 :: "e" abbreviation b  where "b \<equiv> (b_0\<^sup>T)"
consts c_0 :: "e" abbreviation c  where "c \<equiv> (c_0\<^sup>T)"

consts R_0 :: "io"  abbreviation R0  where "R0 \<equiv> (R_0\<^sup>T)"
consts R_1 :: "e\<Rightarrow>io" abbreviation R1  where "R1 \<equiv> (R_1\<^sup>T)"
consts R_2 :: "e\<Rightarrow>e\<Rightarrow>io" abbreviation R2  where "R2 \<equiv> (R_2\<^sup>T)"
consts R_3 :: "e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io"  abbreviation R3  where "R3 \<equiv> (R_3\<^sup>T)"


text {* Testing term and formula constructions *}

lemma "[R1\<bullet>a] = \<top>" apply simp nitpick oops
lemma "(R1\<bullet>a) = X" apply simp oops

lemma "[a\<cdot>R1] = \<top>" nitpick oops
lemma "(a\<cdot>R1) = X" apply simp oops

lemma "[(\<lambda>\<^sup>1(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (R1\<bullet>(x\<^sup>T))))\<bullet>a] = \<top>" apply simp done
lemma "((\<lambda>\<^sup>1(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (R1\<bullet>(x\<^sup>T))))\<bullet>a) = X" apply simp oops

lemma "(\<lambda>\<^sup>1(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> ((x\<^sup>T)\<cdot>R1))) = X" apply simp oops

lemma "[(\<lambda>\<^sup>1(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)))\<bullet>a] = *" apply simp done
lemma "[(\<lambda>\<^sup>1(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)))\<bullet>a] = X" apply simp oops
lemma "((\<lambda>\<^sup>1(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)))\<bullet>a) = X" apply simp oops

lemma "[\<^bold>\<forall>(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (R1\<bullet>(x\<^sup>T)))] = \<top>" apply simp done
lemma "[\<^bold>\<forall>(\<lambda>R. \<^bold>\<forall>(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (R1\<bullet>(x\<^sup>T))))] = \<top>" apply simp done
lemma "\<^bold>\<forall>(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (R1\<bullet>(x\<^sup>T))) = X" apply simp oops

lemma "[\<^bold>\<forall>(\<lambda>x. (x\<^sup>T\<cdot>R1) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1))] = \<top>" apply simp done
lemma "\<^bold>\<forall>(\<lambda>x. (x\<^sup>T\<cdot>R1) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)) = X" apply simp oops

lemma "[\<^bold>\<forall>(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1))] = *" apply simp done
lemma "[\<^bold>\<forall>(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1))] = X" apply simp oops
lemma "\<^bold>\<forall>(\<lambda>x. (R1\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)) = X" apply simp oops
lemma "[\<^bold>\<forall>(\<lambda>R. (R\<^sup>T\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1))] = *" apply simp done
lemma "\<^bold>\<forall>(\<lambda>R. (R\<^sup>T\<bullet>(x\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)) = X" apply simp oops


section {* Are the priorities set correctly?*}

lemma "(\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P) \<^bold>\<rightarrow> (\<chi>\<^sup>P) \<equiv> ((\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P)) \<^bold>\<rightarrow> (\<chi>\<^sup>P)" apply simp done
lemma "(\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P) \<^bold>\<rightarrow> (\<chi>\<^sup>P) \<equiv> (\<phi>\<^sup>P) \<^bold>\<and> ((\<psi>\<^sup>P) \<^bold>\<rightarrow> (\<chi>\<^sup>P))" apply simp nitpick oops

lemma "((\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P) \<^bold>\<equiv> (\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P)) \<equiv> (((\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P)) \<^bold>\<equiv> ((\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P)))" apply simp done
lemma "((\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P) \<^bold>\<equiv> (\<phi>\<^sup>P) \<^bold>\<and> (\<psi>\<^sup>P)) \<equiv> ((\<phi>\<^sup>P) \<^bold>\<and> ((\<psi>\<^sup>P) \<^bold>\<equiv> (\<phi>\<^sup>P)) \<^bold>\<and> (\<psi>\<^sup>P))" apply simp nitpick oops


section {* E!, O!, A! and =E *}

consts E::"(e\<Rightarrow>io)"
text {* Distinguished 1-place relation constant: E! (read: ‘being concrete’ or ‘concreteness’) *}

abbreviation ordinaryObject::"(e\<Rightarrow>io) opt"(**)("O!")(**) where "O! \<equiv> \<lambda>\<^sup>1(\<lambda>x. \<^bold>\<diamond>(E\<^sup>T\<bullet>(x\<^sup>T)))"
text {* Being ordinary is being possibly concrete. *}

abbreviation abstractObject::"(e\<Rightarrow>io) opt"(**)("A!")(**) where "A! \<equiv> \<lambda>\<^sup>1(\<lambda>x. \<^bold>\<not>(\<^bold>\<diamond>(E\<^sup>T\<bullet>(x\<^sup>T))))"
text {* Being abstract is not possibly being concrete. *}

abbreviation identity::"(e\<Rightarrow>e\<Rightarrow>io) opt"(**)("\<^bold>=")(**) where "\<^bold>= \<equiv> 
  \<lambda>\<^sup>2(\<lambda>x y. (((O!\<bullet>(x\<^sup>T)) \<^bold>\<and> (O!\<bullet>(y\<^sup>T))) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>(\<lambda>F. (F\<^sup>T\<bullet>(x\<^sup>T)) \<^bold>\<equiv> (F\<^sup>T\<bullet>(y\<^sup>T))))))"

abbreviation identityE::"e opt\<Rightarrow>e opt\<Rightarrow>io opt"(**)(infixl "\<^bold>=\<^sub>E" 63)(**) where "x \<^bold>=\<^sub>E y \<equiv> (\<^bold>=\<bullet>x,y)"


section {* Further test examples *}

lemma "[\<^bold>\<forall>(\<lambda>x. \<^bold>\<exists>(\<lambda>R. (x\<^sup>T\<cdot>(R\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)))] = \<top>" apply simp by auto
lemma "[\<^bold>\<forall>(\<lambda>x. \<^bold>\<forall>(\<lambda>R. (x\<^sup>T\<cdot>(R\<^sup>T)) \<^bold>\<rightarrow> (x\<^sup>T\<cdot>R1)))] = \<top>" apply simp nitpick oops

lemma "[a \<^bold>=\<^sub>E a] = \<top>" apply simp nitpick oops

lemma "[(O!\<bullet>a) \<^bold>\<rightarrow> a \<^bold>=\<^sub>E a] = \<top>" apply simp done

lemma "[(\<^bold>\<forall>(\<lambda>F. (F\<^sup>T\<bullet>(x\<^sup>T)) \<^bold>\<equiv> (F\<^sup>T\<bullet>(x\<^sup>T))))] = \<top>" apply simp done
lemma "[(O!\<bullet>a) \<^bold>\<rightarrow> ((\<lambda>\<^sup>1(\<lambda>x. (x\<^sup>T) \<^bold>=\<^sub>E a))\<bullet>a)] = \<top>" apply simp done

lemma "[\<^bold>\<exists>(\<lambda>F. (a\<cdot>(F\<^sup>T)))] = \<top>" apply simp by auto

lemma "[\<^bold>\<exists>(\<lambda>\<phi>. (\<phi>\<^sup>P))] = \<top>" apply simp by auto
lemma "[\<^bold>\<exists>(\<lambda>\<phi>. (\<phi>\<^sup>F))] = \<top>" apply simp by auto

section {* Axioms *}

subsection {* Axioms for Negations and Conditionals *}

lemma a21_1_P: "[(\<phi>\<^sup>P) \<^bold>\<rightarrow> ((\<phi>\<^sup>P) \<^bold>\<rightarrow> (\<phi>\<^sup>P))] = \<top>" apply simp done
lemma a21_1_F: "[(\<phi>\<^sup>F) \<^bold>\<rightarrow> ((\<phi>\<^sup>F) \<^bold>\<rightarrow> (\<phi>\<^sup>F))] = \<top>" apply simp done
lemma a21_2_P: "[((\<phi>\<^sup>P) \<^bold>\<rightarrow> ((\<psi>\<^sup>P) \<^bold>\<rightarrow> (\<chi>\<^sup>P))) \<^bold>\<rightarrow> (((\<phi>\<^sup>P) \<^bold>\<rightarrow> (\<psi>\<^sup>P)) \<^bold>\<rightarrow> ((\<phi>\<^sup>P) \<^bold>\<rightarrow> (\<chi>\<^sup>P)))] = \<top>" apply simp done
lemma a21_2_F: "[((\<phi>\<^sup>F) \<^bold>\<rightarrow> ((\<psi>\<^sup>F) \<^bold>\<rightarrow> (\<chi>\<^sup>F))) \<^bold>\<rightarrow> (((\<phi>\<^sup>F) \<^bold>\<rightarrow> (\<psi>\<^sup>F)) \<^bold>\<rightarrow> ((\<phi>\<^sup>F) \<^bold>\<rightarrow> (\<chi>\<^sup>F)))] = \<top>" apply simp done
lemma a21_3_P: "[(\<^bold>\<not>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi>\<^sup>P)) \<^bold>\<rightarrow> ((\<^bold>\<not>(\<phi>\<^sup>P) \<^bold>\<rightarrow> (\<psi>\<^sup>P)) \<^bold>\<rightarrow> (\<phi>\<^sup>P))] = \<top>" apply simp done
lemma a21_3_F: "[(\<^bold>\<not>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi>\<^sup>F)) \<^bold>\<rightarrow> ((\<^bold>\<not>(\<phi>\<^sup>F) \<^bold>\<rightarrow> (\<psi>\<^sup>F)) \<^bold>\<rightarrow> (\<phi>\<^sup>F))] = \<top>" apply simp done

subsection {* Axioms of Identity *}
text {* todo *}

subsection {* Axioms of Quantification *}
text {* todo *}

subsection {* Axioms of Actuality *}

lemma a31_1_P: "[\<A>(\<^bold>\<not>(\<phi>\<^sup>P)) \<^bold>\<equiv> \<^bold>\<not>(\<A>(\<phi>\<^sup>P))] = \<top>" apply simp done
lemma a31_1_F: "[\<A>(\<^bold>\<not>(\<phi>\<^sup>F)) \<^bold>\<equiv> \<^bold>\<not>(\<A>(\<phi>\<^sup>F))] = \<top>" apply simp done
lemma a31_2_P: "[\<A>(\<phi>\<^sup>P \<^bold>\<rightarrow> (\<psi>\<^sup>P)) \<^bold>\<equiv> (\<A>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<A>(\<psi>\<^sup>P))] = \<top>" apply simp done
lemma a31_2_F: "[\<A>(\<phi>\<^sup>F \<^bold>\<rightarrow> (\<psi>\<^sup>F)) \<^bold>\<equiv> (\<A>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<A>(\<psi>\<^sup>F))] = \<top>" apply simp done
lemma a31_3_P: "[\<A>(\<^bold>\<forall>(\<lambda>x. (\<phi>\<^sup>P)) \<^bold>\<equiv> \<^bold>\<forall>(\<lambda>x. \<A>(\<phi>\<^sup>P)))] = \<top>" apply simp done
lemma a31_3_F: "[(\<A>(\<^bold>\<forall>(\<lambda>x. (\<phi>\<^sup>F))) \<^bold>\<equiv> \<^bold>\<forall>(\<lambda>x. \<A>(\<phi>\<^sup>F)))] = \<top>" apply simp done
lemma a31_4_P: "[\<A>(\<phi>\<^sup>P) \<^bold>\<equiv> \<A>(\<A>(\<phi>\<^sup>P))] = \<top>" apply simp done
lemma a31_4_F: "[\<A>(\<phi>\<^sup>F) \<^bold>\<equiv> \<A>(\<A>(\<phi>\<^sup>F))] = \<top>" apply simp done

subsection {* Axioms of Necessity *}

lemma a32_1_P: "[(\<^bold>\<box>(\<phi>\<^sup>P \<^bold>\<rightarrow> (\<phi>\<^sup>P))) \<^bold>\<rightarrow> (\<^bold>\<box>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>P))] = \<top>" apply simp done     (* K Schema *)
lemma a32_1_F: "[(\<^bold>\<box>(\<phi>\<^sup>F \<^bold>\<rightarrow> (\<phi>\<^sup>F))) \<^bold>\<rightarrow> (\<^bold>\<box>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi>\<^sup>F))] = \<top>" apply simp done     (* K Schema *)
lemma a32_2_P: "[\<^bold>\<box>(\<phi>\<^sup>P) \<^bold>\<rightarrow> (\<phi>\<^sup>P)] = \<top>" apply simp done                           (* T Schema *)
lemma a32_2_F: "[\<^bold>\<box>(\<phi>\<^sup>F) \<^bold>\<rightarrow> (\<phi>\<^sup>F)] = \<top>" apply simp done                           (* T Schema *)

lemma a32_3_P: "[\<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>P)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>P)] = \<top>" apply simp done                       (* 5 Schema *)
lemma a32_3_F: "[\<^bold>\<box>(\<^bold>\<diamond>(\<phi>\<^sup>F)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi>\<^sup>F)] = \<top>" apply simp done                       (* 5 Schema *)
lemma a32_4_P: "[\<^bold>\<forall>(\<lambda>x. \<^bold>\<box>(\<phi>\<^sup>P)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>(\<lambda>x. (\<phi>\<^sup>P)))] = \<top>" apply simp done         (* BF *)
lemma a32_4_F: "[\<^bold>\<forall>(\<lambda>x. \<^bold>\<box>(\<phi>\<^sup>F)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>(\<lambda>x. (\<phi>\<^sup>F)))] = \<top>" apply simp done         (* BF *)

text {* The following needs to be an axiom; it does not follow for free: it is possible that there 
are contingently concrete individuals and it is possible that there are not: *}
axiomatization where
  a32_5_P: "[\<^bold>\<diamond>(\<^bold>\<exists>(\<lambda>x. (E\<^sup>T\<bullet>(x\<^sup>T)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(E\<^sup>T\<bullet>(x\<^sup>T))))) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<exists>(\<lambda>x. (E\<^sup>T\<bullet>(x\<^sup>T)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(E\<^sup>T\<bullet>(x\<^sup>T))))))] = \<top>"

subsection {* Axioms of Necessity and Actuality *}

lemma a33_1_P: "[\<A>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>(\<A>(\<phi>\<^sup>P))] = \<top>" apply simp done
lemma a33_1_F:  "[\<A>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<box>(\<A>(\<phi>\<^sup>F))] = \<top>" apply simp done
lemma a33_2_P: "[\<^bold>\<box>(\<phi>\<^sup>P) \<^bold>\<equiv> (\<A>(\<^bold>\<box>(\<phi>\<^sup>P)))] = \<top>" apply simp done
lemma a33_2_F:  "[\<^bold>\<box>(\<phi>\<^sup>F) \<^bold>\<equiv> (\<A>(\<^bold>\<box>(\<phi>\<^sup>F)))] = \<top>" apply simp done


(**) 
end
(**)

