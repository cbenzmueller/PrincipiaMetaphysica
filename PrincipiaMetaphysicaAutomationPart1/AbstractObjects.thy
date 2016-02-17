(*<*) 
theory AbstractObjects
imports Main

begin
(*>*)

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
  \item Can functional type theory, despite the problems pointed at by Zalta and Oppenheimer, 
   be utilized to encode the Theory of Abstract Objects when following the embeddings approach?
  \item How elegant and user-friendly is the resulting formalization? 
   To what extend can Isabelle's  user interface be facilitated to hide 
   unpleasant technicalities of the (extended) embedding from the user?
  \item How far can automation be pushed in the approach? How much user interaction can
   be avoided in the formalization of the (first part) of the Principia Metaphysica? 
  \item Can the consistency of the theory be validated with the available automated 
   reasoning tools?
  \item Can the reasoners eventually even contribute some new knowledge? 
  \item Suggestions for improvements in Isabelle? Any particular problems detected in the course 
  of the study?
  \ldots
  \end{itemize}
  *}

  text {* 
  The encoding of modal functional type theory in functional type theory as explored in 
  previous work \cite{J23,C40} is simple: modal logic formulas are identified with certain functional 
  type theory formulas of predicate type @{text "i\<Rightarrow>bool"} (abbreviated as @{text "io"} below). 
  Possible worlds are explicitly represented by 
  terms of type  @{text "i"}. A modal logic formula @{text "\<phi>"} holds for a world @{text "w"} if and 
  only if the application @{text "\<phi> w"} evaluates to true. The definition of the propositional modal logic 
  connectives is then straightforward and it simply realizes the standard translation as a set of equations 
  in functional type theory. The approach has been successfully extended for quantifiers. A crucial 
  aspect thereby is that in simple type theory quantifiers can be treated
  as ordinary logical connectives. No extra binding mechanism is needed since the already existing 
  lambda binding mechanism can be elegantly utilized. 
  
  The challenge here is to appropriately 'restrict' this embedding for modal relational type theory.
   \begin{figure}[t]
  \includegraphics[height=5.5cm]{ModalRelationalTypeTheory.png}\includegraphics[height=4.5cm]{ModalRelationalTypeTheory2.png}
  \caption{Grammar of Modal Relational Type Theory. \label{mmrt}
  Note that two kinds of (complex) formulas are introduced: ones that may have encoding subformulas and 
  ones that do not. The latter are designated as propositional formulas, the former ones simply as formulas. }
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
  Our formalism explicitly encodes possible world semantics. Hence, we introduce a 
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
  (polymorphic) datatype @{text "'a opt"} (where @{text "'a"} is a polymorphic variable in Isabelle) 
  based on four constructors: @{text "ERR 'a"} (identifies ineligible/erroneous term constructions), @{text "P 'a"} 
  (identifies propositional formulas), @{text "F 'a"} (identifies  formulas), and @{text "T 'a"} (identifies 
  terms, such as lambda abstractions). The embeddings approach will be suitably adapted below so that 
  for each language expression (in the embedded modal relational type theory) the respective datatype 
  is identified and appropriately propagated. The encapsulated expressions  
  realize the actual modeling of the logic embedding analogous 
  to previous work for modal functional type theory.  
  *}

 datatype 'a opt = ERR 'a | P 'a | F 'a | T 'a 

  text {* The following operators support a concise and elegant superscript annotation with these
  four syntactical categories for our language constructs.
  *}

 abbreviation mkP::"io\<Rightarrow>io opt" ("_\<^sup>P" [109] 110)  where "\<phi>\<^sup>P \<equiv> P \<phi>" 
 abbreviation mkF::"io\<Rightarrow>io opt" ("_\<^sup>F" [109] 110)  where "\<phi>\<^sup>F \<equiv> F \<phi>" 
 abbreviation mkT::"'a\<Rightarrow>'a opt" ("_\<^sup>T" [109] 110)  where "\<phi>\<^sup>T \<equiv> T \<phi>"
 abbreviation mkE::"'a\<Rightarrow>'a opt" ("_\<^sup>E" [109] 110)  where "\<phi>\<^sup>E \<equiv> ERR \<phi>" 

  text {* Some language constructs in the Principia Metaphysica, e.g. the actuality operator  
  @{text "\<^bold>\<A>"} ("it is actually the case that"), refer to a (fixed) designated world. To model such a 
  rigid dependence we introduce a constant symbol (name) @{text "dw"} of world type @{text "i"}. 
  Moreover, for technical reasons, 
  which will be clarified below, we introduce further (dummy) constant symbols for various domains. Since
  we assume that all domains are non-empty, introducing these constant symbols is obviously not harmful. 
  *}

 consts dw :: i 
 consts de::"e" dio::"io" deio::"e\<Rightarrow>io" da::'a

section {* Embedding of Modal Relational Type Theory *}

  text {* 
  The language constructs of modal relational type theory are introduced step by step. 
  *}

  text {* The actuality operator @{text "\<^bold>\<A>"} when applied to a formula or propositional formula 
  @{text "\<phi>"} evaluates @{text "\<phi>"} wrt the fixed given world @{text "cw"}. 
  The compound expression @{text "\<^bold>\<A>\<phi>"} inherits its syntactical category  @{text "F"} (formula) or
  @{text "P"} (propositional formula from @{text "\<phi>"}. If the syntactical catagory of  @{text "\<phi>"} is 
  @{text "ERR"} (error) or @{text "T"} (term), then the syntactical catagory of @{text "\<^bold>\<A>\<phi>"} 
  is @{text "ERR"} and a dummy entity of appropriate type is returned. This illustrates the very 
  idea of our explicit structure and constraints and this scheme will repeated below
  for all the other language constructs of modal relational type theory. 
  *}

 abbreviation Actual::"io opt \<Rightarrow> io opt" ("\<^bold>\<A> _" [64] 65) where "\<^bold>\<A>\<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w. \<psi> dw) | P(\<psi>) \<Rightarrow> P(\<lambda>w. \<psi> dw) | _ \<Rightarrow> ERR(dio)"


  text {* 
  The Principia Metaphysica distinguishes between encoding @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} and 
  exemplifying  @{text "\<Pi>\<^sup>n,\<kappa>\<^sub>1,..,\<kappa>\<^sub>n"}. ... say more ...
  Exemplification is supported here only for  @{text "1\<le>n\<le>3"}.

  First we introduce the primitive constant @{text "enc"}. This basic primitives is employed 
  below in the definition of the encoding operation @{text "\<lbrace>\<kappa>\<^sub>1,\<Pi>\<^sup>1\<rbrace>"}. 
  *}
  
 consts enc::"e\<Rightarrow>(e\<Rightarrow>io)\<Rightarrow>io"

  text {* 
  Encoding @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} is noted below as @{text "\<lbrace>\<kappa>\<^sub>1,\<Pi>\<^sup>1\<rbrace>"}.
  Encoding yields formulas and never propositional formulas.
  *}

 abbreviation Enc::"e opt\<Rightarrow>(e\<Rightarrow>io) opt\<Rightarrow>io opt" ("\<lbrace>_,_\<rbrace>") where "\<lbrace>x,\<Phi>\<rbrace> \<equiv> case (x,\<Phi>) of 
    (T(y),T(Q)) \<Rightarrow> F(enc y Q) | _ \<Rightarrow> ERR(dio)"

  text {* 
  Exemplifying formulas @{text "\<Pi>\<^sup>1\<kappa>\<^sub>1"} are noted here as @{text "\<lparr>\<Pi>\<^sup>1,\<kappa>\<^sub>1\<rparr>"}.  
  Exemplification yields propositional formulas. Exemplification is mapped to predicate application.
  *}

 abbreviation Exe1::"(e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_\<rparr>") where "\<lparr>\<Phi>,x\<rparr> \<equiv> case (\<Phi>,x) of 
    (T(Q),T(y)) \<Rightarrow> P(Q y) | _ \<Rightarrow> ERR(dio)"

  text {* 
  The Principia Metaphysica supports @{text "n"}-ary exemplification constructions. 
  We support the cases for @{text "1\<le>n\<le>3"}. Exemplification is mapped to predicate application.
  *}  

 abbreviation Exe2::"(e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_,_\<rparr>")
  where "\<lparr>\<Phi>,x1,x2\<rparr> \<equiv> case (\<Phi>,x1,x2) of 
    (T(Q),T(y1),T(y2)) \<Rightarrow> P(Q y1 y2) | _ \<Rightarrow> ERR(dio)"
 abbreviation Exe3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_,_,_\<rparr>") 
  where "\<lparr>\<Phi>,x1,x2,x3\<rparr> \<equiv> case (\<Phi>,x1,x2,x3) of 
    (T(Q),T(y1),T(y2),T(y3)) \<Rightarrow> P(Q y1 y2 y3) | _ \<Rightarrow> ERR(dio)"

  text {* 
  Formations with negation and implication are supported for both, formulas and propositional
  formulas, and their embeddings are straightforward. In the case of implication the compound formula
  is a propositional formula only of both subformulas are propositional formulas. If at one is a formula
  and the other one eligible, then the compound formula is a formula. In all other
  cases an ERR-Formula is returned. 
  *}  

 abbreviation not::"io opt\<Rightarrow>io opt" ("\<^bold>\<not> _" [58] 59) where "\<^bold>\<not> \<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w.\<not>(\<psi> w)) | P(\<psi>) \<Rightarrow> P(\<lambda>w.\<not>(\<psi> w)) | _ \<Rightarrow> ERR(dio)"  
 abbreviation implies::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>\<rightarrow>" 51) where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (P(\<alpha>),P(\<beta>)) \<Rightarrow> P(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | (F(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | 
    (P(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | (F(\<alpha>),P(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | 
    _ \<Rightarrow> ERR(dio)"  

  text {*
  Also universal quantification @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"} (first-order and higher-order) is supported 
  for formulas  and propositional formulas. Following previous work the embedding maps 
  @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"} to @{text "(\<lambda>w.\<^bold>\<forall>x.\<phi>w)"}. Note that @{text "\<^bold>\<forall>"} is introduced as logical connective
  based on the existing @{text "\<lambda>"}-binder. To improve presentation in the remainder we additional
  introduce binder notation @{text "\<^bold>\<forall>x.\<phi>"} as syntactic sugar for @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"}.
  *}

 abbreviation forall::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> case (\<Phi> da) of
    F(\<phi>) \<Rightarrow> F(\<lambda>w.\<forall>x. case (\<Phi> x) of F(\<psi>) \<Rightarrow> \<psi> w) 
  | P(\<phi>) \<Rightarrow> P(\<lambda>w.\<forall>x. case (\<Phi> x) of P(\<psi>) \<Rightarrow> \<psi> w) | _ \<Rightarrow> ERR(dio)"
 abbreviation forallBinder::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" (binder "\<^bold>\<forall>" [8] 9)  where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"

 lemma binderTest: "(\<^bold>\<forall>x. \<phi> x) = \<^bold>\<forall>(\<lambda>x. \<phi> x)" by simp

  text {* 
  The modal @{text "\<^bold>\<box>"} operator is introduced here for logic S5. Since in an equivalence class
  of possible worlds each world is reachable from any other world, the guarding accessibility clause
  in the usual definition of the @{text "\<^bold>\<box>"} operator can be omitted. This is convenient and should also
  ease theorem proving. In Section \ref{sec:S5} we will actually demonstrate that the expected S5 properties
  are validated by our modeling of @{text "\<^bold>\<box>"}.  @{text "\<^bold>\<box>\<phi>"} is supported 
  for formulas  and propositional formulas.
  *}

 abbreviation box::"io opt\<Rightarrow>io opt" ("\<^bold>\<box>_" [62] 63) where "\<^bold>\<box>\<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w.\<forall>v. \<psi> v) | P(\<psi>) \<Rightarrow> P(\<lambda>w.\<forall>v. \<psi> v) | _ \<Rightarrow> ERR(dio)"  

  text {* 
  n-ary lambda abstraction @{text "\<^bold>\<lambda>\<^sup>0,\<^bold>\<lambda>,\<^bold>\<lambda>\<^sup>2\<^sup>,\<^bold>\<lambda>\<^sup>3,..."}, for $n\geq 0$, is supported in the Principia
  Metaphysica only over propositional formulas. ... say more about @{text "\<^bold>\<lambda>\<^sup>0"} ... Their embedding is 
  straightforward: @{text "\<^bold>\<lambda>\<^sup>0"} is mapped to identity and @{text "\<^bold>\<lambda>,\<^bold>\<lambda>\<^sup>2,\<^bold>\<lambda>\<^sup>3,..."} are mapped to n-ary
  lambda abstractions, that is, @{text "\<^bold>\<lambda>(\<lambda>x.\<phi>)"} is mapped to @{text "(\<lambda>x.\<phi>)"} and @{text "\<^bold>\<lambda>\<^sup>2(\<lambda>xy.\<phi>)"} 
  to @{text "(\<lambda>xy.\<phi>)"}, etc.
  Similar to before, we support only the cases where $n\leq 3$. Binder notation is
  introduced for @{text "\<^bold>\<lambda>"} (... unfortuntaley, I don't know yet how binder notation can be 
  achieved also for @{text "\<^bold>\<lambda>\<^sup>2,\<^bold>\<lambda>\<^sup>3"} ... need to find out.). 
  *}

 abbreviation lam0::"io opt\<Rightarrow>io opt" ("\<^bold>\<lambda>\<^sup>0") where "\<^bold>\<lambda>\<^sup>0\<phi> \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> P(\<psi>) | _ \<Rightarrow> ERR dio"  

 abbreviation lam::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt" ("\<^bold>\<lambda>") where "\<^bold>\<lambda>\<Phi> \<equiv> case (\<Phi> de) of
    P(\<phi>) \<Rightarrow> T(\<lambda>x. case (\<Phi> x) of P(\<phi>) \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR(\<lambda>x. dio)"
 abbreviation lamBinder::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt" (binder "\<^bold>\<lambda>" [8] 9)  where "\<^bold>\<lambda>x. \<phi> x \<equiv> \<^bold>\<lambda> \<phi>"

 abbreviation lam2::"(e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>io) opt" ("\<^bold>\<lambda>\<^sup>2") where "\<^bold>\<lambda>\<^sup>2\<Phi> \<equiv> case (\<Phi> de de) of
    P(\<phi>) \<Rightarrow> T(\<lambda>x y. case (\<Phi> x y) of P(\<phi>) \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR(\<lambda>x y. dio)"

 abbreviation lam3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt" ("\<^bold>\<lambda>\<^sup>3") where "\<^bold>\<lambda>\<^sup>3\<Phi> \<equiv> case (\<Phi> de de de) of
    P(\<phi>) \<Rightarrow> T(\<lambda>x y z. case (\<Phi> x y z) of P(\<phi>) \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR(\<lambda>x y z. dio)"


  text {* 
  The Principia Metaphysica supports rigid definite descriptions. Our definition maps
  @{text "\<^bold>\<iota>(\<lambda>x.\<phi>)"} to @{text "(THE x. \<phi> cw)"}, that is Isabelle's inbuilt definite description operator THE 
  is utilized and evaluation is rigidly carried out with respect to the current world @{text "cw"}.
  We again introduce binder notation for @{text "\<^bold>\<iota>"}.
  *}
 
 abbreviation that::"(e\<Rightarrow>io opt)\<Rightarrow>e opt" ("\<^bold>\<iota>")  where "\<^bold>\<iota>\<Phi> \<equiv> case (\<Phi> de) of
    F(\<phi>) \<Rightarrow> T(THE x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> dw) | P(\<phi>) \<Rightarrow> T(THE x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> dw) | _ \<Rightarrow> ERR(de)"
 abbreviation thatBinder::"(e\<Rightarrow>io opt)\<Rightarrow>e opt" (binder "\<^bold>\<iota>" [8] 9)  where "\<^bold>\<iota>x. \<phi> x \<equiv> \<^bold>\<iota> \<phi>"

 lemma   "\<lparr>F1\<^sup>T,(\<^bold>\<iota>x. \<lbrace>x\<^sup>T,Q1\<^sup>T\<rbrace>)\<rparr> = X" apply simp oops  -- {* X is a propositional formula as intended *}


section {* Further Logical Connectives *}

  text {* 
  Further logical connectives can be defined as usual. For pragmatic reasons (to avoid the blow-up of
  abbreviation expansions) we prefer direct definitions in all cases.
  *}

 abbreviation conj::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>\<and>" 53) where "\<phi> \<^bold>\<and> \<psi> \<equiv> case (\<phi>,\<psi>) of
    (P(\<alpha>),P(\<beta>)) \<Rightarrow> P(\<lambda>w. \<alpha> w \<and> \<beta> w) | (F(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<and> \<beta> w) | 
    (P(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<and> \<beta> w) | (F(\<alpha>),P(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<and> \<beta> w) | 
    _ \<Rightarrow> ERR(dio)"  

 abbreviation disj::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>\<or>" 52) where "\<phi> \<^bold>\<or> \<psi> \<equiv> case (\<phi>,\<psi>) of
    (P(\<alpha>),P(\<beta>)) \<Rightarrow> P(\<lambda>w. \<alpha> w \<or> \<beta> w) | (F(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<or> \<beta> w) | 
    (P(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<or> \<beta> w) | (F(\<alpha>),P(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<or> \<beta> w) | 
    _ \<Rightarrow> ERR(dio)"  

 abbreviation equiv::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>\<equiv>" 51) where "\<phi> \<^bold>\<equiv> \<psi>\<equiv> case (\<phi>,\<psi>) of
    (P(\<alpha>),P(\<beta>)) \<Rightarrow> P(\<lambda>w. \<alpha> w \<longleftrightarrow> \<beta> w) | (F(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longleftrightarrow> \<beta> w) | 
    (P(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longleftrightarrow> \<beta> w) | (F(\<alpha>),P(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longleftrightarrow> \<beta> w) | 
    _ \<Rightarrow> ERR(dio)"  

 abbreviation diamond::"io opt\<Rightarrow>io opt" ("\<^bold>\<diamond> _" [62] 63) where "\<^bold>\<diamond>\<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w.\<exists>v. \<psi> v) | P(\<psi>) \<Rightarrow> P(\<lambda>w.\<exists>v. \<psi> v) | _ \<Rightarrow> ERR(dio)"

 abbreviation exists::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> case (\<Phi> da) of
    P \<phi> \<Rightarrow> P(\<lambda>w.\<exists>x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> w) 
  | F \<phi> \<Rightarrow> F(\<lambda>w. \<exists>x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> w) | _ \<Rightarrow> ERR dio" 
 abbreviation existsBinder::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" (binder "\<^bold>\<exists>" [8] 9)  where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"

 (* abbreviation true::"io opt" ("\<top>\<^sup>z") where "\<top>\<^sup>z \<equiv> todo; not entirely clear yet " *)
 (* abbreviation alse::"io opt" ("\<bottom>\<^sup>z") where "\<bottom>\<^sup>z \<equiv> todo; not entirely clear yet " *)


section {* Meta-Logic*}

  text {* 
  Our approach to rigorously distinguish between proper and improper language constructions 
  and to explicitly maintain respective information is continued also at meta-level. For this 
  we introduce three truth values @{text "tt"},
  @{text "ff"} and @{text "err"}, representing truth, falsity and error. These values aro also 
  noted as @{text "\<top>"}, @{text "\<bottom>"} and @{text "*"}. We could, of course, also introduce  
  respective logical connectives for the meta-level, but in our applications (see below)
  this was not yet relevant.
  *}

 datatype mf = tt ("\<top>") | ff ("\<bottom>") | err ("*")

 (*
 abbreviation meta_not::"mf \<Rightarrow> mf" ("\<not>\<^sup>m") where "\<not>\<^sup>m \<phi>  \<equiv> case \<phi> of 
    error \<Rightarrow> error | tt \<Rightarrow> ff | ff \<Rightarrow> tt"  
 abbreviation meta_implies::"mf \<Rightarrow> mf \<Rightarrow>mf" (infixr "\<longrightarrow>\<^sup>m" 51) where "\<phi> \<longrightarrow>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (tt,ff) \<Rightarrow> ff | _ \<Rightarrow> tt"  
 abbreviation meta_or::"mf \<Rightarrow> mf \<Rightarrow>mf" (infixl "\<or>\<^sup>m" 51) where "\<phi> \<or>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (ff,ff) \<Rightarrow> ff | _ \<Rightarrow> tt"  
 abbreviation meta_and::"mf \<Rightarrow> mf \<Rightarrow>mf" (infixl "\<and>\<^sup>m" 51) where "\<phi> \<and>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (tt,tt) \<Rightarrow> tt | _ \<Rightarrow> ff"  
 abbreviation meta_equiv::"mf \<Rightarrow> mf \<Rightarrow>mf" (infixl "\<longleftrightarrow>\<^sup>m" 51) where "\<phi> \<longleftrightarrow>\<^sup>m \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (error,_) \<Rightarrow> error | (_,error) \<Rightarrow> error | (tt,tt) \<Rightarrow> tt | (ff,ff) \<Rightarrow> tt | _ \<Rightarrow> ff"  
 *)

  text {* 
  Next we define the meta-logical notions of validity, satisfiability, 
  countersatisfiability and invalidity for our embedded modal relational type theory. To support
  concise formula representations in the remainder we introduce the following notations: @{text "[\<phi>]"} 
  (for @{text "\<phi>"} is valid), @{text "[\<phi>]\<^sup>s\<^sup>a\<^sup>t "} (@{text "\<phi>"} is satisfiability), @{text "[\<phi>]\<^sup>c\<^sup>s\<^sup>a\<^sup>t"} 
  (@{text "\<phi>"} is countersatisfiability) and @{text "[\<phi>]\<^sup>i\<^sup>n\<^sup>v"} (@{text "\<phi>"} is invalid). Actually, so far 
  we only use validity.
  *}

 (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
 (*<*) no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
 abbreviation valid :: "io opt\<Rightarrow>mf" ("[_]" [1]) where "[\<phi>] \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<forall>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> 
  | F(\<psi>) \<Rightarrow> if \<forall>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"
 abbreviation satisfiable :: "io opt\<Rightarrow>mf" ("[_]\<^sup>s\<^sup>a\<^sup>t" [1]) where "[\<phi>]\<^sup>s\<^sup>a\<^sup>t \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<exists>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> 
  | F(\<psi>) \<Rightarrow> if \<exists>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"
 abbreviation countersatisfiable :: "io opt\<Rightarrow>mf" ("[_]\<^sup>c\<^sup>s\<^sup>a\<^sup>t" [1]) where "[\<phi>]\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<exists>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> 
  | F(\<psi>) \<Rightarrow> if \<exists>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"
 abbreviation invalid :: "io opt\<Rightarrow>mf" ("[_]\<^sup>i\<^sup>n\<^sup>v" [1]) where "[\<phi>]\<^sup>i\<^sup>n\<^sup>v \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<forall>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> 
  | F(\<psi>) \<Rightarrow> if \<forall>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | _ \<Rightarrow> *"


(*<*)
end
(*>*)

