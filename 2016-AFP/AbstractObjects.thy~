(*<*) 
theory AbstractObjects
imports Main

begin
(*>*)

section {* Introduction *}
  text {* 
  The ambitious Principia Metaphysica \cite{zalta:_princ_metap} project at Stanford University aims
  at providing an encompassing axiomatic foundation for metaphysics, mathematics and the sciences. 
  The starting point is Zalta's theory of abstract objects \cite{zalta83:_abstr_objec}, which \ldots.
 
  The theory of abstract objects utilizes a modal relational type theory (MRTT) as 
  logical foundation.  Arguments
  defending this choice against a modal functional type theory (MFTT)
  have been presented before \cite{zalta11:_relat_versus_funct_found_logic}.
  In a nutshell, the situation is this: functional type theory comes with strong 
  comprehension principles, which, in the context of the theory of abstract objects, 
  have paradoxical implications. When starting off with a relational foundation, however, 
  weaker comprehension principles are provided, and these obstacles can be avoided.

  Isabelle/HOL is a proof assistant based on a functional type theory extending
  Church's theory of types \cite{Church40}, and recently it has been shown 
  that Church's type theory can be elegantly utilized as a meta-logic to semantically embed and 
  automate various quantified non-classical logics, including MFTT \cite{J23,C40}. 
  This embedding of MFTT has subsequently been employed in a case study in
  computational metaphysics, in which different variants of Kurt Gödel's ontological 
  argument were verified resp. falsified \cite{C40,C55}. 
 
  The motivating research questions for the formalisation presented below include:
  \begin{itemize} 
  \item Can functional type theory, despite the problems as pointed 
   out by Zalta and
   Oppenheimer \cite{zalta11:_relat_versus_funct_found_logic}, 
   nevertheless be fruitfully utilized to encode MRTT and subsequently the theory of abstract 
   objects when adapting and utilizing the embeddings approach? As it turns, we will 
   need a significant, technically involved extension of the embeddings approach.
  \item From another viewpoint the issue is to investigate possibilities to handle restricted 
   forms of comprehension in a functional type theory context within the embedding approach.
  \item From a pragmatic point of view, we want to assess the elegance and user-friendliness of 
   the proposed formalization? 
   To what extend can Isabelle's  user interface be facilitated to hide 
   unpleasant technicalities of the extended embedding from the user?
  \item Moreover, how far can automation be pushed in the approach to minimise user interaction  
    in the formalization of the theory of abstract objects? For this note the proof automation has
    worked very well for the simpler embeddings of as used in related work \cite{C40,C55}. 
  \item Can the consistency of the theory eventually be validated with the available automated 
   reasoning tools?
  \item Can the reasoners eventually even contribute some new knowledge? 
  \item Are any suggestions  arising for possible improvements in Isabelle/HOL.
   What are the particular problems detected in the course of the study?
  \end{itemize}

  In this contribution to the Archive of Formal Proofs, however, we primarily focus on presenting 
  the encoding 
  of MRTT in functional type theory. The idea is to extend the fundamental ideas underlying
  the previous encoding of MFTT in functional type theory. 
  In subsequent papers we will then reuse and extend the 
  foundations provided in this article and further address the above questions.q
 
  The encoding of modal functional type theory in functional type theory as explored in 
  previous work  is simple: modal logic formulas are identified with certain functional 
  type theory formulas of predicate type @{text "i\<Rightarrow>bool"} (abbreviated as @{text "io"} below). 
  Possible worlds are explicitly represented by 
  terms of type  @{text "i"}. A modal logic formula @{text "\<phi>"} holds for a world @{text "w"} if and 
  only if the application @{text "\<phi> w"} evaluates to true. The definition of the propositional modal logic 
  connectives is then straightforward and it simply realizes the standard translation as a set of equations 
  in functional type theory. The approach has been successfully extended for quantifiers. A crucial 
  aspect thereby is that in simple type theory quantifiers can be treated
  as ordinary logical connectives. No extra binding mechanism is needed since the already existing 
  lambda binding mechanism can be elegantly utilized. 
  
  The challenge for this work has been to suitably appropriately 'restrict' this embedding for modal relational type theory.
  The grammar of modal relational type theory is presented in Figure~\ref{mmrt}.
   \begin{figure}[t]
  \includegraphics[height=5.5cm]{ModalRelationalTypeTheory.png}\includegraphics[height=4.5cm]{ModalRelationalTypeTheory2.png}
  \caption{Grammar of MRTT, cf. \cite{zalta:_princ_metap} for further details. \label{mmrt}
  Two kinds of (complex) formulas are introduced: the $\varphi$-formulas may have encoding subformulas, while the
  $\varphi^*$-formulas must not. The latter are designated as propositional formulas, the former ones simply as formulas.}
  \end{figure}
  Note that this grammar excludes terms such as $\lambda x. Rx \rightarrow xR$, where $Rx$ represents the 
  exemplification of property $R$ by $x$ and $xR$ stands for the encoding of property $R$ by $x$. The reason is 
  that such kind of  
  lambda-abstractions may lead to paradoxes in the theory of abstract 
  objects \cite{zalta11:_relat_versus_funct_found_logic}.
  

  To achieve our goal we provide means to explicitly represent, maintain and propagate information  on the 
  syntactical structure of MRTT in functional type theory. In particular, we provide means in form of annotations 
  to explicitly distinguish 
  between propositional formulas, formulas, terms and erroneous (ineligible/excluded) formations. 
  Respective annotation information is propagated from the innermost constituents to the top level constructions.
  This creates some non-trivial technical overhead. However, Isabelle/HOL's user 
  interface provide facilities to widely hide these technicalities from the user in applications.

  A note on using abbreviations versus definitions in our approach:  We are aware that abbreviations should
  be used sparsingly in Isabelle/HOL; they are automatically expanded and thus lead to a discrepancy 
  between the internal and the external view of a term. However, we here deliberately deviate from this
  rule, since one aspect of the paper is to exactly illustrate this discrepancy and to emphasize the complexity
  of the embedding MRTT in functional type theory. In fact, this complexity makes pen and paper 
  work with the proposed embedding pragmatically infeasible. In this sense, we agree with earlier findings
   \cite{zalta11:_relat_versus_funct_found_logic}. On the other hand, we demonstrate the general feasibility here, and we
  show, that within a modern interactive proof assistant like Isabelle/HOL the approach can eventually be handled to 
  some modest degree. In fact, as we will also
  illustrate, the simplifier @{text "simp"} of Isabelle/HOL is well capable of effectively reducing
  the technically inflated terms we obtain from the extended embedding again to their logical core content. 
  In other words, the simplifier effectievely analyses and and rewrites the 
  deeply annotated terms and propagates the annotation information as intended to top-level.
  It is exactly this effect which we want to illustrate and exploit here.\footnote{We have also 
  experimented with using definitions instead of abbreviations; the respective 
  encodings can be requested from the authors.}
  *}

section {* Preliminaries *}
  text {* 
  We start out with some type declarations and type abbreviations. 
  Note that our formalism explicitly encodes possible world semantics. Hence, we introduce a 
  distinguished type @{text "i"} to represent the set of possible worlds. 
  Consequently, terms of this type denote possible worlds. 
  Moreover, modal logic formulas are associated in our approach with
  predicates (resp. sets) on possible worlds. Hence, modal logic formulas have
  type @{text "(i \<Rightarrow> bool)"}. To make our representation  more concise in the remainder
  we abbreviate this type as @{text "io"}.
  *}

 typedecl i
 type_synonym io = "(i \<Rightarrow> bool)" 

  text {*
  Entities in the abstract theory of types are represented in our formalism by the
  type @{text "e"}. We call this the raw type of entities resp. objects. The Theory of Abstract Objects 
  later introduces means to distinguish between abstract and ordinary entities.    
  *}

 typedecl e

  text {*
  To explicitly model the syntactical restrictions of MRTT we introduce a 
  (polymorphic) datatype @{text "'a opt"} (@{text "'a"} is a type variable) 
  based on four constructors: @{text "ERR 'a"} (identifies ineligible/excluded constructions), @{text "P 'a"} 
  (identifies propositional formulas), @{text "F 'a"} (identifies  formulas), and @{text "T 'a"} (identifies 
  eligible terms, such as lambda abstractions). The embedding approach (of MFTT in functional type theory)
  will be suitably adapted below so that 
  for each language expression (in the embedded MRTT) the respective datatype 
  is identified and appropriately propagated. The encapsulated expressions  
  correspond to the previous embedding of MRTT in functional type theory  \cite{J23,C40}.  
  *}

 datatype 'a opt = ERR 'a | P 'a | F 'a | T 'a 

  text {* The following operators support a concise and elegant superscript annotation with these
  four syntactical categories for our language constructs.
  *}

 abbreviation mkP::"io\<Rightarrow>io opt" ("_\<^sup>P" [109] 110)  where "\<phi>\<^sup>P \<equiv> P \<phi>" 
 abbreviation mkF::"io\<Rightarrow>io opt" ("_\<^sup>F" [109] 110)  where "\<phi>\<^sup>F \<equiv> F \<phi>" 
 abbreviation mkT::"'a\<Rightarrow>'a opt" ("_\<^sup>T" [109] 110)  where "\<phi>\<^sup>T \<equiv> T \<phi>"
 abbreviation mkE::"'a\<Rightarrow>'a opt" ("_\<^sup>E" [109] 110)  where "\<phi>\<^sup>E \<equiv> ERR \<phi>" 

  text {* Certain language constructs in the Theory of Abstract objects, such as the actuality operator  
  @{text "\<^bold>\<A>"} ("it is actually the case that"), refer to a (fixed) designated world. To model such a 
  rigid dependence we introduce a constant symbol (name) @{text "dw"} of world type @{text "i"}. 
  Moreover, for technical reasons, 
  which will be clarified below, we introduce further (dummy) constant symbols for the various other domains. 
  We anyway assume that all domains are non-empty. Hence, introducing these constant symbols is obviously not harmful. 
  \footnote{The single polymorphic dummy @{text "\<^bold>da::'a"}, utilized e.g. in the definition of the universal 
  quantifier of MRTT below, actually covers already all cases. However, to avoid unnecessary type inferences we
  actually prefer non-polymorphic dummy elements in all those cases where we can statically 
  determine the required type.}
  *}

 consts dw::"i" 
 consts de::"e" dio::"io" deio::"e\<Rightarrow>io" da::"'a"

section {* Embedding of Modal Relational Type Theory *}

  text {* 
  The various language constructs of MRTT (see Figure \ref{mmrt}) are now introduced step by step. 
  *}

  text {* The actuality operator @{text "\<^bold>\<A>"}, when being applied to a formula or propositional formula 
  @{text "\<phi>"}, evaluates @{text "\<phi>"} wrt the fixed given world @{text "dw"}. 
  The compound expression @{text "\<^bold>\<A>\<phi>"} inherits its syntactical category  @{text "F"} (formula) or
  @{text "P"} (propositional formula) from @{text "\<phi>"}. If the syntactical catagory of  @{text "\<phi>"} is 
  @{text "ERR"} (error) or @{text "T"} (term), then the syntactical catagory of @{text "\<^bold>\<A>\<phi>"} 
  is @{text "ERR"} and a dummy entity of appropriate type is returned. This illustrates the core 
  ideas of our explicit modeling of MRTT grammatical structure in functional type theory. 
  This scheme will repeated below for all the other language constructs of MRTT. 
  *}

 abbreviation Actual::"io opt \<Rightarrow> io opt" ("\<^bold>\<A> _" [64] 65) where "\<^bold>\<A>\<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w. \<psi> dw) | P(\<psi>) \<Rightarrow> P(\<lambda>w. \<psi> dw) | _ \<Rightarrow> ERR(dio)"

  text {* 
  The Theory of Abstract Objects distinguishes between encoding properties @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} and 
  exemplifying properties @{text "\<Pi>\<^sup>n,\<kappa>\<^sub>1,..,\<kappa>\<^sub>n"} (for $n\geq 1$). 

  Encoding @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} is noted below as @{text "\<lbrace>\<kappa>\<^sub>1,\<Pi>\<^sup>1\<rbrace>"}.
  Encoding yields formulas and never propositional formulas. It is mapped to expressions of 
  form @{text "(enc Q y)"}, where @{text "enc"} is uninterpreted constant symbol of appropriate 
  type. Exemplification will instead be mapped to predicate application. Unfortunately, we cannot map both, 
  exemplification and encoding, to predicate application, since this would have undesirable effects.
  For example, we could then prove that @{text "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<equiv> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)]"} is true, which we definitely
  want to avoid. See also the basic tests in Subsection \ref{basic-tests-1}.
  *}

 consts enc::"(e\<Rightarrow>io)\<Rightarrow>e\<Rightarrow>io"
 abbreviation Enc::"e opt\<Rightarrow>(e\<Rightarrow>io) opt\<Rightarrow>io opt" ("\<lbrace>_,_\<rbrace>") where "\<lbrace>x,\<Phi>\<rbrace> \<equiv> case (x,\<Phi>) of 
    (T(y),T(Q)) \<Rightarrow> F(enc Q y) | _ \<Rightarrow> ERR(dio)"

  text {* 
  Unary exemplifying formulas @{text "\<Pi>\<^sup>1\<kappa>\<^sub>1"} are noted below as @{text "\<lparr>\<Pi>\<^sup>1,\<kappa>\<^sub>1\<rparr>"}.  
  Exemplification yields propositional formulas. Like encoding, it is then mapped to predicate application.
  *}

 abbreviation Exe1::"(e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_\<rparr>") where "\<lparr>\<Phi>,x\<rparr> \<equiv> case (\<Phi>,x) of 
    (T(Q),T(y)) \<Rightarrow> P(Q y) | _ \<Rightarrow> ERR(dio)"

  text {* 
 For pragmatical reasons we support exemplification formulas @{text "\<Pi>\<^sup>n,\<kappa>\<^sub>1,..,\<kappa>\<^sub>n"} here only for @{text "1\<le>n\<le>3"}.
 In addition to the unary case above, we thus introduce two further cases.
  *}  

 abbreviation Exe2::"(e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_,_\<rparr>")
  where "\<lparr>\<Phi>,x1,x2\<rparr> \<equiv> case (\<Phi>,x1,x2) of 
    (T(Q),T(y1),T(y2)) \<Rightarrow> P(Q y1 y2) | _ \<Rightarrow> ERR(dio)"
 abbreviation Exe3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_,_,_\<rparr>") 
  where "\<lparr>\<Phi>,x1,x2,x3\<rparr> \<equiv> case (\<Phi>,x1,x2,x3) of 
    (T(Q),T(y1),T(y2),T(y3)) \<Rightarrow> P(Q y1 y2 y3) | _ \<Rightarrow> ERR(dio)"

  text {* 
  Formations with negation and implication are supported for both, formulas and propositional
  formulas, and their embeddings are straightforward. In the case of implication, the compound formula
  is a propositional formula if both constituents are propositional formulas. If at least one constituent 
  is a formula and the other one eligible, then the compound formula is a formula. In all other
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
  for both, formulas  and propositional formulas. Following previous work, the embedding maps 
  @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"} to @{text "(\<lambda>w.\<forall>x.\<phi>w)"}, where the latter @{text "\<forall>"} is the universal 
  quantifier from the HOL meta-logic. Note that @{text "\<^bold>\<forall>"} is introduced as logical connective
  based on the existing @{text "\<lambda>"}-binder. To improve the presentation and intuitive use 
  in the remainder we additionally
  introduce binder notation @{text "\<^bold>\<forall>x.\<phi>"} as syntactic sugar for @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"}.
  *}

 abbreviation forall::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> case (\<Phi> da) of
    F(_) \<Rightarrow> F(\<lambda>w.\<forall>x. case (\<Phi> x) of F(\<psi>) \<Rightarrow> \<psi> w) 
  | P(_) \<Rightarrow> P(\<lambda>w.\<forall>x. case (\<Phi> x) of P(\<psi>) \<Rightarrow> \<psi> w) | _ \<Rightarrow> ERR(dio)"
 abbreviation forallBinder::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" (binder "\<^bold>\<forall>" [8] 9)  where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"

(* lemma binderTest: "(\<^bold>\<forall>x. \<phi> x) = \<^bold>\<forall>(\<lambda>x. \<phi> x)" by simp *)

  text {* 
  The modal @{text "\<^bold>\<box>"}-operator is introduced here for logic S5. Since in an equivalence class
  of possible worlds each world is reachable from any other world, the guarding accessibility clause
  in the usual definition of the @{text "\<^bold>\<box>"}-operator can be omitted. This is convenient and also
  improves the efficience of theorem provers, cf. \cite{C55}.  
  In Section \ref{sec:S5} we will actually demonstrate that the expected S5 properties
  are validated by our modeling of @{text "\<^bold>\<box>"}.  The @{text "\<^bold>\<box>"}-operator can be applied to 
  formulas  and propositional formulas.
  *}

 abbreviation box::"io opt\<Rightarrow>io opt" ("\<^bold>\<box>_" [62] 63) where "\<^bold>\<box>\<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w.\<forall>v. \<psi> v) | P(\<psi>) \<Rightarrow> P(\<lambda>w.\<forall>v. \<psi> v) | _ \<Rightarrow> ERR(dio)"  

  text {* 
  n-ary lambda abstraction @{text "\<^bold>\<lambda>\<^sup>0,\<^bold>\<lambda>,\<^bold>\<lambda>\<^sup>2\<^sup>,\<^bold>\<lambda>\<^sup>3,..."}, for $n\geq 0$, is supported in the theory of abstract 
  objects only for propositional formulas. This way constructs such as 
  beforehand mentioned $(\lambda x. Rx \rightarrow xR)$  (noted here as @{text "(\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)"} 
  are excluded, respectively identified as @{text "ERR"}-annotated 
  terms in our framework.
  Their embedding is 
  straightforward: @{text "\<^bold>\<lambda>\<^sup>0"} is mapped to identity and @{text "\<^bold>\<lambda>,\<^bold>\<lambda>\<^sup>2,\<^bold>\<lambda>\<^sup>3,..."} are mapped to n-ary
  lambda abstractions, that is, @{text "\<^bold>\<lambda>(\<lambda>x.\<phi>)"} is mapped to @{text "(\<lambda>x.\<phi>)"} and @{text "\<^bold>\<lambda>\<^sup>2(\<lambda>xy.\<phi>)"} 
  to @{text "(\<lambda>xy.\<phi>)"}, etc.
  Similar to before, we support only the cases for $n\leq 3$. Binder notation is
  introduced for @{text "\<^bold>\<lambda>"}.\footnote{Unfortunately, we could not find out how suitable binder notation
  could be analogously provided for @{text "\<^bold>\<lambda>\<^sup>2"} and @{text "\<^bold>\<lambda>\<^sup>3"}}. 
  *}

 abbreviation lam0::"io opt\<Rightarrow>io opt" ("\<^bold>\<lambda>\<^sup>0") where "\<^bold>\<lambda>\<^sup>0\<phi> \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> P(\<psi>) | _ \<Rightarrow> ERR dio"  
 abbreviation lam::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt" ("\<^bold>\<lambda>") where "\<^bold>\<lambda>\<Phi> \<equiv> case (\<Phi> de) of
    P(_) \<Rightarrow> T(\<lambda>x. case (\<Phi> x) of P(\<phi>) \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR(\<lambda>x. dio)"
 abbreviation lamBinder::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt" (binder "\<^bold>\<lambda>" [8] 9)  where "\<^bold>\<lambda>x. \<phi> x \<equiv> \<^bold>\<lambda> \<phi>"
 abbreviation lam2::"(e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>io) opt" ("\<^bold>\<lambda>\<^sup>2") where "\<^bold>\<lambda>\<^sup>2\<Phi> \<equiv> case (\<Phi> de de) of
    P(_) \<Rightarrow> T(\<lambda>x y. case (\<Phi> x y) of P(\<phi>) \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR(\<lambda>x y. dio)"
 abbreviation lam3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt" ("\<^bold>\<lambda>\<^sup>3") where "\<^bold>\<lambda>\<^sup>3\<Phi> \<equiv> case (\<Phi> de de de) of
    P(_) \<Rightarrow> T(\<lambda>x y z. case (\<Phi> x y z) of P(\<phi>) \<Rightarrow> \<phi>) | _ \<Rightarrow> ERR(\<lambda>x y z. dio)"

  text {* 
  The theory of abstract objects supports rigid definite descriptions. Our definition maps
  @{text "\<^bold>\<iota>(\<lambda>x.\<phi>)"} to @{text "(THE x. \<phi> dw)"}, that is, Isabelle's inbuilt definite description operator 
  @{text "THE"} 
  is utilized and evaluation is rigidly carried out with respect to the current world denoted by @{text "dw"}.
  We again introduce binder notation for @{text "\<^bold>\<iota>"}.
  *}
 
 abbreviation that::"(e\<Rightarrow>io opt)\<Rightarrow>e opt" ("\<^bold>\<iota>")  where "\<^bold>\<iota>\<Phi> \<equiv> case (\<Phi> de) of
    F(_) \<Rightarrow> T(THE x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> dw) | P(_) \<Rightarrow> T(THE x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> dw) | _ \<Rightarrow> ERR(de)"
 abbreviation thatBinder::"(e\<Rightarrow>io opt)\<Rightarrow>e opt" (binder "\<^bold>\<iota>" [8] 9)  where "\<^bold>\<iota>x. \<phi> x \<equiv> \<^bold>\<iota> \<phi>"

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
    P(_) \<Rightarrow> P(\<lambda>w.\<exists>x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> w) 
  | F(_) \<Rightarrow> F(\<lambda>w. \<exists>x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> w) | _ \<Rightarrow> ERR dio" 
 abbreviation existsBinder::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" (binder "\<^bold>\<exists>" [8] 9)  where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"

section {* Meta-Logic*}

  text {* 
  Our approach to rigorously distinguish between proper and improper language constructions 
  and to explicitly maintain respective information is continued also at meta-level. For this 
  we introduce three truth values @{text "tt"},
  @{text "ff"} and @{text "err"}, representing truth, falsity and error. These values are also 
  noted as @{text "\<top>"}, @{text "\<bottom>"} and @{text "*"}. We could, of course, also introduce  
  respective logical connectives for the meta-level, but in our applications (see below)
  this was not yet relevant.
  *}

 datatype mf = tt ("\<top>") | ff ("\<bottom>") | err ("*")

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



section {* Some Basic Tests *}

 subsection {* Exemplification and Encoding \label{basic-tests-1} *} 

 text {* 
  For the following non-theorems we indeed get countermodels by nitpick.
  *}

 lemma "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp nitpick [expect = genuine]  oops -- {* Countermodel by Nitpick *}
 lemma "[(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp nitpick  [expect = genuine] oops -- {* Countermodel by Nitpick *}

  text {* With this example we also want to illustrate the inflation of representations as caused by the
     embedding. For this note, that the formula @{text "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>"} abbreviates the
    actual term  
   @{text "(case case \<lbrace>da\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,da\<^sup>T\<rparr> of P x \<Rightarrow> (\<lambda>w. \<forall>x. case \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr> of P \<psi> \<Rightarrow> \<psi> w)\<^sup>P
          | F x \<Rightarrow> (\<lambda>w. \<forall>x. case \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr> of F \<psi> \<Rightarrow> \<psi> w)\<^sup>F | _ \<Rightarrow> dio\<^sup>E of
     P \<psi> \<Rightarrow> if \<forall>w. \<psi> w = True then \<top> else \<bottom> | F \<psi> \<Rightarrow> if \<forall>w. \<psi> w = True then \<top> else \<bottom> | _ \<Rightarrow> *) = \<top>"}.
  In Isabelle the inflated term is displayed in the output window when placing the mouse on the abbreviated representation.
  However, the simplifier is capable of evaluating the annotations and thereby reducing this inflated term again 
  to @{text "\<forall>w x. R x w \<longrightarrow> enc R x w"} as intended; one can easily see this when placing the mouse on "simp". 
  Below we will see that the inflated representations can 
  easily fill several pages for abbreviated formulas which are only slightly longer than what we have here. 
  This provides evidence for the pragmatic infeasibility of the approach when using pen and paper only. *}

  text {* 
  The next two statements are valid and the simplifier quickly proves this.
  *}

 lemma "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" by simp 
 lemma "[(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" by simp

 subsection {* Verifying Necessitation *}

  text {* The next two lemmata show that neccessitation holds for arbitrary formulas 
  and arbitrary propositional formulas. We present the lemmata in both variants. 
  *}
 
 lemma necessitationF: "[\<phi>\<^sup>F] = \<top> \<longrightarrow> [\<^bold>\<box>\<phi>\<^sup>F] = \<top>" by simp
 lemma necessitationP: "[\<phi>\<^sup>P] = \<top> \<longrightarrow> [\<^bold>\<box>\<phi>\<^sup>P] = \<top>" by simp

 subsection {* Modal Collapse is Countersatisfiable *}

  text {* 
  The modelfinder Nitpick constructs a finite countermodel to the assertion
  that modal collaps holds. 
  *}

 lemma modalCollapseF: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp nitpick [expect = genuine] oops -- {* Countermodel by Nitpick *}
 lemma modalCollapseP: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp nitpick [expect = genuine] oops -- {* Countermodel by Nitpick *}

 (*
 lemma modalCollapseFcsa: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F] = \<top>" sledgehammer [remote_leo2 remote_satallax]
 lemma modalCollapseFcsa: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<top>" sledgehammer [remote_leo2 remote_satallax]
 lemma modalCollapsePcsa: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<top>" sledgehammer [remote_leo2 remote_satallax]
 *)

 subsection {* Verifying S5 Principles \label{sec:S5} *} 

  text {* 
  @{text "\<box>"} could have been modeled by employing an equivalence relation @{text "r"} in a 
  guarding clause. This has been done in previous work. Our alternative, simpler definition of 
  @{text "\<box>"} above omits
  this clause (since all worlds are reachable from any world in an equivalence relation). The 
  following lemmata, which check various conditions for S5, confirm that we have indeed 
  obtain a correct modeling of S5.
  *}

 lemma axiom_T_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_T_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F] = \<top>" apply simp done

 lemma axiom_B_P: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_B_F: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma axiom_4_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp by auto
 lemma axiom_4_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp by auto

 lemma axiom_D_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_D_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma axiom_5_P: "[\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_5_F: "[\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma test_A_P: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma test_A_F: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma test_B_P: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp by auto
 lemma test_B_F: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp by auto

 lemma test_C_P: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}
 lemma test_C_F: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}

 lemma test_D_P: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma test_D_F: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp done


 subsection {* Relations between  Meta-Logical Notions *}

 lemma  "[\<phi>\<^sup>P] = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>P]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>F] = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>F]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done

  text {* 
  However, for terms we have: 
  *}

 lemma  "[\<phi>\<^sup>T] = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>i\<^sup>n\<^sup>v = *" apply simp done

 subsection {* Testing the Propagation of Syntactical Category Information *}

 lemma "\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>P \<and> \<not>(\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>F) \<and> \<not>(\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>T) \<and> \<not>(\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>E)" apply simp done
 lemma "\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>F \<and> \<not>(\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>P) \<and> \<not>(\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>T) \<and> \<not>(\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>E)" apply simp done

  text {* 
  Most importantly, we have that the following language construct is evaluated as ineligible at validity
  level; @{text "error (*)"} is returned. 
  *}
 
 lemma "(\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops

 lemma "[\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr>] = *" apply simp done

  text {* 
  This is also confirmed as follows in Isabelle: Isabelle simplifies the following expression
  to @{text "dio\<^sup>E = X"} (simply move the curse on @{text "simp"} to see this). 
  *}

 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr> = X" apply simp oops     -- {* X is @{text "dio\<^sup>E"} *}
 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<not>\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr> = X" apply simp oops     -- {* X is @{text "dio\<^sup>E"} *}

 subsection {* Are Priorities Defined Correctly? *}

 lemma "\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P \<equiv> (\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<^bold>\<rightarrow> \<chi>\<^sup>P" apply simp done
 lemma "\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P \<equiv> \<phi>\<^sup>P \<^bold>\<and> (\<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P)" apply simp nitpick oops -- {* Countermodel by Nitpick *}

 lemma "(\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<equiv> \<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<equiv> ((\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<^bold>\<equiv> (\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P))" apply simp done
 lemma "(\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<equiv> \<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<equiv> (\<phi>\<^sup>P \<^bold>\<and> (\<psi>\<^sup>P \<^bold>\<equiv> \<phi>\<^sup>P) \<^bold>\<and> \<psi>\<^sup>P)" apply simp nitpick oops -- {* Countermodel by Nitpick *}


section {* E!, O!, A! and =E *}

  text {* 
  We introduce the distinguished 1-place relation constant: E (read: ‘being concrete’ or ‘concreteness’) 
  *}

 consts E::"(e\<Rightarrow>io)"
 
  text {* 
  Being ordinary is defined as being possibly concrete. 
  *}

 abbreviation ordinaryObject::"(e\<Rightarrow>io) opt" ("O!") where "O! \<equiv> \<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>"

 lemma "O! = X" apply simp oops       -- {* X is @{text "(\<lambda>x w. Ex (exe E x))\<^sup>T"} *}

  text {* 
  Being abstract is is defined as not possibly being concrete. 
  *}

 abbreviation abstractObject::"(e\<Rightarrow>io) opt" ("A!") where "A! \<equiv> \<^bold>\<lambda>x. \<^bold>\<not>(\<^bold>\<diamond>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)"

 lemma "A! = X" apply simp oops       -- {* X is @{text "(\<lambda>x w. \<forall>xa. \<not> exe (E x) xa)\<^sup>T"} *}


  text {* 
  Identity relations @{text "\<^bold>=\<^sub>E"} and @{text "\<^bold>="} are introduced. 
  *}

 abbreviation identityE::"e opt\<Rightarrow>e opt\<Rightarrow>io opt" (infixl "\<^bold>=\<^sub>E" 63) where "x \<^bold>=\<^sub>E y \<equiv> 
    \<lparr>O!,x\<rparr> \<^bold>\<and> \<lparr>O!,y\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F\<^sup>T,x\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>T,y\<rparr>)"

 lemma "a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T = X" apply simp oops      -- {* X is "@{text "(...)\<^sup>P"} *}

 subsubsection {* Remark: Nested lambda-expressions *}
 
 lemma "(\<^bold>\<lambda> x. x\<^sup>T \<^bold>=\<^sub>E a\<^sup>T) = X" apply simp oops
 lemma "(\<^bold>\<lambda> x. x\<^sup>T \<^bold>=\<^sub>E a\<^sup>T) = (\<^bold>\<lambda> x. a\<^sup>T \<^bold>=\<^sub>E x\<^sup>T)" apply simp by metis


 subsection {* Identity on Individuals *}

 abbreviation identityI::"e opt\<Rightarrow>e opt\<Rightarrow>io opt" (infixl "\<^bold>=" 63) where "x \<^bold>= y \<equiv> 
    x \<^bold>=\<^sub>E y \<^bold>\<or> (\<lparr>A!,x\<rparr> \<^bold>\<and> \<lparr>A!,y\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<^sup>T\<rbrace>))"

 subsubsection {* Remark: Tracing the propagation of annotations *}
 lemma "a\<^sup>T \<^bold>= a\<^sup>T = X" apply simp oops                                        -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "(\<lparr>A!,a\<^sup>T\<rparr> \<^bold>\<and> \<lparr>A!,a\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace>)) = X" apply simp oops   -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "(\<lparr>A!,a\<^sup>T\<rparr> \<^bold>\<and> \<lparr>A!,a\<^sup>T\<rparr>) = X" apply simp oops                             -- {* X is @{text "(...)\<^sup>P"} *}
 lemma "\<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace>) = X" apply simp oops                       -- {* X is @{text "(...)\<^sup>F"} *}

  text {* 
  As intended: the following two lambda-abstractions are not well-formed/eligible 
  and their evaluation reports in ERR-terms.
  *}

 lemma "\<^bold>\<lambda>\<^sup>2(\<lambda>x y. x\<^sup>T \<^bold>= y\<^sup>T) = X" apply simp oops   -- {* X is @{text "(\<lambda>x y. dio)\<^sup>E"} *}
 lemma "(\<^bold>\<lambda>x. x\<^sup>T \<^bold>= y\<^sup>T) = X" apply simp oops   -- {* X is @{text "(\<lambda>x. dio)\<^sup>E"} *}

 subsection {* Identitiy on Relations *}

 abbreviation identityRel1::" ((e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>1" 63) 
   where "F1 \<^bold>=\<^sup>1 G1 \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,F1\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>T,G1\<rbrace>)"

 abbreviation identityRel2::" ((e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>2" 63) 
   where "F2 \<^bold>=\<^sup>2 G2 \<equiv> \<^bold>\<forall>x1.(  (\<^bold>\<lambda>y.\<lparr>F2,y\<^sup>T,x1\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G2,y\<^sup>T,x1\<^sup>T\<rparr>)
                          \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F2,x1\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G2,x1\<^sup>T,y\<^sup>T\<rparr>))"

 abbreviation identityRel3::" ((e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>3" 63) 
   where "F3 \<^bold>=\<^sup>3 G3 \<equiv> \<^bold>\<forall>x1 x2.(  (\<^bold>\<lambda>y.\<lparr>F3,y\<^sup>T,x1\<^sup>T,x2\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,y\<^sup>T,x1\<^sup>T,x2\<^sup>T\<rparr>)
                             \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F3,x1\<^sup>T,y\<^sup>T,x2\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,x1\<^sup>T,y\<^sup>T,x2\<^sup>T\<rparr>)
                             \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F3,x1\<^sup>T,x2\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,x1\<^sup>T,x2\<^sup>T,y\<^sup>T\<rparr>))"

 lemma "F1\<^sup>T \<^bold>=\<^sup>1 G1\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "F2\<^sup>T \<^bold>=\<^sup>2 G2\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *} 
 lemma "F3\<^sup>T \<^bold>=\<^sup>3 G3\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}   
 lemma "\<lbrace>x\<^sup>T,F1\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>T,G1\<^sup>T\<rbrace> = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}   
 lemma "\<lparr>F1\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<equiv> \<lparr>G1\<^sup>T,x\<^sup>T\<rparr> = X" apply simp oops -- {* X is @{text "(...)\<^sup>P"} *}   
 lemma "(\<^bold>\<lambda>y.\<lparr>F2\<^sup>T,y\<^sup>T,x1\<^sup>T\<rparr>)= X" apply simp oops -- {* X is @{text "(...)\<^sup>T"} *}  

 abbreviation equalityRel0::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>0" 63) 
   where "F0 \<^bold>=\<^sup>0 G0 \<equiv> (\<^bold>\<lambda>y . F0) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y. G0)"

  text {* 
  Some tests: reflexity, symmetry, transitivity
  *}

 lemma "F1\<^sup>T \<^bold>=\<^sup>1 F1\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "[F1\<^sup>T \<^bold>=\<^sup>1 F1\<^sup>T] = \<top>" apply simp done 
 lemma "[F2\<^sup>T \<^bold>=\<^sup>2 F2\<^sup>T] = \<top>" apply simp done
 lemma "[F3\<^sup>T \<^bold>=\<^sup>3 F3\<^sup>T] = \<top>" apply simp done 

 lemma "[(F1\<^sup>T \<^bold>=\<^sup>1 G1\<^sup>T) \<^bold>\<equiv> (G1\<^sup>T \<^bold>=\<^sup>1 F1\<^sup>T)] = \<top>" apply simp by auto
 lemma "[(F2\<^sup>T \<^bold>=\<^sup>2 G2\<^sup>T) \<^bold>\<equiv> (G2\<^sup>T \<^bold>=\<^sup>2 F2\<^sup>T)] = \<top>" apply simp by auto
 lemma "[(F3\<^sup>T \<^bold>=\<^sup>3 G3\<^sup>T) \<^bold>\<equiv> (G3\<^sup>T \<^bold>=\<^sup>3 F3\<^sup>T)] = \<top>" apply simp by auto

 lemma "[(F1\<^sup>T \<^bold>=\<^sup>1 G1\<^sup>T) \<^bold>\<and> (G1\<^sup>T \<^bold>=\<^sup>1 H1\<^sup>T) \<^bold>\<rightarrow> (F1\<^sup>T \<^bold>=\<^sup>1 H1\<^sup>T)] = \<top>" by simp 
 lemma "[(F2\<^sup>T \<^bold>=\<^sup>2 G2\<^sup>T) \<^bold>\<and> (G2\<^sup>T \<^bold>=\<^sup>2 H2\<^sup>T) \<^bold>\<rightarrow> (F2\<^sup>T \<^bold>=\<^sup>2 H2\<^sup>T)] = \<top>" by simp 
 lemma "[(F3\<^sup>T \<^bold>=\<^sup>3 G3\<^sup>T) \<^bold>\<and> (G3\<^sup>T \<^bold>=\<^sup>3 H3\<^sup>T) \<^bold>\<rightarrow> (F3\<^sup>T \<^bold>=\<^sup>3 H3\<^sup>T)] = \<top>" by simp

  text {* The above examples are very resource intensive already *}

  text {* 
  We discuss the example from \cite[pp.365-366]{zalta11:_relat_versus_funct_found_logic}:
  *}

 lemma "(\<^bold>\<lambda>x. \<^bold>\<exists>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>F\<^sup>T,x\<^sup>T\<rparr>) = X" apply simp  oops -- {*  X is @{text "(\<lambda>x. dio)\<^sup>E"} *}

 abbreviation K where "K \<equiv> \<^bold>\<lambda>x.\<^bold>\<exists>F.(\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>F\<^sup>T,x\<^sup>T\<rparr>)"
 
 lemma "K = X" apply simp oops  -- {*  X is @{text "(\<lambda>x. dio)\<^sup>E"} *}

 lemma "[(\<^bold>\<exists>x. \<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> F\<^sup>T \<^bold>=\<^sup>1 K)))] = *" apply simp done
 lemma "(\<^bold>\<exists>x. \<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> F\<^sup>T \<^bold>=\<^sup>1 K))) = X" apply simp oops -- {*  X is @{text "(dio)\<^sup>E"} *}
 

 text {* 
  Tests on identity:
  *}

 lemma "[a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick, as expected *}
 lemma "[\<lparr>O!,a\<^sup>T\<rparr> \<^bold>\<rightarrow> a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T] = \<top>" apply simp done

 lemma "[(\<^bold>\<forall>F. \<lparr>F\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp done
 lemma "[\<lparr>O!,a\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>\<^bold>\<lambda>x. x\<^sup>T \<^bold>=\<^sub>E a\<^sup>T,a\<^sup>T\<rparr>] = \<top>" apply simp done

 lemma "[(a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T) \<^bold>\<equiv>  \<lparr>\<^bold>\<lambda>x. x\<^sup>T \<^bold>=\<^sub>E a\<^sup>T,a\<^sup>T\<rparr>] = \<top>" apply simp done
 lemma "[(a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T) \<^bold>\<equiv> \<lbrace>a\<^sup>T,\<^bold>\<lambda>x. x\<^sup>T \<^bold>=\<^sub>E a\<^sup>T\<rbrace>] = \<top>" apply simp nitpick oops -- {* Countermodel by nitpick, because of "enc" *}

 lemma "[(\<^bold>\<exists>F. \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace>)] = \<top>" apply simp  nitpick oops -- {* Countermodel by Nitpick *}

 lemma "[(\<^bold>\<exists>\<phi>. \<phi>\<^sup>P)] = \<top>" apply simp by auto
 lemma "[(\<^bold>\<exists>\<phi>. \<phi>\<^sup>F)] = \<top>" apply simp by auto


 subsection {* Negation of Properties *}

 abbreviation notProp::"((e\<Rightarrow>io) opt)\<Rightarrow>(e\<Rightarrow>io) opt" ("\<^bold>\<sim>_" [58] 59) where "\<^bold>\<sim> \<Phi> \<equiv> case \<Phi> of 
    T(\<Psi>) \<Rightarrow> \<^bold>\<lambda>x.\<^bold>\<not>\<lparr>\<Phi>,x\<^sup>T\<rparr> | _ \<Rightarrow> ERR(deio)"  


 subsection {* Individual Constant @{text "\<^bold>a\<^sub>V"} and Function Term @{text "\<^bold>a\<^sub>G"} *}

 abbreviation a_V::"e opt" ("\<^bold>a\<^sub>V") where "\<^bold>a\<^sub>V \<equiv> \<^bold>\<iota>x. (\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> (F\<^sup>T \<^bold>=\<^sup>1 F\<^sup>T)))"

 abbreviation a_G::"(e\<Rightarrow>io) opt\<Rightarrow>e opt" ("\<^bold>a\<^sub>_" [58] 59) where "\<^bold>a\<^sub>G \<equiv> \<^bold>\<iota>x. (\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> (F\<^sup>T \<^bold>=\<^sup>1 G)))"

 
section {* Axioms *}

 subsection {* Axioms for Negations and Conditionals *}

 lemma a21_1_P: "[\<phi>\<^sup>P \<^bold>\<rightarrow> (\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a21_1_F: "[\<phi>\<^sup>F \<^bold>\<rightarrow> (\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F)] = \<top>" apply simp done
 lemma a21_2_P: "[(\<phi>\<^sup>P \<^bold>\<rightarrow> (\<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P)) \<^bold>\<rightarrow> ((\<phi>\<^sup>P \<^bold>\<rightarrow> \<psi>\<^sup>P) \<^bold>\<rightarrow> (\<phi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P))] = \<top>" apply simp done
 lemma a21_2_F: "[(\<phi>\<^sup>F \<^bold>\<rightarrow> (\<psi>\<^sup>F \<^bold>\<rightarrow> \<chi>\<^sup>F)) \<^bold>\<rightarrow> ((\<phi>\<^sup>F \<^bold>\<rightarrow> \<psi>\<^sup>F) \<^bold>\<rightarrow> (\<phi>\<^sup>F \<^bold>\<rightarrow> \<chi>\<^sup>F))] = \<top>" apply simp done
 lemma a21_3_P: "[(\<^bold>\<not>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<not>\<psi>\<^sup>P) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi>\<^sup>P \<^bold>\<rightarrow> \<psi>\<^sup>P) \<^bold>\<rightarrow> \<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a21_3_F: "[(\<^bold>\<not>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<not>\<psi>\<^sup>F) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi>\<^sup>F \<^bold>\<rightarrow> \<psi>\<^sup>F) \<^bold>\<rightarrow> \<phi>\<^sup>F)] = \<top>" apply simp done

 subsection {* Axioms of Identity *}
  text {* todo *}

 subsection {* Axioms of Quantification *}
  text {* todo *}

 subsection {* Axioms of Actuality *}

  text {* Here I have a big problem *}

  lemma a31_1_P: "[\<^bold>\<A>\<phi>\<^sup>P \<^bold>\<equiv> \<phi>\<^sup>P] = \<top>" apply simp nitpick oops

(* old version
 lemma a31_1_P: "[\<^bold>\<A>(\<^bold>\<not>\<phi>\<^sup>P) \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>(\<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a31_1_F: "[\<^bold>\<A>(\<^bold>\<not>\<phi>\<^sup>F) \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>(\<phi>\<^sup>F)] = \<top>" apply simp done
 lemma a31_2_P: "[\<^bold>\<A>(\<phi>\<^sup>P \<^bold>\<rightarrow> \<psi>\<^sup>P) \<^bold>\<equiv> (\<^bold>\<A>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<A>(\<psi>\<^sup>P))] = \<top>" apply simp done
 lemma a31_2_F: "[\<^bold>\<A>(\<phi>\<^sup>F \<^bold>\<rightarrow> \<psi>\<^sup>F) \<^bold>\<equiv> (\<^bold>\<A>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<A>(\<psi>\<^sup>F))] = \<top>" apply simp done
 lemma a31_3_P: "[\<^bold>\<A>(\<^bold>\<forall>x. \<phi>\<^sup>P) \<^bold>\<equiv> (\<^bold>\<forall>x. \<^bold>\<A>(\<phi>\<^sup>P))] = \<top>" apply simp done
 lemma a31_3_F: "[(\<^bold>\<A>(\<^bold>\<forall>x. \<phi>\<^sup>F) \<^bold>\<equiv> (\<^bold>\<forall>x. \<^bold>\<A>(\<phi>\<^sup>F)))] = \<top>" apply simp done
 lemma a31_4_P: "[\<^bold>\<A>(\<phi>\<^sup>P) \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<A>(\<phi>\<^sup>P))] = \<top>" apply simp done
 lemma a31_4_F: "[\<^bold>\<A>(\<phi>\<^sup>F) \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<A>(\<phi>\<^sup>F))] = \<top>" apply simp done
*)

 subsection {* Axioms of Necessity *}

 lemma a32_1_P: "[(\<^bold>\<box>(\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P)] = \<top>" apply simp done     (* K Schema *)
 lemma a32_1_F: "[(\<^bold>\<box>(\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F)] = \<top>" apply simp done     (* K Schema *)
 lemma a32_2_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P] = \<top>" apply simp done                           (* T Schema *)
 lemma a32_2_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F] = \<top>" apply simp done                           (* T Schema *)

 lemma a32_3_P: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done                       (* 5 Schema *)
 lemma a32_3_F: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done                       (* 5 Schema *)
 lemma a32_4_P: "[(\<^bold>\<forall>x. \<^bold>\<box>\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<forall>x. \<phi>\<^sup>P))] = \<top>" apply simp done         (* BF *)
 lemma a32_4_F: "[(\<^bold>\<forall>x. \<^bold>\<box>\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<forall>x. \<phi>\<^sup>F))] = \<top>" apply simp done         (* BF *)

  text {* 
  The following needs to be an axiom; it does not follow for free: it is possible that there 
  are contingently concrete individuals and it is possible that there are not: 
  *}
   
 axiomatization where
   a32_5_P: "[\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)))] = \<top>"

   text {* 
   A brief check that this axiom is well-formed, i.e. does not return error 
   *}
 
 lemma "[\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)))] \<noteq> *" apply simp done
 lemma "\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>))) = X" apply simp oops -- {* X is @{text "(...)\<^sup>P"} *}

 subsection {* (Instances of) Barcan Formula and Converse Barcan Formula *}
  
 lemma BF_inst: "[(\<^bold>\<forall>\<alpha>. \<^bold>\<box>\<lparr>R\<^sup>T,\<alpha>\<^sup>T\<rparr>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<alpha>.\<lparr>R\<^sup>T,\<alpha>\<^sup>T\<rparr>)] = \<top>" by simp 
 lemma CBF_inst: "[\<^bold>\<box>(\<^bold>\<forall>\<alpha>.\<lparr>R\<^sup>T,\<alpha>\<^sup>T\<rparr>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<^bold>\<box>\<lparr>R\<^sup>T,\<alpha>\<^sup>T\<rparr>)] = \<top>" apply simp by auto

 subsection {* Axioms of Necessity and Actuality *}

 lemma a33_1_P: "[\<^bold>\<A>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma a33_1_F: "[\<^bold>\<A>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>\<^sup>F] = \<top>" apply simp done
 lemma a33_2_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a33_2_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>\<^sup>F)] = \<top>" apply simp done

 subsection {* Axioms for Descriptions *}

 lemma "(x\<^sup>T \<^bold>= (\<^bold>\<iota>x.\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)) = X" apply simp oops    -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "(\<^bold>\<forall>z. (\<^bold>\<A>(\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) \<^bold>\<equiv> (z\<^sup>T \<^bold>= x\<^sup>T))) = X" apply simp oops    -- {* X is @{text "(...)\<^sup>F"} *} 

  text {* 
  For the following lemma cannot yet be automatically proved, since proof automation for definite
  descriptions is still not well enough developed in ATPs. 
  *}
 
  lemma a34_Inst_1: "[(x\<^sup>T \<^bold>= (\<^bold>\<iota>x.\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)) \<^bold>\<equiv> (\<^bold>\<forall>z. (\<^bold>\<A>(\<lbrace>z\<^sup>T,R\<^sup>T\<rbrace>) \<^bold>\<equiv> (z\<^sup>T \<^bold>= x\<^sup>T)))] = \<top>" apply simp oops


 subsection {* Axioms for Complex relation Terms *}
   
  text {* We check for some $\alpha$-renaming instances *}

  lemma "(\<^bold>\<lambda>z.\<lparr>R\<^sup>T,z\<^sup>T,(\<^bold>\<iota>y.\<lparr>Q\<^sup>T,y\<^sup>T\<rparr>)\<rparr>) = (\<^bold>\<lambda>x.\<lparr>R\<^sup>T,x\<^sup>T,(\<^bold>\<iota>z.\<lparr>Q\<^sup>T,z\<^sup>T\<rparr>)\<rparr>)" apply simp done
  
  lemma "((\<^bold>\<forall>F.\<lparr>F\<^sup>T,a\<^sup>T\<rparr>) \<^bold>\<equiv> (\<^bold>\<forall>G.\<lparr>G\<^sup>T,b\<^sup>T\<rparr>)) = (\<^bold>\<forall>F.\<lparr>F\<^sup>T,a\<^sup>T\<rparr>) \<^bold>\<equiv> (\<^bold>\<forall>F.\<lparr>F\<^sup>T,b\<^sup>T\<rparr>)" apply simp done
  
  text {* Others are analogously valid, we omit them here *}

 subsection {* Axioms of Encoding *}
 
  text {* The following need to become an axioms; they are not implied by the embedding. *}

  axiomatization where 
   a36: "[\<lbrace>x\<^sup>T,G\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x\<^sup>T,G\<^sup>T\<rbrace>] = \<top>" and
   a37: "[\<^bold>\<A>\<lbrace>x\<^sup>T,G\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,G\<^sup>T\<rbrace>] = \<top>" 

  text {* The following however holds *}
  lemma "[\<^bold>\<box>(\<^bold>\<A>\<lbrace>x\<^sup>T,G\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,G\<^sup>T\<rbrace>)] = \<top>" apply simp nitpick oops

(*<*)
section {* Various Further Test Examples *}

  text {* Todo: ... select, adapt, and explain some of examples below ... *}

 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr> = X" apply simp oops     -- {* X is @{text "(...)\<^sup>E"} *}

 lemma "[\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>,a\<^sup>T\<rparr>] = \<top>" apply simp oops

 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>,a\<^sup>T\<rparr> = X\<^sup>P" apply simp oops
 lemma "(\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops

 lemma "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>R. \<^bold>\<forall>(\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>))] = \<top>" apply simp done
 lemma "(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>) = X" apply simp oops

 lemma "[(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp done
 lemma "(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops

 lemma "[(\<^bold>\<exists>x y. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>y\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp done

 lemma "(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops
 lemma "(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>) = X" apply simp oops
 lemma "[(\<^bold>\<forall>R. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp oops
 lemma "(\<^bold>\<forall>R. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops

 lemma "[(\<^bold>\<forall>x. \<^bold>\<exists>(\<lambda>R. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>))] = \<top>" apply simp done
 lemma "[(\<^bold>\<exists>x. \<^bold>\<forall>(\<lambda>R. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>))] = \<top>" apply simp done
(*>*)


section {* Leibniz Theory of Concepts *}
  text {* Below we don't get that far yet, a systematic bottom up development seems to be required 
  first *}

 abbreviation LeibnizianConcept::"(e\<Rightarrow>io) opt" ("C!") 
  where "C! \<equiv> \<^bold>\<lambda>x. \<lparr>A!,x\<^sup>T\<rparr>"
 abbreviation ConceptSummation (infix "\<Oplus>" 100) 
  where "x \<Oplus> y \<equiv> \<^bold>\<iota>z. (\<lparr>C!,x\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>z\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>x,F\<^sup>T\<rbrace> \<^bold>\<or> \<lbrace>y,F\<^sup>T\<rbrace>)))"
 abbreviation ConceptInclusion (infix "\<preceq>" 100) 
  where "x \<preceq> y \<equiv> \<^bold>\<forall>F. (\<lbrace>x,F\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>y,F\<^sup>T\<rbrace>)"
 
lemma "[x\<^sup>T \<preceq> y\<^sup>T \<^bold>\<equiv> (\<^bold>\<exists>z. ((x\<^sup>T \<Oplus> z\<^sup>T) \<^bold>= y\<^sup>T))] = \<top>" apply simp oops
lemma "[x\<^sup>T \<preceq> y\<^sup>T \<^bold>\<equiv> (x\<^sup>T \<Oplus> y\<^sup>T \<^bold>= y\<^sup>T)] = \<top>" apply simp  oops

(* the provers still give up *)

lemma "[\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr>,y\<^sup>T\<rparr>] = X" apply simp oops
lemma "[\<lbrace>y\<^sup>T,\<^bold>\<lambda>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>\<rbrace>] = X" apply simp oops
lemma "[\<lbrace>y\<^sup>T,\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr>\<rbrace>] = X" apply simp oops

(*<*)
end
(*>*)
 
