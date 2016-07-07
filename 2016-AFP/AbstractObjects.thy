(*<*) 
theory AbstractObjects
imports Main

begin
(*>*)

text {*
\begin{abstract}
We present an attempt to formalize modal relational type theory in functional type theory. This
formalization has been motivated to serve as a possible starting point for the subsequent modeling
of Zalta's theory of abstract objects, which  provides an axiomatic foundation for metaphysics.
\end{abstract}
*}

section {* Introduction *}
  text {* 
  The principia metaphysica project\footnote{Cf.~\url{https://mally.stanford.edu/principia/principia.html}} 
  \cite{zalta:_princ_metap} at Stanford University aims
  at providing an encompassing axiomatic foundation for metaphysics, mathematics and the sciences. 
  The starting point is Zalta's theory of abstract objects \cite{zalta83:_abstr_objec}  --- a metaphysical 
  theory providing a systematic description of fundamental and complex abstract objects. This 
  theory provides is at heart of Zalta's ongoing 'principia metaphysica' 
  project.
  
  The theory of abstract objects utilizes a modal relational type theory (MRTT) as 
  logical foundation.  Arguments
  defending this choice against a modal functional type theory (MFTT)
  have been presented before \cite{zalta11:_relat_versus_funct_found_logic}.
  In a nutshell, the situation is this: functional type theory comes with strong 
  comprehension principles, which, in the context of the theory of abstract objects, 
  have paradoxical implications \cite[chap.4]{zalta11:_relat_versus_funct_found_logic}. 
  When starting off with a relational foundation, however, 
  weaker comprehension principles are provided, and these obstacles can be avoided.

  Isabelle/HOL is a proof assistant based on a functional type theory extending
  Church's theory of types \cite{Church40}, and recently it has been shown 
  that Church's type theory can be elegantly utilized as a meta-logic to semantically embed and 
  automate various quantified non-classical logics, including MFTT \cite{J23,C40}. 
  This embedding of MFTT has subsequently been employed in a case study in
  computational metaphysics, in which different variants of Kurt G{\"o}del's ontological 
  argument were verified resp. falsified \cite{C40,C55}. 

  In this paper we explore an idea to encode, respectively embed,  MRTT in functional type theory. 
  Thereby, we want adapt and extend ideas from the previous, successful embedding of MFTT in functional 
  type theory.
  Our contribution here shall serve as possible starting point for the subsequent
  formalization of further chapters of the theory of abstract objects and the principia 
  metaphysica -- as far as this is possible considering the technical challenges we report below. 

 
  The motivating research questions for the formalisation presented below include:
  \begin{itemize} 
  \item Can functional type theory, despite the problems as pointed 
   out by Zalta and
   Oppenheimer \cite{zalta11:_relat_versus_funct_found_logic}, 
   nevertheless be utilized to encode MRTT and subsequently the theory of abstract 
   objects when adapting and utilizing the embeddings approach? 
   % As it turns, we will 
   % need a significant, technically involved extension of the embeddings approach.
  \item From another perspective we are interested in studying options to restrict comprehension in 
   functional type theory when utilizing the embedding approach.
  \item From a pragmatic point of view, we want to assess the user-friendliness of 
   the proposed solution? 
   To what extend can Isabelle's  user interface hide 
   unpleasant technicalities of the extended embedding from the user?
  \item How far can automation be pushed in the approach? For this note that proof automation 
    worked  well for the simpler embeddings as utilized in previous work \cite{C40,C55}. 
  %\item Can the consistency of the theory eventually be validated with the available automated 
  % reasoning tools?
  %\item Can the reasoners eventually even contribute some new knowledge? 
  %\item Are any suggestions  arising for possible improvements in Isabelle/HOL.
  % What are the particular problems detected in the course of the study?
  \end{itemize}

  In this paper we focus mainly on the presentation of the embedding of MRTT in functional type theory.
  Some technical difficulties will be highlighted. However, a proper exploration and discussion of 
  the above questions is left as further work.
 


  The formalization idea we explore below is to adapt and extend the previous encoding of MFTT in 
  functional type theory. 
  The basic idea of this encoding is simple: modal logic formulas are identified with certain functional 
  type theory formulas of predicate type @{text "i\<Rightarrow>bool"} (abbreviated as @{text "io"} below). 
  Possible worlds are explicitly represented as
  terms of type  @{text "i"}. A modal logic formula @{text "\<phi>"} holds for a world @{text "w"} if and 
  only if the application @{text "(\<phi> w)"} evaluates to true. The definitions of the propositional modal logic 
  connectives are straightforward. These definitions realize the well known standard translation as a set of equations 
  in functional type theory and they successfully extend the standard translation also for quantifiers. An important
  aspect thereby is that quantifiers can be handled just as ordinary logical connectives. No binding mechanisms are needed,
  since the binding mechanism for lambda-abstractions can be fruitfully utilised.
  
  The challenge for the work presented here has been to suitably 'restrict' this embedding for MRTT (instead of MFTT).
  However, as we will see, this restriction is achieved below by introducing a technically involved 
  additional layer in the embedding; this additional layer provides means to annotate formulas and terms with
  grammatical information.
 
  The grammar of the second-order fragment of MRTT is presented in Figure~\ref{mmrt}; detailed descriptions
  of MRTT are available in the literature (see e.g. the appendix of \cite{Zalta88}).
 
   \begin{figure}[t]
  \includegraphics[height=5.5cm]{ModalRelationalTypeTheory.png}\includegraphics[height=4.5cm]{ModalRelationalTypeTheory2.png}
  \caption{Grammar of the second-order fragment of MRTT, cf. \cite{zalta:_princ_metap} for further details. \label{mmrt}
  Two kinds of (complex) formulas are introduced: the $\varphi$-formulas may have encoding subformulas, while the
  $\varphi^*$-formulas must not. The latter are designated as propositional formulas, the former ones simply as formulas.}
  \end{figure}
  Note that this grammar successfully excludes terms such as $(\lambda x \exists F. xF \wedge \neg Fx)$, where $Fx$ represents 
  exemplification of property $F$ by $x$ and $xF$ stands for the encoding of property $F$ by $x$. It are such kind of  
  lambda-abstractions which lead to paradoxical situations in the theory of abstract 
  objects \cite[chap.4]{zalta11:_relat_versus_funct_found_logic}.
  

  To achieve our goal we provide means to explicitly represent, maintain and propagate information  on the 
  syntactical structure of MRTT in functional type theory. In particular, we provide means in form of annotations 
  to explicitly distinguish 
  between propositional formulas, formulas, terms and erroneous (ineligible/excluded) formations. 
  Respective annotation information is propagated from the innermost constituents to the top level constructions.
  This creates some non-trivial technical overhead. However, due to Isabelle/HOL's user 
  interface these technicalities can be hidden from the user (to some extend). 

  A note on using abbreviations versus definitions in our approach:  We are aware that abbreviations should
  be used sparsingly in Isabelle/HOL; they are automatically expanded and thus lead to a discrepancy 
  between the internal and the external view of a term. However, we here deliberately deviate from this
  rule, since one aspect of the paper is to particularly illustrate exactly this discrepancy and to emphasize the complexity
  of the embedding MRTT in functional type theory.\footnote{We have also 
  experimented with using definitions instead of abbreviations; respective 
  encoding fragments can be requested from the first author.} 

  In fact, as we believe, the technical  complexity of the embedding presented below  pen and paper 
  work with it pragmatically infeasible. In this sense, we agree with previous 
  findings \cite{zalta11:_relat_versus_funct_found_logic}. 

  On the other hand, we illustrate the feasibility of maintaining and propagating 
  grammatical information in connection with a shallow
  embedding approach. Remember, that one central aim has been to suitably
  restrict the comprehension principles for the embedded MRTT despite the fact that underlying functional 
  type theory comes with full comprehension principles.  
 
  Our hope has been that the proposed approach can eventually be pragmatically handled to 
  at least some modest degree in a modern proof assistant such as Isabelle/HOL. In fact, as we will also
  illustrate, the simplifier @{text "simp"} of Isabelle is indeed well capable of effectively reducing
  the technically inflated terms we obtain from the extended embedding to its logical core content.  
  In other words, Isabelle's simplifier effectievely analyses and and rewrites the 
  deeply annotated terms and propagates the annotation information as intended to top-level.
  It thus seems feasable, to some degree, to seperate the rasoning about annotations from 
  the reasoning about logical content within our shallow embedding approach.
  *}

section {* Preliminaries *}
  text {* 
  We start out with some type declarations and type abbreviations. 
  Remember that our formalism explicitly encodes possible world semantics. Hence, we introduce a 
  distinguished type @{text "i"} to represent the set of possible worlds. 
  Consequently, terms of this type denote possible worlds. 
  Moreover, modal logic formulas are associated in our approach with
  predicates on (resp. sets of) on possible worlds. Hence, modal logic formulas have
  type @{text "(i \<Rightarrow> bool)"}. To make our representation  more concise in the remainder
  we abbreviate this type as @{text "io"}.
  *}

 typedecl i 
 type_synonym io = "(i\<Rightarrow>bool)" 

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
  eligible terms, such as constants and lambda abstractions). The embedding approach (of MFTT in functional type theory)
  is suitably adapted below so that 
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
  We anyway assume that all domains are non-empty. Hence, introducing these constant symbols is obviously not 
  harmful.\footnote{The single polymorphic dummy @{text "da::'a"}, utilized e.g. in the definition of the universal 
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
  @{text "P"} (propositional formula) from @{text "\<phi>"}. If the syntactical category of  @{text "\<phi>"} is 
  @{text "ERR"} (error) or @{text "T"} (term), then the syntactical category of @{text "\<^bold>\<A>\<phi>"} 
  is @{text "ERR"} and a dummy entity of appropriate type is returned. This illustrates the core 
  ideas of our explicit modeling of MRTT grammatical structure in functional type theory. 
  This scheme will repeated below for all the other language constructs of MRTT. 
  *}

 abbreviation Actual::"io opt \<Rightarrow> io opt" ("\<^bold>\<A> _" [64] 65) where "\<^bold>\<A>\<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w. \<psi> dw) | 
    P(\<psi>) \<Rightarrow> P(\<lambda>w. \<psi> dw) | 
    _ \<Rightarrow> ERR(dio)"

  text {* 
  The Theory of Abstract Objects distinguishes between encoding properties @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} and 
  exemplifying properties @{text "\<Pi>\<^sup>n,\<kappa>\<^sub>1,..,\<kappa>\<^sub>n"} (for $n\geq 1$). 

  Encoding @{text "\<kappa>\<Pi>"} is noted below as @{text "\<lbrace>\<kappa>,\<Pi>\<rbrace>"}.
  Encoding yields formulas and never propositional formulas. Below we
  map it to predicate application @{text "\<Pi>(\<kappa>)"} which we then guard by an uninterpreted 
  constant symbol @{text "enc"}, that is we map @{text "\<lbrace>\<kappa>,\<Pi>\<rbrace>"} to @{text "(enc \<Pi>(\<kappa>))"} (note that entire 
  expression denotes a predicate on possible worlds). This way we obtain only some limited amount of 
  lambda conversion principles for encoding from the underlying meta-logic. Additional axioms maybe required
  to obtain further required reasoning principles.
  Exemplification is be noted below as @{text "\<lparr>\<Pi>,x\<rparr>"} (respectively, @{text "\<lparr>\<Pi>,x,...\<rparr>"}).
  It is mapped to predicate application below, that is, to @{text "\<Pi>(\<kappa>)"}. 
  This way lambda conversion principles are inherited 
  from the underlying meta-logic (see Section~\ref{lambda-coversion} for some tests).
  We cannot map both, encoding and exemplification, to unguarded predicate application in the meta-logic, since this
  would conflate both notions and allow us to prove statements such as @{text "\<lbrace>\<kappa>,\<Pi>\<rbrace> \<^bold>\<rightarrow> \<lparr>\<Pi>,x\<rparr>"}.
  *}


 consts enc::"io\<Rightarrow>io" 

 abbreviation Enc::"e opt\<Rightarrow>(e\<Rightarrow>io) opt\<Rightarrow>io opt" ("\<lbrace>_,_\<rbrace>") where "\<lbrace>x,\<Phi>\<rbrace> \<equiv> case (x,\<Phi>) of 
    (T(y),T(Q)) \<Rightarrow> F((enc (Q y))) | 
    _ \<Rightarrow> ERR(dio)"

 text {* We add some exemplary axioms to support reasoning with encodings. Future work will
 be to study and add further principles. *}

 axiomatization where encAxiom1: "(enc x) \<equiv> enc (\<lambda>w. (enc x w))"
 axiomatization where encAxiom2: "(\<lambda>w. \<not>(enc x w)) \<equiv> enc (\<lambda>w. \<not>(x w))"

  text {* 
  Unary exemplifying formulas @{text "\<Pi>\<kappa>"} are noted as @{text "\<lparr>\<Pi>,\<kappa>\<rparr>"}.  
  Exemplification yields propositional formulas. 
  It is mapped to unguarded predicate application.
  *}

 (* consts exe::"io\<Rightarrow>io" *)
 abbreviation Exe1::"(e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_\<rparr>") where "\<lparr>\<Phi>,x\<rparr> \<equiv> case (\<Phi>,x) of 
    (T(Q),T(y)) \<Rightarrow> P((Q y)) | 
    _ \<Rightarrow> ERR(dio)"


  text {* 
 For pragmatical reasons we support n-ary exemplification formulas @{text "\<Pi>\<^sup>n,\<kappa>\<^sub>1,..,\<kappa>\<^sub>n"} here only for @{text "1\<le>n\<le>3"}.
 In addition to the unary case above, we thus introduce two further cases.
  *}  

 abbreviation Exe2::"(e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_,_\<rparr>")
  where "\<lparr>\<Phi>,x1,x2\<rparr> \<equiv> case (\<Phi>,x1,x2) of 
    (T(Q),T(y1),T(y2)) \<Rightarrow> P((Q y1 y2)) | 
    _ \<Rightarrow> ERR(dio)"
 abbreviation Exe3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt" ("\<lparr>_,_,_,_\<rparr>") 
  where "\<lparr>\<Phi>,x1,x2,x3\<rparr> \<equiv> case (\<Phi>,x1,x2,x3) of 
    (T(Q),T(y1),T(y2),T(y3)) \<Rightarrow> P((Q y1 y2 y3)) | 
    _ \<Rightarrow> ERR(dio)"

  text {* 
  Formations with negation and implication are supported for both, formulas and propositional
  formulas, and their embeddings are straightforward. In the case of implication, the compound formula
  is a propositional formula if both constituents are propositional formulas. If at least one constituent 
  is a formula and the other one eligible, then the compound formula is a formula. In all other
  cases an ERR-Formula is returned. 
  *}  

 abbreviation not::"io opt\<Rightarrow>io opt" ("\<^bold>\<not> _" [58] 59) where "\<^bold>\<not> \<phi> \<equiv> case \<phi> of 
    F(\<psi>) \<Rightarrow> F(\<lambda>w.\<not>(\<psi> w)) | 
    P(\<psi>) \<Rightarrow> P(\<lambda>w.\<not>(\<psi> w)) | 
    _ \<Rightarrow> ERR(dio)"  
 abbreviation implies::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>\<rightarrow>" 51) where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (P(\<alpha>),P(\<beta>)) \<Rightarrow> P(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | 
    (F(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | 
    (P(\<alpha>),F(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | 
    (F(\<alpha>),P(\<beta>)) \<Rightarrow> F(\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w) | 
    _ \<Rightarrow> ERR(dio)"  

  text {*
  Also universal quantification @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"} (first-order and higher-order) is supported 
  for both, formulas  and propositional formulas. Following previous work, the embedding maps 
  @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"} to @{text "(\<lambda>w.\<forall>x.\<phi>w)"}, where the latter @{text "\<forall>"} is the universal 
  quantifier from the HOL meta-logic. Note that @{text "\<^bold>\<forall>"} is introduced as logical connective
  based on the existing @{text "\<lambda>"}-binder. To improve the presentation and enable intuitive use 
  in the remainder we additionally
  introduce the binder notation @{text "\<^bold>\<forall>x.\<phi>"} as syntactic sugar for @{text "\<^bold>\<forall>(\<lambda>x.\<phi>)"}.
  *}

 abbreviation forall::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> case (\<Phi> da) of
    F(_) \<Rightarrow> F(\<lambda>w.\<forall>x. case (\<Phi> x) of F(\<psi>) \<Rightarrow> \<psi> w) | 
    P(_) \<Rightarrow> P(\<lambda>w.\<forall>x. case (\<Phi> x) of P(\<psi>) \<Rightarrow> \<psi> w) | 
    _ \<Rightarrow> ERR(dio)"
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
    F(\<psi>) \<Rightarrow> F(\<lambda>w.\<forall>v. \<psi> v) | 
    P(\<psi>) \<Rightarrow> P(\<lambda>w.\<forall>v. \<psi> v) | 
    _ \<Rightarrow> ERR(dio)"  

  text {* 
  n-ary lambda abstraction @{text "\<^bold>\<lambda>\<^sup>0,\<^bold>\<lambda>,\<^bold>\<lambda>\<^sup>2\<^sup>,\<^bold>\<lambda>\<^sup>3,..."}, for $n\geq 0$, is supported in the theory of abstract 
  objects only for propositional formulas. This way constructs such as 
  beforehand mentioned $(\lambda x \exists F. xF \wedge \neg Fx)$  (noted here as @{text "(\<^bold>\<lambda>x. \<^bold>\<exists>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>F\<^sup>T,x\<^sup>T\<rparr>)"} 
  are excluded. More precisely, they are identified as @{text "ERR"}-annotated 
  terms in our framework.
  The embedding of lambda abstraction is 
  straightforward: @{text "\<^bold>\<lambda>\<^sup>0"} is mapped to identity and @{text "\<^bold>\<lambda>,\<^bold>\<lambda>\<^sup>2,\<^bold>\<lambda>\<^sup>3,..."} are mapped to n-ary
  lambda abstractions, that is, @{text "\<^bold>\<lambda>(\<lambda>x.\<phi>)"} is mapped to @{text "(\<lambda>x.\<phi>)"} and @{text "\<^bold>\<lambda>\<^sup>2(\<lambda>xy.\<phi>)"} 
  to @{text "(\<lambda>xy.\<phi>)"}, etc.
  Similar to before, we support only the cases for $n\leq 3$. Binder notation is
  introduced for @{text "\<^bold>\<lambda>"}.\footnote{Unfortunately, we could not find out how binder notation
  could be analogously provided in Isabelle for @{text "\<^bold>\<lambda>\<^sup>2"} and @{text "\<^bold>\<lambda>\<^sup>3"}.}. 
  *}

 abbreviation lam0::"io opt\<Rightarrow>io opt" ("\<^bold>\<lambda>\<^sup>0") where "\<^bold>\<lambda>\<^sup>0\<phi> \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> P(\<psi>) | 
    _ \<Rightarrow> ERR dio"  
 abbreviation lam::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt" ("\<^bold>\<lambda>") where "\<^bold>\<lambda>\<Phi> \<equiv> case (\<Phi> de) of
    P(_) \<Rightarrow> T(\<lambda>x. case (\<Phi> x) of P(\<phi>) \<Rightarrow> \<phi>) | 
    _ \<Rightarrow> ERR(\<lambda>x. dio)"
 abbreviation lamBinder::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt" (binder "\<^bold>\<lambda>" [8] 9)  where "\<^bold>\<lambda>x. \<phi> x \<equiv> \<^bold>\<lambda> \<phi>"
 abbreviation lam2::"(e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>io) opt" ("\<^bold>\<lambda>\<^sup>2") where "\<^bold>\<lambda>\<^sup>2\<Phi> \<equiv> case (\<Phi> de de) of
    P(_) \<Rightarrow> T(\<lambda>x y. case (\<Phi> x y) of P(\<phi>) \<Rightarrow> \<phi>) | 
    _ \<Rightarrow> ERR(\<lambda>x y. dio)"
 abbreviation lam3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt" ("\<^bold>\<lambda>\<^sup>3") where "\<^bold>\<lambda>\<^sup>3\<Phi> \<equiv> case (\<Phi> de de de) of
    P(_) \<Rightarrow> T(\<lambda>x y z. case (\<Phi> x y z) of P(\<phi>) \<Rightarrow> \<phi>) | 
    _ \<Rightarrow> ERR(\<lambda>x y z. dio)"

  text {* 
  The theory of abstract objects supports rigid definite descriptions. Our definition maps
  @{text "\<^bold>\<iota>(\<lambda>x.\<phi>)"} to @{text "(THE x. \<phi> dw)"}, that is, Isabelle's inbuilt definite description operator 
  @{text "THE"} 
  is utilized and evaluation is rigidly carried out with respect to the current world denoted by @{text "dw"}.
  We again introduce binder notation for @{text "\<^bold>\<iota>"}.
  *}
 
 abbreviation that::"(e\<Rightarrow>io opt)\<Rightarrow>e opt" ("\<^bold>\<iota>")  where "\<^bold>\<iota>\<Phi> \<equiv> case (\<Phi> de) of
    F(_) \<Rightarrow> T(THE x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> dw) | 
    P(_) \<Rightarrow> T(THE x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> dw) | 
    _ \<Rightarrow> ERR(de)"
 abbreviation thatBinder::"(e\<Rightarrow>io opt)\<Rightarrow>e opt" (binder "\<^bold>\<iota>" [8] 9)  where "\<^bold>\<iota>x. \<phi> x \<equiv> \<^bold>\<iota> \<phi>"


section {* Further Logical Connectives *}
  text {* 
  Further logical connectives can be defined as usual. For pragmatic reasons (e.g. to avoid further blow-up of
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
    F(\<psi>) \<Rightarrow> F(\<lambda>w.\<exists>v. \<psi> v) | 
    P(\<psi>) \<Rightarrow> P(\<lambda>w.\<exists>v. \<psi> v) | 
    _ \<Rightarrow> ERR(dio)"

 abbreviation exists::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> case (\<Phi> da) of
    P(_) \<Rightarrow> P(\<lambda>w.\<exists>x. case (\<Phi> x) of P \<psi> \<Rightarrow> \<psi> w) | 
    F(_) \<Rightarrow> F(\<lambda>w. \<exists>x. case (\<Phi> x) of F \<psi> \<Rightarrow> \<psi> w) | 
    _ \<Rightarrow> ERR dio" 
 abbreviation existsBinder::"('a\<Rightarrow>io opt)\<Rightarrow>io opt" (binder "\<^bold>\<exists>" [8] 9)  where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"

section {* E!, O!, A! and =E *}

  text {* 
  We introduce some important further notions of the theory of abstract objects \cite{zalta83:_abstr_objec}. We 
  start out with the distinguished 1-place relation constant @{text "E!"} (read ‘being concrete’ or ‘concreteness’). 
  *}

 consts Exists::"(e\<Rightarrow>io)" ("E!")
 
  text {* 
  Next, being ordinary is defined as being possibly concrete. 
  *}

 abbreviation ordinaryObject::"(e\<Rightarrow>io) opt" ("O!") where "O! \<equiv> \<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!\<^sup>T,x\<^sup>T\<rparr>"

  text {* 
  Being abstract is then defined as not possibly being concrete. 
  *}

 abbreviation abstractObject::"(e\<Rightarrow>io) opt" ("A!") where "A! \<equiv> \<^bold>\<lambda>x. \<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!\<^sup>T,x\<^sup>T\<rparr>)"

  text {* 
  Finally, we introduce the identity relations @{text "\<^bold>=\<^sub>E"} and @{text "\<^bold>="} on individuals. 
  *}

 abbreviation identityE::"e opt\<Rightarrow>e opt\<Rightarrow>io opt" (infixl "\<^bold>=\<^sub>E" 63) where "x \<^bold>=\<^sub>E y \<equiv> 
    \<lparr>O!,x\<rparr> \<^bold>\<and> \<lparr>O!,y\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F\<^sup>T,x\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>T,y\<rparr>)"

 abbreviation identityI::"e opt\<Rightarrow>e opt\<Rightarrow>io opt" (infixl "\<^bold>=" 63) where "x \<^bold>= y \<equiv> 
    x \<^bold>=\<^sub>E y \<^bold>\<or> (\<lparr>A!,x\<rparr> \<^bold>\<and> \<lparr>A!,y\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<^sup>T\<rbrace>))"


 text {* Moreover, we introduce the following identity relations on n-ary relations (for $n=0,1,2,3$). *}

 abbreviation identityRel1::" ((e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>1" 63) 
   where "F1 \<^bold>=\<^sup>1 G1 \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,F1\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>T,G1\<rbrace>)"

 abbreviation identityRel2::" ((e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>2" 63) 
   where "F2 \<^bold>=\<^sup>2 G2 \<equiv> \<^bold>\<forall>x1.(  (\<^bold>\<lambda>y.\<lparr>F2,y\<^sup>T,x1\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G2,y\<^sup>T,x1\<^sup>T\<rparr>)
                          \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F2,x1\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G2,x1\<^sup>T,y\<^sup>T\<rparr>))"

 abbreviation identityRel3::" ((e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>3" 63) 
   where "F3 \<^bold>=\<^sup>3 G3 \<equiv> \<^bold>\<forall>x1 x2.(  (\<^bold>\<lambda>y.\<lparr>F3,y\<^sup>T,x1\<^sup>T,x2\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,y\<^sup>T,x1\<^sup>T,x2\<^sup>T\<rparr>)
                             \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F3,x1\<^sup>T,y\<^sup>T,x2\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,x1\<^sup>T,y\<^sup>T,x2\<^sup>T\<rparr>)
                             \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F3,x1\<^sup>T,x2\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,x1\<^sup>T,x2\<^sup>T,y\<^sup>T\<rparr>))"

 abbreviation equalityRel0::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>0" 63) 
   where "F0 \<^bold>=\<^sup>0 G0 \<equiv> (\<^bold>\<lambda>y . F0) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y. G0)"


section {* Three-Valued Meta-Logic*}

  text {* 
  Our approach to rigorously distinguish between proper and improper language constructions 
  and to explicitly maintain respective information is continued also at meta-level. For this 
  we introduce three truth values @{text "tt"},
  @{text "ff"} and @{text "err"}, representing truth, falsity and error. These values are also 
  noted as @{text "\<top>"}, @{text "\<bottom>"} and @{text "*"}. We could, of course, also introduce  
  respective logical connectives for the meta-level, but in our applications (see below)
  this was not yet required.
  *}

 datatype mf = tt ("\<top>") | ff ("\<bottom>") | err ("*")

  text {* 
  Next we define the meta-logical notions of validity, satisfiability, 
  countersatisfiability and invalidity for our embedded modal relational type theory. Moreover, 
  we introduce the following notations: @{text "[\<phi>]"} 
  (for @{text "\<phi>"} is valid), @{text "[\<phi>]\<^sup>s\<^sup>a\<^sup>t "} (@{text "\<phi>"} is satisfiability), @{text "[\<phi>]\<^sup>c\<^sup>s\<^sup>a\<^sup>t"} 
  (@{text "\<phi>"} is countersatisfiability) and @{text "[\<phi>]\<^sup>i\<^sup>n\<^sup>v"} (@{text "\<phi>"} is invalid). Actually, so far 
  we only use validity.
  *}

 (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
 (*<*) no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
 abbreviation valid :: "io opt\<Rightarrow>mf" ("[_]" [1]) where "[\<phi>] \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<forall>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    F(\<psi>) \<Rightarrow> if \<forall>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    _ \<Rightarrow> *"
 abbreviation satisfiable :: "io opt\<Rightarrow>mf" ("[_]\<^sup>s\<^sup>a\<^sup>t" [1]) where "[\<phi>]\<^sup>s\<^sup>a\<^sup>t \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<exists>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    F(\<psi>) \<Rightarrow> if \<exists>w.(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    _ \<Rightarrow> *"
 abbreviation countersatisfiable :: "io opt\<Rightarrow>mf" ("[_]\<^sup>c\<^sup>s\<^sup>a\<^sup>t" [1]) where "[\<phi>]\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<exists>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    F(\<psi>) \<Rightarrow> if \<exists>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    _ \<Rightarrow> *"
 abbreviation invalid :: "io opt\<Rightarrow>mf" ("[_]\<^sup>i\<^sup>n\<^sup>v" [1]) where "[\<phi>]\<^sup>i\<^sup>n\<^sup>v \<equiv> case \<phi> of 
    P(\<psi>) \<Rightarrow> if \<forall>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    F(\<psi>) \<Rightarrow> if \<forall>w.\<not>(\<psi> w) \<longleftrightarrow> True then \<top> else \<bottom> | 
    _ \<Rightarrow> *"



section {* Some Tests and First Applications*}

 subsection {* Exemplification and Encoding \label{basic-tests-1} *} 

 text {* 
  For the following non-theorems we indeed get countermodels by nitpick.
  *}

 lemma "[(\<^bold>\<forall>R.\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" 
   apply simp nitpick [user_axioms, expect = genuine]  oops -- {* Countermodel by Nitpick *}
 lemma "[(\<^bold>\<forall>R.\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" 
   apply simp nitpick [user_axioms, expect = genuine]  oops -- {* Countermodel by Nitpick *}

  text {* With the latter example we also want to illustrate the inflation of representations as caused by our
     embedding. For this note, that the statement @{text "[(\<^bold>\<forall>R.\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>"} abbreviates the
    actual internal term  
   @{text "(case case case \<lbrace>da\<^sup>T,da\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>da\<^sup>T,da\<^sup>T\<rparr> of P x \<Rightarrow> (\<lambda>w. \<forall>x. case \<lbrace>x\<^sup>T,da\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>da\<^sup>T,x\<^sup>T\<rparr> of P \<psi> \<Rightarrow> \<psi> w)\<^sup>P
               | F x \<Rightarrow> (\<lambda>w. \<forall>x. case \<lbrace>x\<^sup>T,da\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>da\<^sup>T,x\<^sup>T\<rparr> of F \<psi> \<Rightarrow> \<psi> w)\<^sup>F | _ \<Rightarrow> dio\<^sup>E of
          P x \<Rightarrow> (\<lambda>w. \<forall>x. case case \<lbrace>da\<^sup>T,x\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>x\<^sup>T,da\<^sup>T\<rparr> of P xa \<Rightarrow> (\<lambda>w. \<forall>xa. case \<lbrace>xa\<^sup>T,x\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>x\<^sup>T,xa\<^sup>T\<rparr> of P \<psi> \<Rightarrow> \<psi> w)\<^sup>P
                               | F xa \<Rightarrow> (\<lambda>w. \<forall>xa. case \<lbrace>xa\<^sup>T,x\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>x\<^sup>T,xa\<^sup>T\<rparr> of F \<psi> \<Rightarrow> \<psi> w)\<^sup>F | _ \<Rightarrow> dio\<^sup>E of
                          P \<psi> \<Rightarrow> \<psi> w)\<^sup>P
          | F x \<Rightarrow> (\<lambda>w. \<forall>x. case case \<lbrace>da\<^sup>T,x\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>x\<^sup>T,da\<^sup>T\<rparr> of P xa \<Rightarrow> (\<lambda>w. \<forall>xa. case \<lbrace>xa\<^sup>T,x\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>x\<^sup>T,xa\<^sup>T\<rparr> of P \<psi> \<Rightarrow> \<psi> w)\<^sup>P
                                 | F xa \<Rightarrow> (\<lambda>w. \<forall>xa. case \<lbrace>xa\<^sup>T,x\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>x\<^sup>T,xa\<^sup>T\<rparr> of F \<psi> \<Rightarrow> \<psi> w)\<^sup>F | _ \<Rightarrow> dio\<^sup>E of
                            F \<psi> \<Rightarrow> \<psi> w)\<^sup>F
          | _ \<Rightarrow> dio\<^sup>E of
     P \<psi> \<Rightarrow> if \<forall>w. \<psi> w = True then \<top> else \<bottom> | F \<psi> \<Rightarrow> if \<forall>w. \<psi> w = True then \<top> else \<bottom> | _ \<Rightarrow> *) =
    \<top>"}.
  In Isabelle the inflated term is displayed in the output window when placing the mouse on the abbreviated representation.
  However, the simplifier is capable of evaluating the annotations and thereby reducing this inflated term again 
  to @{text " \<forall>w x xa. enc (x xa) w \<longrightarrow> x xa w"} as intended; one can easily see this when placing the mouse on "simp". 
  Below we will see that the inflated representations can 
  easily fill several pages for abbreviated formulas which are only slightly longer than our exemple formula here. 
  This illustrates the pragmatic infeasibility of the approach when using pen and paper only. *}

  text {* 
  The next two statements are theorems and the simplifier quickly proves this.
  *}

 lemma "[(\<^bold>\<forall>R.\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" by simp 
 lemma "[(\<^bold>\<forall>R.\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" by simp


 subsection {* Verifying K Principle and Necessitation *}

  text {* The next two lemmata show the K principle  and neccessitation holds for arbitrary formulas 
  and arbitrary propositional formulas. We present the lemmata in both variants. 
  *}

 lemma "[(\<^bold>\<box>(\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F)] = \<top>" apply simp done    --{* K Schema *}

 lemma "[\<phi>\<^sup>F] = \<top> \<longrightarrow> [\<^bold>\<box>\<phi>\<^sup>F] = \<top> " apply simp done    --{* Neccessitation *}
 
 text {* However, as intended, contingent truth does not allow for neccessitation. *}

 lemma "[\<A>\<phi>\<^sup>F] = \<top> \<longrightarrow> [\<^bold>\<box>\<phi>\<^sup>F] = \<top> " apply simp nitpick [user_axioms, expect = genuine] oops  --{* Countermodel *}
 lemma "[\<phi>\<^sup>F]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longrightarrow> [\<^bold>\<box>\<phi>\<^sup>F] = \<top> " apply simp nitpick [user_axioms, expect = genuine] oops  --{* Countermodel *}

 subsection {* Modal Collapse is Countersatisfiable *}

  text {* 
  The modelfinder Nitpick constructs a finite countermodel to the assertion
  that modal collaps holds. 
  *}

 lemma "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp nitpick [user_axioms, expect = genuine] oops --{* Countermodel by Nitpick *}

 subsection {* Verifying S5 Principles \label{sec:S5} *} 

  text {* 
  The @{text "\<box>"}-operator could have alternatively been modeled by employing an equivalence relation @{text "r"} in a 
  guarding clause. This has been done in previous work. Our alternative, simpler definition of 
  @{text "\<box>"} above omits
  this clause (since all worlds are reachable from any world in an equivalence relation). The 
  following lemmata, which check various conditions for S5, confirm that we have indeed 
  obtain a correct modeling of S5.
  *}

 lemma "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F] = \<top>" apply simp done
 lemma "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done
 lemma "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp by auto
 lemma "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp done
 lemma "[\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done
 lemma "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done            --{* 5 Schema *}
 lemma "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp by auto
 lemma "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp nitpick  [user_axioms, expect = genuine] oops   --{* Countermodel by Nitpick *}
 lemma "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp done

 subsection {* Instances of the Barcan and Converse Formulas *}

 lemma "[(\<^bold>\<forall>x.\<^bold>\<box>\<lbrace>x\<^sup>T,\<phi>\<^sup>T\<rbrace>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.\<lbrace>x\<^sup>T,\<phi>\<^sup>T\<rbrace>)] = \<top>" apply simp done         (* BF *)
 lemma "[(\<^bold>\<forall>x.\<^bold>\<box>\<lparr>\<phi>\<^sup>T,x\<^sup>T\<rparr>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.\<lparr>\<phi>\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp done         (* BF *)

 lemma "[(\<^bold>\<forall>x.\<^bold>\<box>(\<^bold>\<forall>x.\<lbrace>x\<^sup>T,\<phi>\<^sup>T\<rbrace>) \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x\<^sup>T,\<phi>\<^sup>T\<rbrace>)] = \<top>" apply simp by auto         (* BF *)
 lemma "[\<^bold>\<box>(\<^bold>\<forall>x.\<lparr>\<phi>\<^sup>T,x\<^sup>T\<rparr>) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>\<lparr>\<phi>\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp by auto         (* BF *)

 subsection {* Relations between  Meta-Logical Notions *}
 text {* We check some well know relations between meta-logical notions. *}

 lemma  "[\<phi>\<^sup>P] = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>P]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>F] = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>F]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done

  text {* However, for terms we have: *}

 lemma  "[\<phi>\<^sup>T] = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>i\<^sup>n\<^sup>v = *" apply simp done

 subsection {* Propagation of Grammatical Information *}

  text {*   
 The expression @{text "(\<^bold>\<lambda>x. \<^bold>\<exists>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>F\<^sup>T,x\<^sup>T\<rparr>)"} is an ineligible 
 construct, cf.~\cite[chap.4]{zalta11:_relat_versus_funct_found_logic}. 
 When placing the
 mouse on 'simp' we see that this is evaluated to @{text "(\<lambda>x. dio)\<^sup>E"} as intended, i.e. an ERR-term
 is returned.  
 *}

 lemma "(\<^bold>\<lambda>x. \<^bold>\<exists>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>F\<^sup>T,x\<^sup>T\<rparr>) = X" apply simp oops  -- {* X is @{text "(\<lambda>x. dio)\<^sup>E"} *}

 text {*   
  Similarly, the following comprehension principle for abstract objects is an ineligible formula,  
  cf.~\cite[chap.4]{zalta11:_relat_versus_funct_found_logic}. The simplifier quickly proves that this
  formula @{text "(\<^bold>\<exists>x.(\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> (F\<^sup>T \<^bold>=\<^sup>1 K)))))"} is equal to @{text "*"}. That is, 
  the evaluation of this formula returns the @{text "err"} truth value for error.
 *}

abbreviation K where "K \<equiv> (\<^bold>\<lambda>x.\<^bold>\<exists>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>F\<^sup>T,x\<^sup>T\<rparr>)"

 lemma "[(\<^bold>\<exists>x.(\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F.(\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> (F\<^sup>T \<^bold>=\<^sup>1 K)))))] = *" apply simp done


text {*
 We also use the latter formula to further illustrate the technical overhead of our embedding. 
 For this see Figure~\ref{large}, which displays approx. 5\% of the unfolded representation of our 
 formula. It should thus be obvious that pen and paper work with the embedding as proposed here 
 is completely infeasible. 
   \begin{figure}[t] \centering
  \includegraphics[width=.9\textwidth]{LargeTerm.png}
  \caption{Display (of about 5\%) of the unfolded 
  expression @{text "[(\<^bold>\<exists>x.(\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> (F\<^sup>T \<^bold>=\<^sup>1 K)))))] = *"} 
 in Isabelle/HOL. \label{large}} 
  \end{figure}
*}

section {* Some Further Tests *}

text {* In this section we present some further test examples of our encoding. Many of these tests are taken
 from papers (e.g. cf.~\cite{zalta11:_relat_versus_funct_found_logic} or presentation slides of Zalta. *}

text {* We show that the derivation from @{text "(\<lbrace>a\<^sup>T,PP\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>PP\<^sup>T,a\<^sup>T\<rparr>)"} 
to @{text "(\<^bold>\<exists>F.\<lbrace>a\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>F\<^sup>T,a\<^sup>T\<rparr>)"} can in fact be 
represented and solved in our approach, 
cf. ~\cite[chap.4]{zalta11:_relat_versus_funct_found_logic} *}

 lemma "[(\<lbrace>a\<^sup>T,PP\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>PP\<^sup>T,a\<^sup>T\<rparr>)] = \<top> \<longrightarrow> [(\<^bold>\<exists>F.\<lbrace>a\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<and> \<^bold>\<not>\<lparr>F\<^sup>T,a\<^sup>T\<rparr>)] = \<top>" apply simp by auto


 subsection {* Properties of Equality *}

 lemma "[(\<^bold>\<forall>x y. (x\<^sup>T \<^bold>= x\<^sup>T))] = \<top>" apply simp by blast
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>= y\<^sup>T \<^bold>\<rightarrow> y\<^sup>T \<^bold>= x\<^sup>T)] = \<top>" apply simp by meson
 lemma "[(\<^bold>\<forall>x y z. (x\<^sup>T \<^bold>= y\<^sup>T \<^bold>\<and> y\<^sup>T \<^bold>= z\<^sup>T) \<^bold>\<rightarrow> x\<^sup>T \<^bold>= z\<^sup>T)] = \<top>" apply simp  by meson 
 lemma "[(\<^bold>\<forall>x y. (x\<^sup>T \<^bold>= y\<^sup>T \<^bold>\<rightarrow> \<^bold>\<box>(x\<^sup>T \<^bold>= y\<^sup>T)))] = \<top>" apply simp done

 lemma "[(\<^bold>\<forall>x. \<lparr>O!,x\<^sup>T\<rparr> \<^bold>\<rightarrow> x\<^sup>T \<^bold>=\<^sub>E x\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sub>E y\<^sup>T \<^bold>\<rightarrow> y\<^sup>T \<^bold>=\<^sub>E x\<^sup>T)] = \<top>" apply simp by meson
 lemma "[(\<^bold>\<forall>x y z. (x\<^sup>T \<^bold>=\<^sub>E y\<^sup>T \<^bold>\<and> y\<^sup>T \<^bold>=\<^sub>E z\<^sup>T) \<^bold>\<rightarrow> x\<^sup>T \<^bold>=\<^sub>E z\<^sup>T)] = \<top>" apply simp by meson
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sub>E y\<^sup>T \<^bold>\<rightarrow> \<^bold>\<box>(x\<^sup>T \<^bold>=\<^sub>E y\<^sup>T))] = \<top>" apply simp done 

 lemma "[(\<^bold>\<forall>x. x\<^sup>P \<^bold>=\<^sup>0 x\<^sup>P)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>P \<^bold>=\<^sup>0 y\<^sup>P \<^bold>\<rightarrow> y\<^sup>P \<^bold>=\<^sup>0 x\<^sup>P)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y z. (x\<^sup>P \<^bold>=\<^sup>0 y\<^sup>P \<^bold>\<and> y\<^sup>P \<^bold>=\<^sup>0 z\<^sup>P) \<^bold>\<rightarrow> x\<^sup>P \<^bold>=\<^sup>0 z\<^sup>P)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>P \<^bold>=\<^sup>0 y\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>(x\<^sup>P \<^bold>=\<^sup>0 y\<^sup>P))] = \<top>" apply simp done 

 lemma "[(\<^bold>\<forall>x. x\<^sup>T \<^bold>=\<^sup>1 x\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sup>1 y\<^sup>T \<^bold>\<rightarrow> y\<^sup>T \<^bold>=\<^sup>1 x\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y z. (x\<^sup>T \<^bold>=\<^sup>1 y\<^sup>T \<^bold>\<and> y\<^sup>T \<^bold>=\<^sup>1 z\<^sup>T) \<^bold>\<rightarrow> x\<^sup>T \<^bold>=\<^sup>1 z\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sup>1 y\<^sup>T \<^bold>\<rightarrow> \<^bold>\<box>(x\<^sup>T \<^bold>=\<^sup>1 y\<^sup>T))] = \<top>" apply simp done 

 lemma "[(\<^bold>\<forall>x. x\<^sup>T \<^bold>=\<^sup>2 x\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sup>2 y\<^sup>T \<^bold>\<rightarrow> y\<^sup>T \<^bold>=\<^sup>2 x\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y z. (x\<^sup>T \<^bold>=\<^sup>2 y\<^sup>T \<^bold>\<and> y\<^sup>T \<^bold>=\<^sup>2 z\<^sup>T) \<^bold>\<rightarrow> x\<^sup>T \<^bold>=\<^sup>2 z\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sup>2 y\<^sup>T \<^bold>\<rightarrow> \<^bold>\<box>(x\<^sup>T \<^bold>=\<^sup>2 y\<^sup>T))] = \<top>" apply simp done 

 lemma "[(\<^bold>\<forall>x. x\<^sup>T \<^bold>=\<^sup>3 x\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sup>3 y\<^sup>T \<^bold>\<rightarrow> y\<^sup>T \<^bold>=\<^sup>3 x\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y z. (x\<^sup>T \<^bold>=\<^sup>3 y\<^sup>T \<^bold>\<and> y\<^sup>T \<^bold>=\<^sup>3 z\<^sup>T) \<^bold>\<rightarrow> x\<^sup>T \<^bold>=\<^sup>3 z\<^sup>T)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sup>3 y\<^sup>T \<^bold>\<rightarrow> \<^bold>\<box>(x\<^sup>T \<^bold>=\<^sup>3 y\<^sup>T))] = \<top>" apply simp done 


 subsection {* Technological Problem --- Pushing Isabelle to its Limits *} 

  text {* While @{text "[(\<^bold>\<forall>x y z. (x\<^sup>T \<^bold>=\<^sup>3 y\<^sup>T \<^bold>\<and> y\<^sup>T \<^bold>=\<^sup>3 z\<^sup>T) \<^bold>\<rightarrow> x\<^sup>T \<^bold>=\<^sup>3 z\<^sup>T)] = \<top>"} can still be verified by simp, 
  its unfolded internal representation cannot be displayed anymore in Isabelle/HOL's jedit based
  user interface on a
  standard Macbook. Isabelle in fact reports the following: 
     ``No subgoals! exception Size raised (line 182 of "./basis/LibrarySupport.sml")''
   Displaying the internal unfolded representation still worked 
  for @{text "[(\<^bold>\<forall>x y. x\<^sup>T \<^bold>=\<^sup>3 y\<^sup>T \<^bold>\<rightarrow> y\<^sup>T \<^bold>=\<^sup>3 x\<^sup>T)] = \<top>"} though. The resulting term is presented in the appendix 
  of this paper (on about 240 pages in scriptsize font). 
  *}


 subsection{* Axioms and Tests for Actuality *}

 text {* One issue that we did not address yet is how one can possibly encode 
 axiom schemata like @{text "\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<phi>"} where @{text "\<^bold>\<phi>"} ranges only 
 over @{text "\<^bold>\<box>"}-free closures. Eventually the grammar should be further refined so that we get a 
 category of @{text "\<^bold>\<box>"}-free formulas? *}

 lemma "[\<^bold>\<A>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<A>\<phi>\<^sup>P)] = \<top>" apply simp done
 lemma "[\<^bold>\<A>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<A>\<phi>\<^sup>F)] = \<top>" apply simp done


 subsection {* Some Tests on Lambda-Conversion \label{lambda-conversion} *}

 text {* Alpha-conversion holds for exemplification. *}

 lemma "[(\<^bold>\<lambda>y. \<^bold>\<not>\<lparr>Q\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>z. \<^bold>\<not>\<lparr>Q\<^sup>T,z\<^sup>T\<rparr>)] = \<top>" apply simp done
 lemma "[\<lbrace>x\<^sup>T,(\<^bold>\<lambda>y. \<^bold>\<not>\<lparr>Q\<^sup>T,y\<^sup>T\<rparr>)\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,(\<^bold>\<lambda>z. \<^bold>\<not>\<lparr>Q\<^sup>T,z\<^sup>T\<rparr>)\<rbrace>] = \<top>" apply simp done
 
 text {* Eta-conversion holds for exemplification. *}

 lemma "[(\<^bold>\<lambda>y. \<lparr>Q\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 Q\<^sup>T] = \<top>" apply simp done

 text {* Eta-conversion can be applied to lambda-predicates in encoding formulas. *}

 lemma "[\<lbrace>x\<^sup>T,(\<^bold>\<lambda>y. \<lparr>Q\<^sup>T,y\<^sup>T\<rparr>)\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,Q\<^sup>T\<rbrace>] = \<top>" apply simp done   
 lemma "[\<lbrace>x\<^sup>T,Q\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,(\<^bold>\<lambda>y. \<lparr>Q\<^sup>T,y\<^sup>T\<rparr>)\<rbrace>] = \<top>" apply simp done

 text {* Some tests related to beta-conversion. *}

 lemma "[(\<^bold>\<forall>z. \<lparr>(\<^bold>\<lambda>y. (\<lparr>Q\<^sup>T,y\<^sup>T\<rparr> \<^bold>\<and> (p\<^sup>P \<^bold>\<or> \<^bold>\<not>p\<^sup>P))),z\<^sup>T\<rparr> \<^bold>\<equiv> \<lparr>(\<^bold>\<lambda>y. (\<lparr>Q\<^sup>T,y\<^sup>T\<rparr> \<^bold>\<and> (q\<^sup>P \<^bold>\<or> \<^bold>\<not>q\<^sup>P))),z\<^sup>T\<rparr>)] = \<top>" apply simp done
 lemma "[(\<^bold>\<lambda>y. (\<lparr>Q\<^sup>T,y\<^sup>T\<rparr> \<^bold>\<and> (q\<^sup>P \<^bold>\<or> \<^bold>\<not>q\<^sup>P))) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y. (\<lparr>Q\<^sup>T,y\<^sup>T\<rparr> \<^bold>\<and> (p\<^sup>P \<^bold>\<or> \<^bold>\<not>p\<^sup>P)))] = \<top>" apply simp done
 lemma "[\<lbrace>x\<^sup>T,(\<^bold>\<lambda>y. (\<lparr>Q\<^sup>T,y\<^sup>T\<rparr> \<^bold>\<and> (q\<^sup>P \<^bold>\<or> \<^bold>\<not>q\<^sup>P)))\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,(\<^bold>\<lambda>y. (\<lparr>Q\<^sup>T,y\<^sup>T\<rparr> \<^bold>\<and> (p\<^sup>P \<^bold>\<or> \<^bold>\<not>p\<^sup>P)))\<rbrace>] = \<top>" apply simp done
 
 
 subsection{* Theory of Encoding *}

 text {* We present a small case study in the theory of encoding. For this we first
 postulate some axioms and provide some further definitions/abbreviations.*}
 
 axiomatization where
  RigityOfEncoding:  "[\<lbrace>x\<^sup>T,FF\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x\<^sup>T,FF\<^sup>T\<rbrace>] = \<top>" and
  OrdinaryObjectsDoNotEncode: "[\<lparr>O!,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace>))] = \<top>" and
  ObjectComprehension: "[(\<^bold>\<exists>x. \<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<phi>))] = \<top>"

 abbreviation Situation::"e opt\<Rightarrow>io opt"  where 
   "Situation x \<equiv> (\<lparr>A!,x\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x,F\<^sup>T\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists>p. F\<^sup>T \<^bold>=\<^sup>1 (\<^bold>\<lambda>y. p\<^sup>P)))))"
 abbreviation PIsTrueInX::"e opt \<Rightarrow> (i \<Rightarrow> bool) opt \<Rightarrow> (i \<Rightarrow> bool) opt" (infixl "\<Turnstile>" 63) where 
   "x \<Turnstile> p \<equiv> \<lbrace>x,(\<^bold>\<lambda>y. p)\<rbrace>"  
 abbreviation PossibleWorld::"e opt\<Rightarrow>io opt" where 
   "PossibleWorld x \<equiv> Situation(x) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<forall>p. (x \<Turnstile> p\<^sup>P) \<^bold>\<equiv> p\<^sup>P)" 
 abbreviation Maximal::"e opt\<Rightarrow>io opt" where 
   "Maximal s \<equiv> (\<^bold>\<forall>p. (s \<Turnstile> p\<^sup>P) \<^bold>\<or> (s \<Turnstile> (\<^bold>\<not> p\<^sup>P)))" 

 text {* We are now in the position to formalize and prove the fundamental theorem of possible worlds,
  which states that possible worlds are maximal. *}

 lemma "[(\<^bold>\<forall>x. PossibleWorld(x\<^sup>T) \<^bold>\<rightarrow> Maximal(x\<^sup>T))] = \<top>" apply simp using encAxiom2 by auto 


 subsection {* Consistency? *}

 text {* Unfortunately, neither Nitpick nor the available
  ATPs are capable of verifying or disproving the consistency of the introduced theory. *} 

 lemma True nitpick [satisfy, user_axioms] oops 
 lemma False sledgehammer [remote_leo2 remote_satallax] oops
 lemma False sledgehammer oops


section {* Conclusion *}
text {*
  We have experimented with an new idea towards a shallow embedding of MRTT in 
  functional type theory 
  and we have pushed the technical 
  elaboration of that idea to some interesting intermediate state.   
  While our embedding is clearly infeasible for pen and paper methods, 
  our original hope has been that -- modulo our embedding -- interactive and automated theorem provers for 
  functional type theory could, at least to a reasonable extend, be (re-)used for reasoning within
  MRTT and subsequently for reasoning in the theory of abstract objects. 


  However, within the system infrastructure of Isabelle/HOL we seem to reach some technological limits (e.g. the 
internal formula representing the transitivity of equality between ternary relations cannot be displayed anymore 
 because of its size and consistency can neither be proved nor disproved anymore, etc.).
 On the other hand, we were still able automatically confirm the 
 fundamental theorem of possible worlds, and in this respect the degree of automation provided in our
 experiments is reaching an interesting level; cf. the experiments in related work where 
 a significant amount of handselected instantiations of schemata was needed (e.g. for comprehension and lambda
 conversion) \cite{FitelsonZ07,Zalta15}.

 Independent of the outcome of the further research based upon the presented embedding it should 
 become clear that building a system similar to Isabelle but with taking MRTT as its foundational 
 core logic (instead of functional type theory) would surely provide
 a technologically more appropriate base environment for the formalization and automation of the 
 theory of abstract objects and the principia metaphysica.
*}



(*<*)
end 
(*>*)

(*
 section{* Some Tests with Comprehension *}

 lemma "[(\<^bold>\<exists>x.(\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lparr>F\<^sup>T,x\<^sup>T\<rparr>))))] = \<top>" apply simp oops


 section{* Some Further Tests (Largely Uncommented) *}


 lemma "[(\<^bold>\<forall>x.\<lbrace>x\<^sup>T,PP\<^sup>T\<rbrace>)] = \<top> \<longrightarrow> [(\<lbrace>a\<^sup>T,PP\<^sup>T\<rbrace>)] = \<top>" apply simp  done
*)



 
