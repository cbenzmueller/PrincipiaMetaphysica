(*<*) 
theory TheoryOfAbstractObjectsV1
imports Main

begin
(*>*)

section {* Introduction *}
text {* This work is related to \cite{J23}, which is significantly extends ... *}

section {* Preliminaries *}
typedecl i
-- "the type possible worlds; the formalism explicitly encodes Kripke style semantics"
type_synonym io = "(i \<Rightarrow> bool)" 
-- "formulas are essentially of this type"
-- "predicates on worlds"
typedecl e
-- "the raw type of entities/objects (abstract or ordinary)"
datatype 'a opt = Error 'a | Term 'a | Form 'a | PropForm 'a


consts cw :: i 
-- "the distinguished actual world"
consts dE::"e" dIO::"io" dEIO::"e\<Rightarrow>io" dEEIO::"e\<Rightarrow>e\<Rightarrow>io" dEEEIO::"e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io" dA::'a
-- "some fixed dummy symbols; we anyway assume that the domains are non-empty"
-- "needed as dummy object in some cases below"

(* 'a indicates polymorphism *)


text {* Meta-logical predicates. *}
abbreviation isWff :: "io opt\<Rightarrow>bool" where "isWff \<phi> \<equiv> case \<phi> of Error \<psi> \<Rightarrow> False | Term \<psi> \<Rightarrow> False |_ \<Rightarrow> True"
abbreviation isForm :: "io opt\<Rightarrow>bool" where "isForm \<phi> \<equiv> case \<phi> of Form \<psi> \<Rightarrow> True | _ \<Rightarrow> False"
abbreviation isPropForm :: "io opt\<Rightarrow>bool" where "isPropForm \<phi> \<equiv> case \<phi> of PropForm \<psi> \<Rightarrow> True | _ \<Rightarrow> False"
abbreviation isTerm :: "io opt\<Rightarrow>bool" where "isTerm \<phi> \<equiv> case \<phi> of Term \<psi> \<Rightarrow> True | _ \<Rightarrow> False"
abbreviation isError :: "io opt\<Rightarrow>bool" where "isError \<phi> \<equiv> case \<phi> of Error \<psi> \<Rightarrow> True | _ \<Rightarrow> False"

(*<*) no_syntax "_list" :: "args\<Rightarrow>e list" ("[(_)]") (*>*) 
abbreviation valid :: "io opt\<Rightarrow>bool" (*<*)("[_]")(*>*) where "[\<phi>] \<equiv> case \<phi> of 
    PropForm \<psi> \<Rightarrow> \<forall>w.(\<psi> w)
  | Form \<psi> \<Rightarrow> \<forall>w.(\<psi> w)
  | _ \<Rightarrow> False"
abbreviation satisfiable :: "io opt\<Rightarrow>bool" (*<*)("[_]\<^sup>s\<^sup>a\<^sup>t")(*>*) where "[\<phi>]\<^sup>s\<^sup>a\<^sup>t \<equiv> case \<phi> of 
    PropForm \<psi> \<Rightarrow> \<exists>w.(\<psi> w)
  | Form \<psi> \<Rightarrow> \<exists>w.(\<psi> w)
  | _ \<Rightarrow> False"
abbreviation countersatisfiable :: "io opt\<Rightarrow>bool" (*<*)("[_]\<^sup>c\<^sup>s\<^sup>a\<^sup>t")(*>*) where "[\<phi>]\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  case \<phi> of 
    PropForm \<psi> \<Rightarrow> \<exists>w.\<not>(\<psi> w)
  | Form \<psi> \<Rightarrow> \<exists>w.\<not>(\<psi> w)
  | _ \<Rightarrow> False"
abbreviation invalid :: "io opt\<Rightarrow>bool" (*<*)("[_]\<^sup>i\<^sup>n\<^sup>v")(*>*) where "[\<phi>]\<^sup>i\<^sup>n\<^sup>v \<equiv> case \<phi> of 
    PropForm \<psi> \<Rightarrow> \<forall>w.\<not>(\<psi> w)
  | Form \<psi> \<Rightarrow> \<forall>w.\<not>(\<psi> w)
  | _ \<Rightarrow> False"


section {* Encoding of the language *}

abbreviation \<A>::"io opt \<Rightarrow> io opt" where "\<A> \<phi> \<equiv> case \<phi> of 
    Form \<psi> \<Rightarrow> Form (\<lambda>w. \<psi> cw)
  | PropForm \<psi> \<Rightarrow> PropForm (\<lambda>w. \<psi> cw)
  | _ \<Rightarrow> Error dIO"
text {* actuality operator; @{text "\<phi>"} is evaluated wrt the current world; Error is passed on *}

abbreviation Enc::"e opt\<Rightarrow>(e\<Rightarrow>io) opt\<Rightarrow>io opt"(*<*)("<_\<circ>_>")(*>*) where "<x\<circ>P> \<equiv> case (x,P) of 
    (Term y,Term Q) \<Rightarrow> Form (\<lambda>w.(Q y) w)   
  | (_,_) \<Rightarrow> Error dIO"
text {* @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} will be written here as @{text "<\<kappa>\<^sub>1\<circ>\<Pi>\<^sup>1>"}; @{text "\<kappa>\<^sub>1\<Pi>\<^sup>1"} is a Form; Error is passed on *}

abbreviation Exe1::"(e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>io opt"(*<*)("<_\<bullet>_>")(*>*) where "<P\<bullet>x> \<equiv> case (P,x) of 
    (Term Q,Term y) \<Rightarrow> PropForm (\<lambda>w.(Q y) w)
  | _ \<Rightarrow> Error dIO"
text {* @{text "\<Pi>\<^sup>1\<kappa>\<^sub>1"}  will be written here as @{text "<\<Pi>\<^sup>2\<bullet>\<kappa>\<^sub>1>"}; @{text "\<Pi>\<^sup>1\<kappa>\<^sub>1 "} is a PropForm; Error is passed on *}

abbreviation Exe2::"(e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt"(*<*)("<_\<bullet>_,_>")(*>*) where "<P\<bullet>x1,x2> \<equiv> case (P,x1,x2) of 
    (Term Q,Term y1,Term y2) \<Rightarrow> PropForm (\<lambda>w.(Q y1 y2) w)
  | _ \<Rightarrow> Error dIO"
text {* @{text "\<Pi>\<^sup>2\<kappa>\<^sub>1\<kappa>\<^sub>2"}   will be written here as @{text "<\<Pi>\<^sup>2\<bullet>\<kappa>\<^sub>1,\<kappa>\<^sub>2>"}; @{text "\<Pi>\<^sup>2\<kappa>\<^sub>1\<kappa>\<^sub>2"} is a PropForm; Error is passed on *}

abbreviation Exe3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>e opt\<Rightarrow>io opt"(*<*)("<_\<bullet>_,_,_>") (*>*) where "<P\<bullet>x1,x2,x3> \<equiv> case (P,x1,x2,x3) of 
    (Term Q,Term y1,Term y2,Term y3) \<Rightarrow> PropForm (\<lambda>w.(Q y1 y2 y3) w)
  | _ \<Rightarrow> Error dIO"
text {* @{text "\<Pi>\<^sup>3\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3"}  will be written here as @{text "<\<Pi>\<^sup>2\<bullet>\<kappa>\<^sub>1,\<kappa>\<^sub>2,\<kappa>\<^sub>3>"}; @{text "\<Pi>\<^sup>3\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3"} is a PropForm; Error is passed on; 
we could, of course, introduce further operators: Exe4, Exe5, etc. *}


abbreviation z_not::"io opt\<Rightarrow>io opt"(*<*)("\<^bold>\<not>")(*>*) 
  where "\<^bold>\<not> \<phi> \<equiv> case \<phi> of 
    Form \<psi> \<Rightarrow> Form (\<lambda>w. \<not> \<psi> w)
  | PropForm \<psi> \<Rightarrow> PropForm (\<lambda>w. \<not> \<psi> w)
  | _ \<Rightarrow> Error dIO"  
text {* negation operator; @{text "\<not>\<^sup>z \<phi>"} inherits its type from @{text "\<phi>"} if @{text "\<phi>"} is Form or PropForm; 
Error is passed on *}
 
abbreviation z_implies::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<^bold>\<rightarrow>" 51)(*>*) 
  where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (PropForm \<alpha>,PropForm \<beta>) \<Rightarrow> PropForm (\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w)
  | (Form \<alpha>,Form \<beta>) \<Rightarrow> Form (\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w)
  | _ \<Rightarrow> Error dIO"  
text {* implication operator; @{text "\<phi> \<rightarrow>\<^sup>z \<psi>"} returns returns a PropForm if both are PropForms, Form if both are Forms,
otherwise it returns Error *}

abbreviation z_forall::"('a\<Rightarrow>io opt)\<Rightarrow>io opt"(*<*)("\<^bold>\<forall>")(*>*) 
  where "\<^bold>\<forall> \<Phi> \<equiv> case (\<Phi> dA) of
    PropForm \<phi> \<Rightarrow> PropForm (\<lambda>w. \<forall>x. case (\<Phi> x) of PropForm \<psi> \<Rightarrow> \<psi> w)
  | Form \<phi> \<Rightarrow> Form (\<lambda>w. \<forall>x. case (\<Phi> x) of Form \<psi> \<Rightarrow> \<psi> w)
  | _ \<Rightarrow> Error dIO"
text {* universal quantification; @{text "\<forall>(\<lambda>x.\<phi>)"} inherits its kind (Form or PropForm) from @{text "\<phi>"}; Error is passed on
@{text "\<forall>(\<lambda>x.\<phi>)"} is mapped to @{text "(\<lambda>w.\<forall>x.\<phi>xw)"} as expected *}

abbreviation z_box::"io opt\<Rightarrow>io opt"(*<*)("\<^bold>\<box>")(*>*) 
  where "\<^bold>\<box> \<phi> \<equiv> case \<phi> of 
    Form \<psi> \<Rightarrow> Form (\<lambda>w. \<forall>v. \<psi> v)
  | PropForm \<psi> \<Rightarrow> PropForm (\<lambda>w. \<forall>v. \<psi> v)
  | _ \<Rightarrow> Error dIO"  
text {* box operator; @{text "\<box> \<phi>"} inherits its type (Form or PropForm) from @{text "\<phi>"}; Error is passed on.
Note that the @{text "\<box>"}-operator is defined here without an accessibility relation; this is ok since we assume logic S5. *} 

abbreviation lam0::"io opt\<Rightarrow>io opt"(*<*)("\<lambda>\<^sup>0")(*>*) where "\<lambda>\<^sup>0 \<phi> \<equiv> case \<phi> of 
    PropForm \<psi> \<Rightarrow> PropForm \<psi>
  | _ \<Rightarrow> Error dIO"  
text {* 0-arity lambda abstraction; @{text "\<lambda>\<^sup>0 \<phi>"} returns PropForm @{text "\<phi>"} if @{text "\<phi>"} is a PropForm, otherwise Error *}

abbreviation lam1::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt"(*<*)("\<lambda>\<^sup>1")(*>*) 
  where "\<lambda>\<^sup>1 \<Phi> \<equiv> case (\<Phi> dE) of
    PropForm \<phi> \<Rightarrow> Term (\<lambda>x. case (\<Phi> x) of PropForm \<phi> \<Rightarrow> \<phi>)
  | _ \<Rightarrow> Error (\<lambda>x. dIO)"
text {* 1-arity lambda abstraction; @{text "\<lambda>\<^sup>1(\<lambda>x.\<phi>)"} returns Term @{text "(\<lambda>x.\<phi>)"} if @{text "\<phi>"} is a PropForm, 
otherwise Error *}

abbreviation lam2::"(e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>io) opt"(*<*)("\<lambda>\<^sup>2")(*>*) 
  where "\<lambda>\<^sup>2 \<Phi> \<equiv> case (\<Phi> dE dE) of
    PropForm \<phi> \<Rightarrow> Term (\<lambda>x y. case (\<Phi> x y) of PropForm \<phi> \<Rightarrow> \<phi>)
  | _ \<Rightarrow> Error (\<lambda>x y. dIO)"
text {* 2-arity lambda abstraction; @{text "\<lambda>\<^sup>2(\<lambda>xy.\<phi>)"} returns Term @{text "(\<lambda>xy.\<phi>)"} if @{text "\<phi>"} is a PropForm, 
otherwise Error *}

abbreviation lam3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt"(*<*)("\<lambda>\<^sup>3")(*>*) 
  where "\<lambda>\<^sup>3 \<Phi> \<equiv> case (\<Phi> dE dE dE) of
    PropForm \<phi> \<Rightarrow> Term (\<lambda>x y z. case (\<Phi> x y z) of PropForm \<phi> \<Rightarrow> \<phi>)
  | _ \<Rightarrow> Error (\<lambda>x y z. dIO)"
text {* 3-arity lambda abstraction; @{text "\<lambda>\<^sup>2(\<lambda>xyz.\<phi>)"} returns Term @{text "(\<lambda>xyz.\<phi>)"} if @{text "\<phi>"} is a PropForm, 
otherwise Error; we could, of course, introduce further operators: @{text "\<lambda>\<^sup>4"}, @{text "\<lambda>\<^sup>5"}, etc. *}

abbreviation that::"(e\<Rightarrow>io opt)\<Rightarrow>e opt"(*<*)("\<epsilon>")(*>*) 
  where "\<epsilon> \<Phi> \<equiv> case (\<Phi> dE) of
    PropForm \<phi> \<Rightarrow> Term (THE x. case (\<Phi> x) of PropForm \<psi> \<Rightarrow> \<psi> cw)
  | _ \<Rightarrow> Error dE"
text {* that operator; that @{text "(\<lambda>x.\<phi>)"} returns Term @{text "(THE x. \<phi> x cw)"}, that is the inbuilt THE 
operator is used and evaluation is wrt to the current world cw; moreover, application of that 
is allowed if @{text "(\<Phi> sRE)"} is a PropForm, otherwise Error is passed on for some someRawEntity *}



section {* Further logical connectives *}

abbreviation z_and::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<^bold>\<and>" 53)(*>*) where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>)"
abbreviation z_or::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<^bold>\<or>" 52)(*>*) where "\<phi> \<^bold>\<or> \<psi> \<equiv> \<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>"
abbreviation z_equiv::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<^bold>\<equiv>" 52)(*>*) where "\<phi> \<^bold>\<equiv> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"
abbreviation z_exists::"('a\<Rightarrow>io opt)\<Rightarrow>io opt"(*<*)("\<^bold>\<exists>")(*>*) where "\<^bold>\<exists> \<Phi> \<equiv> case (\<Phi> dA) of
    PropForm \<phi> \<Rightarrow> PropForm (\<lambda>w. \<exists>x. case (\<Phi> x) of PropForm \<psi> \<Rightarrow> \<psi> w)
  | Form \<phi> \<Rightarrow> Form (\<lambda>w. \<exists>x. case (\<Phi> x) of Form \<psi> \<Rightarrow> \<psi> w)
  | _ \<Rightarrow> Error dIO"
abbreviation z_dia::"io opt\<Rightarrow>io opt"(*<*)("\<^bold>\<diamond>")(*>*) where "\<^bold>\<diamond> \<phi> \<equiv> \<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not> \<phi>))"

(* abbreviation z_true::"io opt"(*<*)("\<top>\<^sup>z")(*>*) where "\<top>\<^sup>z \<equiv> todo; not entirely clear yet " *)
(* abbreviation z_false::"io opt"(*<*)("\<bottom>\<^sup>z")(*>*) where "\<bottom>\<^sup>z \<equiv> todo; not entirely clear yet " *)


section {* Some shortcuts for the constructors *}

abbreviation mkPropForm ::  "io\<Rightarrow>io opt"(*<*)(",_,")(*>*)  where ",p, \<equiv> PropForm p" 
abbreviation mkForm ::  "io\<Rightarrow>io opt"(*<*)(";_;")(*>*)  where ";p; \<equiv> Form p" 
abbreviation mkTerm ::  "'a\<Rightarrow>'a opt"(*<*)("._.")(*>*)  where ".t. \<equiv> Term t" 
abbreviation mkError ::  "'a\<Rightarrow>'a opt"(*<*)("*_*")(*>*)  where "*t* \<equiv> Term t" 


section {* Some Basic Tests *}

subsection {* Meta-Logic *}

lemma "(\<forall>\<phi>. [,\<phi>,]) \<longleftrightarrow> [\<^bold>\<forall>(\<lambda>\<phi>. ,\<phi>,)]" apply simp by auto 
lemma "(\<forall>\<phi>. [;\<phi>;]) \<longleftrightarrow> [\<^bold>\<forall>(\<lambda>\<phi>. ;\<phi>;)]" apply simp by auto 


subsection {* Verifying Modal Logic Principles *}

text {* Necessitation holds *}
lemma necessitation_PropForm: "[,\<phi>,] \<longrightarrow> [\<^bold>\<box> ,\<phi>,]" apply simp done
lemma necessitation_Form:     "[;\<phi>;] \<longrightarrow> [\<^bold>\<box> ;\<phi>;]" apply simp done

text {* Modal Collapse does not hold *}
lemma modalCollapse_PropForm: "[,\<phi>, \<^bold>\<rightarrow> \<^bold>\<box> ,\<phi>,]" apply simp nitpick oops
lemma modalCollapse_Form:     "[;\<phi>; \<^bold>\<rightarrow> \<^bold>\<box> ;\<phi>;]" apply simp nitpick oops


subsection {* S5 Principles *}

lemma axiom_T_PF: "[(\<^bold>\<box> ,\<phi>,) \<^bold>\<rightarrow> ,\<phi>,]" apply simp done
lemma axiom_T_F:  "[(\<^bold>\<box> ;\<phi>;) \<^bold>\<rightarrow> ;\<phi>;]" apply simp done

lemma axiom_B_PF: "[,\<phi>, \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<diamond> ,\<phi>,))]" apply simp done
lemma axiom_B_F:  "[;\<phi>; \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<diamond> ;\<phi>;))]" apply simp done

lemma axiom_D_PF: "[\<^bold>\<box> ,\<phi>, \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<box> ,\<phi>,)]" apply simp done
lemma axiom_D_F:  "[\<^bold>\<box> ;\<phi>; \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<box> ;\<phi>;)]" apply simp done

lemma axiom_4_PF: "[\<^bold>\<box> ,\<phi>, \<^bold>\<rightarrow> \<^bold>\<diamond> ,\<phi>,]" apply simp by auto
lemma axiom_4_F:  "[\<^bold>\<box> ;\<phi>; \<^bold>\<rightarrow> \<^bold>\<diamond> ;\<phi>;]" apply simp by auto

lemma axiom_5_PF: "[\<^bold>\<diamond> ,\<phi>, \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<diamond> ,\<phi>,)]" apply simp done
lemma axiom_5_F:  "[\<^bold>\<diamond> ;\<phi>; \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<diamond> ;\<phi>;)]" apply simp done


lemma test_A_PF: "[\<^bold>\<box> (\<^bold>\<diamond> ,\<phi>,) \<^bold>\<rightarrow> \<^bold>\<diamond> ,\<phi>,]" apply simp done
lemma test_A_F:  "[\<^bold>\<box> (\<^bold>\<diamond> ;\<phi>;) \<^bold>\<rightarrow> \<^bold>\<diamond> ;\<phi>;]" apply simp done

lemma test_B_PF: "[\<^bold>\<diamond> (\<^bold>\<box> ,\<phi>,) \<^bold>\<rightarrow> \<^bold>\<diamond> ,\<phi>,]" apply simp by auto
lemma test_B_F:  "[\<^bold>\<diamond> (\<^bold>\<box> ;\<phi>;) \<^bold>\<rightarrow> \<^bold>\<diamond> ;\<phi>;]" apply simp by auto

lemma test_C_PF: "[\<^bold>\<box> (\<^bold>\<diamond> ,\<phi>,) \<^bold>\<rightarrow> \<^bold>\<box> ,\<phi>,]" apply simp nitpick oops
lemma test_C_F:  "[\<^bold>\<box> (\<^bold>\<diamond> ;\<phi>;) \<^bold>\<rightarrow> \<^bold>\<box> ;\<phi>;]" apply simp nitpick oops

lemma test_D_PF: "[\<^bold>\<diamond> (\<^bold>\<box> ,\<phi>,) \<^bold>\<rightarrow> \<^bold>\<box> ,\<phi>,]" apply simp done
lemma test_D_F:  "[\<^bold>\<diamond> (\<^bold>\<box> ;\<phi>;) \<^bold>\<rightarrow> \<^bold>\<box> ;\<phi>;]" apply simp done


subsection {* Validity, Satisfiabilty, Countersatisfiability and Invalidity *}
lemma  "[,\<phi>,] \<longleftrightarrow> \<not> [,\<phi>,]\<^sup>c\<^sup>s\<^sup>a\<^sup>t" apply simp done
lemma  "[,\<phi>,]\<^sup>s\<^sup>a\<^sup>t \<longleftrightarrow> \<not> [,\<phi>,]\<^sup>i\<^sup>n\<^sup>v" apply simp done
lemma  "[;\<phi>;] \<longleftrightarrow> \<not> [;\<phi>;]\<^sup>c\<^sup>s\<^sup>a\<^sup>t" apply simp done
lemma  "[;\<phi>;]\<^sup>s\<^sup>a\<^sup>t \<longleftrightarrow> \<not> [;\<phi>;]\<^sup>i\<^sup>n\<^sup>v" apply simp done

text {* For Terms and Error objects the above correspondences do not apply *}
lemma  "[.\<phi>.] \<longleftrightarrow> \<not> [.\<phi>.]\<^sup>c\<^sup>s\<^sup>a\<^sup>t" nitpick oops
lemma  "[.\<phi>.]\<^sup>s\<^sup>a\<^sup>t \<longleftrightarrow> \<not> [.\<phi>.]\<^sup>i\<^sup>n\<^sup>v" nitpick oops
lemma  "[*\<phi>*] \<longleftrightarrow> \<not> [*\<phi>*]\<^sup>c\<^sup>s\<^sup>a\<^sup>t" nitpick oops
lemma  "[*\<phi>*]\<^sup>s\<^sup>a\<^sup>t \<longleftrightarrow> \<not> [*\<phi>*]\<^sup>i\<^sup>n\<^sup>v" nitpick oops

subsection {* Example signature; entities and relations *}

consts a_0 :: "e" abbreviation a  where "a \<equiv> .a_0."
consts b_0 :: "e" abbreviation b  where "b \<equiv> .b_0."
consts c_0 :: "e" abbreviation c  where "c \<equiv> .c_0."

consts R_0 :: "io"  abbreviation R0  where "R0 \<equiv> .R_0."
consts R_1 :: "e\<Rightarrow>io" abbreviation R1  where "R1 \<equiv> .R_1."
consts R_2 :: "e\<Rightarrow>e\<Rightarrow>io" abbreviation R2  where "R2 \<equiv> .R_2."
consts R_3 :: "e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io"  abbreviation R3  where "R3 \<equiv> .R_3."


text {* Testing term and formula constructions *}

lemma "[<R1\<bullet>a>]" nitpick oops
lemma "isPropForm <R1\<bullet>a>" apply simp done
lemma "<R1\<bullet>a> = X" apply simp oops

lemma "[<a\<circ>R1>]" nitpick oops
lemma "isPropForm <a\<circ>R1>" apply simp oops
lemma "isForm <a\<circ>R1>" apply simp done
lemma "<a\<circ>R1> = X" apply simp oops

lemma "[<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <R1\<bullet>.x.>)\<bullet>a>]" apply simp done
lemma "<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <R1\<bullet>.x.>)\<bullet>a> = X" apply simp oops

lemma "\<not> isWff (<R1\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>R1>)" apply simp done
lemma "\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>R1>) = X" apply simp oops

lemma "[<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>R1>)\<bullet>a>]" apply simp oops
lemma "<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>R1>)\<bullet>a> = X" apply simp oops

lemma "[\<^bold>\<forall>(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <R1\<bullet>.x.>)]" apply simp done
lemma "[\<^bold>\<forall>(\<lambda>R. \<^bold>\<forall>(\<lambda>x. <.R.\<bullet>.x.> \<^bold>\<rightarrow> <.R.\<bullet>.x.>))]" apply simp done
lemma "\<^bold>\<forall>(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <R1\<bullet>.x.>) = X" apply simp oops

lemma "[\<^bold>\<forall>(\<lambda>x. <.x.\<circ>R1> \<^bold>\<rightarrow> <.x.\<circ>R1>)]" apply simp done
lemma "\<^bold>\<forall>(\<lambda>x. <.x.\<circ>R1> \<^bold>\<rightarrow> <.x.\<circ>R1>) = X" apply simp oops

lemma "[\<^bold>\<forall>(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>R1>)]" apply simp oops
lemma "\<^bold>\<forall>(\<lambda>x. <R1\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>R1>) = X" apply simp oops
lemma "[\<^bold>\<forall>(\<lambda>R. <.R.\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>.R.>)]" apply simp oops
lemma "\<^bold>\<forall>(\<lambda>R. <.R.\<bullet>.x.> \<^bold>\<rightarrow> <.x.\<circ>.R.>) = X" apply simp oops


section {* Are the priorities set correctly?*}

lemma ",\<phi>, \<^bold>\<and> ,\<psi>, \<^bold>\<rightarrow> ,\<chi>, \<equiv> (,\<phi>, \<^bold>\<and> ,\<psi>,) \<^bold>\<rightarrow> ,\<chi>," apply simp done
lemma ",\<phi>, \<^bold>\<and> ,\<psi>, \<^bold>\<rightarrow> ,\<chi>, \<equiv> ,\<phi>, \<^bold>\<and> (,\<psi>, \<^bold>\<rightarrow> ,\<chi>,)" apply simp nitpick oops

lemma "(,\<phi>, \<^bold>\<and> ,\<psi>, \<^bold>\<equiv> ,\<phi>, \<^bold>\<and> ,\<psi>,) \<equiv> ((,\<phi>, \<^bold>\<and> ,\<psi>,) \<^bold>\<equiv> (,\<phi>, \<^bold>\<and> ,\<psi>,))" apply simp done
lemma "(,\<phi>, \<^bold>\<and> ,\<psi>, \<^bold>\<equiv> ,\<phi>, \<^bold>\<and> ,\<psi>,) \<equiv> (,\<phi>, \<^bold>\<and> (,\<psi>, \<^bold>\<equiv> ,\<phi>,) \<^bold>\<and> ,\<psi>,)" apply simp nitpick oops


section {* E!, O!, A! and =E *}

consts E::"(e\<Rightarrow>io)"
text {* Distinguished 1-place relation constant: E! (read: ‘being concrete’ or ‘concreteness’) *}

abbreviation z_ordinary::"(e\<Rightarrow>io) opt"(*<*)("O\<^sup>!")(*>*) where "O\<^sup>! \<equiv> \<lambda>\<^sup>1(\<lambda>x. \<^bold>\<diamond> <.E.\<bullet>.x.>)"
text {* Being ordinary is being possibly concrete. *}

abbreviation z_abstract::"(e\<Rightarrow>io) opt"(*<*)("A\<^sup>!")(*>*) where "A\<^sup>! \<equiv> \<lambda>\<^sup>1(\<lambda>x. \<^bold>\<not> (\<^bold>\<diamond> <.E.\<bullet>.x.>))"
text {* Being abstract is not possibly being concrete. *}

abbreviation z_identity::"(e\<Rightarrow>e\<Rightarrow>io) opt"(*<*)("\<^bold>=\<^sub>e")(*>*) where "\<^bold>=\<^sub>e \<equiv> 
  \<lambda>\<^sup>2(\<lambda>x y. ((<O\<^sup>!\<bullet>.x.> \<^bold>\<and> <O\<^sup>!\<bullet>.y.>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>(\<lambda>F. <.F.\<bullet>.x.> \<^bold>\<equiv> <.F.\<bullet>.y.>))))"

abbreviation z_identityE::"(e opt\<Rightarrow>e opt\<Rightarrow>io opt)"(*<*)(infixr "\<^bold>=\<^sub>E" 63)(*>*) where "x \<^bold>=\<^sub>E y \<equiv> (Exe2 \<^bold>=\<^sub>e x y)" 



section {* Further test examples *}

lemma "[\<^bold>\<forall>(\<lambda>x. \<^bold>\<exists>(\<lambda>R. (<.x.\<circ>.R.> \<^bold>\<rightarrow> <.x.\<circ>R1>)))]" apply simp by auto
lemma "[\<^bold>\<forall>(\<lambda>x. \<^bold>\<forall>(\<lambda>R. (<.x.\<circ>.R.> \<^bold>\<rightarrow> <.x.\<circ>R1>)))]" apply simp nitpick oops

lemma "[a \<^bold>=\<^sub>E a]" apply simp nitpick oops

lemma "[<O\<^sup>!\<bullet>a> \<^bold>\<rightarrow> a \<^bold>=\<^sub>E a]" apply simp done

lemma "[(\<^bold>\<forall>(\<lambda>F. <.F.\<bullet>.x.> \<^bold>\<equiv> <.F.\<bullet>.x.>))]" apply simp done
lemma "[<O\<^sup>!\<bullet>a> \<^bold>\<rightarrow> <\<lambda>\<^sup>1(\<lambda>x. .x. \<^bold>=\<^sub>E a)\<bullet>a>]" apply simp done

lemma "[(\<^bold>\<exists>(\<lambda>F. <a\<circ>.F.>))]" apply simp by auto

lemma "isWff ,(\<lambda>w. True)," apply simp done

lemma "[\<^bold>\<exists>(\<lambda>\<phi>. ,\<phi>,)]" apply simp by auto
lemma "[\<^bold>\<exists>(\<lambda>\<phi>. ;\<phi>;)]" apply simp by auto


section {* Axioms *}

subsection {* Axioms for Negations and Conditionals *}

lemma a21_1_PF: "[,\<phi>, \<^bold>\<rightarrow> (,\<phi>, \<^bold>\<rightarrow> ,\<phi>,)]" apply simp done
lemma a21_1_F:  "[;\<phi>; \<^bold>\<rightarrow> (;\<phi>; \<^bold>\<rightarrow> ;\<phi>;)]" apply simp done
lemma a21_2_PF: "[(,\<phi>, \<^bold>\<rightarrow> (,\<psi>, \<^bold>\<rightarrow> ,\<chi>,)) \<^bold>\<rightarrow> ((,\<phi>, \<^bold>\<rightarrow> ,\<psi>,) \<^bold>\<rightarrow> (,\<phi>, \<^bold>\<rightarrow> ,\<chi>,))]" apply simp done
lemma a21_2_F:  "[(;\<phi>; \<^bold>\<rightarrow> (;\<psi>; \<^bold>\<rightarrow> ;\<chi>;)) \<^bold>\<rightarrow> ((;\<phi>; \<^bold>\<rightarrow> ;\<psi>;) \<^bold>\<rightarrow> (;\<phi>; \<^bold>\<rightarrow> ;\<chi>;))]" apply simp done
lemma a21_3_PF: "[(\<^bold>\<not> ,\<phi>, \<^bold>\<rightarrow> \<^bold>\<not> ,\<psi>,) \<^bold>\<rightarrow> (\<^bold>\<not> ,\<phi>, \<^bold>\<rightarrow> ,\<psi>,) \<^bold>\<rightarrow> ,\<phi>,]" apply simp done
lemma a21_3_F:  "[(\<^bold>\<not> ;\<phi>; \<^bold>\<rightarrow> \<^bold>\<not> ;\<psi>;) \<^bold>\<rightarrow> (\<^bold>\<not> ;\<phi>; \<^bold>\<rightarrow> ;\<psi>;) \<^bold>\<rightarrow> ;\<phi>;]" apply simp done

subsection {* Axioms of Identity *}
text {* todo *}

subsection {* Axioms of Quantification *}
text {* todo *}

subsection {* Axioms of Actuality *}

lemma a31_1_PF: "[\<A> (\<^bold>\<not> ,\<phi>,) \<^bold>\<equiv> (\<^bold>\<not> (\<A> ,\<phi>,))]" apply simp done
lemma a31_1_F: "[\<A> (\<^bold>\<not> ;\<phi>;) \<^bold>\<equiv> (\<^bold>\<not> (\<A> ;\<phi>;))]" apply simp done
lemma a31_2_PF: "[\<A> (,\<phi>, \<^bold>\<rightarrow> ,\<psi>,) \<^bold>\<equiv> (\<A> ,\<phi>, \<^bold>\<rightarrow> \<A> ,\<psi>,)]" apply simp done
lemma a31_2_F: "[\<A> (;\<phi>; \<^bold>\<rightarrow> ;\<psi>;) \<^bold>\<equiv> (\<A> ;\<phi>; \<^bold>\<rightarrow> \<A> ;\<psi>;)]" apply simp done
lemma a31_3_PF: "[(\<A> (\<^bold>\<forall>(\<lambda>x. ,\<phi>,)) \<^bold>\<equiv> \<^bold>\<forall>(\<lambda>x. \<A> ,\<phi>,))]" apply simp done
lemma a31_3_F: "[(\<A> (\<^bold>\<forall>(\<lambda>x. ;\<phi>;)) \<^bold>\<equiv> \<^bold>\<forall>(\<lambda>x. \<A> ;\<phi>;))]" apply simp done
lemma a31_4_PF: "[\<A> ,\<phi>, \<^bold>\<equiv> \<A> (\<A> ,\<phi>,)]" apply simp done
lemma a31_4_F: "[\<A> ;\<phi>; \<^bold>\<equiv> \<A> (\<A> ;\<phi>;)]" apply simp done

subsection {* Axioms of Necessity *}

lemma a32_1_PF: "[\<^bold>\<box> (,\<phi>, \<^bold>\<rightarrow> ,\<phi>,) \<^bold>\<rightarrow> (\<^bold>\<box> ,\<phi>, \<^bold>\<rightarrow> \<^bold>\<box> ,\<phi>,)]" apply simp done       (* K Schema *)
lemma a32_1_F:  "[\<^bold>\<box> (;\<phi>; \<^bold>\<rightarrow> ;\<phi>;) \<^bold>\<rightarrow> (\<^bold>\<box> ;\<phi>; \<^bold>\<rightarrow> \<^bold>\<box> ;\<phi>;)]" apply simp done       (* K Schema *)
lemma a32_2_PF: "[\<^bold>\<box> ,\<phi>, \<^bold>\<rightarrow> ,\<phi>,]" apply simp done                               (* T Schema *)
lemma a32_2_F:  "[\<^bold>\<box> ;\<phi>; \<^bold>\<rightarrow> ;\<phi>;]" apply simp done                               (* T Schema *)
lemma a32_3_PF: "[\<^bold>\<box> (\<^bold>\<diamond> ,\<phi>,) \<^bold>\<rightarrow> (\<^bold>\<diamond> ,\<phi>,)]" apply simp done                       (* 5 Schema *)
lemma a32_3_F:  "[\<^bold>\<box> (\<^bold>\<diamond> ;\<phi>;) \<^bold>\<rightarrow> (\<^bold>\<diamond> ;\<phi>;)]" apply simp done                       (* 5 Schema *)
lemma a32_4_PF: "[(\<^bold>\<forall>(\<lambda>x. \<^bold>\<box> ,\<phi>,)) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>(\<lambda>x. ,\<phi>,))]" apply simp done           (* BF *)
lemma a32_4_F:  "[(\<^bold>\<forall>(\<lambda>x. \<^bold>\<box> ;\<phi>;)) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>(\<lambda>x. ;\<phi>;))]" apply simp done           (* BF *)

text {* The following needs to be an axiom; it does not follow for free: it is possible that there 
are contingently concrete individuals and it is possible that there are not: *}
axiomatization where
  a32_5_PF: "[\<^bold>\<diamond> (\<^bold>\<exists>(\<lambda>x. <.E.\<bullet>.x.> \<^bold>\<and> (\<^bold>\<diamond> (\<^bold>\<not> <.E.\<bullet>.x.>)))) \<^bold>\<and> \<^bold>\<diamond> (\<^bold>\<not> (\<^bold>\<exists>(\<lambda>x. <.E.\<bullet>.x.> \<^bold>\<and> (\<^bold>\<diamond> (\<^bold>\<not> <.E.\<bullet>.x.>)))))]"

subsection {* Axioms of Necessity and Actuality *}

lemma a33_1_PF: "[\<A> ,\<phi>, \<^bold>\<rightarrow> \<^bold>\<box> (\<A> ,\<phi>,)]" apply simp done
lemma a33_1_F:  "[\<A> ;\<phi>; \<^bold>\<rightarrow> \<^bold>\<box> (\<A> ;\<phi>;)]" apply simp done
lemma a33_2_PF: "[\<^bold>\<box> ,\<phi>, \<^bold>\<equiv> (\<A> (\<^bold>\<box> ,\<phi>,))]" apply simp done
lemma a33_2_F:  "[\<^bold>\<box> ;\<phi>; \<^bold>\<equiv> (\<A> (\<^bold>\<box> ;\<phi>;))]" apply simp done



(*<*) 
end
(*>*)

