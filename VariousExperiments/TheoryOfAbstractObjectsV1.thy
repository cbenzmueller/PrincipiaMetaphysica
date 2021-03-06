(*<*) 
theory TheoryOfAbstractObjectsV1
imports Main

begin
(*>*)

section {* Introduction *}

text {* This work significantly adapts and extends the embedding presented in \cite{J23}; say more ... *}

section {* Preliminaries *}

typedecl i
-- "the type possible worlds; the formalism explicitly encodes Kripke style semantics"

type_synonym io = "(i \<Rightarrow> bool)" 
-- "modal logic formulas (or propositional formulas) are essentially of this type: predicates on"
-- "worlds"

typedecl e
-- "the raw type of entities/objects (abstract or ordinary)"

datatype 'a opt = Error 'a | Term 'a | Form 'a | PropForm 'a


consts cw :: i 
-- "some fixed current world"

consts dE::"e" dIO::"io" dEIO::"e\<Rightarrow>io" dEEIO::"e=>e\<Rightarrow>io" dEEEIO::"e=>e=>e\<Rightarrow>io" dA::'a
-- "some fixed dummy symbols; we anyway assume that the domains are on-empty"
-- "needed as dummy object in some cases below"


(* consts sRE :: e 
-- "some fixed entity; we anyway assume that the domain of objects is non-empty" *)


text {* We consider an arbitrary but fixed accessibility relation r *}

consts r :: "(i\<Rightarrow>i\<Rightarrow>bool)" 



text {* Meta-logical predicates. *}


abbreviation isWff :: "'a opt\<Rightarrow>bool" where "isWff \<phi> \<equiv> case \<phi> of Error \<psi> \<Rightarrow> False | _ \<Rightarrow> True"
abbreviation isForm :: "'a opt\<Rightarrow>bool" where "isForm \<phi> \<equiv> case \<phi> of Form \<psi> \<Rightarrow> True | _ \<Rightarrow> False"
abbreviation isPropForm :: "'a opt\<Rightarrow>bool" where "isPropForm \<phi> \<equiv> case \<phi> of PropForm \<psi> \<Rightarrow> True | _ \<Rightarrow> False"
abbreviation isTerm :: "'a opt\<Rightarrow>bool" where "isTerm \<phi> \<equiv> case \<phi> of Term \<psi> \<Rightarrow> True | _ \<Rightarrow> False"
abbreviation isError :: "'a opt\<Rightarrow>bool" where "isError \<phi> \<equiv> case \<phi> of Error \<psi> \<Rightarrow> True | _ \<Rightarrow> False"

(*<*) no_syntax "_list" :: "args\<Rightarrow>e list" ("[(_)]") (*>*) 
abbreviation valid :: "io opt\<Rightarrow>bool" (*<*)("[_]")(*>*) where "[\<phi>] \<equiv> case \<phi> of 
    PropForm \<psi> \<Rightarrow> \<forall>w.(\<psi> w)
  | Form \<psi> \<Rightarrow> \<forall>w.(\<psi> w)
  | _ \<Rightarrow> False"
abbreviation satifiable :: "io opt\<Rightarrow>bool" (*<*)("[_]\<^sup>s\<^sup>a\<^sup>t")(*>*) where "[\<phi>]\<^sup>s\<^sup>a\<^sup>t \<equiv> case \<phi> of 
    PropForm \<psi> \<Rightarrow> \<exists>w.(\<psi> w)
  | Form \<psi> \<Rightarrow> \<exists>w.(\<psi> w)
  | _ \<Rightarrow> False"
abbreviation countersatifiable :: "io opt\<Rightarrow>bool" (*<*)("[_]\<^sup>c\<^sup>s\<^sup>a\<^sup>t")(*>*) where "[\<phi>]\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  case \<phi> of 
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


abbreviation z_not::"io opt\<Rightarrow>io opt"(*<*)("\<not>\<^sup>z")(*>*) where "\<not>\<^sup>z \<phi> \<equiv> case \<phi> of 
    Form \<psi> \<Rightarrow> Form (\<lambda>w. \<not> \<psi> w)
  | PropForm \<psi> \<Rightarrow> PropForm (\<lambda>w. \<not> \<psi> w)
  | _ \<Rightarrow> Error dIO"  
text {* negation operator; @{text "\<not>\<^sup>z \<phi>"} inherits its type from @{text "\<phi>"} if @{text "\<phi>"} is Form or PropForm; 
Error is passed on *}
 
abbreviation z_implies::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<rightarrow>\<^sup>z" 51)(*>*) where "\<phi> \<rightarrow>\<^sup>z \<psi> \<equiv> case (\<phi>,\<psi>) of 
    (PropForm \<alpha>,PropForm \<beta>) \<Rightarrow> PropForm (\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w)
  | (Form \<alpha>,Form \<beta>) \<Rightarrow> Form (\<lambda>w. \<alpha> w \<longrightarrow> \<beta> w)
  | _ \<Rightarrow> Error dIO"  
text {* implication operator; @{text "\<phi> \<rightarrow>\<^sup>z \<psi>"} returns returns a PropForm if both are PropForms, Form if both are Forms,
otherwise it returns Error *}


abbreviation z_forall::"('a\<Rightarrow>io opt)\<Rightarrow>io opt"(*<*)("\<forall>")(*>*) where "\<forall> \<Phi> \<equiv> case (\<Phi> dA) of
    PropForm \<phi> \<Rightarrow> PropForm (\<lambda>w. \<forall>x. case (\<Phi> x) of PropForm \<psi> \<Rightarrow> \<psi> w)
  | Form \<phi> \<Rightarrow> Form (\<lambda>w. \<forall>x. case (\<Phi> x) of Form \<psi> \<Rightarrow> \<psi> w)
  | _ \<Rightarrow> Error dIO"
text {* universal quantification; @{text "\<forall>(\<lambda>x.\<phi>)"} inherits its kind (Form or PropForm) from @{text "\<phi>"}; Error is passed on
@{text "\<forall>(\<lambda>x.\<phi>)"} is mapped to @{text "(\<lambda>w.\<forall>x.\<phi>xw)"} as expected *}


abbreviation z_box::"io opt\<Rightarrow>io opt"(*<*)("\<box>\<^sup>r_")(*>*) where "\<box>\<^sup>r \<phi> \<equiv> case \<phi> of 
    Form \<psi> \<Rightarrow> Form (\<lambda>w. \<forall>v. (r w v) \<longrightarrow> \<psi> v)
  | PropForm \<psi> \<Rightarrow> PropForm (\<lambda>w. \<forall>v. (r w v) \<longrightarrow> \<psi> v)
  | _ \<Rightarrow> Error dIO"  
text {* box operator; @{text "\<box>\<^sup>r \<phi>"} inherits its type (Form or PropForm) from @{text "\<phi>"}; Error is passed on *} 

abbreviation lam0::"io opt\<Rightarrow>io opt"(*<*)("\<lambda>\<^sup>0")(*>*) where "\<lambda>\<^sup>0 \<phi> \<equiv> case \<phi> of 
    PropForm \<psi> \<Rightarrow> PropForm \<psi>
  | _ \<Rightarrow> Error dIO"  
text {* 0-arity lambda abstraction; @{text "\<lambda>\<^sup>0 \<phi>"} returns PropForm @{text "\<phi>"} if @{text "\<phi>"} is a PropForm, otherwise Error *}

abbreviation lam1::"(e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>io) opt"(*<*)("\<lambda>\<^sup>1")(*>*) where "\<lambda>\<^sup>1 \<Phi> \<equiv> case (\<Phi> dE) of
    PropForm \<phi> \<Rightarrow> Term (\<lambda>x. case (\<Phi> x) of PropForm \<phi> \<Rightarrow> \<phi>)
  | _ \<Rightarrow> Error (\<lambda>x. dIO)"
text {* 1-arity lambda abstraction; @{text "\<lambda>\<^sup>1(\<lambda>x.\<phi>)"} returns Term @{text "(\<lambda>x.\<phi>)"} if @{text "\<phi>"} is a PropForm, 
otherwise Error *}

abbreviation lam2::"(e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>io) opt"(*<*)("\<lambda>\<^sup>2")(*>*) where "\<lambda>\<^sup>2 \<Phi> \<equiv> case (\<Phi> dE dE) of
    PropForm \<phi> \<Rightarrow> Term (\<lambda>x y. case (\<Phi> x y) of PropForm \<phi> \<Rightarrow> \<phi>)
  | _ \<Rightarrow> Error (\<lambda>x y. dIO)"
text {* 2-arity lambda abstraction; @{text "\<lambda>\<^sup>2(\<lambda>xy.\<phi>)"} returns Term @{text "(\<lambda>xy.\<phi>)"} if @{text "\<phi>"} is a PropForm, 
otherwise Error *}

abbreviation lam3::"(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io opt)\<Rightarrow>(e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt"(*<*)("\<lambda>\<^sup>3")(*>*) where "\<lambda>\<^sup>3 \<Phi> \<equiv> case (\<Phi> dE dE dE) of
    PropForm \<phi> \<Rightarrow> Term (\<lambda>x y z. case (\<Phi> x y z) of PropForm \<phi> \<Rightarrow> \<phi>)
  | _ \<Rightarrow> Error (\<lambda>x y z. dIO)"
text {* 3-arity lambda abstraction; @{text "\<lambda>\<^sup>2(\<lambda>xyz.\<phi>)"} returns Term @{text "(\<lambda>xyz.\<phi>)"} if @{text "\<phi>"} is a PropForm, 
otherwise Error; we could, of course, introduce further operators: @{text "\<lambda>\<^sup>4"}, @{text "\<lambda>\<^sup>5"}, etc. *}


abbreviation that::"(e\<Rightarrow>io opt)\<Rightarrow>e opt"(*<*)("\<epsilon>")(*>*) where "\<epsilon> \<Phi> \<equiv> case (\<Phi> dE) of
    PropForm \<phi> \<Rightarrow> Term (THE x. case (\<Phi> x) of PropForm \<psi> \<Rightarrow> \<psi> cw)
  | _ \<Rightarrow> Error dE"
text {* that operator; that @{text "(\<lambda>x.\<phi>)"} returns Term @{text "(THE x. \<phi> x cw)"}, that is the inbuilt THE 
operator is used and evaluation is wrt to the current world cw; moreover, application of that 
is allowed if @{text "(\<Phi> sRE)"} is a PropForm, otherwise Error is passed on for some someRawEntity *}



section {* Further logical connectives *}


abbreviation z_and::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<and>\<^sup>z" 53)(*>*) where "\<phi> \<and>\<^sup>z \<psi> \<equiv> \<not>\<^sup>z(\<phi> \<rightarrow>\<^sup>z \<not>\<^sup>z\<psi>)"
abbreviation z_or::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<or>\<^sup>z" 52)(*>*) where "\<phi> \<or>\<^sup>z \<psi> \<equiv> (\<not>\<^sup>z\<phi> \<rightarrow>\<^sup>z \<psi>)"
abbreviation z_equiv::"io opt\<Rightarrow>io opt\<Rightarrow>io opt"(*<*)(infixr "\<equiv>\<^sup>z" 52)(*>*) where "\<phi> \<equiv>\<^sup>z \<psi> \<equiv> (\<phi> \<rightarrow>\<^sup>z \<psi>) \<and>\<^sup>z (\<psi> \<rightarrow>\<^sup>z \<phi>)"
abbreviation z_exists::"('a\<Rightarrow>io opt)\<Rightarrow>io opt"(*<*)("\<exists>")(*>*) where "\<exists> \<Phi> \<equiv> case (\<Phi> dA) of
    PropForm \<phi> \<Rightarrow> PropForm (\<lambda>w. \<exists>x. case (\<Phi> x) of PropForm \<psi> \<Rightarrow> \<psi> w)
  | Form \<phi> \<Rightarrow> Form (\<lambda>w. \<exists>x. case (\<Phi> x) of Form \<psi> \<Rightarrow> \<psi> w)
  | _ \<Rightarrow> Error dIO"
abbreviation z_dia::"io opt\<Rightarrow>io opt"(*<*)("\<diamond>\<^sup>r_")(*>*) where "\<diamond>\<^sup>r \<phi> \<equiv> \<not>\<^sup>z \<box>\<^sup>r (\<not>\<^sup>z \<phi>)"

(* abbreviation z_true::"io opt"(*<*)("\<top>\<^sup>z")(*>*) where "\<top>\<^sup>z \<equiv> todo; not entirely clear yet " *)
(* abbreviation z_false::"io opt"(*<*)("\<bottom>\<^sup>z")(*>*) where "\<bottom>\<^sup>z \<equiv> todo; not entirely clear yet " *)


section {* Some shorthands for the constructors *}

abbreviation mkPropForm ::  "io\<Rightarrow>io opt"(*<*)(",_,")(*>*)  where ",p, \<equiv> PropForm p" 
abbreviation mkForm ::  "io\<Rightarrow>io opt"(*<*)(";_;")(*>*)  where ";p; \<equiv> Form p" 
abbreviation mkTerm ::  "'a\<Rightarrow>'a opt"(*<*)("._.")(*>*)  where ".t. \<equiv> Term t" 



section {* Some basic tests *}


text {* An example signature; entities and relations *}

consts a_0 :: "e" abbreviation a  where "a \<equiv> .a_0."
consts b_0 :: "e" abbreviation b  where "b \<equiv> .b_0."
consts c_0 :: "e" abbreviation c  where "c \<equiv> .c_0."

consts R_0 :: "io"  abbreviation R0  where "R0 \<equiv> .R_0."
consts R_1 :: "e\<Rightarrow>io" abbreviation R1  where "R1 \<equiv> .R_1."
consts R_2 :: "e\<Rightarrow>e\<Rightarrow>io" abbreviation R2  where "R2 \<equiv> .R_2."
consts R_3 :: "e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io"  abbreviation R3  where "R3 \<equiv> .R_3."


text {* Testing some term and formula constructions *}

lemma "[<R1\<bullet>a>]" nitpick oops
lemma "isPropForm <R1\<bullet>a>" apply (simp) done
lemma "<R1\<bullet>a> = X" apply (simp) oops

lemma "[<a\<circ>R1>]" nitpick oops
lemma "isPropForm <a\<circ>R1>" apply (simp) oops
lemma "isForm <a\<circ>R1>" apply (simp) done
lemma "<a\<circ>R1> = X" apply (simp) oops

lemma "[<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <R1\<bullet>.x.>)\<bullet>a>]" apply (simp) done
lemma "<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <R1\<bullet>.x.>)\<bullet>a> = X" apply (simp) oops

lemma "\<not> isWff (<R1\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>R1>)" apply (simp) done
lemma "\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>R1>) = X" apply (simp) oops

lemma "[<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>R1>)\<bullet>a>]" apply (simp) oops
lemma "<\<lambda>\<^sup>1(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>R1>)\<bullet>a> = X" apply (simp) oops

lemma "[\<forall>(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <R1\<bullet>.x.>)]" apply (simp) done
lemma "[\<forall>(\<lambda>R. \<forall>(\<lambda>x. <.R.\<bullet>.x.> \<rightarrow>\<^sup>z <.R.\<bullet>.x.>))]" apply (simp) done
lemma "\<forall>(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <R1\<bullet>.x.>) = X" apply (simp) oops

lemma "[\<forall>(\<lambda>x. <.x.\<circ>R1> \<rightarrow>\<^sup>z <.x.\<circ>R1>)]" apply (simp) done
lemma "\<forall>(\<lambda>x. <.x.\<circ>R1> \<rightarrow>\<^sup>z <.x.\<circ>R1>) = X" apply (simp) oops

lemma "[\<forall>(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>R1>)]" apply (simp) oops
lemma "\<forall>(\<lambda>x. <R1\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>R1>) = X" apply (simp) oops
lemma "[\<forall>(\<lambda>R. <.R.\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>.R.>)]" apply (simp) oops
lemma "\<forall>(\<lambda>R. <.R.\<bullet>.x.> \<rightarrow>\<^sup>z <.x.\<circ>.R.>) = X" apply (simp) oops


section {* Get the priorities right *}

lemma ",\<phi>, \<and>\<^sup>z ,\<psi>, \<rightarrow>\<^sup>z ,\<chi>, \<equiv> (,\<phi>, \<and>\<^sup>z ,\<psi>,) \<rightarrow>\<^sup>z ,\<chi>," apply (simp) done
lemma ",\<phi>, \<and>\<^sup>z ,\<psi>, \<rightarrow>\<^sup>z ,\<chi>, \<equiv> ,\<phi>, \<and>\<^sup>z (,\<psi>, \<rightarrow>\<^sup>z ,\<chi>,)" apply (simp) nitpick oops

lemma "(,\<phi>, \<and>\<^sup>z ,\<psi>, \<equiv>\<^sup>z ,\<phi>, \<and>\<^sup>z ,\<psi>,) \<equiv> ((,\<phi>, \<and>\<^sup>z ,\<psi>,) \<equiv>\<^sup>z (,\<phi>, \<and>\<^sup>z ,\<psi>,))" apply (simp) done
lemma "(,\<phi>, \<and>\<^sup>z ,\<psi>, \<equiv>\<^sup>z ,\<phi>, \<and>\<^sup>z ,\<psi>,) \<equiv> (,\<phi>, \<and>\<^sup>z (,\<psi>, \<equiv>\<^sup>z ,\<phi>,) \<and>\<^sup>z ,\<psi>,)" apply (simp) nitpick oops


section {* E!, O!, A! and =E *}

consts E::"(e\<Rightarrow>io)"
text {* Distinguished 1-place Relation Constant: E! (read: ‘being concrete’ or ‘concreteness’) *}


abbreviation z_ordinary::"(e\<Rightarrow>io) opt"(*<*)("O\<^sup>!")(*>*) where "O\<^sup>! \<equiv> \<lambda>\<^sup>1(\<lambda>x. \<diamond>\<^sup>r <.E.\<bullet>.x.>)"
text {* Being ordinary is being possibly concrete. *}
text {* Question: is the term above a Form or a PropForm? *}

abbreviation z_abstract::"(e\<Rightarrow>io) opt"(*<*)("A\<^sup>!")(*>*) where "A\<^sup>! \<equiv> \<lambda>\<^sup>1(\<lambda>x. \<not>\<^sup>z \<diamond>\<^sup>r <.E.\<bullet>.x.>)"
text {* Being abstract is not possibly being concrete. *}
text {* Question: is the term above a Form or a PropForm? *}


abbreviation z_identity::"(e\<Rightarrow>e\<Rightarrow>io) opt"(*<*)("=\<^sub>e\<^sup>z")(*>*) where "=\<^sub>e\<^sup>z \<equiv> 
  \<lambda>\<^sup>2(\<lambda>x y. ((<O\<^sup>!\<bullet>.x.> \<and>\<^sup>z <O\<^sup>!\<bullet>.y.>) \<and>\<^sup>z \<box>\<^sup>r (\<forall>(\<lambda>F. <.F.\<bullet>.x.> \<equiv>\<^sup>z <.F.\<bullet>.y.>))))"

abbreviation z_identityE::"(e opt\<Rightarrow>e opt\<Rightarrow>io opt)"(*<*)(infixr "=\<^sub>E" 63)(*>*) where "x =\<^sub>E y \<equiv> (Exe2 =\<^sub>e\<^sup>z x y)" 



section {* Some further examples *}

lemma "[\<forall>(\<lambda>x. \<exists>(\<lambda>R. (<.x.\<circ>.R.> \<rightarrow>\<^sup>z <.x.\<circ>R1>)))]" apply (simp) by auto
lemma "[\<forall>(\<lambda>x. \<forall>(\<lambda>R. (<.x.\<circ>.R.> \<rightarrow>\<^sup>z <.x.\<circ>R1>)))]" apply (simp) nitpick oops

lemma "[a =\<^sub>E a]" apply (simp) nitpick oops

lemma "[<O\<^sup>!\<bullet>a> \<rightarrow>\<^sup>z a =\<^sub>E a]" apply (simp) done

lemma "[(\<forall>(\<lambda>F. <.F.\<bullet>.x.> \<equiv>\<^sup>z <.F.\<bullet>.x.>))]" apply (simp) done
lemma "[<O\<^sup>!\<bullet>a> \<rightarrow>\<^sup>z <\<lambda>\<^sup>1(\<lambda>x. .x. =\<^sub>E a)\<bullet>a>]" apply (simp) done

lemma "[(\<exists>(\<lambda>F. <a\<circ>.F.>))]" apply (simp) by auto

lemma "isWff ,(\<lambda>w. True)," apply (simp) done

lemma "[(\<exists>(\<lambda>F. ,F,))]" apply (simp) by auto
lemma "[(\<exists>(\<lambda>F. ;F;))]" apply (simp) by auto

(*<*) 
end
(*>*)

