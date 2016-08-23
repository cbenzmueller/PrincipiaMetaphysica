theory FunctorsInCategoryTheory_Var_f imports Main
begin 

section {* Embedding of Free Logic in HOL *}

typedecl i -- {* Type for individuals *}
consts fExistence:: "i\<Rightarrow>bool" ("E") --{* Existence/definedness predicate in free logic *}

abbreviation fNot ("\<^bold>\<not>") --{* Free negation *}                          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies (infixr "\<^bold>\<rightarrow>" 13) --{* Free implication *}        
 where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
abbreviation fForall ("\<^bold>\<forall>") --{* Free universal quantification is guarded by existence predicate @{text "E"}*}                  
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

section {* Preliminaries *}

consts 
 domain:: "i\<Rightarrow>i" ("dom _" [108] 109) 
 codomain:: "i\<Rightarrow>i" ("cod _" [110] 111) 
 composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

abbreviation KlEq (infixr "\<cong>" 56) -- {* Kleene equality *}
 where "x \<cong> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x = y"  
abbreviation ExId (infixr "\<simeq>" 56) -- {* Existing identity *}  
 where "x \<simeq> y \<equiv> E x \<^bold>\<and> E y \<^bold>\<and> x = y"
abbreviation I where "I i \<equiv> (\<^bold>\<forall>x. E(i\<cdot>x) \<^bold>\<rightarrow> i\<cdot>x \<cong> x) \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>i) \<^bold>\<rightarrow> x\<cdot>i \<cong> x)"

section {* Functors *}

(* consts f::"i\<Rightarrow>i" *)

context -- {* S-Axioms; extended by functor *}
assumes 
 S1: "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: "x\<cdot>(dom x) \<cong> x" and
 S6: "(cod y)\<cdot>y \<cong> y" and

 Str:  "E(f x) \<^bold>\<rightarrow> E x" and
 Tot:  "E x \<^bold>\<rightarrow> E(f x)" and
 Comp: "E(x\<cdot>y) \<^bold>\<rightarrow> f(x\<cdot>y) \<cong> (f x)\<cdot>(f y)"
begin
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops

 lemma Iden: "((E x) \<^bold>\<and> (I x)) \<^bold>\<rightarrow> I(f x)"  -- {* Countermodel by Nitpick *} 
   sledgehammer [remote_leo2 remote_satallax](S1 S2 S3 S5 S6 Str Tot Comp)
   nitpick [user_axioms, show_all, format = 2, card = 6] sorry
 
end 

declare [[ smt_solver = cvc4]]

context -- {* S-Axioms; extended by functor *}
assumes 
 S1: "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: "x\<cdot>(dom x) \<cong> x" and
 S6: "(cod y)\<cdot>y \<cong> y" and

 Str:  "E(f x) \<^bold>\<rightarrow> E x" and
 Tot:  "E x \<^bold>\<rightarrow> E(f x)" and
 Comp: "E(x\<cdot>y) \<^bold>\<rightarrow> f(x\<cdot>y) \<cong> (f x)\<cdot>(f y)" and
 Iden: "((E x) \<^bold>\<and> (I x)) \<^bold>\<rightarrow> I(f x)"
begin
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops

 lemma Cod_free_f: "(cod (f x)) \<cong> (f (cod x))" 
   by (metis S3 S5 S6 Tot Iden)
 lemma Dom_free_f: "(dom (f x)) \<cong> (f (dom x))" 
   by (smt Comp S1 S3 S5 S6 Str Tot Iden)
 lemma CoDo_free_f: "((cod (f x)) \<cong> (f (cod x))) \<^bold>\<and> ((dom (f x)) \<cong> (f (dom x)))"
   using Cod_free_f Dom_free_f by blast 
end 

section {* Functors *}

consts f::"i\<Rightarrow>i" 

context -- {* S-Axioms; extended by functor *}
assumes 
 S1: "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: "x\<cdot>(dom x) \<cong> x" and
 S6: "(cod y)\<cdot>y \<cong> y" and

 Str:  "E(f x) \<^bold>\<rightarrow> E x" and
 Tot:  "E x \<^bold>\<rightarrow> E(f x)" and
 Comp: "E(x\<cdot>y) \<^bold>\<rightarrow> f(x\<cdot>y) \<cong> (f x)\<cdot>(f y)"
begin
 lemma Iden_free_f: "((E x) \<^bold>\<and> (I x)) \<^bold>\<rightarrow> I(f x)"  -- {* Countermodel by Nitpick *} 
   nitpick [user_axioms, show_all, format = 2, card = 2] sorry
 (* Nitpick found a counterexample for card i = 2:
  Free variable:
    x = i\<^sub>1
  Skolem constants:
    x = i\<^sub>1
    x = i\<^sub>1
  Constants:
    codomain = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>1, i\<^sub>2 := i\<^sub>1)
    op \<cdot> = (\<lambda>x. _)((i\<^sub>1, i\<^sub>1) := i\<^sub>1, (i\<^sub>1, i\<^sub>2) := i\<^sub>2, (i\<^sub>2, i\<^sub>1) := i\<^sub>2, (i\<^sub>2, i\<^sub>2) := i\<^sub>2)
    domain = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>1, i\<^sub>2 := i\<^sub>1)
    f = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>2, i\<^sub>2 := i\<^sub>2)
    E = (\<lambda>x. _)(i\<^sub>1 := True, i\<^sub>2 := True)  *)
end 


declare [[ smt_solver = cvc4]]

context -- {* S-Axioms; extended by functor *}
assumes 
 S1: "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: "x\<cdot>(dom x) \<cong> x" and
 S6: "(cod y)\<cdot>y \<cong> y" and

 Str:  "E(f x) \<^bold>\<rightarrow> E x" and
 Tot:  "E x \<^bold>\<rightarrow> E(f x)" and
 Comp: "E(x\<cdot>y) \<^bold>\<rightarrow> f(x\<cdot>y) \<cong> (f x)\<cdot>(f y)" and
 Iden: "((E x) \<^bold>\<and> (I x)) \<^bold>\<rightarrow> I(f x)"
begin

 lemma CodInteractive: "(cod (f x)) \<cong> (f (cod x))"
    proof -
   have 2: "(cod x)\<cdot>x \<cong> x" using S6 by blast
   have 3: "(f (cod x))\<cdot>(f x) \<cong> (f x)" by (metis 2 Comp S2 S3 Str)
   have 4: "I(cod x)" by (smt S2 S3 S5 S6)
   have 5: "I(f (cod x))" nitpick by (metis 4 S1 S2 S3 Str Iden) 
   then show ?thesis by (metis 3 5 S1 S2 S3 S5 Str Tot)
  qed

 lemma Cod: "(cod (f x)) \<cong> (f (cod x))"
   by (smt Comp S2 S3 S5 S6 Str Tot Iden)
 lemma Dom: "(dom (f x)) \<cong> (f (dom x))" 
   by (smt Comp S1 S3 S5 S6 Str Tot Iden)
 lemma CoDo: "((cod (f x)) \<cong> (f (cod x))) \<^bold>\<and> ((dom (f x)) \<cong> (f (dom x)))"
   using Cod Dom by blast 
end 



(*
   proof -
   obtain a where 1: "(E a)" using assms by auto
   have 2: "(cod a)\<cdot>a \<cong> a" using S6 by blast
   have 3: "(f (cod a))\<cdot>(f a) \<cong> (f a)" by (metis "1" "2" Comp)
   have 4: "I(cod a)" by (metis (full_types) "1" S3 S5 S6)
   have 5: "I(f (cod a))" nitpick [user_axioms, show_all, format = 2, card = 2, timeout = 100]
   (*
  Free variables:
    a = i\<^sub>1
    x = i\<^sub>2
  Skolem constants:
    x = i\<^sub>2
    x = i\<^sub>2
  Constants:
    codomain = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>2, i\<^sub>2 := i\<^sub>2)
    op \<cdot> = (\<lambda>x. _)
           ((i\<^sub>1, i\<^sub>1) := i\<^sub>1, (i\<^sub>1, i\<^sub>2) := i\<^sub>1, (i\<^sub>2, i\<^sub>1) := i\<^sub>1, (i\<^sub>2, i\<^sub>2) := i\<^sub>2)
    domain = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>2, i\<^sub>2 := i\<^sub>2)
    f = (\<lambda>x. _)(i\<^sub>1 := i\<^sub>1, i\<^sub>2 := i\<^sub>1)
    E = (\<lambda>x. _)(i\<^sub>1 := True, i\<^sub>2 := True)
   *)
   sorry
   then show ?thesis sorry
  qed

begin
 lemma "((cod (f x)) \<cong> (f (cod x))) \<^bold>\<and> ((dom (f x)) \<cong> (f (dom x)))" 
 nitpick [user_axioms, show_all, format = 2]
  
end

*)


(*<*)
end
(*>*)


