theory FunctorsInCategoryTheory_Const_f imports Main
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

text {* Equality *}
abbreviation KlEq (infixr "\<cong>" 56) -- {* Kleene equality *} where "x \<cong> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x = y"  
abbreviation ExId (infixr "\<simeq>" 56) -- {* Existing identity *}  where "x \<simeq> y \<equiv> E x \<^bold>\<and> E y \<^bold>\<and> x = y"


(*
consts fIn::"i\<Rightarrow>i\<Rightarrow>bool" (infix "in" 70)
consts fAbstr::"(i\<Rightarrow>bool)\<Rightarrow>i"  
abbreviation fAbstrBinder (binder "abstr" [8]9)                     
 where "abstr x. \<phi> x \<equiv> fAbstr \<phi>"

axiomatization where
  Str:  "x in y \<^bold>\<rightarrow> E x" and
  Extn: "(\<^bold>\<forall>x. x in y \<^bold>\<leftrightarrow> x in z) \<^bold>\<rightarrow> y = z" and
  Abst: "y in (abstr x. \<Phi> x) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. x \<cong> y \<^bold>\<and> \<Phi> x)" and
  Extn': "(abstr x. \<Phi> x) = (abstr x. \<Psi> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. \<Phi> x \<^bold>\<leftrightarrow> \<Psi> x)"   
abbreviation isClass where "isClass \<Phi> \<equiv> \<Phi> = (abstr x. \<Phi> x)"
*)


section {* Preliminaries *}

consts 
 domain:: "i\<Rightarrow>i" ("dom _" [108] 109) 
 codomain:: "i\<Rightarrow>i" ("cod _" [110] 111) 
 composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

abbreviation I where "I i \<equiv> (\<^bold>\<forall>x. E(i\<cdot>x) \<^bold>\<rightarrow> i\<cdot>x \<cong> x) \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>i) \<^bold>\<rightarrow> x\<cdot>i \<cong> x)"


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
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
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
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops

 lemma CodInteractive: "(cod (f x)) \<cong> (f (cod x))"
  proof -
   have 2: "(cod x)\<cdot>x \<cong> x" using S6 by blast
   have 3: "(f (cod x))\<cdot>(f x) \<cong> (f x)" by (metis 2 Comp S2 S3 Str)
   have 4: "I(cod x)" by (smt S2 S3 S5 S6)
   have 5: "I(f (cod x))" by (metis 4 S1 S2 S3 Str Iden) 
   then show ?thesis by (metis 3 5 S1 S2 S3 S5 Str Tot)
  qed

 lemma Cod: "(cod (f x)) \<cong> (f (cod x))" by (smt Comp S2 S3 S5 S6 Str Tot Iden)
 lemma Dom: "(dom (f x)) \<cong> (f (dom x))" by (smt Comp S1 S3 S5 S6 Str Tot Iden)
 lemma CoDo: "((cod (f x)) \<cong> (f (cod x))) \<^bold>\<and> ((dom (f x)) \<cong> (f (dom x)))" using Cod Dom by blast 
end 


consts A::"i\<Rightarrow>bool" B::"i\<Rightarrow>bool" 
abbreviation Equi (infix "\<^bold>=\<^bold>=" 56) where "x \<^bold>=\<^bold>= y \<equiv>  ((A x \<^bold>\<and> x \<cong> y) \<^bold>\<rightarrow> A y) \<^bold>\<and> ((B x \<^bold>\<and> x \<cong> y) \<^bold>\<rightarrow> B y)"
abbreviation IA where "IA i \<equiv> (\<^bold>\<forall>x. A(i\<cdot>x) \<^bold>\<rightarrow> i\<cdot>x \<cong> x) \<^bold>\<and> (\<^bold>\<forall>x. A(x\<cdot>i) \<^bold>\<rightarrow> x\<cdot>i \<cong> x)"
abbreviation IB where "IB i \<equiv> (\<^bold>\<forall>x. B(i\<cdot>x) \<^bold>\<rightarrow> i\<cdot>x \<cong> x) \<^bold>\<and> (\<^bold>\<forall>x. B(x\<cdot>i) \<^bold>\<rightarrow> x\<cdot>i \<cong> x)"

context -- {* S-Axioms; extended by functor *}
assumes 
 Disj: "(A x \<^bold>\<rightarrow> E x) \<^bold>\<and> (B x \<^bold>\<rightarrow> E x) \<^bold>\<and> (A x \<^bold>\<rightarrow> \<^bold>\<not>(B x))" and
 SA: "(A(x\<cdot>y) \<^bold>\<rightarrow> (A x \<^bold>\<and> A y)) \<^bold>\<and> (A(dom x ) \<^bold>\<rightarrow> A x) \<^bold>\<and> (A(cod y) \<^bold>\<rightarrow> A y)" and
 SB: "(B(x\<cdot>y) \<^bold>\<rightarrow> (B x \<^bold>\<and> B y)) \<^bold>\<and> (B(dom x ) \<^bold>\<rightarrow> B x) \<^bold>\<and> (B(cod y) \<^bold>\<rightarrow> B y)" and
 EA: "A(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>=\<^bold>= cod y \<^bold>\<and> A(cod x))" and
 EB: "B(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>=\<^bold>= cod y \<^bold>\<and> B(cod x))" and
(* A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and — is implied by Disj, see below *) 
(* C: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and — is implied by Disj, see below *)
(* D: "(cod y)\<cdot>y \<^bold>=\<^bold>= y" — is implied by Disj, see below *) 
 Map: "A x \<^bold>\<leftrightarrow> B (f x)" and
 CompAB: "A(x\<cdot>y) \<^bold>\<rightarrow> f(x\<cdot>y) \<^bold>=\<^bold>= f(x)\<cdot>f(y)" and
 IdenAB: "(A x \<^bold>\<and> IA x) \<^bold>\<rightarrow> IB (f x)"
begin
  (* Various forms of consistency *)
  lemma True  -- {* Nitpick finds a model *}
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<and> (\<exists>x. A x) \<^bold>\<and> (\<exists>x. B x)" shows True   -- {* Nitpick finds a model *}  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  (* A and B are disjunct *)
  lemma Disj': "\<^bold>\<not>(A x \<^bold>\<and> B x)" using Disj by blast 
  (* A, C, D are implied by Disj *)
  lemma A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using Disj by auto
  lemma C: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" using Disj by auto
  lemma D: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" using Disj by auto  
  (* Proving A-/B-copies of the axioms from Axiom Set III *)
  lemma S\<^sub>i\<^sub>i\<^sub>iA: "(A(x\<cdot>y) \<^bold>\<rightarrow> (A x \<^bold>\<and> A y)) \<^bold>\<and> (A(dom x ) \<^bold>\<rightarrow> A x) \<^bold>\<and> (A(cod y) \<^bold>\<rightarrow> A y)" using SA by blast
  lemma S\<^sub>i\<^sub>i\<^sub>iB: "(B(x\<cdot>y) \<^bold>\<rightarrow> (B x \<^bold>\<and> B y)) \<^bold>\<and> (B(dom x ) \<^bold>\<rightarrow> B x) \<^bold>\<and> (B(cod y) \<^bold>\<rightarrow> B y)" using SB by blast
  lemma E\<^sub>i\<^sub>i\<^sub>iA: "A(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<^bold>=\<^bold>= cod y \<^bold>\<and> A(cod y))" by (metis Disj EA SA) 
  lemma E\<^sub>i\<^sub>i\<^sub>iB: "B(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<^bold>=\<^bold>= cod y \<^bold>\<and> B(cod y))" by (metis Disj EB SB) 
  lemma A\<^sub>i\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using Disj by auto
  lemma C\<^sub>i\<^sub>i\<^sub>iA:  "A y \<^bold>\<rightarrow> (IA(cod y) \<^bold>\<and> (cod y)\<cdot>y \<^bold>=\<^bold>= y)" by (metis Disj EA Map SA)
  lemma C\<^sub>i\<^sub>i\<^sub>iB:  "B y \<^bold>\<rightarrow> (IB(cod y) \<^bold>\<and> (cod y)\<cdot>y \<^bold>=\<^bold>= y)" by (metis Disj EB Map SB)
  lemma D\<^sub>i\<^sub>i\<^sub>iA: "A x \<^bold>\<rightarrow> (IA(dom x) \<^bold>\<and> x\<cdot>(dom x) \<^bold>=\<^bold>= x)" by (metis Disj EA Map SA)
  lemma D\<^sub>i\<^sub>i\<^sub>iB: "B x \<^bold>\<rightarrow> (IB(dom x) \<^bold>\<and> x\<cdot>(dom x) \<^bold>=\<^bold>= x)"  by (metis Disj EB Map SB)
  (* Proving A-/B-copies of the axioms from Axiom Set II *)
  lemma S\<^sub>i\<^sub>iA: "(A(x\<cdot>y) \<^bold>\<rightarrow> (A x \<^bold>\<and> A y)) \<^bold>\<and> (A(dom x) \<^bold>\<rightarrow> A x) \<^bold>\<and> (A(cod y) \<^bold>\<rightarrow> A y)" using SA by blast
  lemma S\<^sub>i\<^sub>iB: "(B(x\<cdot>y) \<^bold>\<rightarrow> (B x \<^bold>\<and> B y)) \<^bold>\<and> (B(dom x) \<^bold>\<rightarrow> B x) \<^bold>\<and> (B(cod y) \<^bold>\<rightarrow> B y)" using SB by blast
  lemma E\<^sub>i\<^sub>iA:  "A(x\<cdot>y) \<^bold>\<leftarrow> (A x \<^bold>\<and> A y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))" nitpick  [show_all, format = 2, card = 3] sorry (* Countermodel *) 
  lemma E\<^sub>i\<^sub>iB:  "A(x\<cdot>y) \<^bold>\<leftarrow> (B x \<^bold>\<and> B y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))" nitpick  [show_all, format = 2, card = 3] sorry (* Countermodel *)
  lemma C\<^sub>i\<^sub>iA: "A y \<^bold>\<rightarrow> (IA(cod y) \<^bold>\<and> (cod y)\<cdot>y \<^bold>=\<^bold>= y)" by (metis Disj EA Map SA) 
  lemma C\<^sub>i\<^sub>iB: "B y \<^bold>\<rightarrow> (IB(cod y) \<^bold>\<and> (cod y)\<cdot>y \<^bold>=\<^bold>= y)" by (metis Disj EB Map SB)  
  lemma D\<^sub>i\<^sub>iA: "A x \<^bold>\<rightarrow> (IA(dom x) \<^bold>\<and> x\<cdot>(dom x) \<^bold>=\<^bold>= x)" by (metis Disj EA Map SA)
  lemma D\<^sub>i\<^sub>iB: "B x \<^bold>\<rightarrow> (IB(dom x) \<^bold>\<and> x\<cdot>(dom x) \<^bold>=\<^bold>= x)" by (metis Disj EB Map SB)  


 declare [[ smt_solver = cvc4, smt_timeout = 300]]

 lemma  C\<^sub>iA: "\<^bold>\<forall>y.\<^bold>\<exists>i. IA i \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y" by (smt Disj Map SA)
 lemma  C\<^sub>iB: "\<^bold>\<forall>y.\<^bold>\<exists>i. IB i \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y" (* by (smt  Disj Map SB) timeout *) sorry
 lemma  D\<^sub>iA: "\<^bold>\<forall>x.\<^bold>\<exists>j. IA j \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x" by (smt Disj Map SA) 
 lemma  D\<^sub>iB: "\<^bold>\<forall>x.\<^bold>\<exists>j. IB j \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x" (* by (smt Disj Map SB)  timeout *) sorry

end 


text {* Definite Description *}
                                   
consts fThe::"(i\<Rightarrow>bool) \<Rightarrow> i"
abbreviation fTheBinder (binder "the" [8]9)                     
 where "the x. \<phi> x \<equiv> fThe \<phi>"
axiomatization where 
  Desc: "y \<cong> (the x. \<Phi> x) \<^bold>\<leftrightarrow> (E y \<^bold>\<rightarrow> (\<^bold>\<forall>x. (\<Phi> x \<^bold>\<leftrightarrow> x \<cong> y)))"


text {* Virtual Classes *}

consts fIn::"i\<Rightarrow>i\<Rightarrow>bool" (infix "in" 70)
consts fAbstr::"(i\<Rightarrow>bool)\<Rightarrow>i"  
abbreviation fAbstrBinder (binder "abstr" [8]9)                     
 where "abstr x. \<phi> x \<equiv> fAbstr \<phi>"

axiomatization where
  Str:  "x in y \<^bold>\<rightarrow> E x" and
(*  Extn: "(\<^bold>\<forall>x. x in y \<^bold>\<leftrightarrow> x in z) \<^bold>\<rightarrow> y = z" and *)
  Abst: "y in (abstr x. \<Phi> x) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. x \<cong> y \<^bold>\<and> \<Phi> x)" and 
  Extn': "(abstr x. \<Phi> x) = (abstr x. \<Psi> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. \<Phi> x \<^bold>\<leftrightarrow> \<Psi> x)" 

abbreviation isClass where "isClass \<Phi> \<equiv> \<Phi> = (abstr x. x in \<Phi>)"

axiomatization where
  Set: "\<^bold>\<forall>y. isClass y" 

lemma True  -- {* Nitpick finds a model *}
  nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
  nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops




(*<*)
end
(*>*)


