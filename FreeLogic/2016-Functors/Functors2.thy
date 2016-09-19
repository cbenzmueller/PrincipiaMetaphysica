theory Functors2 imports Main
begin 

declare [[ smt_solver = cvc4]]


abbreviation fNot ("\<^bold>\<not>") --{* Free negation *}                          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies (infixr "\<^bold>\<rightarrow>" 13) --{* Free implication *}        
 where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
abbreviation fForall ("\<^bold>\<forall>") 
  --{* Free universal quantification guarded by a set S *}                  
 where "\<^bold>\<forall> S \<Phi> \<equiv> \<forall>x. S x \<longrightarrow> \<Phi> x"   


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
  --{* Free universal quantification guarded by a set S *}                  
 where "\<^bold>\<exists> S \<Phi> \<equiv> \<exists>x. S x \<^bold>\<and> \<Phi> x"   


text {* Equality for sets E, A and B *}
abbreviation KlEqSet -- {* Kleene equality on Set *} 
  where "KlEqSet Set x y \<equiv> (Set x \<^bold>\<or> Set y) \<^bold>\<rightarrow> x = y"  
abbreviation ExIdSet -- {* Existing identity on Set *}  
  where "ExIdSet Set x y \<equiv> Set x \<^bold>\<and> Set y \<^bold>\<and> x = y"

abbreviation KlEq ("_\<cong>\<^sup>__") -- {* Kleene equality E *} where "x \<cong>\<^sup>S y \<equiv> KlEqSet S x y"  
abbreviation ExId ("_\<simeq>\<^sup>__") -- {* Existing identity E *}  where "x \<simeq>\<^sup>S y \<equiv> ExIdSet S x y"

consts 
 domain::"'a\<Rightarrow>'a" ("dom _" [108] 109) 
 codomain:: "'a\<Rightarrow>'a" ("cod _" [110] 111) 
 composition:: "'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110)



abbreviation ID where "ID S i \<equiv> (\<^bold>\<forall> S (\<lambda>x. S(i\<cdot>x) \<^bold>\<rightarrow> ((i\<cdot>x) \<cong>\<^sup>S x)) \<^bold>\<and> (\<^bold>\<forall> S (\<lambda>x. S(x\<cdot>i) \<^bold>\<rightarrow> ((x\<cdot>i) \<cong>\<^sup>S x))))"

abbreviation I ("I\<^sup>__") where "I\<^sup>S i \<equiv> ID S i"


definition CATEGORY 
  where "CATEGORY \<equiv> \<lambda>S.
   ((\<forall>x. (S(dom x) \<^bold>\<rightarrow> S x)) \<^bold>\<and>
    (\<forall>y. S(cod y) \<^bold>\<rightarrow> S y) \<^bold>\<and>
    (\<forall>x y. S(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>\<^sup>S (cod y))) \<^bold>\<and>
    (\<forall>x y z. ((x\<cdot>(y\<cdot>z)) \<cong>\<^sup>S ((x\<cdot>y)\<cdot>z))) \<^bold>\<and>
    (\<forall>x. ((x\<cdot>(dom x)) \<cong>\<^sup>S x)) \<^bold>\<and>
    (\<forall>y. (((cod y)\<cdot>y) \<cong>\<^sup>S y)))"

definition SUBCATEGORY  
  where "SUBCATEGORY \<equiv> \<lambda>A S. 
   (CATEGORY S \<^bold>\<and> 
    (\<forall>x. A(dom x) \<^bold>\<leftrightarrow> A x) \<^bold>\<and> 
    (\<forall>x. A(cod x) \<^bold>\<leftrightarrow> A x) \<^bold>\<and>
    (\<forall>x. A x \<^bold>\<rightarrow> S x))"

abbreviation CAT_E ("CAT\<^sup>__")
  where "CAT\<^sup>S A \<equiv> SUBCATEGORY A S"

definition FUNCTOR
  where "FUNCTOR \<equiv> \<lambda>A f B E.
   ((CAT\<^sup>E A) \<^bold>\<and>
    (CAT\<^sup>E B) \<^bold>\<and>
    (\<forall>x. B(f x) \<^bold>\<rightarrow> A x) \<^bold>\<and>
    (\<forall>x. A x \<^bold>\<rightarrow> B(f x)) \<^bold>\<and>
    (\<forall>x::'a. \<forall>y::'a. A(x\<cdot>y) \<^bold>\<rightarrow> ((f(x\<cdot>y)) \<cong>\<^sup>B ((f x)\<cdot>(f y)))) \<^bold>\<and>
    (\<forall>x::'a. \<forall>y::'a. ((A x) \<^bold>\<and> (I\<^sup>A x)) \<^bold>\<rightarrow> I\<^sup>B(f x)))"
    

typedecl i
consts A:: "i\<Rightarrow>bool" --{* A *}
consts B:: "i\<Rightarrow>bool" --{* B *}

consts E:: "i\<Rightarrow>bool" --{* Existence/definedness predicate in free logic *}

consts 
 f::"i\<Rightarrow>i"  -- {* Functor f *}

axiomatization
  where  1: "FUNCTOR A f B E"

  lemma True  -- {* Nitpick finds a model *}
  nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   -- {* Nitpick finds a model *}  
  nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops

  lemma 2: "CAT\<^sup>E A" using 1 unfolding FUNCTOR_def by blast
  lemma 3: "CAT\<^sup>E B" using 1 unfolding FUNCTOR_def by blast
  lemma 4: "CATEGORY E" using 1 unfolding FUNCTOR_def SUBCATEGORY_def by blast
  lemma 5: "CATEGORY A" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by smt
  lemma 6: "CATEGORY B" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by smt

  lemma (*S1E:*) "E(dom x) \<^bold>\<rightarrow> E x" using 4 unfolding CATEGORY_def by blast 
  lemma (*S2E:*) "E(cod y) \<^bold>\<rightarrow> E y" using 4 unfolding CATEGORY_def by blast 
  lemma (*S3E:*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>\<^sup>E (cod y))" using 4 unfolding CATEGORY_def by blast 
  lemma (*S4E:*) "(x\<cdot>(y\<cdot>z)) \<cong>\<^sup>E ((x\<cdot>y)\<cdot>z)" using 4 unfolding CATEGORY_def by blast 
  lemma (*S5E:*) "(x\<cdot>(dom x)) \<cong>\<^sup>E x" using 4 unfolding CATEGORY_def by blast 
  lemma (*S6E:*) "((cod y)\<cdot>y) \<cong>\<^sup>E y" using 4 unfolding CATEGORY_def by blast 

  lemma (*S1A:*) "A(dom x) \<^bold>\<rightarrow> A x" using 5 unfolding CATEGORY_def by blast 
  lemma (*S2A:*) "A(cod y) \<^bold>\<rightarrow> A y" using 5 unfolding CATEGORY_def by blast
  lemma (*S3A:*) "A(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>\<^sup>A (cod y))" using 5 unfolding CATEGORY_def by blast
  lemma (*S4A:*) "(x\<cdot>(y\<cdot>z)) \<cong>\<^sup>A ((x\<cdot>y)\<cdot>z)" using 5 unfolding CATEGORY_def by blast  
  lemma (*S5A:*) "(x\<cdot>(y\<cdot>z)) \<cong>\<^sup>A ((x\<cdot>y)\<cdot>z)" using 5 unfolding CATEGORY_def by blast 
  lemma (*S6A:*) "((cod y)\<cdot>y) \<cong>\<^sup>A y" using 5 unfolding CATEGORY_def by blast 

  lemma (*S1B:*) "B(dom x) \<^bold>\<rightarrow> B x" using 6 unfolding CATEGORY_def by blast
  lemma (*S2B:*) "B(cod y) \<^bold>\<rightarrow> B y" using 6 unfolding CATEGORY_def by blast
  lemma (*S3B:*) "B(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>\<^sup>B (cod y))" using 6 unfolding CATEGORY_def by blast
  lemma (*S4B:*) "(x\<cdot>(y\<cdot>z)) \<cong>\<^sup>B ((x\<cdot>y)\<cdot>z)" using 6 unfolding CATEGORY_def by blast
  lemma (*S5B:*) "(x\<cdot>(dom x)) \<cong>\<^sup>B x" using 6 unfolding CATEGORY_def by blast
  lemma (*S6B:*) "((cod y)\<cdot>y) \<cong>\<^sup>B y" using 6 unfolding CATEGORY_def by blast




lemma "CATEGORY (\<lambda>S::i\<Rightarrow>bool. CAT\<^sup>E S)" nitpick [user_axioms, show_all, format=3]







context -- {* Scott's Axiom Set V duplicated for sets E, A and B *}
assumes
(*>*)
 S1E: "E(dom x) \<^bold>\<rightarrow> E x" and
 S2E: "E(cod y) \<^bold>\<rightarrow> E y" and
 S3E: "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>\<^sup>E (cod y))" and
 S4E: "(x\<cdot>(y\<cdot>z)) \<cong>\<^sup>E ((x\<cdot>y)\<cdot>z)" and
 S5E: "(x\<cdot>(dom x)) \<cong>\<^sup>E x" and
 S6E: "((cod y)\<cdot>y) \<cong>\<^sup>E y" and

 STA1: "A(dom x) \<^bold>\<leftrightarrow> A x" and
 STA2: "A(cod x) \<^bold>\<leftrightarrow> A x" and

 STB1: "B(dom x) \<^bold>\<leftrightarrow> B x" and
 STB2: "B(cod y) \<^bold>\<leftrightarrow> B y" and

 ABE: "(A x \<^bold>\<rightarrow> E x) \<^bold>\<and> (B x \<^bold>\<rightarrow> E x)" and  -- {* this is not needed as it seems *} 
 Str:  "B(f x) \<^bold>\<rightarrow> A x" and
 Tot:  "A x \<^bold>\<rightarrow> B(f x)" and
 Comp: "A(x\<cdot>y) \<^bold>\<rightarrow> ((f(x\<cdot>y)) \<cong>\<^sup>B ((f x)\<cdot>(f y)))" and
 Iden: "((A x) \<^bold>\<and> (IA x)) \<^bold>\<rightarrow> IB(f x)"
begin

(*<*)
end
(*>*)


