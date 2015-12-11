(*<*) 
theory FreeHOL   
imports Main 

begin
(*>*)

typedecl \<iota>                -- "the type for indiviuals"   
type_synonym \<sigma> = "bool"   -- "the type for Booleans"   

consts  f_r  :: "\<iota> \<Rightarrow> \<iota> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>r" 70)(*>*) 
   
consts f_e :: "\<iota> \<Rightarrow> \<sigma>" (*<*)("\<^bold>e")(*>*)

consts f_star :: "\<iota>" (*<*)("\<^bold>\<star>")(*>*)

axiomatization where f_star_axiom: "\<not> \<^bold>e \<^bold>\<star>"


abbreviation f_not :: "\<sigma> \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<not> _" [58] 59)(*>*) 
  where "\<^bold>\<not> \<phi> \<equiv> \<not> \<phi>"    
abbreviation f_and :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<and>" 52)(*>*) 
  where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<phi> \<and> \<psi>"   
abbreviation f_or :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<or>" 51)(*>*) 
  where "\<phi> \<^bold>\<or> \<psi> \<equiv> \<phi> \<or> \<psi>"   
abbreviation f_implies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<rightarrow>" 49)(*>*) 
  where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"  
abbreviation f_equiv :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<leftrightarrow>" 50)(*>*) 
  where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> \<phi> \<longleftrightarrow> \<psi>"  
abbreviation f_equals :: "\<iota> \<Rightarrow> \<iota> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>=" 56)(*>*) 
  where "x \<^bold>= y \<equiv> x = y"
abbreviation f_forall :: "(\<iota> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<forall>")(*>*) 
  where "\<^bold>\<forall> \<Phi> \<equiv> \<forall>x. \<^bold>e x \<longrightarrow>  \<Phi> x"   
abbreviation f_forall_binder :: "(\<iota> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*) (binder "\<^bold>\<forall>" [8] 9) (*>*)
  where "\<^bold>\<forall> x. \<phi> x \<equiv> \<^bold>\<forall> \<phi>"
abbreviation f_mexists :: "(\<iota> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<exists>")(*>*) 
  where "\<^bold>\<exists> \<Phi> \<equiv> \<exists>x. \<^bold>e x \<and> \<Phi> x"
abbreviation f_exists_binder :: "(\<iota> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*) (binder "\<^bold>\<exists>" [8] 9) (*>*)
  where "\<^bold>\<exists> x. \<phi> x \<equiv> \<^bold>\<exists> \<phi>"
abbreviation f_that :: "(\<iota> \<Rightarrow> \<sigma>) \<Rightarrow> \<iota>" (*<*)("\<^bold>I")(*>*) 
  where "\<^bold>I \<Phi> \<equiv> if \<^bold>\<exists>(\<lambda>x. (\<Phi> x) \<and> \<^bold>\<forall>(\<lambda>y. (\<Phi> y) \<longrightarrow> (y = x))) then THE x. (\<Phi> x) else \<^bold>\<star>"
abbreviation f_that_binder :: "(\<iota> \<Rightarrow> \<sigma>) \<Rightarrow> \<iota>" (*<*) (binder "\<^bold>I" [8] 9) (*>*)
  where "\<^bold>I x. \<phi> x \<equiv> \<^bold>I \<phi>"

section {* Some Introductory Tests *} 

lemma "x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x" by simp
lemma "(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" nitpick oops
lemma "\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y" nitpick oops
lemma "((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> (\<^bold>\<exists>y. y \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" by simp


lemma "\<^bold>\<not>(\<^bold>\<exists>x. (x \<^bold>= (\<^bold>Iy. \<^bold>\<not> y \<^bold>= y)))" by (simp add: f_star_axiom) 


lemma "(\<^bold>\<exists>x. x \<^bold>= a) \<^bold>\<rightarrow>  \<^bold>e a" by simp


section {* Some Principles from Scott 1967 *}

consts a::\<iota> b::\<iota> 

axiomatization where ax1: "\<^bold>e a \<^bold>\<and> \<^bold>e b \<^bold>\<and> \<^bold>\<not> (a \<^bold>= b) \<^bold>\<and> \<^bold>\<not> (a \<^bold>=  \<^bold>\<star>) \<^bold>\<and> \<^bold>\<not> (b \<^bold>=  \<^bold>\<star>)"

lemma test: "\<^bold>\<star> \<^bold>= (\<^bold>I (\<lambda>x. x  \<^bold>= a \<^bold>\<or> x \<^bold>= b))" apply simp using ax1 by auto

lemma I1: "\<^bold>\<forall>y. (y \<^bold>= (\<^bold>Ix. \<phi>(x)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. (x \<^bold>= y) \<^bold>\<leftrightarrow> \<phi>(x)))" apply simp nitpick oops

axiomatization where I1: "\<^bold>\<forall>y. (y \<^bold>= (\<^bold>Ix. \<phi>(x)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. (x \<^bold>= y) \<^bold>\<leftrightarrow> \<phi>(x)))" 

lemma I2: "\<^bold>\<not>(\<^bold>\<exists>y. (y \<^bold>= (\<^bold>Ix. \<phi>(x)))) \<^bold>\<rightarrow> ( \<^bold>\<star> \<^bold>= (\<^bold>Ix. \<phi>(x)))" apply simp nitpick oops

lemma ext: "(\<^bold>\<forall>x. \<phi>(x) \<^bold>\<leftrightarrow> \<psi>(x)) \<^bold>\<rightarrow> (\<^bold>Ix. \<phi>(x)) \<^bold>= (\<^bold>Ix. \<psi>(x))" apply simp nitpick oops



