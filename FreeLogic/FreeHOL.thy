(*<*) 
theory FreeHOL   
imports Main 

begin
(*>*)

typedecl \<iota>                -- "the type for indiviuals"   
type_synonym \<sigma> = "bool"   -- "the type for Booleans"   

consts  f_r  :: "\<iota> \<Rightarrow> \<iota> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>r" 70)(*>*) 
   
consts f_e :: "'a \<Rightarrow> \<sigma>" (*<*)("\<^bold>e")(*>*)

consts f_star :: "'a" (*<*)("\<^bold>\<star>")(*>*)

axiomatization where f_star_axiom: "\<not> \<^bold>e \<^bold>\<star>"
  

abbreviation f_not :: "\<sigma> \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<not>")(*>*) 
  where "\<^bold>\<not> \<phi> \<equiv> \<not> \<phi>"    
abbreviation f_and :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<and>" 52)(*>*) 
  where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<phi> \<and> \<psi>"   
abbreviation f_or :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<or>" 51)(*>*) 
  where "\<phi> \<^bold>\<or> \<psi> \<equiv> \<phi> \<or> \<psi>"   
abbreviation f_implies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<rightarrow>" 49)(*>*) 
  where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"  
abbreviation f_equals :: "\<iota> \<Rightarrow> \<iota> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>=" 49)(*>*) 
  where "x \<^bold>= y \<equiv> x = y"
abbreviation f_forall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<forall>")(*>*) 
  where "\<^bold>\<forall> \<Phi> \<equiv> \<forall>x. \<^bold>e x \<longrightarrow>  \<Phi> x"   
abbreviation f_mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<exists>")(*>*) 
  where "\<^bold>\<exists> \<Phi> \<equiv> \<exists>x. \<^bold>e x \<and> \<Phi> x"
abbreviation f_that :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> 'a" (*<*)("\<^bold>I")(*>*) 
  where "\<^bold>I \<Phi> \<equiv> if \<exists>x. (\<Phi> x) \<and> (\<forall>y. (\<Phi> y) \<longrightarrow> y = x) then THE x. (\<Phi> x) else \<^bold>\<star>"


lemma "x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x" apply simp done
lemma "(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> \<^bold>\<exists>(\<lambda>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" nitpick oops
lemma "\<^bold>\<exists>(\<lambda>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" nitpick oops
lemma "((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> \<^bold>\<exists>(\<lambda>y. (y \<^bold>= y))) \<^bold>\<rightarrow> \<^bold>\<exists>(\<lambda>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" apply simp done
