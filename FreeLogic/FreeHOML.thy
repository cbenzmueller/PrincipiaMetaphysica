(*<*) 
theory FreeHOML   
imports Main 

begin
(*>*)

  typedecl \<iota>                -- "the type for indiviuals" 
  typedecl \<omega>                -- "the type for possible worlds"     
  type_synonym \<sigma> = "\<omega> \<Rightarrow> bool"   -- "the type for Booleans"   

  consts  f_r  :: "\<iota> \<Rightarrow> \<iota> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>r" 70)(*>*) 
  consts  f_ar  :: "\<omega> \<Rightarrow> \<omega> \<Rightarrow> bool" (*<*)(infixr "\<^bold>a\<^bold>r" 70)(*>*)
  
   
  consts f_e :: "'a \<Rightarrow> \<sigma>" (*<*)("\<^bold>e")(*>*)

 

abbreviation f_not :: "\<sigma> \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<not>")(*>*) 
  where "\<^bold>\<not> \<phi> \<equiv> (\<lambda> w. \<not> \<phi> w)"    
abbreviation f_and :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<and>" 52)(*>*) 
  where "\<phi> \<^bold>\<and> \<psi> \<equiv> (\<lambda> w. \<phi> w \<and> \<psi> w)"   
abbreviation f_or :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<or>" 51)(*>*) 
  where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<lambda> w. \<phi> w \<or> \<psi> w)"   
abbreviation f_implies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>\<rightarrow>" 49)(*>*) 
  where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> (\<lambda> w. \<phi> w \<longrightarrow> \<psi> w)"  
abbreviation f_equals :: "\<iota> \<Rightarrow> \<iota> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>=" 49)(*>*) 
  where "x \<^bold>= y \<equiv> (\<lambda> w. x = y)"
abbreviation f_forall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<forall>")(*>*) 
  where "\<^bold>\<forall> \<Phi> \<equiv> (\<lambda> w. \<forall>x. \<^bold>e x w \<longrightarrow>  \<Phi> x w)"   
abbreviation f_mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<^bold>\<exists>")(*>*) 
  where "\<^bold>\<exists> \<Phi> \<equiv> (\<lambda> w. \<exists>x. \<^bold>e x w \<and> \<Phi> x w)"
abbreviation f_mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>") 
  where "\<^bold>\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v. w \<^bold>a\<^bold>r v \<longrightarrow> \<phi> v)"
abbreviation f_mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<diamond>") 
  where "\<^bold>\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w \<^bold>a\<^bold>r v \<and> \<phi> v)" 
  
(*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") 
  where "[p] \<equiv> \<forall>w. p w"
  


lemma "[x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x]" apply simp done
lemma "[(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> \<^bold>\<exists>(\<lambda>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)]" nitpick oops
lemma "[\<^bold>\<exists>(\<lambda>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)]" nitpick oops
lemma "[((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> \<^bold>\<exists>(\<lambda>y. (y \<^bold>= y))) \<^bold>\<rightarrow> \<^bold>\<exists>(\<lambda>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)]" apply simp done
