theory FreeHOL imports Main 
begin


typedecl \<iota>                -- "the type for indiviuals"   
type_synonym \<sigma> = "bool"   -- "the type for Booleans"   

consts f_r  :: "\<iota>\<Rightarrow>\<iota>\<Rightarrow>\<sigma>" (infixr "\<^bold>r" 70) 
   
consts f_e :: "\<iota>\<Rightarrow>\<sigma>" ("\<^bold>e")

consts f_star :: "\<iota>" ("\<^bold>\<star>")

axiomatization where f_star_axiom: "\<not> \<^bold>e \<^bold>\<star>"


abbreviation f_not :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_" [58] 59)            where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation f_implies :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<rightarrow>" 49)   where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 
abbreviation f_all :: "(\<iota>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")                 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. \<^bold>e(x) \<longrightarrow>  \<Phi>(x)"   
abbreviation f_all_bind :: "(\<iota>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"
 
abbreviation f_or :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<or>" 51)         where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation f_and :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<and>" 52)        where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation f_equiv :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<leftrightarrow>" 50)     where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation f_equals :: "\<iota>\<Rightarrow>\<iota>\<Rightarrow>\<sigma>" (infixr "\<^bold>="56)       where "x\<^bold>=y \<equiv> x=y"

abbreviation f_exi :: "(\<iota>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>")                 where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>\<^bold>\<forall>(\<lambda>y. \<not> (\<Phi> y))"
abbreviation f_exi_b :: "(\<iota>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"  (binder "\<^bold>\<exists>" [8]9)  where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists> \<phi>"
abbreviation f_that :: "(\<iota>\<Rightarrow>\<sigma>)\<Rightarrow>\<iota>" ("\<^bold>I") 
  where "\<^bold>I \<Phi> \<equiv> if \<exists>x. \<^bold>e(x) \<and> (\<Phi> x) \<and> (\<forall>y. (\<^bold>e(x) \<and> (\<Phi> y)) \<longrightarrow> (y = x)) 
                then THE x. \<^bold>e(x) \<and> (\<Phi> x) 
                else \<^bold>\<star>"
abbreviation f_that_b :: "(\<iota>\<Rightarrow>\<sigma>)\<Rightarrow>\<iota>"  (binder "\<^bold>I" [8]9) where "\<^bold>I x. \<phi> x \<equiv> \<^bold>I \<phi>"

section {* Some Introductory Tests *} 

-- "See Scott 1967, pages 183-184"
lemma "x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x" by simp        
-- "... valid in all domains including the empty one"
lemma "\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y" nitpick oops    
-- "... not valid in the empty domain; hence, the valid formulas formulas are not closed under the rule"
-- "of modus ponens when the empty domain is included"
lemma "(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" nitpick oops
-- "not valid"
lemma "((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> (\<^bold>\<exists>y. y \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" by simp
-- "... now the empty domain is excluded and the statement is valid"


-- "See Scott 1967, page 185"
lemma S1_inst : "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<Psi>(x)))" by auto
lemma S2 :      "\<^bold>\<forall>y. \<^bold>\<exists>x. x = y" by auto
lemma S3 :      "\<alpha> = \<alpha>" by auto
lemma S4_inst : "(\<Phi>(\<alpha>) \<^bold>\<and> (\<alpha> = \<beta>)) \<^bold>\<rightarrow> \<Phi>(\<beta>)" by auto
lemma UI_inst : "((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<and> (\<^bold>\<exists>x. x = \<alpha>)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" by auto
lemma UI_test : "(\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" nitpick [user_axioms] oops -- "Countermodel"
lemma UI_cor1 : "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y))" by auto
lemma UI_cor2 : "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<^bold>\<not>(x \<^bold>= y)) \<^bold>\<rightarrow> \<^bold>\<not>(y \<^bold>= y))" by auto
lemma UI_cor3 : "\<^bold>\<forall>y.((y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<exists>x. x = y))" by auto
lemma UI_cor4 : "(\<^bold>\<forall>y. y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<forall>y.(\<^bold>\<exists>x. x = y))" by simp

lemma "(\<^bold>\<exists>x. x = \<alpha>) \<longrightarrow> \<^bold>e(\<alpha>)" by simp
-- "... to say that (\<^bold>\<exists>x. x = \<alpha>) is true means that the value of \<alpha> exists (properly" 

-- "Problems start here"
lemma I1_inst : "\<^bold>\<forall>y. ((y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))))" nitpick [user_axioms] oops
-- "There seems something wrong with my modeling of definite description!"

-- "This is again ok"
lemma I2_inst : "\<^bold>\<not>(\<^bold>\<exists>y. y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<rightarrow>  \<^bold>\<star> = (\<^bold>Ix. \<Phi>(x))" by (metis (no_types, lifting) the_equality)

-- "Extensionality: again a Problem"
lemma Ext_inst : "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<leftrightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>Ix. \<Phi>(x)) \<^bold>= (\<^bold>Ix. \<Psi>(x)))" nitpick [user_axioms] oops


-- "the following schema is not valid as intended"
lemma I3 : "(\<^bold>\<star> \<^bold>= \<alpha> \<^bold>\<or> \<^bold>\<star> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)" nitpick [user_axioms] oops

lemma Russel_inst : 
 "((\<^bold>\<star> \<^bold>= \<alpha> \<^bold>\<or> \<^bold>\<star> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)) 
  \<^bold>\<rightarrow> 
  ((\<alpha> \<^bold>r (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<exists>y.((\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))) \<^bold>\<and> (\<alpha> \<^bold>r y))))"
nitpick [user_axioms] oops


lemma "\<^bold>\<not>(\<^bold>\<exists>x. (x \<^bold>= (\<^bold>Iy. \<^bold>\<not> (y \<^bold>= y))))" using f_star_axiom by auto
lemma "(\<^bold>\<exists>x. x \<^bold>= a) \<^bold>\<rightarrow>  \<^bold>e a" by simp


-- "Some further test"

consts a::\<iota> b::\<iota> 
axiomatization where ax1: "\<^bold>e a \<^bold>\<and> \<^bold>e b \<^bold>\<and> \<^bold>\<not> (a \<^bold>= b) \<^bold>\<and> \<^bold>\<not> (a \<^bold>=  \<^bold>\<star>) \<^bold>\<and> \<^bold>\<not> (b \<^bold>=  \<^bold>\<star>)"
lemma test: "\<^bold>\<star> \<^bold>= (\<^bold>I (\<lambda>x. x  \<^bold>= a \<^bold>\<or> x \<^bold>= b))" by (metis ax1)




