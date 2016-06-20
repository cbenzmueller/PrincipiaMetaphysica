(*<*)
theory FreeFOLminimal 
imports Main 
begin

typedecl i   \<comment> "the type for indiviuals" 
consts fExistence:: "i\<Rightarrow>bool" ("\<^bold>E")    \<comment> "Existence predicate"

(*
consts fStar:: "i" ("\<^bold>\<star>")   \<comment> "Distinguished symbol for undefinedness"
axiomatization where fStarAxiom: "\<not>\<^bold>E(\<^bold>\<star>)"
*)

abbreviation fNot:: "bool\<Rightarrow>bool" ("\<^bold>\<not>")          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr "\<^bold>\<rightarrow>" 49)   
 where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 
abbreviation fForall:: "(i\<Rightarrow>bool)\<Rightarrow>bool" ("\<^bold>\<forall>")                 
 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. \<^bold>E(x)\<longrightarrow>\<Phi>(x)"   
abbreviation fForallBinder:: "(i\<Rightarrow>bool)\<Rightarrow>bool" (binder "\<^bold>\<forall>" [8] 9) 
 where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"


abbreviation fThat:: "(i\<Rightarrow>bool)\<Rightarrow>i" ("\<^bold>I") 
 where "\<^bold>I\<Phi> \<equiv> if \<exists>x. \<^bold>E(x) \<and> \<Phi>(x) \<and> (\<forall>y. (\<^bold>E(y) \<and> \<Phi>(y)) \<longrightarrow> (y = x)) 
              then THE x. \<^bold>E(x) \<and> \<Phi>(x) 
              else SOME x. \<not>(\<^bold>E(x))"
abbreviation fThatBinder:: "(i\<Rightarrow>bool)\<Rightarrow>i"  (binder "\<^bold>I" [8] 9) 
 where "\<^bold>Ix. \<phi>(x) \<equiv> \<^bold>I(\<phi>)"

lemma "\<exists>x. \<^bold>\<not> (\<^bold>E(x))"  nitpick [user_axioms, show_all] oops

abbreviation fOr (infixr "\<^bold>\<or>" 51) where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 52) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 50) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation fEquals (infixr "\<^bold>=" 56) where "x\<^bold>=y \<equiv> x=y"
abbreviation fExists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"


section \<open>Functionality Tests\<close> 
text \<open>
We exemplarily investigate some example proof problems from Scott's paper @{cite "scott67:_exist"}, pp. 183-184, 
where a free logic with a  single relation symbol 
\<open>\<^bold>r\<close> is discussed.
\<close>
consts r:: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "\<^bold>r" 70)   

text \<open>
The implication \<open>x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x\<close>, where \<open>x\<close> is a free variable, is valid 
independently whether \<open>x\<close> is defined (i.e. ``exists'') or not. In Isabelle/HOL this 
quickly confirmed by 
the simplification procedure simp.
\<close>
lemma "x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x" by simp  

text \<open>
However, as intended, the formula \<open>\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y\<close> is not valid, since set of existing
objects \<open>\<^bold>E\<close> could be empty.  Nitpick quickly presents a respective countermodel.
\<close>
lemma "\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y" nitpick [user_axioms] oops
text \<open>
Consequently, also the implication \<open>(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)\<close> 
has a countermodel, where \<open>\<^bold>E\<close> is empty. 
\<close>
lemma "(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" nitpick [user_axioms]  oops
text \<open>
If we rule out that \<open>\<^bold>E\<close> is empty, e.g. with additional condition \<open>\<^bold>(\<^bold>\<exists>y. y \<^bold>= y)\<close> 
in the antecedent of the above formula, then we obtain a valid implication. Isabelle trivially 
proves this with procedure simp.
\<close>
lemma "((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> (\<^bold>\<exists>y. y \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" by simp
text \<open>
We analyse some further statements (respectively statement instances) from Scott's paper
@{cite "scott67:_exist"}, p. 185. Because of space restrictions we do not further comment these 
statements here. Altogether they provide further evidence that our implementation of free logic in fact 
obeys the intended properties.
\<close>
lemma S1: "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<Psi>(x)))" by auto
lemma S2: "\<^bold>\<forall>y. \<^bold>\<exists>x. x \<^bold>= y" by auto
lemma S3: "\<alpha> \<^bold>= \<alpha>" by auto
lemma S4: "(\<Phi>(\<alpha>) \<^bold>\<and> (\<alpha> \<^bold>= \<beta>)) \<^bold>\<rightarrow> \<Phi>(\<beta>)" by auto
lemma UI_1: "((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<and> (\<^bold>\<exists>x. x \<^bold>= \<alpha>)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" by auto
lemma UI_2: "(\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" nitpick [user_axioms] oops \<comment> "Countermodel by Nitpick"
lemma UI_cor1: "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y))" by auto
lemma UI_cor2: "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<^bold>\<not>(x \<^bold>= y)) \<^bold>\<rightarrow> \<^bold>\<not>(y \<^bold>= y))" by auto
lemma UI_cor3: "\<^bold>\<forall>y.((y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<exists>x. x \<^bold>= y))" by auto
lemma UI_cor4: "(\<^bold>\<forall>y. y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<forall>y.\<^bold>\<exists>x. x \<^bold>= y)" by simp
lemma Existence: "(\<^bold>\<exists>x. x \<^bold>= \<alpha>) \<longrightarrow> \<^bold>E(\<alpha>)" by simp (* ... to say that (\<^bold>\<exists>x. x = \<alpha>) is true means that the value of \<alpha> exists (properly) *)
lemma I1: "\<^bold>\<forall>y. ((y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))))" nitpick oops
abbreviation Star ("\<Otimes>") where "\<Otimes> \<equiv> \<^bold>Iy. \<^bold>\<not> (y \<^bold>= y)"
(* lemma StarTest: "\<Otimes> = \<^bold>\<star>" by simp *)
lemma I2: "\<^bold>\<not>(\<^bold>\<exists>y. y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<rightarrow>  (\<Otimes> \<^bold>= (\<^bold>Ix. \<Phi>(x)))" by (metis (no_types, lifting) the_equality)
lemma ExtI: "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<leftrightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>Ix. \<Phi>(x)) \<^bold>= (\<^bold>Ix. \<Psi>(x)))" by (smt the1_equality)
lemma I3: "(\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)" nitpick [user_axioms] oops \<comment> "Countermodel by Nitpick"
(*<*)
lemma Russel:     
 "((\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)) 
  \<^bold>\<rightarrow> 
  ((\<alpha> \<^bold>r (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<exists>y.((\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))) \<^bold>\<and> (\<alpha> \<^bold>r y))))"
 nitpick [user_axioms] oops
lemma "\<^bold>\<not>(\<^bold>\<exists>x. (x \<^bold>= (\<^bold>Iy. \<^bold>\<not> (y \<^bold>= y))))" nitpick [user_axioms, show_all] oops
lemma "(\<^bold>\<exists>x. (x \<^bold>= (\<^bold>Iy. \<^bold>\<not> (y \<^bold>= y))))" nitpick [user_axioms, show_all] oops
lemma "(\<^bold>\<exists>x. x \<^bold>= a) \<^bold>\<rightarrow>  \<^bold>E(a)" by simp
consts ca::i cb::i 
axiomatization where ax1: "\<^bold>E(ca) \<^bold>\<and> \<^bold>E(cb) \<^bold>\<and> \<^bold>\<not> (ca \<^bold>= cb) \<^bold>\<and> \<^bold>\<not> (ca \<^bold>= \<Otimes>) \<^bold>\<and> \<^bold>\<not> (cb \<^bold>= \<Otimes>)"
lemma test2: "\<Otimes> \<^bold>= (\<^bold>I (\<lambda>x. x  \<^bold>= ca \<^bold>\<or> x \<^bold>= cb))" by (metis ax1)
(*<*)
end
(*>*)