theory Scott2 imports FreeFOL 
begin

type_synonym e = i   -- \<open>raw type of morphisms\<close> 

abbreviation Definedness ::  "e\<Rightarrow>bool" ("E_"[100]60)    (* we map it to definedness in Free Logic *)
 where "E x \<equiv> \<A> x"   
abbreviation Equivalence :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<^bold>\<equiv>"60) 
 where "x \<^bold>\<equiv> y \<equiv> (E x \<^bold>\<leftrightarrow> E y) \<^bold>\<and> x \<^bold>= y"  

text {* From this we get eq_ for free. *}
lemma eq_: "(x \<^bold>\<equiv> y \<^bold>\<and> \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y)" by blast

text {* in_ is not implied. *}
lemma "(\<^bold>\<forall>z . x \<^bold>\<equiv> z \<^bold>\<leftrightarrow> y \<^bold>\<equiv> z) \<^bold>\<rightarrow> x \<^bold>\<equiv> y"  nitpick [user_axioms] oops

text {* We thus postulate it. *}
axiomatization where 
 in_: "(\<^bold>\<forall>z . x \<^bold>\<equiv> z \<^bold>\<leftrightarrow> y \<^bold>\<equiv> z) \<^bold>\<rightarrow> x \<^bold>\<equiv> y" 

text {* We have reflexivity, symmetry and transitivity. *}
lemma refl_: "x \<^bold>\<equiv> x" by simp
lemma sym_: "x \<^bold>\<equiv> y \<^bold>\<leftrightarrow> y \<^bold>\<equiv> x" by simp
lemma trans_: "x \<^bold>\<equiv> y \<^bold>\<and> y \<^bold>\<equiv> z \<^bold>\<rightarrow> x \<^bold>\<equiv> z" by simp

text {* Now we define equality based on equivalence. *}
abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<approx>"60) 
 where "x \<approx> y \<equiv> (E x \<^bold>\<and> E y \<^bold>\<and> x \<^bold>\<equiv> y)" 

text {* We verify the original refl, sym, and trans *}
lemma refl: "x \<approx> x \<^bold>\<leftrightarrow> E x" by simp
lemma sym: "x \<approx> y \<^bold>\<leftrightarrow> y \<approx> x" by simp
lemma trans: "x \<approx> y \<^bold>\<and> y \<approx> z \<^bold>\<rightarrow> x \<approx> z" by simp

text {* It remains to prove equiv: *}
lemma equiv: "x \<^bold>\<equiv> y \<^bold>\<leftrightarrow> ((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y)" 
 proof -
 have equiv1: "x \<^bold>\<equiv> y \<^bold>\<rightarrow> ((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y)" by blast
 have equiv2: "((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y) \<^bold>\<rightarrow> x \<^bold>\<equiv> y" using in_ by blast
 then show ?thesis using equiv1 equiv2 by blast
 qed

end 

