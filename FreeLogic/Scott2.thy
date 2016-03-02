theory Scott2 imports FreeHOL 
begin
 
typedecl e -- \<open>raw type of morphisms\<close> 

abbreviation Definedness ::  "e\<Rightarrow>bool" ("E_"[100]60)    (* we map it to definedness in Free Logic *)
 where "E x \<equiv> \<A> x"   
abbreviation Equivalence :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<^bold>\<equiv>"60) 
 where "x \<^bold>\<equiv> y \<equiv> (E x \<^bold>\<leftrightarrow> E y) \<^bold>\<and> x \<^bold>= y"  

text {* ... we now assume (in_) and (eq_) and use (=) as the definition ... *}
axiomatization where 
 in_: "(\<^bold>\<forall>z . x \<^bold>\<equiv> z \<^bold>\<leftrightarrow> y \<^bold>\<equiv> z) \<^bold>\<rightarrow> x \<^bold>\<equiv> y" and
 eq_: "(x \<^bold>\<equiv> y \<^bold>\<and> \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y)" 

abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<approx>"60) 
 where "x \<approx> y \<equiv> (E x \<^bold>\<and> E y \<^bold>\<and> x \<^bold>\<equiv> y)" 

lemma refl: "x \<approx> x \<^bold>\<leftrightarrow> E x" by simp
lemma sym: "x \<approx> y \<^bold>\<leftrightarrow> y \<approx> x" by simp
lemma trans: "x \<approx> y \<^bold>\<and> y \<approx> z \<^bold>\<rightarrow> x \<approx> z" by simp

lemma equiv1: "x \<^bold>\<equiv> y \<^bold>\<rightarrow> ((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y)" by blast
lemma equiv2: "((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y) \<^bold>\<rightarrow> x \<^bold>\<equiv> y" using in_ by blast
lemma equiv: "x \<^bold>\<equiv> y \<^bold>\<leftrightarrow> ((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y)" using equiv1 equiv2 by blast

end 

