theory Scott1 imports FreeFOL 
begin

type_synonym e = i   -- \<open>raw type of morphisms\<close> 

abbreviation Definedness ::  "e\<Rightarrow>bool" ("E_"[100]60)    (* we map it to definedness in Free Logic *)
 where "E x \<equiv> \<A> x"   
abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<approx>"60) 
 where "x \<approx> y \<equiv> ((E x) \<^bold>\<and> (E y)) \<^bold>\<and> x \<^bold>= y"  


text {* Ordinary equality is not reflexive in general. *}
lemma "x \<approx> x" nitpick [user_axioms,mono] oops

text {* However, we still have: *}
lemma "\<^bold>\<forall>x. x \<approx> x" by simp 

axiomatization where
 refl: "x \<approx> x \<^bold>\<leftrightarrow> E x" 

text {* Symmetry and transitivity are for free: *}
lemma sym: "x \<approx> y \<^bold>\<leftrightarrow> y \<approx> x" by simp
lemma trans: "x \<approx> y \<^bold>\<and> y \<approx> z \<^bold>\<rightarrow> x \<approx> z" by simp

lemma "x \<approx> y \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" by simp
lemma "(\<^bold>\<forall>z. (x \<approx> z \<^bold>\<leftrightarrow> y \<approx> z)) \<^bold>\<rightarrow> ((E x \<^bold>\<rightarrow> x \<approx> y) \<^bold>\<and> (E y \<^bold>\<rightarrow> x \<approx> y))" by blast
lemma "(\<^bold>\<forall>z. (x \<approx> z \<^bold>\<leftrightarrow> y \<approx> z)) \<^bold>\<rightarrow> (((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y))" by blast

text {* The axiom of equivalence *}
text {* ... is not implied by the above theory; Nitpick finds a countermodel *}
lemma  "((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y) \<^bold>\<and> \<Phi>(x) \<^bold>\<rightarrow> \<Phi>(y)" nitpick [user_axioms] oops

text {* ... so we state as an axiom *}
axiomatization where 
 eq: "(((E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y) \<^bold>\<and> \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y)"


text {* Metatheorem *}

text {* First we define equivalence based on equality *}
abbreviation Equivalence :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<^bold>\<equiv>"60) 
 where "x \<^bold>\<equiv> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<approx> y"  

text {* Now we can prove in_, eq_, equals_ and E. *}
lemma in_: "(\<^bold>\<forall>z . (x \<^bold>\<equiv> z \<^bold>\<leftrightarrow> y \<^bold>\<equiv> z)) \<^bold>\<rightarrow> x \<^bold>\<equiv> y" by blast
lemma eq_: "(x \<^bold>\<equiv> y \<^bold>\<and> \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y)" using eq by metis
lemma equals_: "x \<approx> y \<^bold>\<leftrightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (x \<^bold>\<equiv> y))" by blast 

lemma E: "E x \<^bold>\<leftrightarrow> (\<^bold>\<exists> y. x \<^bold>\<equiv> y)" by blast  

text {* Hence we have shown that (in_), (eq_), (equals_) and (E) are provable 
in the theory of equality *}

end 

