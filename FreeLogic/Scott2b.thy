theory Scott2b imports Scott2
begin
 
text {* Section 3 of Id&Ex: Relations and Functions *}

text {* The following are consequences of eq_ *}
lemma test1: "(x \<^bold>\<equiv> x' \<^bold>\<and> y \<^bold>\<equiv> y' \<^bold>\<and> R(x)(y)) \<^bold>\<rightarrow> R(x')(y')" by blast
lemma test2: "x \<^bold>\<equiv> x'\<^bold>\<rightarrow> f(x) \<^bold>\<equiv> f(x')" by blast 

text {* ... but this here does not hold (contermodel by nitpick); it is stronger ... *}
lemma test3: "x \<approx> x'\<^bold>\<rightarrow> f(x) \<approx> f(x')" nitpick [user_axioms,mono] oops   

text {* ... since it means ... *}
lemma "(E x) \<^bold>\<rightarrow> (E (f(x)))" nitpick [user_axioms,mono] oops
lemma tot: "\<^bold>\<forall>x. \<^bold>\<exists>y. (y \<approx> (f(x)))" nitpick [user_axioms,mono] oops

text {* Note: According to the paper, this should be provable, but it isn't *}
lemma "((E x) \<^bold>\<rightarrow> (E (f(x)))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<^bold>\<exists>y. (y \<approx> (f(x))))" nitpick [user_axioms,mono] oops

lemma "(E (f(x))) \<^bold>\<rightarrow> (E x)" nitpick [user_axioms,mono] oops

text {* Note: should this be provable? *}
lemma "(((x \<approx> y) \<^bold>\<and> \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y))" by blast

lemma str_implies_eq': "((E (f(x))) \<^bold>\<rightarrow> (E x)) \<^bold>\<rightarrow> (((x \<^bold>= y) \<^bold>\<and> \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y))" by simp


end 

