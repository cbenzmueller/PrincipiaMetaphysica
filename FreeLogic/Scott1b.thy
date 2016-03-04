theory Scott1b imports Scott1
begin
 
text {* Section 3 of Id&Ex: Relations and Functions; here with Scott1 as import *}

text {* The following are consequences of eq_ *}
(* provers still fail, but nitpick doesn't find a counterexample *)
lemma test1: "(x \<^bold>\<equiv> x' \<^bold>\<and> y \<^bold>\<equiv> y' \<^bold>\<and> R x y) \<^bold>\<rightarrow> R x' y'" sorry  
lemma test2: "x \<^bold>\<equiv> x'\<^bold>\<rightarrow> f(x) \<^bold>\<equiv> f(x')" sorry

text {* The first statement still holds if we replace equivalence by equality *}
lemma test1_1: "(x \<approx> x' \<^bold>\<and> y \<approx> y' \<^bold>\<and> R x y) \<^bold>\<rightarrow> R x' y'" by blast

text {* ... but the second doesn't  (countermodel by nitpick); it is stronger ... *}
lemma test2_1: "x \<approx> x'\<^bold>\<rightarrow> f(x) \<approx> f(x')" nitpick [user_axioms] oops   

text {* ... since it means ... *}
lemma "E x \<^bold>\<rightarrow> E f(x)" nitpick [user_axioms] oops
lemma tot: "\<^bold>\<forall>x. \<^bold>\<exists>y. y \<approx> f(x)" nitpick [user_axioms] oops

text {* Having @{text "E x \<^bold>\<rightarrow> (E f(x)"} is the same as 
 having @{text "(\<^bold>\<forall>x. \<^bold>\<exists>y. (y \<approx> (f(x))))"}. Note that have to use @{text "\<forall>"}
 below, which is the raw universal quantifier ranging over all objects, not just
 the existing ones. *}
lemma "(\<forall>x . E x \<^bold>\<rightarrow> E f(x)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. \<^bold>\<exists>y. y \<approx> f(x))" by blast

text {* The converse to the above statement of totality is this here; again it is 
 not implied *}
lemma "E f(x) \<^bold>\<rightarrow> E x" nitpick [user_axioms] oops

text {* Strictness of predicates doesn't hold either *}
lemma "P x y \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)"  nitpick [user_axioms] oops

text {* NOTE: should this be provable without any assumptions on strictness? 
 I guess not? We need to discuss ... *}
lemma "(((x \<approx> y) \<^bold>\<and> \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y))" by blast

end 

