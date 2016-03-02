theory Scott3 imports Scott1
begin
 
text {* We have dom, cod, and comp (\<cdot>) *}
consts dom::"e\<Rightarrow>e" cod::"e\<Rightarrow>e" comp::"e\<Rightarrow>e\<Rightarrow>e" (infix "\<cdot>" 110)

text {* Scott"s axioms *}
axiomatization where
 a1: "E x \<^bold>\<leftrightarrow> E dom(x)" and 
 a2: "E x \<^bold>\<leftrightarrow> E cod(x)" and 
 a3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom(x) \<approx> cod(y)" and 
 a4: "x\<cdot>(y\<cdot>z) \<^bold>\<equiv> (x\<cdot>y)\<cdot>z" and
 a5: "x\<cdot>dom(x) \<^bold>\<equiv> x" and 
 a6: "cod(x)\<cdot>x \<^bold>\<equiv> x"

text {* All the functions are strict and dom and cod are total *}
lemma str_dom: "E dom(x) \<^bold>\<rightarrow> E x" using a1 by blast
lemma str_cod: "E cod(x) \<^bold>\<rightarrow> E x" using a2 by blast
lemma str_comp: "E (x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using a1 a2 a3 by blast
lemma tot_dom: "\<^bold>\<forall>x.\<^bold>\<exists>y. y \<approx> dom(x)" using a1 by blast
lemma tot_cod: "\<^bold>\<forall>x.\<^bold>\<exists>y. y \<approx> cod(x)" using a2 by blast

text {* Now we can prove the following automatically *}
lemma  a7: "dom(x) \<^bold>\<equiv> cod(dom(x))" by (meson a1 a2 a3 a5)  
lemma  a8: "cod(x) \<^bold>\<equiv> dom(cod(x))" by (metis a1 a2 a3 a6)
lemma  a9: "E (x\<cdot>y) \<^bold>\<rightarrow> dom(x\<cdot>y) \<approx> dom(y)" by (metis a2 a3 a4 a5)
lemma a10: "E (x\<cdot>y) \<^bold>\<rightarrow> cod(x\<cdot>y) \<approx> cod(x)" by (metis a1 a3 a4 a6)
lemma a11: "(E(x\<cdot>y) \<^bold>\<and> E(y\<cdot>z)) \<^bold>\<rightarrow> E(x\<cdot>(y\<cdot>z))" by (metis a10 a3)

text {* Important remark: The proofs seem much harder if we use Scott2.thy instead of Scott1.thy in 
 the import; that is, if we use the alternative theory of equality. In fact the provers, including 
 sledgehammer, fail to deliver proofs in this case!?! Thus the theory of equality in Scott1 seems 
 better suited for automation. However, we should stil check again whether we missed something 
 in Scott2. *}

text {* We check the derivability of Freyd's axioms. We have to be careful in the case
of composition since Freyd's version is defined in reversed order to Scott's. This explains the 
reversed order of composition used below \<in>some case when compared to the presentation 
in Freyd's book.  *}

abbreviation OrdinaryEqualityFreyd :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<approx>F"60) 
 where "x \<approx>F y \<equiv> ((E x) \<^bold>\<leftrightarrow> (E y)) \<^bold>\<and> x \<^bold>= y"  

lemma Freyd_1: "E(y\<cdot>x) \<^bold>\<leftrightarrow> cod(x) \<approx>F dom(y)" nitpick [user_axioms,mono] oops (* counterexample, why? *)
lemma Freyd_2a: "cod(dom(x)) \<approx>F dom(x)" sledgehammer nitpick [user_axioms,mono] oops (* no counterexample, but also no proof *) 
lemma Freyd_2b: "dom(cod(x)) \<approx>F cod(x)" sledgehammer nitpick [user_axioms,mono] oops (* no counterexample, but also no proof *) 
lemma Freyd_3a: "x\<cdot>dom(x) \<approx>F x" sledgehammer nitpick [user_axioms,mono] oops (* no counterexample, but also no proof *) 
lemma Freyd_3b: "cod(x)\<cdot>x \<approx>F x" sledgehammer nitpick [user_axioms,mono] oops (* no counterexample, but also no proof *) 
lemma Freyd_4a: "dom(y\<cdot>x) \<approx>F dom(dom(y)\<cdot>x)" sledgehammer nitpick [user_axioms,mono] oops (* no counterexample, but also no proof *)  
lemma Freyd_4b: "cod(y\<cdot>x) \<approx>F cod(y\<cdot>cod(x))" sledgehammer nitpick [user_axioms,mono] oops (* no counterexample, but also no proof *) 
lemma Freyd_A5: "x\<cdot>(y\<cdot>z) \<approx>F (x\<cdot>y)\<cdot>z" sledgehammer nitpick [user_axioms,mono] oops (* no counterexample, but also no proof *) 
end 

