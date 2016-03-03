theory Scott3_2 imports Scott2
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
lemma  a7: "dom(x) \<^bold>\<equiv> cod(dom(x))" sledgehammer nitpick [user_axioms] oops (* no countermodel, no proof *) 
axiomatization where a7: "dom(x) \<^bold>\<equiv> cod(dom(x))"

lemma  a8: "cod(x) \<^bold>\<equiv> dom(cod(x))" sledgehammer nitpick [user_axioms] oops (* no countermodel, no proof *) 
axiomatization where a8: "cod(x) \<^bold>\<equiv> dom(cod(x))" 

lemma  a9: "E (x\<cdot>y) \<^bold>\<rightarrow> dom(x\<cdot>y) \<approx> dom(y)"   by (metis a2 a3 a4 a5)
lemma a10: "E (x\<cdot>y) \<^bold>\<rightarrow> cod(x\<cdot>y) \<approx> cod(x)"   by (metis a1 a3 a4 a6)
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

text {* Only 1b holds *} 
lemma F1_1: "E(y\<cdot>x) \<^bold>\<leftrightarrow> cod(x) \<approx>F dom(y)" nitpick [user_axioms] oops (* countermodel *)
lemma F1_2: "E(y\<cdot>x) \<^bold>\<leftrightarrow> cod(x) \<approx> dom(y)"  by (metis a3) (* proof *)
lemma F1_3: "E(y\<cdot>x) \<^bold>\<leftrightarrow> cod(x) \<^bold>\<equiv> dom(y)"  nitpick [user_axioms] oops (* countermodel *)

lemma F2a_1: "cod(dom(x)) \<approx>F dom(x)" using a7 by auto (* proof *) 
lemma F2a_2: "cod(dom(x)) \<approx> dom(x)"  nitpick [user_axioms] oops (* countermodel *) 
lemma F2a_3: "cod(dom(x)) \<^bold>\<equiv> dom(x)"  using a7 by force (* proof *) 

lemma F2b_1: "dom(cod(x)) \<approx>F cod(x)" using a8 by auto (* proof *) 
lemma F2b_2: "dom(cod(x)) \<approx> cod(x)"  nitpick [user_axioms] oops (* countermodel *) 
lemma F2b_3: "dom(cod(x)) \<^bold>\<equiv> cod(x)"  using a8 by fastforce (* proof *) 

lemma F3a_1: "x\<cdot>dom(x) \<approx>F x" using a5 by blast (* proof *)
lemma F3a_2: "x\<cdot>dom(x) \<approx> x"  nitpick [user_axioms] oops (* countermodel *)
lemma F3a_3: "x\<cdot>dom(x) \<^bold>\<equiv>  x" using a5 by blast (* proof *)
 
lemma F3b_1: "cod(x)\<cdot>x \<approx>F x" using a6 by blast (* proof *) 
lemma F3b_2: "cod(x)\<cdot>x \<approx> x"  nitpick [user_axioms] oops (* countermodel *)
lemma F3b_3: "cod(x)\<cdot>x \<^bold>\<equiv> x"  using a6 by blast (* proof *)

lemma F4a_1: "dom(y\<cdot>x) \<approx>F dom(dom(y)\<cdot>x)" sledgehammer nitpick [user_axioms] oops (* no countermodel, no proof *)  
lemma F4a_2: "dom(y\<cdot>x) \<approx> dom(dom(y)\<cdot>x)"  nitpick [user_axioms] oops (* countermodel *) 
lemma F4a_3: "dom(y\<cdot>x) \<^bold>\<equiv> dom(dom(y)\<cdot>x)" sledgehammer nitpick [user_axioms] oops (* no countermodel, no proof *) 
(* by (metis F3a_3 a3 a7 a9) *) 

lemma F4b_1: "cod(y\<cdot>x) \<approx>F cod(y\<cdot>cod(x))" sledgehammer nitpick [user_axioms] oops (* no countermodel, no proof *)
lemma F4b_2: "cod(y\<cdot>x) \<approx> cod(y\<cdot>cod(x))"  nitpick [user_axioms] oops (* countermodel *)
lemma F4b_3: "cod(y\<cdot>x) \<^bold>\<equiv> cod(y\<cdot>cod(x))"  sledgehammer nitpick [user_axioms] oops (* no countermodel, no proof *)
(* by (metis F3b_3 a10 a2 a3) *) 

lemma FA5_1: "x\<cdot>(y\<cdot>z) \<approx>F (x\<cdot>y)\<cdot>z" using a4 by blast (* proof *)
lemma FA5_2: "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"  nitpick [user_axioms] oops (* countermodel *)
lemma FA5_3: "x\<cdot>(y\<cdot>z) \<^bold>\<equiv> (x\<cdot>y)\<cdot>z"  using a4 by blast (* proof *)
end 

