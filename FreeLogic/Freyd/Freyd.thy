theory Freyd imports FreeFOL 
begin
type_synonym e = i   -- \<open>raw type of morphisms\<close> 

abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<approx>"60) 
 where "x \<approx> y \<equiv> ((E x) \<^bold>\<leftrightarrow> (E y)) \<^bold>\<and> x \<^bold>= y"  

consts source :: "e\<Rightarrow>e" ("\<box>_" [108]109) 
       target :: "e\<Rightarrow>e" ("_\<box>" [110]111) 
       composition :: "e\<Rightarrow>e\<Rightarrow>e" (infix "\<cdot>" 110)

axiomatization FreydsAxioms where               (* Freyd's axioms, where A2a seems redundant *)
 A1:  "(E x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
(* A2a: "((\<box>x)\<box>) \<approx> \<box>x" *)
 A2b: "\<box>(x\<box>) \<approx> \<box>x" and
 A3a: "(\<box>x)\<cdot>x \<approx> x" and
 A3b: "x\<cdot>(x\<box>) \<approx> x" and
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" and
 A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" and
 A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"


(* Detailed derivation of A2a from the other axioms *)
lemma A2a: "(\<box>x)\<box> \<approx> \<box>x" 
 proof -                    
 have  L1:  "\<forall>x. (\<box>\<box>x)\<cdot>((\<box>x)\<cdot>x) \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x" using A5 by metis
 hence L2:  "\<forall>x. (\<box>\<box>x)\<cdot>x \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x"        using A3a by metis
 hence L3:  "\<forall>x. (\<box>\<box>x)\<cdot>x \<approx> (\<box>x)\<cdot>x"                using A3a by metis
 hence L4:  "\<forall>x. (\<box>\<box>x)\<cdot>x \<approx> x"                     using A3a by metis
 have  L5:  "\<forall>x. \<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>((\<box>\<box>x)\<cdot>(\<box>x))"     using A4a by auto
 hence L6:  "\<forall>x .\<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>\<box>x"               using A3a by metis
 hence L7:  "\<forall>x. \<box>\<box>(x\<box>) \<approx> \<box>(\<box>\<box>(x\<box>))\<cdot>(x\<box>)"       by auto
 hence L8:  "\<forall>x. \<box>\<box>(x\<box>) \<approx> \<box>(x\<box>)"                 using L4 by metis
 hence L9:  "\<forall>x. \<box>\<box>(x\<box>) \<approx> \<box>x"                     using A2b by metis
 hence L10: "\<forall>x. \<box>\<box>x \<approx> \<box>x"                        using A2b by metis
 hence L11: "\<forall>x. \<box>\<box>((\<box>x)\<box>) \<approx> \<box>\<box>(x\<box>)"             using A2b by metis
 hence L12: "\<forall>x. \<box>\<box>((\<box>x)\<box>) \<approx> \<box>x"                  using L9 by metis
 have  L13: "\<forall>x. (\<box>\<box>((\<box>x)\<box>))\<cdot>((\<box>x)\<box>) \<approx> ((\<box>x)\<box>)"  using L4 by auto   
 hence L14: "\<forall>x. (\<box>x)\<cdot>((\<box>x)\<box>) \<approx> (\<box>x)\<box>"            using L12 by metis
 hence L15: "\<forall>x. (\<box>x)\<box> \<approx> (\<box>x)\<cdot>((\<box>x)\<box>)"            using L14 by auto
 then show ?thesis using A3b by metis
qed                     


abbreviation DirectedEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<greaterapprox>" 60) 
 where "x \<greaterapprox> y \<equiv> ((E x) \<^bold>\<rightarrow> (E y)) \<^bold>\<and> x \<^bold>= y"  

lemma L1_13: "((\<box>(x\<cdot>y)) \<approx> (\<box>(x\<cdot>(\<box>y)))) \<^bold>\<leftrightarrow> ((\<box>(x\<cdot>y)) \<greaterapprox> \<box>x)" 
by (metis A1 A2a A3a)


lemma "(\<^bold>\<exists>x. e \<approx> (\<box>x)) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))" by (metis A1 A2b A3b)
lemma "(\<^bold>\<exists>x. e \<approx> (x\<box>)) \<^bold>\<leftrightarrow> e \<approx> (\<box>e)"       by (metis A1 A2b A3a A3b)
lemma "e \<approx> (\<box>e) \<^bold>\<leftrightarrow> e \<approx> (e\<box>)"             by (metis A1 A2b A3a A3b A4a)
lemma "e \<approx> (e\<box>) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)"         by (metis A1 A2b A3a A3b A4a) 
lemma "(\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x)"     by (metis A1 A2b A3a A3b)


abbreviation IdentityMorphism :: "e\<Rightarrow>bool" ("IdM_" [100]60) where "IdM x \<equiv> x \<approx> (\<box>x)"

lemma "(IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (\<box>x))) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))) \<^bold>\<and> 
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (\<box>e)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (e\<box>)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x))"
 by (smt A1 A2a A3a A3b)
end