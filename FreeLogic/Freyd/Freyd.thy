theory Freyd imports FreeHOL 
begin

typedecl e  -- \<open>raw type of morphisms\<close>
abbreviation Definedness ::  "e\<Rightarrow>bool" ("D_"[8]60)    (* we map it to definedness in Free Logic *)
 where "D x \<equiv> \<A> x"   
abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix"\<approx>"60) 
 where "x \<approx> y \<equiv> ((D x) \<^bold>\<leftrightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

consts source :: "e\<Rightarrow>e" ("\<box>_" [108]109) 
       target :: "e\<Rightarrow>e" ("_\<box>" [110]111) 
       composition :: "e\<Rightarrow>e\<Rightarrow>e" (infix "\<cdot>" 110)

axiomatization FreydsAxioms where               (* Freyd's axioms, where A2a seems redundant *)
 A1:  "(D x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
(* A2a: "((\<box>x)\<box>) \<approx> \<box>x" *)
 A2b: "\<box>(x\<box>) \<approx> \<box>x" and
 A3a: "(\<box>x)\<cdot>x \<approx> x" and
 A3b: "x\<cdot>(x\<box>) \<approx> x" and
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" and
 A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" and
 A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"

(* Detailed derivation of A2a from the other axioms *)
lemma L1:  "(\<box>\<box>x)\<cdot>((\<box>x)\<cdot>x) \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x"  using A5 by metis
lemma L2:  "(\<box>\<box>x)\<cdot>x \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x"         using L1 A3a by metis
lemma L3:  "(\<box>\<box>x)\<cdot>x \<approx> (\<box>x)\<cdot>x"                 using L2 A3a by metis
lemma L4:  "(\<box>\<box>x)\<cdot>x \<approx> x"                      using L3 A3a by metis
lemma L5:  "\<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>((\<box>\<box>x)\<cdot>(\<box>x))"      using A4a by auto
lemma L6:  "\<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>\<box>x"                using L5 A3a by metis
lemma L7:  "\<box>\<box>(x\<box>) \<approx> \<box>(\<box>\<box>(x\<box>))\<cdot>(x\<box>)"        using L6 by auto
lemma L8:  "\<box>\<box>(x\<box>) \<approx> \<box>(x\<box>)"                 using L4 L7 by metis
lemma L9:  "\<box>\<box>(x\<box>) \<approx> \<box>x"                     using A2b L8 by metis
lemma L10: "\<box>\<box>x \<approx> \<box>x"                        using A2b L9 by metis
lemma L11: "\<box>\<box>((\<box>x)\<box>) \<approx> \<box>\<box>(x\<box>)"             using A2b L10 by metis
lemma L12: "\<box>\<box>((\<box>x)\<box>) \<approx> \<box>x"                  using L11 L9 by metis
lemma L13: "(\<box>\<box>((\<box>x)\<box>))\<cdot>((\<box>x)\<box>) \<approx> ((\<box>x)\<box>)"  using L4 by auto   
lemma L14: "(\<box>x)\<cdot>((\<box>x)\<box>) \<approx> (\<box>x)\<box>"            using L12 L13 by metis
lemma LM10: "(\<box>x)\<box> \<approx> (\<box>x)\<cdot>((\<box>x)\<box>)"           using L14 by auto
lemma A2a: "(\<box>x)\<box> \<approx> \<box>x"                      using A3b LM10 by metis


abbreviation DirectedEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<greaterapprox>" 60) 
 where "x \<greaterapprox> y \<equiv> ((D x) \<^bold>\<rightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

lemma L1_13: "((\<box>(x\<cdot>y)) \<approx> (\<box>(x\<cdot>(\<box>y)))) \<^bold>\<leftrightarrow> ((\<box>(x\<cdot>y)) \<greaterapprox> \<box>x)" 
by (metis A1 A2a A3a)


lemma "(\<^bold>\<exists>x. e \<approx> (\<box>x)) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))" 
 by (metis A1 A2b A3b)
lemma "(\<^bold>\<exists>x. e \<approx> (x\<box>)) \<^bold>\<leftrightarrow> e \<approx> (\<box>e)"
 by (metis A1 A2b A3a A3b)
lemma "e \<approx> (\<box>e) \<^bold>\<leftrightarrow> e \<approx> (e\<box>)"
 by (metis A1 A2b A3a A3b A4a)
lemma "e \<approx> (e\<box>) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)"
 by (metis A1 A2b A3a A3b A4a) 
lemma "(\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x)"
 by (metis A1 A2b A3a A3b)


abbreviation IdentityMorphism :: "e\<Rightarrow>bool" ("IdM_" [8]60) where "IdM x \<equiv> x \<approx> (\<box>x)"

lemma "(IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (\<box>x))) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))) \<^bold>\<and> 
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (\<box>e)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (e\<box>)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x))"
 by (smt A1 A2a A3a A3b)
end