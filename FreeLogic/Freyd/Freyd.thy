(*<*)
theory Freyd imports FreeFOL 
begin
(*>*)
section \<open>Application in Category Theory\<close>
text \<open>
We exemplarily employ our above implementation of free logic for an application in
category theory. More, precisely we analyse the foundational axiom system 
for catgeory theory as proposed in the very beginning of textbook by Freyd and 
Scedrov @{cite "FreydScedrov90"}. Our exploration shows that this axiom system is redundant.

Free logic, as opposed to classical logic, is required as a base logic in this context, since the 
composition of two morphisms could be undefined. In the textbook by Freyd and 
Scedrov the properties of free logic are left implicit in the beginning; they only become 
apparent in appendix ???.  

In the remainder we identify the base type @{text "i"} of free logic with the raw type of 
morphisms. Moreover, we introduce constant symbols for the following operations: 
source of a morphism @{text "x"}, target of a morphism @{text "x"} and composition of morphisms
@{text "x"} and @{text "y"}. These operations are denoted by Freyd and Scedrov as 
@{text "\<box>x"}, @{text "x\<box>"} and @{text "x\<cdot>y"}. While we do not particularly support the use 
@{text "\<box>"} in this context, we nevertheless adopt their notation here.
\<close>
(* type_synonym e = i   -- \<open>raw type of morphisms\<close> *)
consts source::"i\<Rightarrow>i" ("\<box>_" [108] 109) 
       target::"i\<Rightarrow>i" ("_\<box>" [110] 111) 
       composition::"i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)
text \<open>
Ordinary equality on morphisms is defined as follows:
\<close>
abbreviation OrdinaryEquality::"i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> ((\<^bold>E x) \<^bold>\<leftrightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y"  
text \<open>
We are now in the position to state the axiom system of Freyd and Scedrov, 
cf. @{cite "FreydScedrov90"}, p. ???
\<close>
axiomatization FreydsAxioms where              
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
 A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
 A2b: "\<box>(x\<box>) \<approx> \<box>x" and
 A3a: "(\<box>x)\<cdot>x \<approx> x" and
 A3b: "x\<cdot>(x\<box>) \<approx> x" and
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" and
 A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" and
 A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
text \<open>
In our subsequent experiments, the new free logic theorem prover(s) in Isabelle quickly found out 
that Axiom @{text "A2a"} is redundant. For example, the prover Isabelle's internal prover metis 
confirms that @{text "A2a"} is already implied by @{text "A2b"}, @{text "A3a"}, @{text "A3b"} 
and @{text "A4a"}.
\<close>
lemma A2aIsRedundant_1: "(\<box>x)\<box> \<approx> \<box>x" 
by (metis A2b A3a A3b A4a)
text \<open>
A human readable and easily comprehensible, detailed reconstruction of the redundancy is 
presented next. This proof employs axioms @{text "A2b"}, @{text "A3a"}, @{text "A3b"}, 
@{text "A4a"} and @{text "A5"}, that is, this proof could be further optimized.
\<close>
lemma A2aIsRedundant_2: "(\<box>x)\<box> \<approx> \<box>x" 
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
text \<open>
Thus, axiom @{text "A2a"} can be removed from the theory. Alternatively, 
we could reduce @{text "A2b"} which is implied by @{text "A1"}, 
@{text "A2a"} and @{text "A3a"} as metis proves.
\<close>
lemma A2bIsRedundant_2: "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a)

(* lemma A3aIsRedundant_2: "(\<box>x)\<cdot>x \<approx> x" sledgehammer (A1 A2a A2b A3b A4a A4b A5) *)
(* lemma A3bIsRedundant_2: "x\<cdot>(x\<box>) \<approx> x" sledgehammer (A1 A2a A2b A3a A4a A4b A5) *)
text \<open>
In fact, by straightforward experimentation on can show that Freyd's and Scedroc's theory can be 
reduced as follows, that is, three axioms can be dropped:
\<close>

axiomatization FreydsAxiomsReduced where              
 B1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
 B2a: "((\<box>x)\<box>) \<approx> \<box>x" and
 B3a: "(\<box>x)\<cdot>x \<approx> x" and
 B3b: "x\<cdot>(x\<box>) \<approx> x" and
 B5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"

lemma B2b: "\<box>(x\<box>) \<approx> \<box>x" by (metis B1 B2a B3a)
lemma B4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis B1 B2a B3a)
lemma B4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis B1 B2a B3a)

text \<open>
Below we present some further tests wrt Freyd's and Scedrov's textbook. In fact, we believe
that some substantial parts of the textbook can eventually be formalised.
\<close>
abbreviation DirectedEquality :: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<greaterapprox>" 60) 
 where "x \<greaterapprox> y \<equiv> ((\<^bold>E x) \<^bold>\<rightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y"  

lemma L1_13: "((\<box>(x\<cdot>y)) \<approx> (\<box>(x\<cdot>(\<box>y)))) \<^bold>\<leftrightarrow> ((\<box>(x\<cdot>y)) \<greaterapprox> \<box>x)" 
by (metis A1 A2a A3a)

lemma "(\<^bold>\<exists>x. e \<approx> (\<box>x)) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))" by (metis A1 A2b A3b)
lemma "(\<^bold>\<exists>x. e \<approx> (x\<box>)) \<^bold>\<leftrightarrow> e \<approx> (\<box>e)"       by (metis A1 A2b A3a A3b)
lemma "e \<approx> (\<box>e) \<^bold>\<leftrightarrow> e \<approx> (e\<box>)"             by (metis A1 A2b A3a A3b A4a)
lemma "e \<approx> (e\<box>) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)"         by (metis A1 A2b A3a A3b A4a) 
lemma "(\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x)"     by (metis A1 A2b A3a A3b)


abbreviation IdentityMorphism :: "i\<Rightarrow>bool" ("IdM_" [100]60) where "IdM x \<equiv> x \<approx> (\<box>x)"

lemma "(IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (\<box>x))) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))) \<^bold>\<and> 
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (\<box>e)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (e\<box>)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x))"
 by (smt A1 A2a A3a A3b)
end