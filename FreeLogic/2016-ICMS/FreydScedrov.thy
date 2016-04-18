(*<*)
theory FreydScedrov imports FreeFOL 
begin
(*>*)
section \<open>Application in Category Theory\<close>
text \<open>
We exemplary employ the our free logic reasoning framework for an application in
category theory. More precisely, we study some
properties of the category theory axiom system of Freyd and 
Scedrov; see their textbook ``Categories, Allegories'' @{cite "FreydScedrov90"}, p.~3. 
As expected, the composition @{text "x\<cdot>y"}, for morphisms @{text "x"} and 
@{text "y"},  is introduced by Freyd and Scedrov as a partial operation, cf. axiom @{text "A1"} 
below: the composition @{text "x\<cdot>y"} exists if and only if the target of @{text "x"} coincides 
with the source  of @{text "y"}. This is why free logic, as opposed to e.g. classical logic, is 
better suited as a starting point for the modeling of their work.\footnote{The precise logic 
setting is unfortunately not discussed in the beginning of Freyd's and Scedrov's textbook. 
Appendix B, however, contains a concise formal definition of the logic setting they assume.}

In the remainder we identify the base type @{text "i"} of free logic with the raw type of 
morphisms. Moreover, we introduce constant symbols for the following operations: 
source of a morphism @{text "x"}, target of a morphism @{text "x"} and composition of morphisms
@{text "x"} and @{text "y"}. These operations are denoted by Freyd and Scedrov as 
@{text "\<box>x"}, @{text "x\<box>"} and @{text "x\<cdot>y"}, respectively.
We adopt their notation below, even though  we are not particularly fond of 
the use of @{text "\<box>"} in this context.
\<close>
consts source::"i\<Rightarrow>i" ("\<box>_" [108] 109) 
       target::"i\<Rightarrow>i" ("_\<box>" [110] 111) 
       composition::"i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)
text \<open>
Ordinary equality on morphisms is then defined as follows:
\<close>
abbreviation OrdinaryEquality::"i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> ((\<^bold>E x) \<^bold>\<leftrightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y"  
text \<open>
We are now in the position to model the axiom system of Freyd and Scedrov.
\<close>
axiomatization FreydsAxiomSystem where              
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
 A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
 A2b: "\<box>(x\<box>) \<approx> \<box>x" and
 A3a: "(\<box>x)\<cdot>x \<approx> x" and
 A3b: "x\<cdot>(x\<box>) \<approx> x" and
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" and
 A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" and
 A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
text \<open>
Experiments with our new reasoning framework for free logic quickly confirm 
that axiom @{text "A2a"} is redundant. For example, as Isabelle's internal prover 
metis\footnote{Metis is trusted prover of Isabelle, since it returns proofs in Isabelle's 
trusted kernel. In the initial experiments we have worked with the sledgehammer tool, which in turn
performs calls several first-order theorem provers integrated with Isabelle. These calls then 
return valuable information on the particular proof dependencies, which in turn suggest the 
successful calls with metis as presented below.}
confirms, @{text "A2a"} is implied by @{text "A2b"}, @{text "A3a"}, @{text "A3b"} 
and @{text "A4a"}.
\<close>
lemma A2aIsRedundant_1: "(\<box>x)\<box> \<approx> \<box>x" 
by (metis A2b A3a A3b A4a)
text \<open>
A human readable and comprehensible reconstruction of this redundancy is 
presented below. This proof employs axioms @{text "A2b"}, @{text "A3a"}, @{text "A3b"}, 
@{text "A4a"} and @{text "A5"}, that is, this proof could be further optimized by eleminating 
the dependency on @{text "A5"}.
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
we could also eliminate @{text "A2b"} which is implied by @{text "A1"}, 
@{text "A2a"} and @{text "A3a"}: 
\<close>
lemma A2bIsRedundant_2: "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a)
(* lemma A3aIsRedundant_2: "(\<box>x)\<cdot>x \<approx> x" sledgehammer (A1 A2a A2b A3b A4a A4b A5) *)
(* lemma A3bIsRedundant_2: "x\<cdot>(x\<box>) \<approx> x" sledgehammer (A1 A2a A2b A3a A4a A4b A5) *)
text \<open>
In fact, by straightforward experimentation with our provers, we can show that Freyd's and 
Scedroc's axiomatic theory can be reduced to just the following five axioms:
\<close>
axiomatization FreydsAxiomSystemReduced where              
 B1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
 B2a: "((\<box>x)\<box>) \<approx> \<box>x" and
 B3a: "(\<box>x)\<cdot>x \<approx> x" and
 B3b: "x\<cdot>(x\<box>) \<approx> x" and
 B5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
text \<open>
The dropped axioms can now be introduced as lemmas.
\<close>
lemma B2b: "\<box>(x\<box>) \<approx> \<box>x" by (metis B1 B2a B3a)
lemma B4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis B1 B2a B3a)
lemma B4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis B1 B2a B3a)

text \<open>
In the remainder of this section we present some further tests wrt Freyd's and Scedrov's theory. 
We leave these tests uncommented.
\<close>
abbreviation DirectedEquality :: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<greaterapprox>" 60) 
 where "x \<greaterapprox> y \<equiv> ((\<^bold>E x) \<^bold>\<rightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y"  

lemma L1_13: "((\<box>(x\<cdot>y)) \<approx> (\<box>(x\<cdot>(\<box>y)))) \<^bold>\<leftrightarrow> ((\<box>(x\<cdot>y)) \<greaterapprox> \<box>x)" by (metis A1 A2a A3a)

lemma "(\<^bold>\<exists>x. e \<approx> (\<box>x)) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))" by (metis A1 A2b A3b)
lemma "(\<^bold>\<exists>x. e \<approx> (x\<box>)) \<^bold>\<leftrightarrow> e \<approx> (\<box>e)"       by (metis A1 A2b A3a A3b)
lemma "e \<approx> (\<box>e) \<^bold>\<leftrightarrow> e \<approx> (e\<box>)"             by (metis A1 A2b A3a A3b A4a)
lemma "e \<approx> (e\<box>) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)"         by (metis A1 A2b A3a A3b A4a) 
lemma "(\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x)"     by (metis A1 A2b A3a A3b)


abbreviation IdentityMorphism :: "i\<Rightarrow>bool" ("IdM_" [100]60) 
 where "IdM x \<equiv> x \<approx> (\<box>x)"

lemma "(IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (\<box>x))) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))) \<^bold>\<and> 
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (\<box>e)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (e\<box>)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x))"
 by (smt A1 A2a A3a A3b)

section \<open> Conclusion and Further Work \<close>
text \<open> 
We have presented a new reasoning framework for free logic, and we have exemplary applied it for 
some initial  experiments in category theory. We have shown that, in our logic setting, the category
axiom system of Freyd and Scedrov is redundant and that three axioms can be dropped.

Our free logic reasoning framework is freely available for reuse: Simply download 
Isabelle from \url{https://isabelle.in.tum.de} and initialize it (respectively import) the file
\texttt{FreeFOL.thy} from our sources available at \url{www.christoph-benzmueller.de/papers/2016-ICMS.zip}.
Our category theory experiments are contained in the file \texttt{FreydScedrov.thy}

This paper has been written entirely within the Isabelle/HOL framework by utilizing
the Isabelle \textsc{build} tool {@cite "Isabelle-build"}. It is thus an
example of a formally verified mathematical document. The independently verifiable Isabelle 
source code is available at \url{www.christoph-benzmueller.de/papers/2016-ICMS.zip}. Running
this code the prerequires the installation of the Isabelle system available at \url{???}.
The following command, to be executed in the downloaded and unzip-ed source directory, first 
verifies our text  sources for formal correctness and then generates 
the vorliegende pdf document from them. 

\<close>
(*<*)
end
(*>*)