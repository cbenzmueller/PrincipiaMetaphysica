(*<*)
theory FreydScedrov imports FreeFOL 
begin
(*>*)
section \<open>Application in Category Theory\<close>
text \<open>
We exemplarily employ our free logic reasoning framework from above for an application in
category theory. More precisely, we study some
properties of the foundational axiom system of Freyd and 
Scedrov; see their textbook ``Categories, Allegories'' @{cite "FreydScedrov90"}, p.~3. 
As expected, the composition \<open>x\<cdot>y\<close>, for morphisms \<open>x\<close> and 
\<open>y\<close>,  is introduced by Freyd and Scedrov as a partial operation, cf. axiom \<open>A1\<close> 
below: the composition \<open>x\<cdot>y\<close> exists if and only if the target of \<open>x\<close> coincides 
with the source  of \<open>y\<close>. This is why free logic, as opposed to e.g. classical logic, is 
better suited as a starting point in this mathematical application area.\footnote{The precise logic 
setting is unfortunately not discussed in the very beginning of Freyd's and Scedrov's textbook. 
Appendix B, however, contains a concise formal definition of the assumed logic.}

In the remainder we identify the base type \<open>i\<close> of free logic with the raw type of 
morphisms. Moreover, we introduce constant symbols for the following operations: 
\<open>source\<close> of a morphism \<open>x\<close>, \<open>target\<close> of a morphism \<open>x\<close> and 
\<open>composition\<close> of morphisms
\<open>x\<close> and \<open>y\<close>. These operations are denoted by Freyd and Scedrov as 
\<open>\<box>x\<close>, \<open>x\<box>\<close> and \<open>x\<cdot>y\<close>, respectively.
We adopt their notation as syntactic sugar below, even though  we are not particularly fond of 
the use of \<open>\<box>\<close> in this context.
\<close>
consts source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
        target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
        composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)
text \<open>
Ordinary equality on morphisms is defined as follows:
\<close>
abbreviation OrdinaryEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> ((\<^bold>E x) \<^bold>\<leftrightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y"  
text \<open>
We are now in the position to model the category theory axiom system of Freyd and Scedrov.
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
Experiments with our new reasoning framework for free logic quickly showed
that axiom \<open>A2a\<close> is redundant. For example, as Isabelle's internal prover 
metis\footnote{Metis is a trusted prover of Isabelle, since it returns proofs in Isabelle's 
trusted proof kernel. Initially, however, we have worked with Isabelle's Sledgehammer tool in our 
experiments, which in turn
performs calls to several integrated first-order theorem provers. These calls 
then return valuable information on the particular proof dependencies, which in turn suggest the 
successful calls with metis as presented here.}
confirms, \<open>A2a\<close> is implied by \<open>A2b\<close>, \<open>A3a\<close>, \<open>A3b\<close> 
and \<open>A4a\<close>.
\<close>
lemma A2aIsRedundant_1: "(\<box>x)\<box> \<approx> \<box>x" by (metis A2b A3a A3b A4a)
text \<open>
A human readable and comprehensible reconstruction of this redundancy is 
presented below. Our handmade proof employs axioms \<open>A2b\<close>, \<open>A3a\<close>, \<open>A3b\<close>, 
\<open>A4a\<close> and \<open>A5\<close>, that is, this proof could be further optimized by eleminating 
the dependency on \<open>A5\<close>.
\<close>
lemma A2aIsRedundant_2: "(\<box>x)\<box> \<approx> \<box>x" 
 proof -                    
 have  L1:  "\<forall>x. (\<box>\<box>x)\<cdot>((\<box>x)\<cdot>x) \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x" using A5 by metis
 hence L2:  "\<forall>x. (\<box>\<box>x)\<cdot>x \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x" using A3a by metis
 hence L3:  "\<forall>x. (\<box>\<box>x)\<cdot>x \<approx> (\<box>x)\<cdot>x" using A3a by metis
 hence L4:  "\<forall>x. (\<box>\<box>x)\<cdot>x \<approx> x" using A3a by metis
 have  L5:  "\<forall>x. \<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>((\<box>\<box>x)\<cdot>(\<box>x))" using A4a by auto
 hence L6:  "\<forall>x .\<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>\<box>x" using A3a by metis
 hence L7:  "\<forall>x. \<box>\<box>(x\<box>) \<approx> \<box>(\<box>\<box>(x\<box>))\<cdot>(x\<box>)" by auto
 hence L8:  "\<forall>x. \<box>\<box>(x\<box>) \<approx> \<box>(x\<box>)" using L4 by metis
 hence L9:  "\<forall>x. \<box>\<box>(x\<box>) \<approx> \<box>x" using A2b by metis
 hence L10: "\<forall>x. \<box>\<box>x \<approx> \<box>x" using A2b by metis
 hence L11: "\<forall>x. \<box>\<box>((\<box>x)\<box>) \<approx> \<box>\<box>(x\<box>)" using A2b by metis
 hence L12: "\<forall>x. \<box>\<box>((\<box>x)\<box>) \<approx> \<box>x" using L9 by metis
 have  L13: "\<forall>x. (\<box>\<box>((\<box>x)\<box>))\<cdot>((\<box>x)\<box>) \<approx> ((\<box>x)\<box>)" using L4 by auto   
 hence L14: "\<forall>x. (\<box>x)\<cdot>((\<box>x)\<box>) \<approx> (\<box>x)\<box>" using L12 by metis
 hence L15: "\<forall>x. (\<box>x)\<box> \<approx> (\<box>x)\<cdot>((\<box>x)\<box>)" using L14 by auto
 then show ?thesis using A3b by metis
qed                     
text \<open>
Thus, axiom \<open>A2a\<close> can be removed from the theory. Alternatively, 
we could also eliminate \<open>A2b\<close> which is implied by \<open>A1\<close>, 
\<open>A2a\<close> and \<open>A3a\<close>: 
\<close>
lemma A2bIsRedundant: "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a)
(* lemma A3aIsRedundant_2: "(\<box>x)\<cdot>x \<approx> x" sledgehammer (A1 A2a A2b A3b A4a A4b A5) *)
(* lemma A3bIsRedundant_2: "x\<cdot>(x\<box>) \<approx> x" sledgehammer (A1 A2a A2b A3a A4a A4b A5) *)
text \<open>
In fact, by a systematic experimentation within our free logic theorem proving framework, 
we can show that Freyd's and Scedroc's axiomatic theory can be reduced to just the following 
five axioms:
\<close>
axiomatization FreydsAxiomSystemReduced where              
 B1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
 B2a: "((\<box>x)\<box>) \<approx> \<box>x" and
 B3a: "(\<box>x)\<cdot>x \<approx> x" and
 B3b: "x\<cdot>(x\<box>) \<approx> x" and
 B5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"

text \<open>
The dropped axioms can then be introduced as lemmas.
\<close>
lemma B2b: "\<box>(x\<box>) \<approx> \<box>x" by (metis B1 B2a B3a)
lemma B4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis B1 B2a B3a)
lemma B4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" sledgehammer (B1 B2a B3a B3b B5)

(*<*)
text \<open>
In the remainder of this section we present some further tests wrt Freyd's and Scedrov's theory. 
We leave these tests uncommented.
\<close>

abbreviation DirectedEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<greaterapprox>" 60) 
 where "x \<greaterapprox> y \<equiv> ((\<^bold>E x) \<^bold>\<rightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y"  

lemma L1_13: "((\<box>(x\<cdot>y)) \<approx> (\<box>(x\<cdot>(\<box>y)))) \<^bold>\<leftrightarrow> ((\<box>(x\<cdot>y)) \<greaterapprox> \<box>x)" by (metis A1 A2a A3a)

lemma "(\<^bold>\<exists>x. e \<approx> (\<box>x)) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))" by (metis A1 A2b A3b)
lemma "(\<^bold>\<exists>x. e \<approx> (x\<box>)) \<^bold>\<leftrightarrow> e \<approx> (\<box>e)"       by (metis A1 A2b A3a A3b)
lemma "e \<approx> (\<box>e) \<^bold>\<leftrightarrow> e \<approx> (e\<box>)"             by (metis A1 A2b A3a A3b A4a)
lemma "e \<approx> (e\<box>) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)"         by (metis A1 A2b A3a A3b A4a) 
lemma "(\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x)"     by (metis A1 A2b A3a A3b)


abbreviation IdentityMorphism:: "i\<Rightarrow>bool" ("IdM_" [100]60) 
 where "IdM x \<equiv> x \<approx> (\<box>x)"

lemma "(IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (\<box>x))) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))) \<^bold>\<and> 
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (\<box>e)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (e\<box>)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x))"
 by (smt A1 A2a A3a A3b)
(*>*)

section \<open> Summary of Technical Contribution and Further Work \<close>
text \<open> \sloppy
We have presented a new reasoning framework for free logic, and we have exemplary applied it for 
some first experiments in category theory. We have shown that, in our free logic setting, the 
category theory axiom system of Freyd and Scedrov is redundant and that three axioms can be dropped.

Our free logic reasoning framework is publicly available for reuse: Simply download 
Isabelle from \url{https://isabelle.in.tum.de} and initialize it (respectively import) the file
\texttt{FreeFOL.thy} from our sources available at 
\url{www.christoph-benzmueller.de/papers/2016-ICMS.zip}.
Our category theory experiments are contained in the file \texttt{FreydScedrov.thy}.

Comparisons with other theorem provers for free logic are not possible at this stage, 
since we are not aware of  any other existing systems.

We also want to emphasize that this paper has been written entirely within the Isabelle 
framework by utilizing the Isabelle ``build'' tool; cf. @{cite "IsabelleManual2016"}, section~2. 
It is thus an example of a formally verified mathematical document, where the pdf document as 
presented here has been generated directly from the verified source files mentioned above.\footnote{By suitably 
adapting the Isabelle call as contained in file \texttt{runIsabelle.sh} in our zip-package,
the verification and generation process can be easily reproduced by the reader.}

Further work includes the continuation of our formalization studies in category theory. 
It seems plausible that substantial parts of the textbook of Freyd and Scedrov
can now be formalised in our framework. An interesting question clearly is how far automation 
scales and whether some further (previously unknown) insights can eventually be 
contributed by the theorem provers.
Moreover, we have already started to compare the axiom system by Freyd and Scedrov with a more elegant
set of self-dual axioms developed by Scott. 
Furthermore, we plan to extend our studies to projective geometry, which is
another area where free logic may serve as a suitable starting point for formalisation. 

In addition to our implementation of free logic as a theory in Isabelle/HOL, we plan to 
support an analogous logic embedding in the new \textsc{Leo-III} theorem prover @{cite "C45"}. 
The idea is that  \textsc{Leo-III} can then be envoked with a specific flag telling it to automatically 
switch its underlying logic setting from higher-order classical logic to first-order and 
higher-order free logic, while retaining TPTP TH0 @{cite "J22"} as the common input syntax.  
\<close>
(*<*)
end
(*>*)