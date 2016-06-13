(*<*)
theory FreydScedrovMinimal imports FreeFOL 
begin
(*>*)

consts source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
       target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
       composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

abbreviation OrdinaryEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> (((\<^bold>E x) \<^bold>\<leftrightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y)"  


context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma "\<^bold>E((\<box>x)\<cdot>x)" using A1 A2a by blast
   lemma A2b: "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a) 
   lemma A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
   lemma A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
   lemma A3b: "x\<cdot>(x\<box>) \<approx> x" using A1 A2a A3a fStarAxiom by blast
  end


context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2b: "\<box>(x\<box>) \<approx> \<box>x" and
   (* A3a: "(\<box>x)\<cdot>x \<approx> x" *) 
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma A3a: "(\<box>x)\<cdot>x \<approx> x" nitpick 
   lemma A2b: "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a) 
   lemma A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
   lemma A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
   lemma A3b: "x\<cdot>(x\<box>) \<approx> x" using A1 A2a A3a fStarAxiom by blast
  end

context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin  (* not minimal *)
   lemma "\<^bold>E((\<box>x)\<cdot>x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma A2a: "((\<box>x)\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma A2b: "\<box>(x\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" nitpick [user_axioms, show_all, format = 2] oops
   lemma A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" nitpick [user_axioms, show_all, format = 2] oops
  end
 
context 
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2b: "\<box>(x\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" and
   A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))"
  begin
   lemma A2a: "((\<box>x)\<box>) \<approx> \<box>x" by (metis A3a A3b A2b A4a)
   lemma "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
  end





lemma "\<^bold>E((\<box>x)\<cdot>x)" using A1 A2a by blast   (* not provable without A2a; hence Freyds new minimal set 
 without A2a is not  *)
 

(* lemma A2a: "((\<box>x)\<box>) \<approx> \<box>x" nitpick [user_axioms](A1 A3a A3b A5) oops *)
lemma B2b: "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a)
lemma B4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
lemma B4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" sledgehammer (A1 A2a A3a A3b A5)



lemma 
  assumes 1: "\<not>G \<longrightarrow> \<not>(P \<longrightarrow> A)" and
          2: "\<not>P"
  shows "G"





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