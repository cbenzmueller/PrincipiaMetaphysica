(*<*)
theory FreydScedrovMinimal imports FreeFOL 
begin 
(*>*)
consts source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
       target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
       composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

abbreviation OrdinaryEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 (* where "x \<approx> y \<equiv> (((\<^bold>E x) \<^bold>\<leftrightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y)" *)
 (* Peter Freyd, email on June 15, 2016: "To borrow your notation I would want:
    x \<approx> y  \<equiv>  ((E x) v (E y)) => ((E x) \<and> (E y) \<and> (x = y))" *)
 where "x \<approx> y  \<equiv>  (((\<^bold>E x) \<^bold>\<or> (\<^bold>E y)) \<^bold>\<rightarrow> ((\<^bold>E x) \<^bold>\<and> (\<^bold>E y) \<^bold>\<and> (x = y)))"


context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
  begin 
   (* Dana Scott, email from June 16, 2016:  
      Just off the top of the head the confusion might be in proving: Ex => E(x[]) and Ex => E([]x)
      Yes?*)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(\<box>x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(x\<box>)" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A2a*) "((\<box>x)\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   (* this only holds when we assume that x is defined *)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> ((\<box>x)\<box>) \<approx> \<box>x" using A1 A3a by blast 
   lemma "\<^bold>E((\<box>x)\<cdot>x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E((\<box>x)\<cdot>x)" using A3a by blast
   lemma "(\<box>x)\<cdot>x \<approx> x \<^bold>\<rightarrow> \<^bold>E(x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "(\<^bold>E(x) \<^bold>\<and> ((\<box>x)\<cdot>x \<approx> x)) \<^bold>\<rightarrow> \<box>(x\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A2b*) "\<box>(x\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4a*) "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4b*) "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" nitpick [user_axioms, show_all, format = 2] oops
  end


context (* A minimal axioms system for Freyd/Scedrov *)
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
  (* Dana Scott, email from June 16, 2016:  
      Just off the top of the head the confusion might be in proving: Ex => E(x[]) and Ex => E([]x)
      Yes?*)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(\<box>x)" using A1 A2a A3a by auto
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(x\<box>)" using A1 A2a A3a by auto
   lemma "\<^bold>E((\<box>x)\<cdot>x)" using A1 A2a by blast
   lemma (*A2b*) "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a) 
   lemma (*A4a*) "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
   lemma (*A4b*) "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
   lemma (*A3b*) "x\<cdot>(x\<box>) \<approx> x" using A1 A2a A3a fStarAxiom by blast
  end









context (* A minimal axioms system for Freyd/Scedrov *)
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma "\<^bold>E((\<box>x)\<cdot>x)" using A1 A2a by blast
   lemma (*A2b*) "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a) 
   lemma (*A4a*) "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
   lemma (*A4b*) "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
   lemma (*A3b*) "x\<cdot>(x\<box>) \<approx> x" using A1 A2a A3a fStarAxiom by blast
  end


(* 
My first email to Peter Freyd on Feb 27, 2016, mentioned the redundancy 
of their axiom system. I pointed to the following example. 
*)

context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   (* A2a: "((\<box>x)\<box>) \<approx> \<box>x" and*)
   A2b: "\<box>(x\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" and
   A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma A2a: "((\<box>x)\<box>) \<approx> \<box>x" by (smt A1 A2b A3a A3b A4a A5)
  end





(* 
Together with Dana Scott I then wrote a paper for ICMS 2016 conference on Free 
Logic. As an application example we demonstrated the use in category theory. 
In our experiments we reduced the 8 axioms of Freyd/Scedrov to the following 
5 axioms. The paper is available at http://christoph-benzmueller.de/papers/C57.pdf 
*)

context 
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma (*A2b*) "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a) 
   lemma (*A4a*) "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
   lemma (*A4b*) "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
  end



(* 
On June 8, 2016, I wrote an email to Andre Scedrov in which I pointed them to 
the above paper.
On June 12, 2016, Peter Freyd replied:
"Take a look at the first item in http://www.math.upenn.edu/~pjf/amplifications.pdf
I did some work on the last section on June 6. I think the first item dates from 
the beginning of the website some decades ago. Martin Knopman is the only human 
I know who caught the redundancy.         Best thoughts,  Peter Freyd"
Here is the version proposed in http://www.math.upenn.edu/~pjf/amplifications.pdf 
However, the provers cannot confirm this version, and Nitpick tells us that there 
is a countermodel.    
*)

context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
  begin 
   lemma (*A2a*) "((\<box>x)\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   (* this only holds when we assume that x is defined *)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> ((\<box>x)\<box>) \<approx> \<box>x" using A1 A3a by blast 
   lemma "\<^bold>E((\<box>x)\<cdot>x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E((\<box>x)\<cdot>x)" using A3a by blast
   lemma "(\<box>x)\<cdot>x \<approx> x \<^bold>\<rightarrow> \<^bold>E(x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "(\<^bold>E(x) \<^bold>\<and> ((\<box>x)\<cdot>x \<approx> x)) \<^bold>\<rightarrow> \<box>(x\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A2b*) "\<box>(x\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4a*) "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4b*) "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" nitpick [user_axioms, show_all, format = 2] oops
  end


(* 
However, after playing a bit more with the axiom set, I was able to reduce it to
the following four axioms. 
*)   

context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma "\<^bold>E((\<box>x)\<cdot>x)" using A1 A2a by blast
   lemma (*A2b*) "\<box>(x\<box>) \<approx> \<box>x" by (metis A1 A2a A3a) 
   lemma (*A4a*) "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
   lemma (*A4b*) "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
   lemma (*A3b*) "x\<cdot>(x\<box>) \<approx> x" using A1 A2a A3a fStarAxiom by blast
  end




(* 
I claim that this is a minimal set of axioms. Neither A2a nor A3a can be omitted. 
For A1 and A5 that is anyway clear
*)

context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma (*A2a*) "((\<box>x)\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
  end

context
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma (*A3a*) "(\<box>x)\<cdot>x \<approx> x" nitpick [user_axioms, show_all, format = 2] oops
  end

(*<*)
end
(*>*)