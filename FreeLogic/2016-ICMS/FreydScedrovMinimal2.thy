(*<*)
theory FreydScedrovMinimal2 imports FreeFOLMinimal
begin 
(*>*)
consts source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
       target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
       composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

abbreviation OrdinaryEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> (((\<^bold>E x) \<^bold>\<leftrightarrow> (\<^bold>E y)) \<^bold>\<and> x \<^bold>= y)" 

(* 
My first email to Peter Freyd on Feb 27, 2016, mentioned the redundancy 
of their axiom system. I pointed to the following example. 
*)

context (* First detection of redundancy *)
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
   lemma A2a: "((\<box>x)\<box>) \<approx> \<box>x" by (smt A1 A2b A3a A3b A4a A4b A5)  
  end


(* 
Together with Dana Scott I then wrote a paper for ICMS 2016 conference on Free 
Logic. As an application example we demonstrated in this paper the use in category theory. 
In our experiments we reduced the eight axioms of Freyd/Scedrov to the following 
five axioms. The paper is available at http://christoph-benzmueller.de/papers/C57.pdf 
*)

context (* My first proposal of a reduced system: still five axioms in ICMS 2016 paper *)
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

context   (* Knopman's proposal of a minimal axiom set, which does not work *)
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
   lemma "(\<box>x)\<cdot>x \<approx> x \<^bold>\<rightarrow> \<^bold>E(x)"  nitpick [user_axioms, show_all, format = 2] oops
   lemma "(\<^bold>E(x) \<^bold>\<and> ((\<box>x)\<cdot>x \<approx> x)) \<^bold>\<rightarrow> \<box>(x\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A2b*) "\<box>(x\<box>) \<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4a*) "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4b*) "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" nitpick [user_axioms, show_all, format = 2] oops
  end



(* Dana Scott, email from June 16, 2016:  
   Just off the top of the head the confusion [in the discussion/email exchange with Freyd] might 
   be in proving: Ex => E(x[]) and Ex => E([]x)
   Yes?
This hint is good. But it is actually the other direction that is the problem, but only
for Knopman's axioms of course.
*)


context  (* Knopman's axioms *)
  assumes 
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
  begin 
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(\<box>x)" by (metis A1 A3a A3b A5)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(x\<box>)" by (metis A1 A3a A3b A5)
   lemma "\<^bold>E(\<box>x) \<^bold>\<rightarrow> \<^bold>E(x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "\<^bold>E(x\<box>) \<^bold>\<rightarrow> \<^bold>E(x)" nitpick [user_axioms, show_all, format = 2] oops
  end



context (* My first proposal of a reduced system: still five axioms in ICMS 2016 paper *)
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
  begin 
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(\<box>x)" by (meson A1 A3a A2a)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(x\<box>)" by (meson A1 A3a A2a)
   lemma "\<^bold>E(\<box>x) \<^bold>\<rightarrow> \<^bold>E(x)" by (metis A1 A3a A2a)
   lemma "\<^bold>E(x\<box>) \<^bold>\<rightarrow> \<^bold>E(x)" by (metis A1 A3a A2a)
  end


(* Peter Freyd, email on June 15, 2016: 
"The double arrow in  "x \<approx> y \<equiv> (((E x) \<leftrightarrow> (E y)) \<and> x = y)"
seems to be the problem. If you replace the double arrow with
another conjunction sign then I agree that the Knopman axioms
fail. But even with the the double arrow it is not equivalent
to the way I defined Kleene equality. As it stands your
definition says that  x \<approx> y  implies  x = y  (surely
((E x) \<leftrightarrow> (E y)) \<and> x = y  implies  x = y). Can undefined terms
be (plain) equal?
To borrow your notation I would want:
   x \<approx> y  \<equiv>  ((E x) v (E y)) => ((E x) \<and> (E y) \<and> (x = y))" *)

abbreviation OrdinaryEquality2:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>\<approx>" 60)  
  where "x \<^bold>\<approx> y  \<equiv>  (((\<^bold>E x) \<^bold>\<or> (\<^bold>E y)) \<^bold>\<rightarrow> ((\<^bold>E x) \<^bold>\<and> (\<^bold>E y) \<^bold>\<and> (x = y)))"

context 
  assumes (* My proposal with new equality *) 
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<^bold>\<approx> (\<box>y))" and
   A2a: "((\<box>x)\<box>) \<^bold>\<approx> \<box>x" and
   A3a: "(\<box>x)\<cdot>x \<^bold>\<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<^bold>\<approx> (x\<cdot>y)\<cdot>z"
  begin
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(\<box>x)" by (meson A1 A3a A2a)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(x\<box>)" by (meson A1 A3a A2a)
   lemma "\<^bold>E(\<box>x) \<^bold>\<rightarrow> \<^bold>E(x)" by (metis A1 A3a A2a)
   lemma "\<^bold>E(x\<box>) \<^bold>\<rightarrow> \<^bold>E(x)" by (metis A1 A3a A2a)
   lemma (*A2b*) "\<box>(x\<box>) \<^bold>\<approx> \<box>x" by (metis A1 A2a A3a) 
   lemma (*A4a*) "\<box>(x\<cdot>y) \<^bold>\<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A2a A3a)
   lemma (*A4b*) "(x\<cdot>y)\<box> \<^bold>\<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A2a A3a)
  end


context (* Knopman's axioms with new equality *)
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<^bold>\<approx> (\<box>y))" and
   A3a: "(\<box>x)\<cdot>x \<^bold>\<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<^bold>\<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<^bold>\<approx> (x\<cdot>y)\<cdot>z" 
  begin 
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(\<box>x)" nitpick [user_axioms, show_all, format = 2] oops 
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(x\<box>)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "\<^bold>E(\<box>x) \<^bold>\<rightarrow> \<^bold>E(x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma "\<^bold>E(x\<box>) \<^bold>\<rightarrow> \<^bold>E(x)" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A2a*) "((\<box>x)\<box>) \<^bold>\<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A2b*) "\<box>(x\<box>) \<^bold>\<approx> \<box>x" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4a*) "\<box>(x\<cdot>y) \<^bold>\<approx> \<box>(x\<cdot>(\<box>y))" nitpick [user_axioms, show_all, format = 2] oops
   lemma (*A4b*) "(x\<cdot>y)\<box> \<^bold>\<approx> ((x\<box>)\<cdot>y)\<box>" nitpick [user_axioms, show_all, format = 2] oops
  end


context (* Knopman's axioms with new equality and with two additional axioms *)
  assumes  
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<^bold>\<approx> (\<box>y))" and
   A3a: "(\<box>x)\<cdot>x \<^bold>\<approx> x" and
   A3b: "x\<cdot>(x\<box>) \<^bold>\<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<^bold>\<approx> (x\<cdot>y)\<cdot>z" and
   A6a: "\<^bold>E(\<box>x) \<^bold>\<rightarrow> \<^bold>E(x)" and
   A6b: "\<^bold>E(x\<box>) \<^bold>\<rightarrow> \<^bold>E(x)"
  begin 
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(\<box>x)" by (meson A1 A3a A3b A6a)
   lemma "\<^bold>E(x) \<^bold>\<rightarrow> \<^bold>E(x\<box>)" by (metis A1 A3a A3b A5 A6a)
   lemma (*A2a*) "((\<box>x)\<box>) \<^bold>\<approx> \<box>x" by (meson A1 A3a A6a A6b)
   lemma (*A2b*) "\<box>(x\<box>) \<^bold>\<approx> \<box>x" by (metis A1 A3a A6a A6b)
   lemma (*A4a*) "\<box>(x\<cdot>y) \<^bold>\<approx> \<box>(x\<cdot>(\<box>y))" by (metis A1 A3a A6a A6b)
   lemma (*A4b*) "(x\<cdot>y)\<box> \<^bold>\<approx> ((x\<box>)\<cdot>y)\<box>" by (metis A1 A3a A6a A6b)
  end




(*<*)
end
(*>*)