theory Scott_FreeFOL_and_CategoryTheory imports Main
begin 

typedecl i                                       (* Type for indiviuals *)
consts fExistence:: "i\<Rightarrow>bool" ("E")   (* Existence predicate *)

abbreviation fNot:: "bool\<Rightarrow>bool" ("\<^bold>\<not>")                           where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr "\<^bold>\<rightarrow>" 49)       where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 
abbreviation fForall:: "(i\<Rightarrow>bool)\<Rightarrow>bool" ("\<^bold>\<forall>")                    where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E(x)\<longrightarrow>\<Phi>(x)"   
abbreviation fForallBinder:: "(i\<Rightarrow>bool)\<Rightarrow>bool" (binder "\<^bold>\<forall>" [8] 9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"
abbreviation fOr (infixr "\<^bold>\<or>" 51)                                 where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 52)                                where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 50)                             where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation fExists ("\<^bold>\<exists>")                                       where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

 
  (* We now introduce the basic notions for category theory. *)
consts domain:: "i\<Rightarrow>i" ("dom _" [108] 109) 
       codomain:: "i\<Rightarrow>i" ("cod _" [110] 111) 
       composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)


(* We now repeat our experiments from the ICMS paper and the email exchange with Freyd. These
   experiments studied Freyd's axiom system:

Freyd's axioms for category theory
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" 
 A2a: "(\<box>x)\<box> \<approx> \<box>x" 
 A2b: "\<box>(x\<box>) \<approx> x\<box>" 
 A3a: "(\<box>x)\<cdot>x \<approx> x" 
 A3b: "x\<cdot>(x\<box>) \<approx> x" 
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" 
 A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" 
 A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"

We translate them here step-by-step into Scott's notation. The first thing is to reverse 
all x\<cdot>y by y\<cdot>x, to appropriately map their different order wrt. composition:
 A1:  "\<^bold>E(y\<cdot>x) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" 
 A2a: "(\<box>x)\<box> \<approx> \<box>x" 
 A2b: "\<box>(x\<box>) \<approx> x\<box>" 
 A3a: "x\<cdot>(\<box>x) \<approx> x" 
 A3b: "(x\<box>)\<cdot>x \<approx> x" 
 A4a: "\<box>(y\<cdot>x) \<approx> \<box>((\<box>y)\<cdot>x)" 
 A4b: "(y\<cdot>x)\<box> \<approx> (y\<cdot>(x\<box>))\<box>" 
 A5:  "(z\<cdot>y)\<cdot>x \<approx> z\<cdot>(y\<cdot>x)"

We rename the variables to get them in usual order: 
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((y\<box>) \<approx> (\<box>x))" 
 A2a: "(\<box>x)\<box> \<approx> \<box>x" 
 A2b: "\<box>(x\<box>) \<approx> x\<box>" 
 A3a: "x\<cdot>(\<box>x) \<approx> x" 
 A3b: "(x\<box>)\<cdot>x \<approx> x" 
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>((\<box>x)\<cdot>y)" 
 A4b: "(x\<cdot>y)\<box> \<approx> (x\<cdot>(y\<box>))\<box>" 
 A5:  "(x\<cdot>y)\<cdot>z \<approx> x\<cdot>(y\<cdot>z)"

We replace _\<box> by cod_ and \<box>_ by dom_:
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((cod y) \<approx> (dom x))" 
 A2a: "cod (dom x) \<approx> dom x" 
 A2b: "dom (cod x) \<approx> cod x" 
 A3a: "x\<cdot>(dom x) \<approx> x" 
 A3b: "(cod x)\<cdot>x \<approx> x" 
 A4a: "dom (x\<cdot>y) \<approx> dom ((dom x)\<cdot>y)" 
 A4b: "cod (x\<cdot>y) \<approx> cod (x\<cdot>(cod y))" 
 A5:  "(x\<cdot>y)\<cdot>z \<approx> x\<cdot>(y\<cdot>z)"

Freyd's \<approx> is symmetric, hence we get:

We replace _\<box> by cod_ and \<box>_ by dom_:
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ( (dom x) \<approx> (cod y))" 
 A2a: "cod (dom x) \<approx> dom x" 
 A2b: "dom (cod x) \<approx> cod x" 
 A3a: "x\<cdot>(dom x) \<approx> x" 
 A3b: "(cod x)\<cdot>x \<approx> x" 
 A4a: "dom (x\<cdot>y) \<approx> dom ((dom x)\<cdot>y)" 
 A4b: "cod (x\<cdot>y) \<approx> cod (x\<cdot>(cod y))" 
 A5:  "(x\<cdot>y)\<cdot>z \<approx> x\<cdot>(y\<cdot>z)"

In an email, Dana Scott presented me his translation of Freyd's axioms in his own notation. Here is 
the copied text from his email (note that his versions coincides with the above):

FREYD'S AXIOMS FOR A CATEGORY IN FREE LOGIC (Sott's notation)
 (A1) E(x o y) <==> dom(x) \<approx> cod(y)
 (A2a) cod(dom(x)) \<approx> dom(x)
 (A2b) dom(cod(x)) \<approx> cod(x)
 (A3a) x o dom(x) \<approx> x
 (A3b) cod(x) o x \<approx> x
 (A4a) dom(x o y) \<approx> dom(dom(x) o y)
 (A4b) cod(x o y) \<approx> cod(x o cod(y))
 (A5) x o (y o z) \<approx> (x o y) o z
*)

(* My first interpretation of Freyd's equality (which is given informal in his textbook in 1.11) was 
   "x \<approx> y \<equiv> (E(x) \<^bold>\<leftrightarrow> E(y)) \<^bold>\<and> (x = y)". We denote this version of equality with "\<approx>". Freyd later 
   told me via email that he intended Kleene equality instead; but see the experiments 
   for Kleene equality below! *)
abbreviation FreydEquality1:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> (E(x) \<^bold>\<leftrightarrow> E(y)) \<^bold>\<and> (x = y)"  


context (* Freyd_1:
   Freyd's axioms are consistent with "\<approx>" as equality; but note that the model generated
   by Nitpick identifies E with D, that is, in this model D-E is empty. *)
assumes 
     A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<approx> cod y)" 
 and A2a: "cod (dom x) \<approx> dom x"  
 and A2b: "dom (cod x) \<approx> cod x"  
 and A3a: "x\<cdot>(dom x) \<approx> x" 
 and A3b: "(cod x)\<cdot>x \<approx> x" 
 and A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" 
 and A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" 
 and A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
begin 
 (* Nitpick does find a model; in this model D-E is empty.  *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
end


context (* Freyd_2:
   Freyd's axioms are redundant for "\<approx>" and non-empty D-E. 
   This coincides with the results the results in our ICMS 2016 paper. *)
assumes 
     A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<approx> cod y)" 
      (* A2a:  "cod (dom x) \<approx> dom x" and *)
 and A2b: "dom (cod x) \<approx> cod x" 
 and A3a: "x\<cdot>(dom x) \<approx> x"
 and A3b: "(cod x)\<cdot>x \<approx> x" 
 and A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)"
 and A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))"
 and A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"
 and NE:  "\<exists>x. \<^bold>\<not>(E(x))"    (* Note that "\<exists>" is existence from the meta-logic, which ranges over D. *)
begin 
  lemma (*A2a*) "cod (dom x) \<approx> dom x" by (metis A1 A2b A3b)
end

 
context (* Freyd_3:
   Freyd's axioms are even more redundant for "\<approx>" and non-empty D-E.
   This coincides with the results the results in our ICMS 2016 paper. *)
assumes 
     A1:   "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<approx> (cod y))" 
 and A2a:  "cod (dom x) \<approx> dom x" 
     (* A2b:  "dom (cod x) \<approx> cod x" and *)
 and A3a: "x\<cdot>(dom x) \<approx> x"
 and A3b: "(cod x)\<cdot>x \<approx> x"
     (* A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and *)
     (* A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and *)
 and A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
 and NE: "\<exists>x. \<^bold>\<not>(E(x))"   
begin 
  lemma (*A2b*) "dom (cod x) \<approx> cod x" by (metis A1 A3a A2a)
  lemma (*A4a*) "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" by (metis A1 A3a A2a)
  lemma (*A4b*) "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" by (metis A1 A3a A2a)
end


context (* Freyd_4: 
   Freyd's axioms are inconsistent for "\<approx>" and non-empty D-E. 
   This coincides with the results the results in our ICMS 2016 paper. *)
assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" 
 and A2a:  "cod (dom x) \<approx> dom x" 
 and A2b:  "dom (cod x) \<approx> cod x" 
 and A3a: "x\<cdot>(dom x) \<approx> x" 
 and A3b: "(cod x)\<cdot>x \<approx> x" 
 and A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" 
 and A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" 
 and A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
 and NE: "\<exists>x. \<^bold>\<not>(E(x))" 
begin 
  (* Nitpick does *not* find a model. *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
  (* We can prove falsity. *)
  lemma False by (metis A1 A3a NE local.A2a) 
end


(* 
   Peter Freyd wrote me in an email, that he wants Kleene equality, which we denote as "\<simeq>" below. 
   Peter Freyd, email on June 15, 2016: 
      "... To borrow your notation I would want:
                 x \<approx> y  \<equiv>  ((E x) v (E y)) => ((E x) \<and> (E y) \<and> (x = y))"

   Hence, We now introduce "\<simeq>" and repeat the above experiments with it.
 *)

abbreviation KleeneEquality_Freyd:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<simeq>" 60) 
 where "x \<simeq> y  \<equiv>  (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (x = y))" 

lemma ref: "x \<simeq> x" by simp
lemma sym: "x \<simeq> y \<^bold>\<rightarrow> y \<simeq> x" by blast
lemma tra: "(x \<simeq> y \<^bold>\<and> y \<simeq> z) \<^bold>\<rightarrow> x \<simeq> z" by blast


context (* Freyd_5: 
   Freyd's axioms are consistent for "\<simeq>"; but note that the model generated
   by Nitpick identifies E with D, that is, in this model D-E is empty. *)
assumes 
     A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<simeq> cod y)" 
 and A2a: "cod (dom x) \<simeq> dom x"
 and A3a: "x\<cdot>(dom x) \<simeq> x" 
 and A3b: "(cod x)\<cdot>x \<simeq> x" 
 and A4a: "dom(x\<cdot>y) \<simeq> dom(dom(x)\<cdot>y)" 
 and A5b: "cod(x\<cdot>y) \<simeq> cod(x\<cdot>cod(y))"
 and A5:  "x\<cdot>(y\<cdot>z) \<simeq> (x\<cdot>y)\<cdot>z"
begin 
  (* nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
end



context (* Freyd_6: 
   Freyd's axioms are inconsistent for "\<simeq>" and non-empty D-E. *)
assumes 
     A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<simeq> cod y)" 
 and A2a: "cod (dom x) \<simeq> dom x"
 and A3a: "x\<cdot>(dom x) \<simeq> x" 
 and A3b: "(cod x)\<cdot>x \<simeq> x"
 and A4a: "dom(x\<cdot>y) \<simeq> dom(dom(x)\<cdot>y)" 
 and A5b: "cod(x\<cdot>y) \<simeq> cod(x\<cdot>cod(y))" 
 and A5:  "x\<cdot>(y\<cdot>z) \<simeq> (x\<cdot>y)\<cdot>z" 
 and NE:  "\<exists>x. \<^bold>\<not>(E(x))" 
begin 
  (* Nitpick does *not* find a model. *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops (* no model *)
  (* We can prove falsity. *)
  lemma False by (metis A1 A3a A2a NE)
end


context (* Freyd_7: 
   Freyd's axioms are inconsistent for "\<simeq>" and non-empty D-E. 
   We present a detailed, intuitive proof. *)   
assumes 
     A1:   "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<simeq> cod y)"
 and A2a:  "cod (dom x) \<simeq> dom x" 
 and A3a:  "x\<cdot>(dom x) \<simeq> x" 
begin 
  lemma Nonexistence_implies_Falsity:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then prove falsity. *) 
  proof -
     (* Let a be an undefined object *)
   obtain a where 1: "\<^bold>\<not>(E a)" using assms by auto
     (* We instantiate axiom A3a with "a". *)
   have 2: "a\<cdot>(dom a) \<simeq> a" using A3a by blast  
     (* By unfolding the definition of "\<simeq>" we get from L1 that "a\<cdot>(dom a)" is not defined. This is 
        easy to see, since if "a\<cdot>(dom a)" were defined, we also had that "a" is defined, which is 
        not the case by assumption. *)
   have 3: "\<^bold>\<not>(E(a\<cdot>(dom a)))" using 1 2 by blast
     (* We instantiate axiom A1 with "a" and "dom a". *)
   have 4: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<simeq> cod(dom a)" using A1 by blast
     (* We instantiate axiom A2a with "a". *)
   have 5: "cod(dom a) \<simeq> dom a" using A2a by blast 
     (* We use L4 (and symmetry and transitivity of "\<simeq>") to rewrite the right-hand of the 
        equivalence L3 into into "dom a \<simeq> dom a". *) 
   have 6: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<simeq> dom a" using 4 5 tra sym by blast
     (* By reflexivity of "\<simeq>" we get that "a\<cdot>(dom a)" must be defined. *)
   have 7: "E(a\<cdot>(dom a))" using 6 ref by blast
     (* We have shown in L6 that "a\<cdot>(dom a)" is defined, and in L2 that it is undefined.  
        Contradiction. *)
   then show ?thesis using 7 3 by blast
  qed

    (* Hence: all objects must be defined in Freyd's theory (or we get inconsistency). *)
  lemma "\<forall>x. E(x)" using Nonexistence_implies_Falsity by auto
end


 (*
 Dana Scott proposes a slightly different variant of axioms in his paper 
 "Identity and Existence in Intuitionistic Logic (1977, published 1979)". 
 In particular Scott distinguishes two notions of equality: 
   (i) Kleene equality as also used by Freyd above (denoted here as "\<^bold>=\<^bold>="), and 
  (ii) a weaker, non-reflexive notion of equality (denoted here as "\<^bold>=").
 
 Scott uses "\<^bold>=" in the axiom on existence of morphism compositions (A1 above, and S3 below)
 and "\<^bold>=\<^bold>=" in all other axioms. 

 SCOTT'S AXIOMS FOR A CATEGORY IN FREE LOGIC (Scott's notation)

  (S1) Ex <==> Edom(x)              (we actually only need right to left direction)
  (S2) Ex <==> Ecod(x)              (we actually only need right to left direction)
  (S3) E(x o y) <==> dom(x) = cod(y)
  (S4) x o (y o z) == (x o y) o z
  (S5) x o dom(x) == x
  (S6) cod(x) o x == x
 *)


 (* Non-bold "=" is identity on the raw domain D. Bold-face "\<^bold>=" is weak, non-reflexive
   identity on E. Bold-face  "\<^bold>=\<^bold>=" is Kleene equality. *) 
abbreviation eq1 (infixr "\<^bold>=" 56)  where "x \<^bold>= y \<equiv> (E(x) \<^bold>\<and> E(y)  \<^bold>\<and> (x = y))"
abbreviation eq2 (infixr "\<^bold>=\<^bold>=" 56) where "x \<^bold>=\<^bold>= y \<equiv> ((E(x) \<^bold>\<or> E(y)) \<^bold>\<rightarrow> (x\<^bold>=y))"

 (* We prove some properties of "=", "\<^bold>=" and "\<^bold>=\<^bold>="  *)
lemma "x \<^bold>= y \<^bold>\<leftrightarrow> ((x = y) \<^bold>\<and> E(x))" by simp 
lemma "x \<^bold>= y \<^bold>\<leftrightarrow> ((x = y) \<^bold>\<and> E(y))" by simp 
lemma "x \<^bold>=\<^bold>= y \<^bold>\<leftrightarrow> ((x \<^bold>= y) \<^bold>\<or> (\<^bold>\<not>(E(x)) \<^bold>\<and> \<^bold>\<not>(E(y))))" by auto

(* "\<^bold>=" is an equivalence relation on E *)
lemma "\<^bold>\<forall>x. (x \<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y. (x \<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y z. ((x \<^bold>= y) \<^bold>\<and> (y \<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>= z)" by simp

(* Reflexivity fails on D for "\<^bold>=" , i.e. "\<^bold>=" is only a partial equivalence rel on D *)
lemma "(x \<^bold>= x)" nitpick [user_axioms, show_all] oops  (* countermodel *)
lemma "(x \<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>= x)" by auto
lemma "((x \<^bold>= y) \<^bold>\<and> (y \<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>= z)" by simp

(* "\<^bold>=\<^bold>=" is an equivalence relation on E *)
lemma "\<^bold>\<forall>x. (x \<^bold>=\<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y. (x \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>=\<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y z. ((x \<^bold>=\<^bold>= y) \<^bold>\<and> (y \<^bold>=\<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= z)" by simp

(* "\<^bold>=\<^bold>=" is also an equivalence relation on D, i.e. "\<^bold>=\<^bold>=" is a total equivalence rel on D *)
lemma "(x \<^bold>=\<^bold>= x)" by simp
lemma "(x \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>=\<^bold>= x)" by auto
lemma "((x \<^bold>=\<^bold>= y) \<^bold>\<and> (y \<^bold>=\<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= z)" by auto

(* If elements of D-E are not important, then we need say nothing about them, for example: *)
lemma "(\<^bold>\<not>(E(x\<cdot>y)) \<^bold>\<and> \<^bold>\<not>(E(u\<cdot>v))) \<^bold>\<rightarrow> ((x\<cdot>y) \<^bold>=\<^bold>= (u\<cdot>v))" by simp
(* But there is no reason to assume (non-bold "=" is raw identity on D): *)
lemma "(\<^bold>\<not>(E(x\<cdot>y)) \<^bold>\<and> \<^bold>\<not>(E(u\<cdot>v))) \<^bold>\<rightarrow> ((x\<cdot>y) = (u\<cdot>v))" nitpick [user_axioms, show_all] oops (* countermodel *)


context (* S-Axioms_1: 
   We get consistency for Scott's axioms for "\<^bold>=" in S3. *)
assumes 
     S1: "E(dom x) \<^bold>\<rightarrow> E(x)" 
 and S2: "E(cod x) \<^bold>\<rightarrow> E(x)"  
 and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)"  
 and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x"  
 and S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops
end


context (* S-Axioms_2: 
    We additionally assume that D-E is nonempty (i.e. "\<exists>x. \<^bold>\<not>(E(x))" holds, for "\<exists>" ranging over D); 
    we still get consistency. That is what we want! *)
assumes 
     S1: "E(dom x) \<^bold>\<rightarrow> E(x)" 
 and S2: "E(cod x) \<^bold>\<rightarrow> E(x)"  
 and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)"  
 and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x"  
 and S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x"
 and ex: "\<exists>x. \<^bold>\<not>(E(x))" 
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
end


(* Finally, we repeat the central inconsistency argument again in Freyd's original notation *)

consts  source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
        target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
    (*  composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110) *)

context (* Freyd_8: 
   Freyd's axioms are inconsistent for "\<simeq>" and non-empty D-E. 
   We present a detailed, intuitive proof. *)   
assumes           
     A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (x\<box> \<simeq> \<box>y)" 
 and A2a: "((\<box>x)\<box>) \<simeq> \<box>x" 
 and A2b: "\<box>(x\<box>) \<simeq> \<box>x" 
 and A3a: "(\<box>x)\<cdot>x \<simeq> x" 
 and A3b: "x\<cdot>(x\<box>) \<simeq> x" 
 and A4a: "\<box>(x\<cdot>y) \<simeq> \<box>(x\<cdot>(\<box>y))" 
 and A4b: "(x\<cdot>y)\<box> \<simeq> ((x\<box>)\<cdot>y)\<box>" 
 and A5:  "x\<cdot>(y\<cdot>z) \<simeq> (x\<cdot>y)\<cdot>z"
begin
  (* Nitpick does find a model; in this model D-E is empty.  *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 

  lemma Nonexistence_implies_Falsity_2:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty. *) 
    shows False            (* We then prove falsity. *) 
  using A1 A2a A3a assms by blast

  lemma Nonexistence_implies_Falsity_3:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then prove falsity. *) 
  proof -
     (* Let a be an undefined object *)
   obtain a where 1: "\<^bold>\<not>(E a)" using assms by auto
     (* We instantiate axiom A3a with "a". *)
   have 2: "(\<box>a)\<cdot>a \<simeq> a" using A3a by blast
     (* By unfolding the definition of "\<simeq>" we get from 1 that "(\<box>a)\<cdot>a)" is not defined. This is 
        easy to see, since if "(\<box>a)\<cdot>a)" were defined, we also had that "a" is defined, which is 
        not the case by assumption. *)
   have 3: "\<^bold>\<not>(E((\<box>a)\<cdot>a))" using 1 2 by blast
     (* We instantiate axiom A1 with "(\<box>a)" and "a". *)
   have 4: "E((\<box>a)\<cdot>a) \<^bold>\<leftrightarrow> (\<box>a)\<box> \<simeq> \<box>a" using A1 by blast
     (* We instantiate axiom A2a with "a". *)
   have 5: "(\<box>a)\<box> \<simeq> \<box>a" using A2a by blast 
     (* We use 4 (and symmetry and transitivity of "\<simeq>") to rewrite the right-hand of the 
        equivalence 3 into into "\<box>a \<simeq> \<box>a". *) 
   have 6: "E((\<box>a)\<cdot>a)" using 4 5 by blast
     (* We have "\<^bold>\<not>(E((\<box>a)\<cdot>a))" and "\<^bold>(E((\<box>a)\<cdot>a))", hence Falsity. *)
   then show ?thesis using 6 3 by blast
  qed

  lemma "\<forall>x. E(x)" using Nonexistence_implies_Falsity_3 by auto

  lemma Nonexistence_implies_Falsity_4:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False            (* We then prove falsity. *) 
  proof -
     (* Let a be an undefined object *)
   obtain a where 1: "\<^bold>\<not>(E a)" using assms by auto
     (* We instantiate axiom A3a with "a". *)
   have 2: "(\<box>a)\<cdot>a \<simeq> a" using A3a by blast  
     (* By unfolding the definition of "\<simeq>" we get from L1 that "(\<box>a)\<cdot>a)" is not defined. This is 
        easy to see, since if "(\<box>a)\<cdot>a)" were defined, we also had that "a" is defined, which is 
        not the case by assumption. *)
   have 3: "\<^bold>\<not>(E((\<box>a)\<cdot>a))" using 1 2 by blast
     (* We instantiate axiom A1 with "a" and "dom a". *)
   have 4: "E((\<box>a)\<cdot>a) \<^bold>\<leftrightarrow> (\<box>a)\<box> \<simeq> \<box>a" using A1 by blast
     (* We instantiate axiom A2a with "a". *)
   have 5: "(\<box>a)\<box> \<simeq> \<box>a" using A2a by blast 
     (* We use L4 (and symmetry and transitivity of "\<simeq>") to rewrite the right-hand of the 
        equivalence L3 into into "\<box>a \<simeq> \<box>a". *) 
   have 6: "E((\<box>a)\<cdot>a) \<^bold>\<leftrightarrow> \<box>a \<simeq> \<box>a" using 4 5 tra sym by blast
     (* By reflexivity of "\<simeq>" we get that "a\<cdot>(dom a)" must be defined. *)
   have 7: "E((\<box>a)\<cdot>a)" using 6 ref by blast
     (* We have shown in L6 that "a\<cdot>(dom a)" is defined, and in L2 that it is undefined.  
        Contradiction. *)
   then show ?thesis using 7 3 by blast
  qed
end

context (* S-Axioms in Freyd's Notation: 
    We study Scott's axioms in Freyd's notation. *)
assumes 
     S1: "E(\<box>x) \<^bold>\<rightarrow> E(x)" 
 and S2: "E(x\<box>) \<^bold>\<rightarrow> E(x)"  
 and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (x\<box> \<^bold>= \<box>y)" 
 and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and S5: "(\<box>x)\<cdot>x \<^bold>=\<^bold>= x"
 and S6: "x\<cdot>(x\<box>) \<^bold>=\<^bold>= x" 
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 

  lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

  lemma Another_Test:
    assumes "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<and> (\<exists>x. (E x))"   
                 (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 
end


abbreviation Id where "Id i \<equiv> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> (E(u\<cdot>v) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v))))"
(* Later we discovered that this was a wrong definition of identity morphism (the bracketing is not correct). *)

context (* Experiments with new axioms from Dana Scott 1: Are these axioms derivable from the S-axioms? *)
assumes 
      S1: "E(dom x) \<^bold>\<rightarrow> E(x)" 
  and S2: "E(cod x) \<^bold>\<rightarrow> E(x)" 
  and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)"
  and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z"
  and S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" 
  and S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
begin 
  lemma (*test*)  "\<^bold>\<forall>x. Id(cod(x))" nitpick  [user_axioms, show_all, format = 2] oops (* Countermodel *)

  lemma (*D2:*) "\<^bold>\<forall>i.(dom x \<^bold>=\<^bold>= i \<^bold>\<leftrightarrow> (Id(i) \<^bold>\<and> i\<cdot>x \<^bold>=\<^bold>= x))" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*D3:*) "\<^bold>\<forall>i.(cod x \<^bold>=\<^bold>= i \<^bold>\<leftrightarrow> (Id(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x))" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*E1:*) "E(x\<cdot>y) \<^bold>\<rightarrow>  (E(x) \<^bold>\<and> E(y))" using S1 S2 S3 by blast 
  lemma (*E2:*) "(\<^bold>\<forall>x.\<^bold>\<exists>y. E(x\<cdot>y)) \<^bold>\<and> (\<^bold>\<forall>y.\<^bold>\<exists>x. E(x\<cdot>y))" by (meson S3 S5 S6)
  lemma (*E3:*) "E(x\<cdot>y) \<^bold>\<rightarrow> (\<^bold>\<exists>i. (Id(i) \<^bold>\<and> x\<cdot>(i\<cdot>y) \<^bold>=\<^bold>= x\<cdot>y))" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*E4:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using S4 by blast

  lemma (*F1:*) "E(x\<cdot>y) \<^bold>\<rightarrow>  (E(x) \<^bold>\<and> E(y))" using S1 S2 S3 by blast 
  lemma (*F2:*) "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> E(x\<cdot>y)" by (metis S2 S3)
  lemma (*F3:*) "\<^bold>\<forall>x. \<^bold>\<exists>i. (i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<rightarrow> i\<cdot>y \<^bold>=\<^bold>= y))" by (metis S3 S5 S6) 
  lemma (*F4:*) "\<^bold>\<forall>y. \<^bold>\<exists>j. (j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>y) \<^bold>\<rightarrow> x\<cdot>j \<^bold>=\<^bold>= x))" by (metis S3 S5 S6) 
  lemma (*F5:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using S4 by blast
end


context (* Experiments with new axioms from Dana Scott 2: Are the S-Axioms/F-Axioms implied? *)
assumes 
  (*   D1: "Id(i) \<^bold>\<leftrightarrow> (i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> (E(u\<cdot>v) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v)))))" and 
    Id is now defined as an abbreviation, see above  *)   
     D2: "\<^bold>\<forall>i. (dom x \<^bold>=\<^bold>= i \<^bold>\<leftrightarrow> (Id(i) \<^bold>\<and> i\<cdot>x \<^bold>=\<^bold>= x))"
 and D3: "\<^bold>\<forall>i. (cod x \<^bold>=\<^bold>= i \<^bold>\<leftrightarrow> (Id(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x))"
 and E1: "E(x\<cdot>y) \<^bold>\<rightarrow>  (E(x) \<^bold>\<and> E(y))"
 and E2: "(\<^bold>\<forall>x.\<^bold>\<exists>y. E(x\<cdot>y)) \<^bold>\<and> (\<^bold>\<forall>y.\<^bold>\<exists>x. E(x\<cdot>y))"
 and E3: "E(x\<cdot>y) \<^bold>\<rightarrow> (\<^bold>\<exists>i. (Id(i) \<^bold>\<and> x\<cdot>(i\<cdot>y) \<^bold>=\<^bold>= x\<cdot>y))"   
 and E4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops
  lemma Nonexistence_implies_Falsity:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

  lemma (*F1:*) "E(x\<cdot>y) \<^bold>\<rightarrow>  (E(x) \<^bold>\<and> E(y))" using E1 by blast 
  lemma (*F2:*) "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> E(x\<cdot>y)" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*F3:*) "\<^bold>\<forall>x. \<^bold>\<exists>i. (i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<rightarrow> i\<cdot>y \<^bold>=\<^bold>= y))" oops (* Timeout *)
  lemma (*F4:*) "\<^bold>\<forall>y. \<^bold>\<exists>j. (j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>y) \<^bold>\<rightarrow> x\<cdot>j \<^bold>=\<^bold>= x))" oops (* Timeout *)
  lemma (*F5:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using E4 by blast
  
  lemma (*S1:*) "E(dom x) \<^bold>\<rightarrow> E(x)" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*S2:*) "E(cod x) \<^bold>\<rightarrow> E(x)" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*S3:*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*S4:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using E4 by blast 
  lemma (*S5:*) "x\<cdot>(dom x) \<^bold>=\<^bold>= x" oops (* Timeout *)
  lemma (*S6:*) "(cod x)\<cdot>x \<^bold>=\<^bold>= x" oops (* Timeout *)
end


context (* Experiments with new axioms from Dana Scott 2: Are the S-Axioms/F-Axioms implied? *)
 assumes 
     F1: "E(x\<cdot>y) \<^bold>\<rightarrow>  (E(x) \<^bold>\<and> E(y))"
 and F2: "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> E(x\<cdot>y)"
 and F3: "\<^bold>\<forall>x. \<^bold>\<exists>i. (i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<rightarrow> i\<cdot>y \<^bold>=\<^bold>= y))"
 and F4: "\<^bold>\<forall>y. \<^bold>\<exists>j. (j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>y) \<^bold>\<rightarrow> x\<cdot>j \<^bold>=\<^bold>= x))"
 and F5: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops
  lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 
  
  lemma (*T1*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(Id(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>j.((Id(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))" 
    nitpick  [user_axioms, show_all, format = 2] oops (* Countermodel *)

  lemma (*T2*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(Id(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>i.((Id(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))" 
    nitpick  [user_axioms, show_all, format = 2] oops (* Countermodel *)

  (* We try to verify the previous axioms from Scott *)
  lemma (*S1:*) "E(dom x) \<^bold>\<rightarrow> E(x)" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*S2:*) "E(cod x) \<^bold>\<rightarrow> E(x)" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*S3:*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
  lemma (*S4:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using F5 by blast 
  lemma (*S5:*) "x\<cdot>(dom x) \<^bold>=\<^bold>= x" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *) 
  lemma (*S6:*) "(cod x)\<cdot>x \<^bold>=\<^bold>= x" nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *)
end


context (* Experiments with new axioms from Dana Scott 3: Are the S-Axioms implied? *)
 assumes 
     F1:  "E(x\<cdot>y) \<^bold>\<rightarrow>  (E(x) \<^bold>\<and> E(y))"
 and F2:  "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> E(x\<cdot>y)"
 and F3:  "\<^bold>\<forall>x. \<^bold>\<exists>i. (i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<rightarrow> i\<cdot>y \<^bold>=\<^bold>= y))"
 and F4:  "\<^bold>\<forall>y. \<^bold>\<exists>j. (j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>y) \<^bold>\<rightarrow> x\<cdot>j \<^bold>=\<^bold>= x))"
 and F5:  "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and Cod: "(E(cod(x)) \<^bold>\<leftrightarrow> E(x)) \<^bold>\<and> (\<^bold>\<forall>x.(Id(cod(x)) \<^bold>\<and> x\<cdot>cod(x) \<^bold>=\<^bold>= x)) \<^bold>\<and> (\<^bold>\<forall>x.\<^bold>\<forall>j.(Id(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x \<^bold>\<rightarrow> cod(x) \<^bold>=\<^bold>= j))"
 and Dom: "(E(dom(y)) \<^bold>\<leftrightarrow> E(y)) \<^bold>\<and> (\<^bold>\<forall>y.(Id(dom(y)) \<^bold>\<and> dom(y)\<cdot>y \<^bold>=\<^bold>= y)) \<^bold>\<and> (\<^bold>\<forall>y.\<^bold>\<forall>i.(Id(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<rightarrow> dom(y) \<^bold>=\<^bold>= i))"
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops

  lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 
  
  (* We try to verify the previous axioms from Scott *)
  lemma (*S1:*) "E(dom x) \<^bold>\<rightarrow> E(x)" sledgehammer nitpick [user_axioms, show_all, format = 2] oops (* Timeout *)
  lemma (*S2:*) "E(cod x) \<^bold>\<rightarrow> E(x)" oops (* Timeout *)
  lemma (*S3:*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" nitpick [user_axioms, show_all, format = 2] oops (* Timeout *)
  lemma (*S4:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using F5 by blast 
  lemma (*S5:*) "x\<cdot>(dom x) \<^bold>=\<^bold>= x" oops (* Timeout *)
  lemma (*S6:*) "(cod x)\<cdot>x \<^bold>=\<^bold>= x" oops (* Timeout *)
end


(* The following is the correct definition of identity morphism; we call it ID instead of Id above.
   The incorrectness of ID was revealed by Nitpick; the analysis of a countermodel above provided the clue. *)
abbreviation ID where "ID i \<equiv> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> E(u\<cdot>v)) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v))" 

context (* F-Axioms 1: A new set of axioms, developed in a joint effort between Dana, Christoph and ATPs. 
   Now we use the correct version of identity morphism. The S-Axioms are implied.*)
 assumes 
     F1:    "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and F5:    "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and Cod_a: "(E(cod(x)) \<^bold>\<rightarrow> E(x))"
 and Cod_b: "(\<^bold>\<forall>x.(ID(cod(x)) \<^bold>\<and> x\<cdot>cod(x) \<^bold>=\<^bold>= x))" 
 and Dom_a: "(E(dom(y)) \<^bold>\<rightarrow> E(y))"
 and Dom_b: "(\<^bold>\<forall>y.(ID(dom(y)) \<^bold>\<and> dom(y)\<cdot>y \<^bold>=\<^bold>= y))"
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops

  lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 
  
  (* We try to verify the previous axioms from Scott *)
  lemma (*S1:*)  "E(dom x) \<^bold>\<rightarrow> E(x)" using Dom_a by blast
  lemma (*S2:*)  "E(cod x) \<^bold>\<rightarrow> E(x)" using Cod_a by blast 
  lemma (*S3:*)  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" by (metis Cod_a Cod_b Dom_a Dom_b F1)
  lemma (*S4:*)  "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using F5 by blast 
  lemma (*S5:*)  "x\<cdot>(dom x) \<^bold>=\<^bold>= x"  by (metis Dom_a Dom_b F1)
  lemma (*S6:*)  "(cod x)\<cdot>x \<^bold>=\<^bold>= x"  by (metis Cod_b Dom_a Dom_b F1)

  lemma (*F2:*) "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> E(x\<cdot>y)" by (metis  Dom_a Dom_b F1)
  lemma (*F3*)  "\<^bold>\<forall>x. \<^bold>\<exists>i. (i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<rightarrow> i\<cdot>y \<^bold>=\<^bold>= y))" by (metis Dom_a Dom_b) 
  lemma (*F4:*) "\<^bold>\<forall>y. \<^bold>\<exists>j. (j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>y) \<^bold>\<rightarrow> x\<cdot>j \<^bold>=\<^bold>= x))" by (metis Dom_a Dom_b) 
end

context (* SACD-Axioms, pre-version: 
   A new set of axioms, developed in a joint effort between Dana, Christoph and ATPs.
   Our first attempt did not include axiom E; Nitpick constructed useful countermodels that
   got us on the right track. *)
assumes 
     S:  "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A:  "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C': "\<^bold>\<forall>x. \<^bold>\<exists>i.  (i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D': "\<^bold>\<forall>y. \<^bold>\<exists>j.  (j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops

  lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

  lemma (*UC*) "\<^bold>\<forall>x. \<^bold>\<exists>i.( (ID(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j. ( (ID(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j )))" 
    nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *) 
  lemma (*UD*) "\<^bold>\<forall>y. \<^bold>\<exists>j.( (ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i. ( (ID(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i )))" 
    nitpick [user_axioms, show_all, format = 2] oops (* Countermodel *) 
end


context (* SACDE-Axioms (with ID): 
   A new set of axioms, developed in a joint effort between Dana, Christoph and ATPs.
   Analysis of implied axioms.  *)
assumes 
     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(ID(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"
begin 
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops   (* Nitpick finds a model *)
  lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
   nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

  lemma (*UC_attempt_1:*) "\<^bold>\<forall>x. \<^bold>\<exists>i.((ID(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j.((ID(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))" 
    sledgehammer (C A) oops
   (* Attempts to prove UC with sledgehammer directly from the axioms fail, the ATPs are to weak. 
      Attempts to prove UC from C and A succeed, but we run into proof reconstruction errors. 
      Lemmata are needed. *)
  lemma UC_L1: "(E(x) \<^bold>\<and> E(i) \<^bold>\<and> E(j) \<^bold>\<and> ID(i) \<^bold>\<and> (x\<cdot>i = x) \<^bold>\<and> ID(j) \<^bold>\<and> (x\<cdot>j = x)) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j" by (smt A)
  lemma (*UC:*) "\<^bold>\<forall>x. \<^bold>\<exists>i.((ID(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j.((ID(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))" by (smt UC_L1 C)
   (* Adding L1 helps, so that the smt command, entered by hand, finally succeeds in verifying UC. *)

  lemma (*UD_attempt_1*) "\<^bold>\<forall>y. \<^bold>\<exists>j.((ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i.((ID(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))" 
    sledgehammer (D) oops
   (* Attempts to prove UC with sledgehammer directly from the axioms fail, the ATPs are to weak. 
      Attempts to prove UC from D succeeds, but runs into proof reconstruction errors. 
      Lemmata are needed. *)
  lemma UD_L1: "(E(x) \<^bold>\<and> E(i) \<^bold>\<and> E(j) \<^bold>\<and> ID(i) \<^bold>\<and> (i\<cdot>x = x) \<^bold>\<and> ID(j) \<^bold>\<and> (j\<cdot>x = x)) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i" by (smt A)
  lemma (*UD:*) "\<^bold>\<forall>y. \<^bold>\<exists>j.((ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i.((ID(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))" by (smt UD_L1 D)
   (* Adding L2 helps, so that the smt command, entered by hand, finally succeeds in verifying UD. *)

  lemma (*F2:*) "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> E(x\<cdot>y)" using E S by blast
  lemma (*F3:*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<rightarrow> i\<cdot>y \<^bold>=\<^bold>= y))" by (metis (full_types) A C)
  lemma (*F4:*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>y) \<^bold>\<rightarrow> x\<cdot>j \<^bold>=\<^bold>= x))" by (metis D)

  lemma (*L3:*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. ( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y )))" by (metis E D S)

  lemma (*F1:*) "(E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y)))" using S by blast
  lemma (*F5:*) "(x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z)" using A by blast

  lemma "(\<exists>Cod. ((E(Cod(x)) \<^bold>\<rightarrow> E(x))))" using S by blast 
  lemma "(\<exists>Cod. (\<^bold>\<forall>x.(ID(Cod(x)))))" by (metis C)   (* only Leo2 helped to find this *)
  lemma "(\<exists>Cod. (\<^bold>\<forall>x.(x\<cdot>Cod(x) \<^bold>=\<^bold>= x)))" by (metis C)    (* only Leo2 helped to find this*)
  lemma "(\<exists>Cod. (\<^bold>\<forall>x.(ID(Cod(x)) \<^bold>\<and> (x\<cdot>Cod(x) \<^bold>=\<^bold>= x))))"  sledgehammer [timeout = 100, remote_leo2] (C)  
   (*  Leo2 can prove this, but proof reconstruction fails **)
   (* by (metis (full_types) C) *)
   oops

  lemma "(\<exists>Cod. ((\<forall>y. (E(Cod(y)) \<^bold>\<rightarrow> E(y))) \<^bold>\<and> (\<^bold>\<forall>x.(ID(Cod(x)) \<^bold>\<and> x\<cdot>Cod(x) \<^bold>=\<^bold>= x))))" 
      sledgehammer [remote_leo2 remote_satallax, verbose] (S C) 
      sledgehammer [timeout = 100] (S C) 
      nitpick [user_axioms, show_all, format = 2]  
      (* by (metis S C)  *)
      oops
  lemma (*Dom_ab:*) "(\<exists>Dom. ((E(Dom(y)) \<^bold>\<rightarrow> E(y)) \<^bold>\<and> ((\<^bold>\<forall>y.(ID(Dom(y)) \<^bold>\<and> Dom(y)\<cdot>y \<^bold>=\<^bold>= y)))))"
     (* by (metis S C D) *)
      nitpick [user_axioms, show_all, format = 2] 
      oops
end


context (* SACDE-Axioms (with ID): The new SACDE-Axioms are implied by the S-axioms.  *)
 assumes 
     S1: "E(dom x) \<^bold>\<rightarrow> E(x)" 
 and S2: "E(cod x) \<^bold>\<rightarrow> E(x)"  
 and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" 
 and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x"
 and S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
begin 
   lemma (*S:*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using S1 S2 S3 by blast
   lemma (*A:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using S4 by blast
   lemma (*C:*) "\<^bold>\<forall>x. \<^bold>\<exists>i.  (ID(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" by (smt S3 S5 S6) 
   lemma (*D:*) "\<^bold>\<forall>y. \<^bold>\<exists>j.  (ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" by (smt S3 S5 S6)
   lemma (*E:*) "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))" by (metis S3)
end

context (* SACDE-Axioms (with ID): The new SACDE-Axioms are implied by the F-axioms.  *)
 assumes 
     F1:    "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and F5:    "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and Cod_a: "(E(cod(x)) \<^bold>\<rightarrow> E(x))"
 and Cod_b: "(\<^bold>\<forall>x.(ID(cod(x)) \<^bold>\<and> x\<cdot>cod(x) \<^bold>=\<^bold>= x))" 
 and Dom_a: "(E(dom(y)) \<^bold>\<rightarrow> E(y))"
 and Dom_b: "(\<^bold>\<forall>y.(ID(dom(y)) \<^bold>\<and> dom(y)\<cdot>y \<^bold>=\<^bold>= y))"
begin 
   lemma (*S:*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using F1 by blast
   lemma (*A:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using F5 by blast
   lemma (*C:*) "\<^bold>\<forall>x. \<^bold>\<exists>i.  (ID(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" by (metis (full_types) Dom_a Dom_b) 
   lemma (*D:*) "\<^bold>\<forall>y. \<^bold>\<exists>j.  (ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" by (metis (full_types) Dom_a Dom_b) 
   lemma (*E:*) "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))" by (metis Dom_a Dom_b)
end






(* In order to improve the notion of identity morphism ID, we run some experiments with Freyd's 
   notion(s) of identity morphism *)
abbreviation IdF1 where "IdF1 i \<equiv> (\<^bold>\<forall>x. (E(i\<cdot>x) \<^bold>\<rightarrow> (i\<cdot>x \<^bold>=\<^bold>= x)))"
(* Freyd's definition of identity morphism; version 1 *)
abbreviation IdF2 where "IdF2 i \<equiv> (\<^bold>\<forall>x. (E(x\<cdot>i) \<^bold>\<rightarrow> (x\<cdot>i \<^bold>=\<^bold>= x)))"
(* Freyd's definition of identity morphism; version 2 *)

(* Remember: ID(i) \<equiv> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> E(u\<cdot>v)) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v)) *)

context (* Tests about notions of identity morphism in the context of the S-axioms: ID and IdF1 are
   equivalent, and so are ID and IdF2. *)
assumes 
     S1: "E(dom x) \<^bold>\<rightarrow> E(x)" 
 and S2: "E(cod x) \<^bold>\<rightarrow> E(x)"  
 and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)"  
 and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" 
 and S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
begin 
  lemma "ID(x) \<^bold>\<leftrightarrow> IdF1(x)" by (smt S2 S3 S5 S6)
  lemma "ID(x) \<^bold>\<leftrightarrow> IdF2(x)" by (smt S2 S3 S5 S6)
end


context (* Tests about notions of identity morphism in the context of the SACDE-axioms with ID. 
  In this context IdF1 and ID are equivalent. And so are IdF2 and ID. *)
assumes 
     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(ID(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"
begin 
 lemma  "ID(x) \<^bold>\<rightarrow> IdF1(x)" by (metis A S) 
 lemma  "IdF1(x) \<^bold>\<rightarrow> ID(x)" sledgehammer nitpick oops (* sledgehammer timeout; need lemmata, see below *)
 lemma IdF1_help1: "IdF1(i) \<^bold>\<rightarrow>  i\<cdot>i \<^bold>=\<^bold>= i" by (metis C S) 
 lemma IdF1_help2: "IdF1(i) \<^bold>\<rightarrow>  (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> E(u\<cdot>v)) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v))" by (metis D S)
 lemma  "IdF1(x) \<^bold>\<rightarrow> ID(x)" using IdF1_help1 IdF1_help2 by blast

 lemma  "ID(x) \<^bold>\<rightarrow> IdF2(x)" by (metis S) 
 lemma  "IdF2(x) \<^bold>\<rightarrow> ID(x)" sledgehammer nitpick oops (* sledgehammer timeout; need lemmata, see below *)
 lemma IdF2_help1: "IdF2(i) \<^bold>\<rightarrow>  i\<cdot>i \<^bold>=\<^bold>= i" by (metis D S) 
 lemma IdF2_help2: "IdF2(i) \<^bold>\<rightarrow>  (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> E(u\<cdot>v)) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v))" by (metis D S)
 lemma  "IdF2(x) \<^bold>\<rightarrow> ID(x)" using IdF2_help1 IdF2_help2 by blast
end

context (* Tests about notions of identity morphism in the context of the SACDE-axioms with IdF1. 
  In this context IdF1 and ID are not equivalent. *)
assumes 
     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(IdF1(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(IdF1(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"
begin 
 lemma  "ID(x) \<^bold>\<rightarrow> IdF1(x)" by (metis A S) 
 lemma  "IdF1(x) \<^bold>\<rightarrow> ID(x)" nitpick [user_axioms, show_all, format = 2] oops  (* countermodel *)
end

context (* Tests about notions of identity morphism in new SACDE-axioms with IdF2. 
  In this context IdF2 and ID are not equivalent. *)
assumes 
     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(IdF2(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(IdF2(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"
begin 
 lemma  "ID(x) \<^bold>\<rightarrow> IdF2(x)" by (metis S) 
 lemma  "IdF2(x) \<^bold>\<rightarrow> ID(x)" nitpick [user_axioms, show_all, format = 2] oops (* countermodel *)
end


abbreviation I where "I i \<equiv> (\<^bold>\<forall>x. (E(i\<cdot>x) \<^bold>\<rightarrow> (i\<cdot>x \<^bold>=\<^bold>= x))) \<^bold>\<and> (\<^bold>\<forall>x. (E(x\<cdot>i) \<^bold>\<rightarrow> (x\<cdot>i \<^bold>=\<^bold>= x)))"
(* A new definition of identity morphism; we call this I. *)

(* Remember: ID(i) \<equiv> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> E(u\<cdot>v)) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v)) *)

context (* Tests about notions of identity morphism in new SACDE-axioms with I. 
  In this context ID and I are equivalent. *)
assumes 
     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"
begin 
 lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops   (* Nitpick finds a model *)
 lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
   nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

 lemma "ID(x) \<^bold>\<rightarrow> I(x)" by (metis A S) 
 lemma "I(x) \<^bold>\<rightarrow> ID(x)" sledgehammer nitpick [user_axioms] oops (* timeout by sledgehammer, lemma needed. *)
 lemma I_help1: "I(i) \<^bold>\<rightarrow>  i\<cdot>i \<^bold>=\<^bold>= i" by (metis C S) 
 lemma "I(x) \<^bold>\<rightarrow> ID(x)" by (metis I_help1 A S) 
end


context (* The SACDE-axioms with I are implied by the S-axioms. *)
assumes 
     S1: "E(dom x) \<^bold>\<rightarrow> E(x)" 
 and S2: "E(cod x) \<^bold>\<rightarrow> E(x)" 
 and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" 
 and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x"  
 and S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
begin 
   lemma (*S:*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using S1 S2 S3 by blast
   lemma (*A:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using S4 by blast
   lemma C_help1: "E(x) \<^bold>\<rightarrow> (\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x))" by (smt S3 S5 S6) 
   lemma (*C:*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" using C_help1 by blast
     (* In C sledgehammer succeeds but smt/metis verification gets a timeout; therefore C_help1 is needed. *)
   lemma D_help1: "E(y) \<^bold>\<rightarrow> (\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y))" by (smt S3 S5 S6)
   lemma (*D:*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" using D_help1 by blast
     (* In D sledgehammer succeeds but smt/metis verification gets a timeout; therefore D_help1 is needed. *)
   lemma (*E:*) "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))" by (metis S3)
end


context (* The set of SACDE-axioms with I are implied by the F-axioms. *)
assumes 
     F1:    "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and F5:    "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and Cod_a: "(E(cod(x)) \<^bold>\<rightarrow> E(x))"
 and Cod_b: "(\<^bold>\<forall>x.(ID(cod(x)) \<^bold>\<and> x\<cdot>cod(x) \<^bold>=\<^bold>= x))" 
 and Dom_a: "(E(dom(y)) \<^bold>\<rightarrow> E(y))"
 and Dom_b: "(\<^bold>\<forall>y.(ID(dom(y)) \<^bold>\<and> dom(y)\<cdot>y \<^bold>=\<^bold>= y))"
begin 
   lemma (*S:*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using F1 by blast
   lemma (*A:*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using F5 by blast
   lemma (*C:*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" by (metis (full_types) Dom_a Dom_b) 
   lemma (*D:*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" by (metis (full_types) Dom_a Dom_b) 
   lemma (*E:*) "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))" by (metis Dom_a Dom_b)
end


context (* We further analyze the SACDE-axioms with I: What axioms are implied? *)
assumes 
     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x. \<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y. \<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"
begin 
  lemma (*UC_attempt_1:*) "\<^bold>\<forall>x. \<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j.((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))" 
    sledgehammer (S A C D E) oops
   (* Attempts to prove UC with sledgehammer directly from the axioms fail, the ATPs are to weak. 
      Attempts to prove UC from S, C and A succeed, but we run into proof reconstruction errors. We need two lemmata. *)
  lemma L1_UC_I: "E(x) \<^bold>\<rightarrow> (\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<forall>j. (E(j) \<^bold>\<rightarrow> ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))))" by (smt A C S) 
  lemma L2_UC_I: "\<^bold>\<forall>x.\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<forall>j. (E(j) \<^bold>\<rightarrow> ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j))))" using  C L1_UC_I by blast  
  lemma (*UC:*) "\<^bold>\<forall>x.\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j. ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))"  using L2_UC_I by blast 
   
  lemma (*UD_attempt_1*) "\<^bold>\<forall>y. \<^bold>\<exists>j.((ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i.((ID(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))" 
    sledgehammer (D) oops
   (* Attempts to prove UC with sledgehammer directly from the axioms fail, the ATPs are to weak. 
      Attempts to prove UC from A D S succeeds, but runs into proof reconstruction errors. We need two lemmata. *)
  lemma L1_UD_I: "E(y) \<^bold>\<rightarrow> (\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<forall>i. (E(i) \<^bold>\<rightarrow> ((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))))" by (smt A D S) 
  lemma L2_UD_I: "\<^bold>\<forall>y.\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<forall>i. (E(i) \<^bold>\<rightarrow> ((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i))))" using  C L1_UD_I by blast  
  lemma (*UD:*)    "\<^bold>\<forall>y.\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i.((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))"  using L2_UD_I by blast 
   
  lemma (*F2:*) "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> E(x\<cdot>y)" using E S by blast
  lemma (*F3:*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x \<^bold>\<and> (\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<rightarrow> i\<cdot>y \<^bold>=\<^bold>= y))" by (metis (full_types) A C S)
  lemma (*F4:*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(j\<cdot>j \<^bold>=\<^bold>= j \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>y) \<^bold>\<rightarrow> x\<cdot>j \<^bold>=\<^bold>= x))"  by (metis (full_types) A D S)

  lemma (*L3:*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. ( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y )))" by (smt A C E S)
  lemma (*F1:*) "(E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y)))" using S by blast
  lemma (*F5:*) "(x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z)" using A by blast
end


(* The final part: Our new axioms *)

(*
The axioms for a category then come down to:

S: Composition is a strict operation.
A: Composition is associative.
C: Every element has a left identity (codomain).
D: Every element has a right identity (domain).
E: Elements sharing a left and right idempotent invariant
   multiplier are always compossable.

In symbols we have:

S: E(x\<cdot>y) ==> [E(x) & E(y)]
A: x\<cdot>(y\<cdot>z) == (x\<cdot>y)\<cdot>z
C: (all x)(exist i)[ I(i) & x\<cdot>i == x ]
D: (all y)(exist j)[ I(j) & j\<cdot>y == y ]
E: (all x,y,z)[[ z.z == z & x.z == x & z.y == y ] ==> E(x.y)]

In C and D the codomain and domain for an element can be proved
to be unique; hence, a semantical proof by Skolem functions shows
that this set of axioms has the same consequences in the language
without the two new function symbols:

S: [ E(x\<cdot>y) ==> [E(x) & E(y) ] & [ E( dom(x)) ==> E(x) ] & [E(cod(x )) ==> E(x)]
A: x.(y.z) == (x.y).z
C: cod( x).x == x
D: x.dom(x ) == x
E: [cod(x) == dom( y) & E(cod(x))] ==> E(x.y)

Does that make a good story now?

(And I think I can do by hand all the proofs to justify the assertions.)
*)

(* Remember: "I(i) \<equiv> (\<^bold>\<forall>x. (E(i\<cdot>x) \<^bold>\<rightarrow> (i\<cdot>x \<^bold>=\<^bold>= x))) \<^bold>\<and> (\<^bold>\<forall>x. (E(x\<cdot>i) \<^bold>\<rightarrow> (x\<cdot>i \<^bold>=\<^bold>= x)))" *)
(* Remember: ID(i) \<equiv> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> E(u\<cdot>v)) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v)) *)

context (* Tests about the SACDE-axioms with I. 
  In this context ID and I are equivalent. UC and UD are implied. *)
assumes 
     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"
 and A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"
begin 
 lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops   (* Nitpick finds a model *)
 lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
   nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

 lemma "ID(x) \<^bold>\<rightarrow> I(x)" by (metis A S) 
 lemma "I(x) \<^bold>\<rightarrow> ID(x)" sledgehammer nitpick [user_axioms] oops (* timeout by sledgehammer, lemma needed. *)
 lemma I_h1: "I(i) \<^bold>\<rightarrow>  i\<cdot>i \<^bold>=\<^bold>= i" by (metis C S) 
 lemma "I(x) \<^bold>\<rightarrow> ID(x)" by (metis I_h1 A S) 

  lemma (*UC_attempt_1*) "\<^bold>\<forall>x. \<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j.((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))" 
    sledgehammer (S A C D E) oops
   (* Attempts to prove UC with sledgehammer directly from the axioms fail, the ATPs are to weak. 
      Attempts to prove UC from S, C and A succeed, but we run into proof reconstruction errors. We need two lemmata. *)
  lemma L1: "E(x) \<^bold>\<rightarrow> (\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<forall>j. (E(j) \<^bold>\<rightarrow> ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))))" by (smt A C S) 
  lemma L2: "\<^bold>\<forall>x.\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<forall>j. (E(j) \<^bold>\<rightarrow> ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j))))" using  C L1 by blast  
  lemma (*UC*) "\<^bold>\<forall>x.\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j. ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))"  using L2 by blast 
   
  lemma (*UD_attempt_1*) "\<^bold>\<forall>y. \<^bold>\<exists>j.((ID(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i.((ID(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))" 
    sledgehammer (D) oops
   (* Attempts to prove UC with sledgehammer directly from the axioms fail, the ATPs are to weak. 
      Attempts to prove UC from A D S succeeds, but runs into proof reconstruction errors. We need two lemmata. *)
  lemma L3: "E(y) \<^bold>\<rightarrow> (\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<forall>i. (E(i) \<^bold>\<rightarrow> ((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))))" by (smt A D S) 
  lemma L4: "\<^bold>\<forall>y.\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<forall>i. (E(i) \<^bold>\<rightarrow> ((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i))))" using  C L3 by blast  
  lemma (*UD*)    "\<^bold>\<forall>y.\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i.((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))"  using L4 by blast 
end


context (* Chris at Dana: We need \<^bold>\<leftrightarrow> in axiom E' and cod(x) \<^bold>=\<^bold>= dom(y) should be 
   replaced by dom(x) \<^bold>=\<^bold>= cod(y); otherwise we cannot show that the SACDE-axioms with I are 
   implied by the SACDE'-axioms. *)
assumes 
     S': "(E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))) \<^bold>\<and> (E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))"
 and A': "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C': "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x"  
 and D': "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" 
 and E': "(cod(x) \<^bold>=\<^bold>= dom(y) \<^bold>\<and> E(cod(x))) \<^bold>\<rightarrow> E(x\<cdot>y)"
begin 
   lemma (*S*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using S' by blast
   lemma (*A*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A' by blast
   lemma (*C*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" nitpick [user_axioms, show_all, format = 2] oops  (* countermodel *)
   lemma (*D*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" nitpick [user_axioms, show_all, format = 2] oops  (* countermodel *)
   lemma (*E*) "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))" nitpick [user_axioms, show_all, format = 2] oops  (* countermodel *)
end 

context (* Chris at Dana: We need \<^bold>\<leftrightarrow> in axiom E' and cod(x) \<^bold>=\<^bold>= dom(y) should be 
   replaced by dom(x) \<^bold>=\<^bold>= cod(y); otherwise we cannot show that the SACDE-axioms with I are 
   implied by the SACDE'-axioms. *)
assumes 
     S': "(E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))) \<^bold>\<and> (E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))"
 and A': "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C': "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x"  
 and D': "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" 
 and E': "(dom(x) \<^bold>=\<^bold>= cod(y) \<^bold>\<and> E(dom(x))) \<^bold>\<rightarrow> E(x\<cdot>y)"
begin 
   lemma (*S*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using S' by blast
   lemma (*A*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A' by blast
   lemma (*C*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" nitpick [user_axioms, show_all, format = 2] oops  (* countermodel *)
   lemma (*D*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" nitpick [user_axioms, show_all, format = 2] oops  (* countermodel *)
   lemma (*E*) "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))" nitpick [user_axioms, show_all, format = 2] oops  (* countermodel *)
end 

context (* The SACDE-axioms with I are implied by the SACDE'-axioms with corrected E'. *)
assumes 
     S': "(E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))) \<^bold>\<and> (E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))"
 and A': "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C': "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x"  
 and D': "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" 
 and E': "(dom(x) \<^bold>=\<^bold>= cod(y) \<^bold>\<and> (E(cod(y)))) \<^bold>\<leftrightarrow> E(x\<cdot>y)"
begin 
   lemma (*S*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using S' by blast
   lemma (*A*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A' by blast
   lemma C_h1: "E(x) \<^bold>\<rightarrow> (\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x))" by (smt C' D' E') 
   lemma (*C*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" using C_h1 by blast
     (* In C sledgehammer succeeds but smt/metis verification gets a timeout; therefore C_help1 is needed. *)
   lemma D_h1: "E(y) \<^bold>\<rightarrow> (\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y))" by (smt C' D' E')
   lemma (*D*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" using D_h1 by blast
     (* In D sledgehammer succeeds but smt/metis verification gets a timeout; therefore D_help1 is needed. *)
   lemma (*E*) "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z.(( z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y ) \<^bold>\<rightarrow> E(x\<cdot>y))"   by (metis E')
end


context (* The S-axioms are implied by the SACDE'-axioms with corrected E'. *)
assumes 
     S': "(E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))) \<^bold>\<and> (E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))"
 and A': "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C': "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x"  
 and D': "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" 
 and E': "(dom(x) \<^bold>=\<^bold>= cod(y) \<^bold>\<and> (E(cod(y)))) \<^bold>\<leftrightarrow> E(x\<cdot>y)"
begin 
 lemma (*S1*) "E(dom(x)) \<^bold>\<rightarrow> E(x)" using S' by blast
 lemma (*S2*) "E(cod(x)) \<^bold>\<rightarrow> E(x)" using S' by blast 
 lemma (*S3*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom(x) \<^bold>= cod(y))" by (metis E') 
 lemma (*S4*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A' by blast
 lemma (*S5*) "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x" using C' by blast
 lemma (*S6*) "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" using D' by blast
end

context (* The SACDE'-axioms with corrected E' are implied by the S-axioms. *)
assumes 
     S1: "E(dom(x)) \<^bold>\<rightarrow> E(x)"
 and S2: "E(cod(x)) \<^bold>\<rightarrow> E(x)"  
 and S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom(x) \<^bold>= cod(y))" 
 and S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and S5: "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x" 
 and S6: "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" 

begin 
 lemma (*S'*) "(E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))) \<^bold>\<and> (E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))" using S1 S2 S3 by blast
 lemma (*A'*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using S4 by blast
 lemma (*C'*) "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x" using S5 by blast 
 lemma (*D'*) "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" using S6 by blast
 lemma (*E'*) "(dom(x) \<^bold>=\<^bold>= cod(y) \<^bold>\<and> (E(cod(y)))) \<^bold>\<leftrightarrow> E(x\<cdot>y)" using S3 by blast
end



(* The final final experiments *)


(* Remember: "I(i) \<equiv> (\<^bold>\<forall>x. (E(i\<cdot>x) \<^bold>\<rightarrow> (i\<cdot>x \<^bold>=\<^bold>= x))) \<^bold>\<and> (\<^bold>\<forall>x. (E(x\<cdot>i) \<^bold>\<rightarrow> (x\<cdot>i \<^bold>=\<^bold>= x)))" *)
(* Remember: ID(i) \<equiv> i\<cdot>i \<^bold>=\<^bold>= i \<^bold>\<and> (\<^bold>\<forall>u.\<^bold>\<forall>v.(u\<cdot>(i\<cdot>v) \<^bold>=\<^bold>= u\<cdot>v \<^bold>\<and> E(u\<cdot>v)) \<^bold>\<rightarrow> (u\<cdot>i \<^bold>=\<^bold>= u \<^bold>\<and> i\<cdot>v \<^bold>=\<^bold>= v)) *)

context (* Tests about the SACDE-axioms with I. 
  Consistency holds. 
  The older ID and I are equivalent. 
  S is redundant. 
  UC and UD are implied. *)
assumes 
  (*     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"   becomes redundant  *)
     A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)" 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))"
begin 
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops   (* Nitpick finds a model *)
  lemma
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
   nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

  lemma "ID(x) \<^bold>\<rightarrow> I(x)" by (metis A E) 
  lemma "I(x) \<^bold>\<rightarrow> ID(x)" by (metis A D E)

  lemma (*S*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using E by blast

  lemma L_1: "E(x) \<^bold>\<rightarrow> (\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<forall>j. (E(j) \<^bold>\<rightarrow> ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))))" by (smt A C E)
  lemma L_2: "\<^bold>\<forall>x.\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<forall>j. (E(j) \<^bold>\<rightarrow> ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j))))" using  D L_1 by blast  
  lemma (*UC*) "\<^bold>\<forall>x.\<^bold>\<exists>i.((I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x) \<^bold>\<and> (\<^bold>\<forall>j. ((I(j) \<^bold>\<and> x\<cdot>j \<^bold>=\<^bold>= x) \<^bold>\<rightarrow> i \<^bold>=\<^bold>= j)))"  using L_2 by blast 
   
  lemma L_3: "E(y) \<^bold>\<rightarrow> (\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<forall>i. (E(i) \<^bold>\<rightarrow> ((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))))" by (smt A D E) 
  lemma L_4: "\<^bold>\<forall>y.\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<forall>i. (E(i) \<^bold>\<rightarrow> ((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i))))" using  D L_3 by blast  
  lemma (*UD*)    "\<^bold>\<forall>y.\<^bold>\<exists>j.((I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<and> (\<^bold>\<forall>i.((I(i) \<^bold>\<and> i\<cdot>y \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> j \<^bold>=\<^bold>= i)))"  using L_4 by blast 
end



(*
context (* Tests about the SACDE'-axioms with I.
   Consistency holds. 
   ID and I are equivalent. 
   S' is implied.
   The SACDE-Axioms are implied.
   The SACDE''-Axioms are implied.
   THE old S-Axioms are implied (Freyd's axioms in his book when corrected. ).
   *)
assumes 
     S': "(E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))"   
 and A': "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z"
 and C': "(E(x) \<^bold>\<rightarrow> (I(cod(x)) \<^bold>\<and> x\<cdot>(cod(x)) \<^bold>=\<^bold>= x))"
 and D': "(E(y) \<^bold>\<rightarrow> (I(dom(y)) \<^bold>\<and> (dom(y))\<cdot>y \<^bold>=\<^bold>= y))" 
 and E': "(E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y)))" 
begin
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops   (* Nitpick finds a model *)
  lemma 
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
    nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 

  lemma "ID(x) \<^bold>\<rightarrow> I(x)" by (metis E')
  lemma "I(x) \<^bold>\<rightarrow> ID(x)" by (metis A' C' E')

  lemma S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using E' by blast
  lemma A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A' by blast
  lemma C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)"  by (metis C' E')
  lemma D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)"  by (metis D' E')
  lemma E: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))" by (metis E')

  lemma (*S1:*)  "E(dom x) \<^bold>\<rightarrow> E(x)"  using S' by blast
  lemma (*S2:*)  "E(cod x) \<^bold>\<rightarrow> E(x)"  using S' by blast
  lemma (*S3:*)  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" sledgehammer (S' C' D' E') nitpick
  lemma (*S4:*)  "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" sledgehammer (S' C' D' E')
  lemma (*S5:*)  "x\<cdot>(dom x) \<^bold>=\<^bold>= x" sledgehammer (S' C' D' E')
  lemma (*S6:*)  "(cod x)\<cdot>x \<^bold>=\<^bold>= x" sledgehammer (S' C' D' E')

  lemma (*S''*) "(E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))" using S' by blast
  lemma (*A''*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A' by blast
  lemma (*C''*) "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x" sledgehammer (S A C D E) nitpick
  lemma (*D''*) "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" sledgehammer (S' C' D' E')
  lemma (*E''*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(cod(x)) \<^bold>\<and> cod(x) \<^bold>=\<^bold>= dom(y))" by (metis C' E')


end



context 
 assumes 
      S'': "(E(Dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(Cod(x)) \<^bold>\<rightarrow> E(x))"
  and A'': "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
  and C'': "x\<cdot>(dom(x)) \<^bold>=\<^bold>= x" 
  and D'': "(cod(x))\<cdot>x \<^bold>=\<^bold>= x" 
  and E'': "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(cod(x)) \<^bold>\<and> cod(x) \<^bold>=\<^bold>= dom(y))"
begin
 lemma (*S*) "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using E'' S'' by blast
 lemma (*A*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A'' by blast
 lemma (*C*) "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)"  by (metis C'' D'' E'' S'')
 lemma (*D*) "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" by (metis C'' D'' E'' )
 lemma (*E*) "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))"  by (metis C'' D'' E'' S'')

  lemma S1:  "E(dom x) \<^bold>\<rightarrow> E(x)"  using S'' by blast
  lemma S2:  "E(cod x) \<^bold>\<rightarrow> E(x)"  using S'' by blast
  lemma S3:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" by (metis C'' D'' E'' S'')
  lemma S4:  "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A'' by blast
  lemma S5:  "x\<cdot>(dom x) \<^bold>=\<^bold>= x" using C'' by blast
  lemma S6:  "(cod x)\<cdot>x \<^bold>=\<^bold>= x" using D'' by blast

  lemma (*S'*) "(E(dom(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(cod(x)) \<^bold>\<rightarrow> E(x))" using S'' by blast
  lemma (*A'*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A'' by blast
  lemma (*C'*) "(E(x) \<^bold>\<rightarrow> (I(cod(x)) \<^bold>\<and> x\<cdot>(cod(x)) \<^bold>=\<^bold>= x))" sledgehammer (S'' C'' D'' E'')  sledgehammer (S1 S2 S3 S5 S6)  by (metis A'' C'' D'' E'' S'')
  lemma (*D'*) "(E(y) \<^bold>\<rightarrow> (I(dom(y)) \<^bold>\<and> (dom(y))\<cdot>y \<^bold>=\<^bold>= y))" sledgehammer (S'' A'' C'' D'' E'') nitpick
  lemma (*E'*) "(E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y)))" by (metis A'' C'' D'' E'' S'')
end



context (* Tests about the SACDE-axioms with I. 
  The ADE'-Axioms are implied. *)
assumes 
  (*     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))"   redundant  *)
     A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
  (* and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)"   redundant *) 
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(z) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))"
begin 
 lemma HH1: "\<exists>Cod. \<forall>x. ((E(Cod(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(x) \<^bold>\<rightarrow> (I(Cod(x)) \<^bold>\<and> x\<cdot>(Cod(x)) \<^bold>=\<^bold>= x)))"  
   by (metis D E) (* Leo2 helped to find this *)
 lemma HH2: "\<exists>Cod. (\<forall>x. (E(x) \<^bold>\<rightarrow> (I(Cod(x)) \<^bold>\<and> x\<cdot>(Cod(x)) \<^bold>=\<^bold>= x)))" 
   by (metis HH1)
 lemma HH3: "\<exists>Cod. (
    (*A'*)      (\<forall>x y z. (x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z)) \<^bold>\<and>
    (*D'*)      (\<forall>x. (E(x) \<^bold>\<rightarrow> (I(Cod(x)) \<^bold>\<and> x\<cdot>(Cod(x)) \<^bold>=\<^bold>= x))) \<^bold>\<and>
    (*E'*)      (\<forall>x y. E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(z) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))) )" 
        sledgehammer (A E HH2)

  (* sledgehammer (H2 H4 A E) *) sorry (* proof found, but reconstruction failed due to timeout *)

end 

context (* Tests about the SACDE-axioms with I. 
  From Dana's email: 
  Next, by introducing Skolem functions, the axioms become:
    S': [E(dom(x)) ==> E(x)] & [E(cod(x )) ==> E(x)]
    A': x\<cdot>(y\<cdot>z) == (x\<cdot>y)\<cdot>z
    C': E(x) ==> [I(cod(x)) & x\<cdot>cod(x) == x]
    D': E(y) ==> [I(dom(y)) & dom(y)\<cdot>y == y]
    E': E(x.y) <==> [E(x) & E(y) & (exist z)[z.z == z & x.z == x & z.y == y]]
  In fact, the existence of the functions can be proved; see the development of H5 below.
  Proofs are found by the ATPs, but proof reconstruction failed.
   *)
assumes 
 (*     S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" is redundant  *)
     A: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" 
 and C: "\<^bold>\<forall>x.\<^bold>\<exists>i.(I(i) \<^bold>\<and> x\<cdot>i \<^bold>=\<^bold>= x)"
 and D: "\<^bold>\<forall>y.\<^bold>\<exists>j.(I(j) \<^bold>\<and> j\<cdot>y \<^bold>=\<^bold>= y)" 
 and E: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))"
begin 
 lemma  S: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" using E by blast

 lemma H1: "\<exists>Dom. (\<forall>y. ((E(Dom(y)) \<^bold>\<rightarrow> E(y)) \<^bold>\<and> (E(y) \<^bold>\<rightarrow> (I(Dom(y)) \<^bold>\<and> (Dom(y))\<cdot>y \<^bold>=\<^bold>= y))))"  
   sledgehammer (S C)
   by (metis S C) (* Leo2 helped to find this *) 

 lemma HH1: "\<exists>Dom. (\<forall>y. ((E(y) \<^bold>\<rightarrow> (I(Dom(y)) \<^bold>\<and> (Dom(y))\<cdot>y \<^bold>=\<^bold>= y))))"  
   sledgehammer (S C)
   by (metis S C) (* Leo2 helped to find this *) 

 lemma H2: "\<exists>Dom. ( (\<forall>x. (E(Dom(x)) \<^bold>\<rightarrow> E(x))) \<^bold>\<and> 
                    (\<forall>x. (E(x) \<^bold>\<rightarrow> (I(Dom(x)) \<^bold>\<and> (Dom(x))\<cdot>x \<^bold>=\<^bold>= x))) )"  
   (* sledgehammer (H1) *) sorry (* proof found, but reconstruction failed due to timeout *)
 lemma H3: "\<exists>Cod. \<forall>x. ((E(Cod(x)) \<^bold>\<rightarrow> E(x)) \<^bold>\<and> (E(x) \<^bold>\<rightarrow> (I(Cod(x)) \<^bold>\<and> x\<cdot>(Cod(x)) \<^bold>=\<^bold>= x)))"  
   by (metis S D) (* Leo2 helped to find this *)
 lemma H4: "\<exists>Cod. ( (\<forall>x. (E(Cod(x)) \<^bold>\<rightarrow> E(x))) \<^bold>\<and> 
                    (\<forall>x. (E(x) \<^bold>\<rightarrow> (I(Cod(x)) \<^bold>\<and> x\<cdot>(Cod(x)) \<^bold>=\<^bold>= x))))"  
   (* sledgehammer (H3) *) sorry (* proof found, but reconstruction failed due to timeout *)
 lemma H5: "\<exists>Dom Cod. 
    (*S'*)    ( (\<forall>x. ((E(Dom(y)) \<^bold>\<rightarrow> E(y)) \<^bold>\<and> ((E(Cod(x)) \<^bold>\<rightarrow> E(x))))) \<^bold>\<and>
    (*A'*)      (\<forall>x y z. (x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z)) \<^bold>\<and>
    (*C'*)      (\<forall>x. (E(x) \<^bold>\<rightarrow> (I(Dom(x)) \<^bold>\<and> (Dom(x))\<cdot>x \<^bold>=\<^bold>= x))) \<^bold>\<and>
    (*D'*)      (\<forall>x. (E(x) \<^bold>\<rightarrow> (I(Cod(x)) \<^bold>\<and> x\<cdot>(Cod(x)) \<^bold>=\<^bold>= x))) \<^bold>\<and>
    (*E'*)      (E(x\<cdot>y) \<^bold>\<leftrightarrow> (E(z) \<^bold>\<and> E(y) \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<^bold>=\<^bold>= z \<^bold>\<and> x\<cdot>z \<^bold>=\<^bold>= x \<^bold>\<and> z\<cdot>y \<^bold>=\<^bold>= y))) )" 
  (* sledgehammer (H2 H4 A E) *) sorry (* proof found, but reconstruction failed due to timeout *)
end 

*)


end


