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
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<approx> cod y)" and
  A2a:  "cod (dom x) \<approx> dom x" and 
  A2b:  "dom (cod x) \<approx> cod x" and 
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and
  A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
 begin 
  (* Nitpick does find a model. *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
 end



context (* Freyd_2:
   Freyd's axioms are redundant for "\<approx>" and non-empty D-E. 
   This coincides with the results the results in our ICMS 2016 paper. *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<approx> cod y)" and
  (* A2a:  "cod (dom x) \<approx> dom x" and *)
  A2b:  "dom (cod x) \<approx> cod x" and 
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and
  A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"  and
  NE:  "\<exists>x. \<^bold>\<not>(E(x))"    (* Note that "\<exists>" is existence from the meta-logic, which ranges over D. *)
 begin 
  lemma (*A2a*) "cod (dom x) \<approx> dom x" by (metis A1 A2b A3b)
 end


context (* Freyd_3:
   Freyd's axioms are even more redundant for "\<approx>" and non-empty D-E.
   This coincides with the results the results in our ICMS 2016 paper. *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<approx> (cod y))" and
  A2a:  "cod (dom x) \<approx> dom x" and 
  (* A2b:  "dom (cod x) \<approx> cod x" and *)
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  (* A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and *)
  (* A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and *)
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"  and
  NE: "\<exists>x. \<^bold>\<not>(E(x))"   
 begin 
  lemma (*A2b*) "dom (cod x) \<approx> cod x" by (metis A1 A3a A2a)
  lemma (*A4a*) "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" by (metis A1 A3a A2a)
  lemma (*A4b*) "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" by (metis A1 A3a A2a)
 end


context (* Freyd_4: 
   Freyd's axioms are inconsistent for "\<approx>" and non-empty D-E. 
   This coincides with the results the results in our ICMS 2016 paper. *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" and
  A2a:  "cod (dom x) \<approx> dom x" and 
  A2b:  "dom (cod x) \<approx> cod x" and 
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and
  A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"  and
  NE: "\<exists>x. \<^bold>\<not>(E(x))" 
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
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<simeq> cod y)" and
  A2a:  "cod (dom x) \<simeq> dom x" and
  A3a: "x\<cdot>(dom x) \<simeq> x" and
  A3b: "(cod x)\<cdot>x \<simeq> x" and
  A4a: "dom(x\<cdot>y) \<simeq> dom(dom(x)\<cdot>y)" and 
  A5b: "cod(x\<cdot>y) \<simeq> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<simeq> (x\<cdot>y)\<cdot>z"
 begin 
  (* nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
 end



context (* Freyd_6: 
   Freyd's axioms are inconsistent for "\<simeq>" and non-empty D-E. 
   This seems very problematic for Freyd, doesn't it? *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<simeq> cod y)" and
  A2a:  "cod (dom x) \<simeq> dom x" and
  A3a: "x\<cdot>(dom x) \<simeq> x" and
  A3b: "(cod x)\<cdot>x \<simeq> x" and
  A4a: "dom(x\<cdot>y) \<simeq> dom(dom(x)\<cdot>y)" and 
  A5b: "cod(x\<cdot>y) \<simeq> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<simeq> (x\<cdot>y)\<cdot>z" and
  NE: "\<exists>x. \<^bold>\<not>(E(x))" 
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
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<simeq> cod y)" and
  A2a:  "cod (dom x) \<simeq> dom x" and
  A3a: "x\<cdot>(dom x) \<simeq> x" 
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


context (* Scott_1: 
   We get consistency for Scott's axioms for "\<^bold>=" in S3. *)
 assumes 
  S1: "E(dom x) \<^bold>\<rightarrow> E(x)" and
  S2: "E(cod x) \<^bold>\<rightarrow> E(x)" and 
  S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" and 
  S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
 begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops
 end


context (* Scott_2: 
    We additionally assume that D-E is nonempty (i.e. "\<exists>x. \<^bold>\<not>(E(x))" holds, for "\<exists>" ranging over V); 
    we still get consistency. That is what we want! *)
 assumes 
  S1: "E(dom x) \<^bold>\<rightarrow> E(x)" and
  S2: "E(cod x) \<^bold>\<rightarrow> E(x)" and 
  S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" and 
  S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" and
  ex: "\<exists>x. \<^bold>\<not>(E(x))" 
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
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<simeq> (\<box>y))" and
  A2a: "((\<box>x)\<box>) \<simeq> \<box>x" and
  A2b: "\<box>(x\<box>) \<simeq> \<box>x" and
  A3a: "(\<box>x)\<cdot>x \<simeq> x" and
  A3b: "x\<cdot>(x\<box>) \<simeq> x" and
  A4a: "\<box>(x\<cdot>y) \<simeq> \<box>(x\<cdot>(\<box>y))" and
  A4b: "(x\<cdot>y)\<box> \<simeq> ((x\<box>)\<cdot>y)\<box>" and
  A5:  "x\<cdot>(y\<cdot>z) \<simeq> (x\<cdot>y)\<cdot>z"
 begin

  lemma Nonexistence_implies_Falsity_2:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty. *) 
    shows False  (* We then prove falsity. *) 
  using A1 A2a A3a assms by blast

  lemma Nonexistence_implies_Falsity_3:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then prove falsity. *) 
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

  lemma "\<forall>x. E(x)" using Nonexistence_implies_Falsity_3 by auto


  lemma Nonexistence_implies_Falsity_4:
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
 end

context (* Scott_in_Frey_Notation: 
    We study Scott's axioms in Freyd's notation. *)
 assumes 
  S1: "E(\<box>x) \<^bold>\<rightarrow> E(x)" and
  S2: "E(x\<box>) \<^bold>\<rightarrow> E(x)" and 
  S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (x\<box> \<^bold>= \<box>y)" and 
  S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  S5: "(\<box>x)\<cdot>x \<^bold>=\<^bold>= x" and 
  S6: "x\<cdot>(x\<box>) \<^bold>=\<^bold>= x" 
 begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 

  lemma Nonexistence_implies_Falsity_1:
    assumes "\<exists>x. \<^bold>\<not>(E x)"   (* We assume an undefined object, i.e. that D-E is non-empty.  *) 
    shows False  (* We then try to prove falsity. Nitpick finds a countermodel. *) 
  nitpick [user_axioms, show_all, format = 2, expect = genuine] oops   (* Countermodel *) 
 end


end


