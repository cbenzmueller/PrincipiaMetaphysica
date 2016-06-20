theory Scott_FreeFOL_and_CategoryTheory imports Main 
begin 

typedecl i                                       (* Type for indiviuals *)
consts fExistence:: "i\<Rightarrow>bool" ("E_" [108] 109)   (* Existence predicate *)

abbreviation fNot:: "bool\<Rightarrow>bool" ("\<^bold>\<not>")                           where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr "\<^bold>\<rightarrow>" 49)       where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 
abbreviation fForall:: "(i\<Rightarrow>bool)\<Rightarrow>bool" ("\<^bold>\<forall>")                    where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E(x)\<longrightarrow>\<Phi>(x)"   
abbreviation fForallBinder:: "(i\<Rightarrow>bool)\<Rightarrow>bool" (binder "\<^bold>\<forall>" [8] 9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"
abbreviation fOr (infixr "\<^bold>\<or>" 51)                                 where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 52)                                where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 50)                             where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation fExists ("\<^bold>\<exists>")                                       where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

(* Non-bold "=" is identity on the raw domain V, bold-face "\<^bold>=" is idenity on E *) 
abbreviation fEquals1 (infixr "\<^bold>=" 56)  where "x \<^bold>= y \<equiv> ((x = y) \<^bold>\<and> E(x) \<^bold>\<and> E(y))"
abbreviation fEquals2 (infixr "\<^bold>=\<^bold>=" 56) where "x \<^bold>=\<^bold>= y \<equiv> ((E(x) \<^bold>\<or> E(y)) \<^bold>\<rightarrow> (x\<^bold>=y))"
 
(* We prove some properties of "=" and "\<^bold>=" *)
lemma "x \<^bold>= y \<^bold>\<leftrightarrow> ((x = y) \<^bold>\<and> E(x))" by simp 
lemma "x \<^bold>= y \<^bold>\<leftrightarrow> ((x = y) \<^bold>\<and> E(y))" by simp 
lemma "x \<^bold>=\<^bold>= y \<^bold>\<leftrightarrow> ((x \<^bold>= y) \<^bold>\<or> (\<^bold>\<not>(E(x)) \<^bold>\<and> \<^bold>\<not>(E(y))))" by auto
(* "\<^bold>=" is an equivalence relation on E *)
lemma "\<^bold>\<forall>x. (x \<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y. (x \<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y z. ((x \<^bold>= y) \<^bold>\<and> (y \<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>= z)" by simp
(* Reflexivity fails on V for "\<^bold>=" , i.e. "\<^bold>=" is only a partial equivalence rel on V *)
lemma "(x \<^bold>= x)" nitpick [user_axioms, show_all] oops  (* countermodel *)
lemma "(x \<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>= x)" by auto
lemma "((x \<^bold>= y) \<^bold>\<and> (y \<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>= z)" by simp
(* "\<^bold>=\<^bold>=" is an equivalence relation on E *)
lemma "\<^bold>\<forall>x. (x \<^bold>=\<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y. (x \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>=\<^bold>= x)" by simp
lemma "\<^bold>\<forall>x y z. ((x \<^bold>=\<^bold>= y) \<^bold>\<and> (y \<^bold>=\<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= z)" by simp
(* "\<^bold>=\<^bold>=" is also an equivalence relation on V, i.e. "\<^bold>=\<^bold>=" is a total equivalence rel on V *)
lemma "(x \<^bold>=\<^bold>= x)" by simp
lemma "(x \<^bold>=\<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>=\<^bold>= x)" by auto
lemma "((x \<^bold>=\<^bold>= y) \<^bold>\<and> (y \<^bold>=\<^bold>= z)) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= z)" by auto

(* We now introduce category theory notions *)
consts domain:: "i\<Rightarrow>i" ("dom _" [108] 109) 
       codomain:: "i\<Rightarrow>i" ("cod _" [110] 111) 
       composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

(* If elements of V-E are not important, then we need say nothing about them, for example: *)
lemma "(\<^bold>\<not>(E(x\<cdot>y)) \<^bold>\<and> \<^bold>\<not>(E(u\<cdot>v))) \<^bold>\<rightarrow> ((x\<cdot>y) \<^bold>=\<^bold>= (u\<cdot>v))" by simp
(* But there is no reason to assume (non-bold "=" is raw identity on V): *)
lemma "(\<^bold>\<not>(E(x\<cdot>y)) \<^bold>\<and> \<^bold>\<not>(E(u\<cdot>v))) \<^bold>\<rightarrow> ((x\<cdot>y) = (u\<cdot>v))" nitpick [user_axioms, show_all] oops (* countermodel *)

(*
SCOTT'S AXIOMS FOR A CATEGORY IN FREE LOGIC (Scott's notation)
 (S1) Ex <==> Edom(x)              (we only need right to left direction)
 (S2) Ex <==> Ecod(x)              (we only need right to left direction)
 (S3) E(x o y) <==> dom(x) = cod(y)
 (S4) x o (y o z) == (x o y) o z
 (S5) x o dom(x) == x
 (S6) cod(x) o x == x
*)

context (* C1: We get consistency for Scott's axioms for "\<^bold>=" in S3. *)
 assumes 
  S1: "E(dom x) \<^bold>\<rightarrow> E(x)" and
  S2: "E(cod x) \<^bold>\<rightarrow> E(x)" and 
  S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" and 
  S4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  S5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  S6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
 begin 
  (* Nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms] oops 
 end


context (* C2: We additionally assume that V-E is nonempty (i.e. "\<exists>x. \<^bold>\<not>(E(x))" holds, for
   raw existence predice \<exists> ranging over V): we still get consistency. Very Good! *)
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
  lemma True nitpick [satisfy, user_axioms] oops 
 end



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
all x\<cdot>y by y\<cdot>x, to appropriately map their different order wrt. composition
 A1:  "\<^bold>E(y\<cdot>x) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" 
 A2a: "(\<box>x)\<box> \<approx> \<box>x" 
 A2b: "\<box>(x\<box>) \<approx> x\<box>" 
 A3a: "x\<cdot>(\<box>x) \<approx> x" 
 A3b: "(x\<box>)\<cdot>x \<approx> x" 
 A4a: "\<box>(y\<cdot>x) \<approx> \<box>((\<box>y)\<cdot>x)" 
 A4b: "(y\<cdot>x)\<box> \<approx> (y\<cdot>(x\<box>))\<box>" 
 A5:  "(z\<cdot>y)\<cdot>x \<approx> z\<cdot>(y\<cdot>x)"

We rename the variables again to get them in usual order: 
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((y\<box>) \<approx> (\<box>x))" 
 A2a: "(\<box>x)\<box> \<approx> \<box>x" 
 A2b: "\<box>(x\<box>) \<approx> x\<box>" 
 A3a: "x\<cdot>(\<box>x) \<approx> x" 
 A3b: "(x\<box>)\<cdot>x \<approx> x" 
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>((\<box>x)\<cdot>y)" 
 A4b: "(x\<cdot>y)\<box> \<approx> (x\<cdot>(y\<box>))\<box>" 
 A5:  "(x\<cdot>y)\<cdot>z \<approx> x\<cdot>(y\<cdot>z)"

We replace _\<box> by cod_ and \<box>_ by dom_
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((cod y) \<approx> (dom x))" 
 A2a: "cod (dom x) \<approx> dom x" 
 A2b: "dom (cod x) \<approx> cod x" 
 A3a: "x\<cdot>(dom x) \<approx> x" 
 A3b: "(cod x)\<cdot>x \<approx> x" 
 A4a: "dom (x\<cdot>y) \<approx> dom ((dom x)\<cdot>y)" 
 A4b: "cod (x\<cdot>y) \<approx> cod (x\<cdot>(cod y))" 
 A5:  "(x\<cdot>y)\<cdot>z \<approx> x\<cdot>(y\<cdot>z)"

Freyd's \<approx> is symmetric, hence we get:

We replace _\<box> by cod_ and \<box>_ by dom_
 A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ( (dom x) \<approx> (cod y))" 
 A2a: "cod (dom x) \<approx> dom x" 
 A2b: "dom (cod x) \<approx> cod x" 
 A3a: "x\<cdot>(dom x) \<approx> x" 
 A3b: "(cod x)\<cdot>x \<approx> x" 
 A4a: "dom (x\<cdot>y) \<approx> dom ((dom x)\<cdot>y)" 
 A4b: "cod (x\<cdot>y) \<approx> cod (x\<cdot>(cod y))" 
 A5:  "(x\<cdot>y)\<cdot>z \<approx> x\<cdot>(y\<cdot>z)"

From Dana's email (so Dana was right):

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

(* My first interpretation of Freyd's equality (given informal in his text) was this here. 
   We denote this version of equality with non-bold "\<approx>". Freyd later told me via email 
   that he intended Kleene equality instead, but see the experiments below! *)
abbreviation FreydEquality1:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> ((E x) \<^bold>\<leftrightarrow> (E y)) \<^bold>\<and> x \<^bold>= y"  

context (* C3: Freyd's axioms are consistent with "\<approx>" as equality (and when V-E may be empty). *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" and
  A2a:  "(cod (dom x)) \<approx> dom x" and 
  A2b:  "(dom (cod x)) \<approx> cod x" and 
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and
  A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
 begin 
  (* Nitpick does find a model. *)
  lemma True nitpick [satisfy, user_axioms] oops 
 end

context (* C4: Freyd's axioms are redundant for "\<approx>" and non-empty V-E, 
  this coincides with ICMS paper results. *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" and
  (* A2a:  "(cod (dom x)) \<approx> dom x" and *)
  A2b:  "(dom (cod x)) \<approx> cod x" and 
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and
  A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"  and
  NE: "\<exists>x. \<^bold>\<not>(E(x))" 
 begin 
  lemma (*A2a*) "(cod (dom x)) \<approx> dom x" using A3a NE by blast
 end

context (* C5: Freyd's axioms are even more redundant for "\<approx>" and non-empty V-E,  
  this coincides with ICMS paper results. *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" and
  A2a:  "(cod (dom x)) \<approx> dom x" and 
  (* A2b:  "(dom (cod x)) \<approx> cod x" and *)
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  (* A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and *)
  (* A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and *)
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"  and
  NE: "\<exists>x. \<^bold>\<not>(E(x))" 
 begin 
  lemma (*A2b*) "(dom (cod x)) \<approx> cod x" using A3a NE by blast
  lemma (*A4a*) "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" using A3a NE by blast
  lemma (*A4b*) "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" using A3a NE by blast
 end

context (* C6: Freyd's axioms are inconsistent for "\<approx>" and non-empty V-E, 
  this extends the ICMS paper results. *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" and
  A2a:  "(cod (dom x)) \<approx> dom x" and 
  (* A2b:  "(dom (cod x)) \<approx> cod x" and *)
  A3a: "x\<cdot>(dom x) \<approx> x" and
  A3b: "(cod x)\<cdot>x \<approx> x" and
  (* A4a: "dom(x\<cdot>y) \<approx> dom(dom(x)\<cdot>y)" and *)
  (* A4b: "cod(x\<cdot>y) \<approx> cod(x\<cdot>cod(y))" and *)
  A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"  and
  NE: "\<exists>x. \<^bold>\<not>(E(x))" 
 begin 
  (* Nitpick does *not* find a model. *)
  lemma True nitpick [satisfy, user_axioms] oops 
  (* We can prove falsity. *)
  lemma False using A3a NE by blast
 end


(* Freyd told me, that he wants Kleene equality. We use bold-face "\<^bold>\<approx>" below and repeat 
   the experiments. *)
abbreviation FreydEquality2:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>\<approx>" 60) 
 where "x \<^bold>\<approx> y  \<equiv>  ((E(x) \<^bold>\<or> E(y)) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (x = y)))" 

(* Trivially, "\<^bold>\<approx>" is the same as Scott's "\<^bold>=\<^bold>=" from above. *)
lemma "x \<^bold>=\<^bold>= y \<^bold>\<leftrightarrow> x \<^bold>\<approx> y" by auto 

context (* C7: Freyd's axioms are consistent for "\<^bold>\<approx>" (when V-E may be empty). ") *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<^bold>\<approx> (cod y))" and
  A2a:  "(cod (dom x)) \<^bold>\<approx> dom x" and
  A3a: "x\<cdot>(dom x) \<^bold>\<approx> x" and
  A3b: "(cod x)\<cdot>x \<^bold>\<approx> x" and
  A4a: "dom(x\<cdot>y) \<^bold>\<approx> dom(dom(x)\<cdot>y)" and 
  A5b: "cod(x\<cdot>y) \<^bold>\<approx> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<^bold>\<approx> (x\<cdot>y)\<cdot>z"
 begin 
  (* nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms] oops 
 end

context (* C6: Freyd's axioms are inconsistent for "\<^bold>\<approx>" and non-empty V-E. This seems very 
           problematic for Freyd, doesn't it? *)
 assumes 
  A1:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<^bold>\<approx> (cod y))" and
  A2a:  "(cod (dom x)) \<^bold>\<approx> dom x" and
  A3a: "x\<cdot>(dom x) \<^bold>\<approx> x" and
  A3b: "(cod x)\<cdot>x \<^bold>\<approx> x" and
  A4a: "dom(x\<cdot>y) \<^bold>\<approx> dom(dom(x)\<cdot>y)" and 
  A5b: "cod(x\<cdot>y) \<^bold>\<approx> cod(x\<cdot>cod(y))" and
  A5:  "x\<cdot>(y\<cdot>z) \<^bold>\<approx> (x\<cdot>y)\<cdot>z" and
  NE: "\<exists>x. \<^bold>\<not>(E(x))" 
 begin 
  (* Nitpick does *not* find a model. *)
  lemma True nitpick [satisfy, user_axioms] oops (* Nitpick finds no model *)
  (* We can prove falsity. *)
  lemma False by (metis A1 A3a A2a NE)
 end

end


