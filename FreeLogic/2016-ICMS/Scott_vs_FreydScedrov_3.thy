theory Scott_vs_FreydScedrov_3 imports Main
begin 

typedecl i   \<comment> "the type for indiviuals" 
consts fExistence:: "i\<Rightarrow>bool" ("\<^bold>E")    \<comment> "Existence predicate"

consts fStar:: "i" ("\<^bold>\<star>")   \<comment> "Distinguished symbol for undefinedness"
axiomatization where fStarAxiom: "\<not>\<^bold>E(\<^bold>\<star>)"

abbreviation fNot:: "bool\<Rightarrow>bool" ("\<^bold>\<not>")          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr "\<^bold>\<rightarrow>" 49)   
 where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 
abbreviation fForall:: "(i\<Rightarrow>bool)\<Rightarrow>bool" ("\<^bold>\<forall>")                 
 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. \<^bold>E(x)\<longrightarrow>\<Phi>(x)"   
abbreviation fForallBinder:: "(i\<Rightarrow>bool)\<Rightarrow>bool" (binder "\<^bold>\<forall>" [8] 9) 
 where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"

abbreviation fThat:: "(i\<Rightarrow>bool)\<Rightarrow>i" ("\<^bold>I") 
 where "\<^bold>I\<Phi> \<equiv> if \<exists>x. \<^bold>E(x) \<and> \<Phi>(x) \<and> (\<forall>y. (\<^bold>E(y) \<and> \<Phi>(y)) \<longrightarrow> (y = x)) 
              then THE x. \<^bold>E(x) \<and> \<Phi>(x) 
              else \<^bold>\<star>"
abbreviation fThatBinder:: "(i\<Rightarrow>bool)\<Rightarrow>i"  (binder "\<^bold>I" [8] 9) 
 where "\<^bold>Ix. \<phi>(x) \<equiv> \<^bold>I(\<phi>)"

abbreviation fOr (infixr "\<^bold>\<or>" 51) where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 52) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 50) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation fEquals (infixr "\<^bold>=" 56) where "x\<^bold>=y \<equiv> x=y"
abbreviation fExists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

consts source:: "i\<Rightarrow>i" ("dom _" [108] 109) 
       target:: "i\<Rightarrow>i" ("cod _" [110] 111) 
       composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

(*
SCOTT'S AXIOMS FOR A CATEGORY IN FREE LOGIC (his notation)
 (1) Ex <==> Edom(x)
 (2) Ex <==> Ecod(x)
 (3) E(x o y) <==> dom(x) = cod(y)
 (4) x o (y o z) == (x o y) o z
 (5) x o dom(x) == x
 (6) cod(x) o x == x
*)

abbreviation FreydEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y  \<equiv>  ((\<^bold>E(x) \<^bold>\<or> \<^bold>E(y)) \<^bold>\<rightarrow> (\<^bold>E(x) \<^bold>\<and> \<^bold>E(y) \<^bold>\<and> (x \<^bold>= y)))"
abbreviation ScottEquality1:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>=\<^bold>=" 60) 
 where "x \<^bold>=\<^bold>= y  \<equiv>  ((\<^bold>E(x) \<^bold>\<or> \<^bold>E(y)) \<^bold>\<rightarrow> (x \<^bold>= y))"



context (* With strong equality in axiom 3 we do not get consistency *)
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<rightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(cod x) \<^bold>\<rightarrow> \<^bold>E(x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((\<^bold>E(x) \<^bold>\<and> \<^bold>E(y)) \<^bold>\<rightarrow> (dom x \<^bold>= cod y))" and 
  4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
 begin 
  (* nitpick does not find a model *)
  lemma True nitpick [satisfy, user_axioms] oops 
  (* proof of falsity *)
  lemma False using 3 5 fStarAxiom by force
  (* we now prove Freyds axioms; here we only check the five axioms we proposed *)
  lemma  (*A1*)  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" by (metis 3 5) 
  lemma  (*A2a*) "(cod (dom x)) \<approx> dom x" by (metis 2 3 5)
  lemma  (*A3a*) "x\<cdot>(dom x) \<approx> x" using 5 by force
  lemma  (*A3b*) "(cod x)\<cdot>x \<approx> x" using 6 by force
  lemma  (*A5*)  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" using 4 by force
 end



context (* With this weaker equality in axiom 3 we still do not get consistency *)
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<rightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(cod x) \<^bold>\<rightarrow> \<^bold>E(x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((\<^bold>E(x) \<^bold>\<or> \<^bold>E(y)) \<^bold>\<rightarrow> (dom x \<^bold>= cod y))" and 
  4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
 begin 
  (* nitpick does not find a model  *)
  lemma True nitpick [satisfy, user_axioms] oops 
  (* proof of falsity *)
  lemma False by (metis 1 3 5 fStarAxiom)
 end


context (* Use of plain identity in axiom 3 gets us consistent *)
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<rightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(cod x) \<^bold>\<rightarrow> \<^bold>E(x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" and 
  4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
 begin 
  (* nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms] oops 
  (* we now prove Freyds axioms; here we only check the five axioms we proposed *)
  lemma  (*A1*)  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" nitpick [user_axioms, show_all] oops
  lemma  (*A2a*) "(cod (dom x)) \<approx> dom x" by (metis 1 2 3 5)
  lemma  (*A3a*) "x\<cdot>(dom x) \<approx> x" using 5 by force
  lemma  (*A3b*) "(cod x)\<cdot>x \<approx> x" using 6 by force
  lemma  (*A5*)  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" using 4 by force
 end

context (* Freyd's (reduced set of) axioms in Scott's notation; inconsistency *)
 assumes
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<approx> (cod y))" and
   A2a: "(cod (dom x)) \<approx> dom x" and
   A3a: "x\<cdot>(dom x) \<approx> x" and
   A3b: "(cod x)\<cdot>x \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
 begin 
  (* nitpick does not find a model *)
  lemma True nitpick [satisfy, user_axioms] oops 
 end

context (* Freyd's (reduced set of) axioms in Scott's notation with identity in A3; consistency *)
 assumes
   A1:  "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) = (cod y))" and
   A2a: "(cod (dom x)) \<approx> dom x" and
   A3a: "x\<cdot>(dom x) \<approx> x" and
   A3b: "(cod x)\<cdot>x \<approx> x" and
   A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" 
 begin 
  (* nitpick does not find a model anymore *)
  lemma True nitpick [satisfy, user_axioms] oops 
  (* We prove Scott's axioms *)
  lemma (*1*) "\<^bold>E(dom x) \<^bold>\<rightarrow> \<^bold>E(x)" by (metis A1 A2a A3a)
  lemma (*2*) "\<^bold>E(cod x) \<^bold>\<rightarrow> \<^bold>E(x)" nitpick [user_axioms, show_all] oops
  lemma (*3*) "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>= cod y)" using A1 by blast
  lemma (*4*) "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" using A5 by blast
  lemma (*5*) "x\<cdot>(dom x) \<^bold>=\<^bold>= x" using A3a by blast
  lemma (*6*) "(cod x)\<cdot>x \<^bold>=\<^bold>= x" using A3b by blast
 end

(* That clearly also holds for Freyd's axioms *)

(*<*)
end
(*>*)