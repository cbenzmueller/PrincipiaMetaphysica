theory Scott_vs_FreydScedrov_2 imports FreeFOL 
begin 

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

abbreviation ScottEquality1:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>=\<^bold>=" 60) 
 where "x \<^bold>=\<^bold>= y  \<equiv>  ((\<^bold>E(x) \<^bold>\<or> \<^bold>E(y)) \<^bold>\<rightarrow> (x \<^bold>= y))"
abbreviation ScottEquality2:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>=\<^bold>=\<^bold>=" 60) 
 where "x \<^bold>=\<^bold>=\<^bold>= y  \<equiv>  ((\<^bold>E(x) \<^bold>\<and> \<^bold>E(y)) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= y))"

context
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<leftrightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(x) \<^bold>\<leftrightarrow> \<^bold>E(cod x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>=\<^bold>=\<^bold>= cod y)" and 
  4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
 begin 
  (* nitpick cannot find a model *)
  (* lemma True nitpick [satisfy, user_axioms, expect = genuine] oops *)
  lemma False
   proof -  
   have B1: "\<^bold>\<not>(\<^bold>E(\<^bold>\<star>))" using fStarAxiom by blast
   have B2: "\<^bold>\<not>(\<^bold>E(dom \<^bold>\<star>))" using 1 B1 by blast
   have B3: "\<^bold>E(\<^bold>\<star>\<cdot>(dom \<^bold>\<star>))" using 3 B2 by blast
   have B4: "((\<^bold>\<star>\<cdot>(dom \<^bold>\<star>)) \<^bold>= \<^bold>\<star>)" using B3 5 by blast
   have B5: "\<^bold>E(\<^bold>\<star>)" using B3 B4 by auto
   have False using B5 B1 by auto
   then show ?thesis .
  qed       
 end

context
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<leftrightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(x) \<^bold>\<leftrightarrow> \<^bold>E(cod x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>=\<^bold>= cod y)" and 
  4: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) \<^bold>=\<^bold>= x" and 
  6: "(cod x)\<cdot>x \<^bold>=\<^bold>= x" 
 begin 
  (* nitpick cannot find a model *)
  (* lemma True nitpick [satisfy, user_axioms, expect = genuine] oops *)
  lemma False by (metis 1 2 3 6 fStarAxiom)
 end


abbreviation FreydEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y  \<equiv>  ((\<^bold>E(x) \<^bold>\<or> \<^bold>E(y)) \<^bold>\<rightarrow> (\<^bold>E(x) \<^bold>\<and> \<^bold>E(y) \<^bold>\<and> (x \<^bold>= y)))"

context
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<leftrightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(x) \<^bold>\<leftrightarrow> \<^bold>E(cod x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>=\<^bold>=\<^bold>= cod y)" and 
  4: "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) \<approx> x" and 
  6: "(cod x)\<cdot>x \<approx> x" 
 begin 
  (* nitpick cannot find a model *)
  (* lemma True nitpick [satisfy, user_axioms, expect = genuine] oops *)
  lemma False by (metis 2 3 6 fStarAxiom)
 end

context
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<leftrightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(x) \<^bold>\<leftrightarrow> \<^bold>E(cod x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>=\<^bold>=\<^bold>= cod y)" and 
  4: "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) \<approx> x" and 
  6: "(cod x)\<cdot>x \<approx> x" 
 begin 
  (* nitpick cannot find a model *)
  (* lemma True nitpick [satisfy, user_axioms, expect = genuine] oops *)
  lemma False by (metis 2 3 6 fStarAxiom)
 end



context
 assumes 
  1: "\<^bold>E(dom x) \<^bold>\<leftrightarrow> \<^bold>E(x)" and
  2: "\<^bold>E(x) \<^bold>\<leftrightarrow> \<^bold>E(cod x)" and 
  3: "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<^bold>=\<^bold>= cod y)" and 
  4: "x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z" and 
  5: "x\<cdot>(dom x) = x" and 
  6: "(cod x)\<cdot>x = x" 
 begin 
  (* nitpick cannot find a model *)
  (* lemma True nitpick [satisfy, user_axioms, expect = genuine] oops *)
  lemma False by (metis 1 2 3 6 fStarAxiom)
 end

(*<*)
end
(*>*)