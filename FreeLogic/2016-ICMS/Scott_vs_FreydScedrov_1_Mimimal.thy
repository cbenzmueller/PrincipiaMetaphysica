theory Scott_vs_FreydScedrov_1_Mimimal imports FreeFOLMinimal
begin 

(*
SCOTT'S AXIOMS FOR A CATEGORY IN FREE LOGIC (his notation)
 (1) Ex <==> Edom(x)
 (2) Ex <==> Ecod(x)
 (3) E(x o y) <==> dom(x) = cod(y)
 (4) x o (y o z) == (x o y) o z
 (5) x o dom(x) == x
 (6) cod(x) o x == x
Since composition is defined the other way around in Freyd and Scott
we first need to modify the axioms to get both version aligned.
For this we replace "x o y" by "y o x":
 (1) Ex <==> Edom(x)
 (2) Ex <==> Ecod(x)
 (3) E(y o x) <==> dom(x) = cod(y)
 (4) (x o y) o z == x o (y o z) 
 (5) dom(x) o x == x
 (6) x o cod(x) == x
Now let's map as follows: 
 "[]x" means domain/source of x 
 "x[]" means codomain/target of x
moreover we use the following definitions 
 x == y <==> (Ex \/ Ey) ==> x = y
 x === y <==> (Ex /\ Ey) /\ x == y
Hence, we get:
 (1) Ex <==> E([]x)
 (2) Ex <==> E(x[])
 (3) E(y o x) <==> []x === y[]
 (4) (x o y) o z == x o (y o z)
 (5) ([]x) o x == x
 (6) x o (x[]) == x
*)

consts source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
       target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
       composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

abbreviation FreydEquality:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y  \<equiv>  ((\<^bold>E(x) \<^bold>\<or> \<^bold>E(y)) \<^bold>\<rightarrow> (\<^bold>E(x) \<^bold>\<and> \<^bold>E(y) \<^bold>\<and> (x \<^bold>= y)))"
abbreviation ScottEquality1:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>=\<^bold>=" 60) 
 where "x \<^bold>=\<^bold>= y  \<equiv>  ((\<^bold>E(x) \<^bold>\<or> \<^bold>E(y)) \<^bold>\<rightarrow> (x \<^bold>= y))"
abbreviation ScottEquality2:: "i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>=\<^bold>=\<^bold>=" 60) 
 where "x \<^bold>=\<^bold>=\<^bold>= y  \<equiv>  ((\<^bold>E(x) \<^bold>\<and> \<^bold>E(y)) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= y))"


context
 assumes 
  A1: "\<^bold>Ex \<^bold>\<leftrightarrow> \<^bold>E(\<box>x)" and
  A2: "\<^bold>Ex \<^bold>\<leftrightarrow> \<^bold>E(x\<box>)" and
  A3: "\<^bold>E(y\<cdot>x) \<^bold>\<leftrightarrow> (\<box>x \<^bold>=\<^bold>=\<^bold>= y\<box>)" and 
  A4: "(x\<cdot>y)\<cdot>z \<^bold>=\<^bold>= x\<cdot>(y\<cdot>z)" and  
  A5: "(\<box>x)\<cdot>x \<^bold>=\<^bold>= x" (* and *)
  (* A6: "x\<cdot>(x\<box>) \<^bold>=\<^bold>= x" *)
 begin 
  (* Inconsistency *)
  (* lemma True nitpick [satisfy, user_axioms, expect = genuine] oops *)
  lemma False by (metis A1 A3 A5 fStarAxiom)

(*
  (* Proving redundant axioms *)
  lemma (*A4*) "(x\<cdot>y)\<cdot>z \<^bold>=\<^bold>= x\<cdot>(y\<cdot>z)" by (meson A3)
  lemma (*A5*) "(\<box>x)\<cdot>x \<^bold>=\<^bold>= x" by (meson A3)
  lemma (*A6*) "x\<cdot>(x\<box>) \<^bold>=\<^bold>= x" by (meson A3)
  (* Proving Freyds Axioms; fStarAxiom is used: "\<not>\<^bold>E(\<^bold>\<star>)" 
     Question: Can "\<^bold>\<star>" cause trouble here? I mean the fact that we always assume a nonexisting 
     object? *)
  lemma "\<^bold>E(x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" by (meson A1 A3 fStarAxiom) 
  lemma "((\<box>x)\<box>) \<approx> \<box>x" by (meson A1 A3 fStarAxiom)
  lemma "\<box>(x\<box>) \<approx> \<box>x" by (meson A1 A3 fStarAxiom)
  lemma "(\<box>x)\<cdot>x \<approx> x" by (meson A1 A3 fStarAxiom)
  lemma "x\<cdot>(x\<box>) \<approx> x" by (meson A1 A3 fStarAxiom)
  lemma "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" by (meson A1 A3 fStarAxiom)
  lemma "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" by (meson A1 A3 fStarAxiom)
  lemma "x\<cdot>(y\<cdot>z) \<approx>  (x\<cdot>y)\<cdot>z" by (meson A1 A3 fStarAxiom)
*)

  end

(*<*)
end
(*>*)