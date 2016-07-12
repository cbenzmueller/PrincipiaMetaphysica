theory BeyondQuaternions imports Main 
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


consts zero::i ("\<zero>") one::i ("\<one>") minusone::i ("-\<one>")  comp::"i\<Rightarrow>i\<Rightarrow>i" ("_\<cdot>_") 
 R::"i\<Rightarrow>bool" plus::"i\<Rightarrow>i\<Rightarrow>i" ("_\<^bold>+_") divided::"i\<Rightarrow>i\<Rightarrow>i" (infix "#" 100)


axiomatization where
 A1a: "(R \<zero>)" and
 A1b: "R(\<one>)" and
 A1c: "R(-\<one>)" and
 A1d: "\<^bold>\<not>(\<zero> \<^bold>=\<^bold>= \<one>)" and
 A2:  "R(x) \<^bold>\<rightarrow> E(x)" and
 A3:  "(R(x) \<^bold>\<and> R(y)) \<^bold>\<rightarrow> (((R(x \<^bold>+ y) \<^bold>\<and> R(x \<cdot> y)) \<^bold>\<and> R(\<one> # x)) \<^bold>\<and> (x \<cdot> y \<^bold>= y \<cdot> x))" 

end


 A4:  "(R(x) \<^bold>\<and> E(y)) \<^bold>\<rightarrow> E(x+y)" and
 A5:  "(R(x) \<^bold>\<and> E(y)) \<^bold>\<rightarrow> (E(x.y) \<^bold>\<and> x.y \<^bold>=\<^bold>= y.x)" and
 A6:  "E(x) \<^bold>\<rightarrow> E(1/x)" and
 A7:  "x+y \<^bold>=\<^bold>= y+x" and
 A8:  "0+x \<^bold>=\<^bold>= x" and
 A9:  "E(x) \<^bold>\<rightarrow> x+((-1).x) \<^bold>=\<^bold>= 0" and
 A10: "E(x) \<^bold>\<rightarrow> 0.x \<^bold>= 0" and
 A11: "x+(y+z) \<^bold>=\<^bold>= (x+y)+z" and
 A12: "(R(a) \<^bold>\<and> E(x+y)) \<^bold>\<rightarrow> a.(x+y) \<^bold>=\<^bold>= (a.x)+(a.y)" and
 A13: "x.(y.z) \<^bold>=\<^bold>= (x.y).z" and
 A14: "E(x) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= 0 \<^bold>\<or> (x.(1/x) \<^bold>=\<^bold>= 1 \<^bold>\<and> (1/x).x \<^bold>=\<^bold>= 1))" and (* or? *)
 A15: "x \<^bold>=\<^bold>= 0 \<^bold>\<or> y \<^bold>=\<^bold>= 0 \<^bold>\<or> (E(x + y) \<^bold>\<leftrightarrow> E(x.y))"


  (* nitpick does find a model *)
  lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
 

end 

(*
(1)  R 0 & R 1 & R(-1) & not 0 == 1
(2)  R x ==> E x
(3)  R x & R y ==> R(x + y) & R(x y) & R(1/x) & x y = y x
(4)  R x & E y ==> E(x + y)
(5)  R x & E y ==> E(x y) & x y == y x
(6)  E x ==> E(1/x)
(7)  x + y == y + x
(8)  0 + x == x
(9)  E x ==> x + (-1)x == 0
(10) E x ==> 0 x = 0
(11) x + (y + z) == (x + y) + z
(12) R a & E(x + y) ==> a (x + y) == (a x) + (a y)
(13) x (y z) == (x y) z
(14) E x ==> x == 0 \/ [x (1/x) == 1 & (1/x) x == 1]
(15) x == 0 \/ y == 0 \/ [E(x + y) <==> E(x y)]
*)


