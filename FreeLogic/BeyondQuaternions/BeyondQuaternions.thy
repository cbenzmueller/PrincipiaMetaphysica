theory BeyondQuaternions imports HOL Nitpick begin 

typedecl i             (* Type for indiviuals *)
consts E:: "i\<Rightarrow>bool"   (* Existence predicate *)

abbreviation fNot:: "bool\<Rightarrow>bool" ("\<^bold>\<not>")                           where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr "\<^bold>\<rightarrow>" 49)       where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 
abbreviation fForall:: "(i\<Rightarrow>bool)\<Rightarrow>bool" ("\<^bold>\<forall>")                    where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E(x)\<longrightarrow>\<Phi>(x)"   
abbreviation fForallBinder:: "(i\<Rightarrow>bool)\<Rightarrow>bool" (binder "\<^bold>\<forall>" [8] 9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"
abbreviation fOr (infixr "\<^bold>\<or>" 51)                                 where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 52)                                where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 50)                             where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation fExists ("\<^bold>\<exists>")                                       where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

abbreviation eq1 (infixr "\<^bold>=" 56)  where "x \<^bold>= y \<equiv> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (x = y))"
abbreviation eq2 (infixr "\<^bold>=\<^bold>=" 56) where "x \<^bold>=\<^bold>= y \<equiv> ((E(x) \<^bold>\<or> E(y)) \<^bold>\<rightarrow> (x\<^bold>=y))"

consts zero::i ("0") one::i ("1") minusone::i ("-1")  comp::"i\<Rightarrow>i\<Rightarrow>i" ("_\<cdot>_" [90,91] 100) 
 R::"i\<Rightarrow>bool" plus::"i\<Rightarrow>i\<Rightarrow>i" ("_+_"  [92,93] 101) div::"i\<Rightarrow>i\<Rightarrow>i" ("_\<bar>_" [98,97] 102)

axiomatization where
 A1: "R(0) \<^bold>\<and> R(1) \<^bold>\<and> R(-1) \<^bold>\<and> \<^bold>\<not>(0 \<^bold>=\<^bold>= 1)" and
 A2:  "R(x) \<^bold>\<rightarrow> E(x)" and
 A3:  "(R(x) \<^bold>\<and> R(y)) \<^bold>\<rightarrow> (((R(x+y) \<^bold>\<and> R(x\<cdot>y)) \<^bold>\<and> R(1\<bar>x)) \<^bold>\<and> (x\<cdot>y \<^bold>= y\<cdot>x))" and
 A4:  "(R(x) \<^bold>\<and> E(y)) \<^bold>\<rightarrow> E(x+y)" and
 A5:  "(R(x) \<^bold>\<and> E(y)) \<^bold>\<rightarrow> (E(x\<cdot>y) \<^bold>\<and> x\<cdot>y \<^bold>=\<^bold>= y\<cdot>x)" and
 A6:  "E(x) \<^bold>\<rightarrow> E(1\<bar>x)" and
 A7:  "x+y \<^bold>=\<^bold>= y+x" and
 A8:  "0+x \<^bold>=\<^bold>= x" and
 A9:  "E(x) \<^bold>\<rightarrow> x+((-1)\<cdot>x) \<^bold>=\<^bold>= 0" and
 A10: "E(x) \<^bold>\<rightarrow> 0\<cdot>x \<^bold>= 0" and
 A11: "x+(y+z) \<^bold>=\<^bold>= (x+y)+z" and
 A12: "(R(a) \<^bold>\<and> E(x+y)) \<^bold>\<rightarrow> a\<cdot>(x+y) \<^bold>=\<^bold>= (a\<cdot>x)+(a\<cdot>y)" and
 A13: "x\<cdot>(y\<cdot>z) \<^bold>=\<^bold>= (x\<cdot>y)\<cdot>z" and
 A14: "E(x) \<^bold>\<rightarrow> (x \<^bold>=\<^bold>= 0 \<^bold>\<or> (x\<cdot>(1\<bar>x) \<^bold>=\<^bold>= 1 \<^bold>\<and> (1\<bar>x)\<cdot>x \<^bold>=\<^bold>= 1))" and 
 A15: "x \<^bold>=\<^bold>= 0 \<^bold>\<or> y \<^bold>=\<^bold>= 0 \<^bold>\<or> (E(x+y) \<^bold>\<leftrightarrow> E(x\<cdot>y))" and
 Str1: "E(x\<cdot>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" and
 Str2: "E(x+y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" and
 Str3: "E(x\<bar>y) \<^bold>\<rightarrow> (E(x) \<^bold>\<and> E(y))" 

 (* Nitpick does find a model *)
 lemma True nitpick [satisfy, user_axioms, show_all, format = 2] oops 
 (* Does E collapse to R? No, Nitpick finds a countermodel. *)
 lemma "E(x) \<^bold>\<rightarrow> R(x)" nitpick [user_axioms, show_all, format = 2, card = 4] oops 
 (* Nitpick finds a countermodel for the following statement *)
 lemma "x\<cdot>(y+z) == (x\<cdot>y)+(x\<cdot>z)" nitpick [user_axioms, show_all, format = 2, card = 8] oops 

 (* And these here can be proved  *)
 lemma "(R(x) \<^bold>\<and> R(y) \<^bold>\<and> R(z)) \<^bold>\<rightarrow> (x\<cdot>(y+z) \<^bold>=\<^bold>= (x\<cdot>y)+(x\<cdot>z))" using A12 A2 A4 by blast 
 lemma "(R(x) \<^bold>\<and> E(y) \<^bold>\<and> R(z)) \<^bold>\<rightarrow> (x\<cdot>(y+z) \<^bold>=\<^bold>= (x\<cdot>y)+(x\<cdot>z))" by (meson A12 A4 A7)
 lemma "(R(x) \<^bold>\<and> R(y) \<^bold>\<and> E(z)) \<^bold>\<rightarrow> (x\<cdot>(y+z) \<^bold>=\<^bold>= (x\<cdot>y)+(x\<cdot>z))" by (meson A12 A4 A7)
 lemma "(R(x) \<^bold>\<and> E(y) \<^bold>\<and> E(z)) \<^bold>\<rightarrow> (x\<cdot>(y+z) \<^bold>=\<^bold>= (x\<cdot>y)+(x\<cdot>z))" by (metis A10 A11 A12 A5 A7 A8 A9 Str1 Str2) 

 (* No answer by the provers; I need to play with higher timeouts *)
 lemma "(E(x) \<^bold>\<and> E(y) \<^bold>\<and> E(z)) \<^bold>\<rightarrow> (x\<cdot>(y+z) \<^bold>=\<^bold>= (x\<cdot>y)+(x\<cdot>z))" sledgehammer nitpick [user_axioms, show_all, format = 2] oops 
 lemma "(E(x) \<^bold>\<and> R(y) \<^bold>\<and> R(z)) \<^bold>\<rightarrow> (x\<cdot>(y+z) \<^bold>=\<^bold>= (x\<cdot>y)+(x\<cdot>z))" sledgehammer nitpick [user_axioms, show_all, format = 2] oops 





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


