theory Freyd2 imports Freyd 
begin


abbreviation category where "category S T C \<equiv>
 (\<^bold>\<forall>x y. (D (C x y)) \<^bold>\<leftrightarrow> ((T x) \<approx> (S y))) \<^bold>\<and>
 (\<^bold>\<forall>x. (T (S x)) \<approx> (S x)) \<^bold>\<and>
 (\<^bold>\<forall>x. (S (T x)) \<approx> (S x)) \<^bold>\<and>
 (\<^bold>\<forall>x. (C (S x) x) \<approx> x) \<^bold>\<and>
 (\<^bold>\<forall>x. (C x (T x)) \<approx> x) \<^bold>\<and>
 (\<^bold>\<forall>x y. (S (C x y)) \<approx> (S (C x (S y)))) \<^bold>\<and>
 (\<^bold>\<forall>x y. (T (C x y)) \<approx> (T (C (T x) y))) \<^bold>\<and>
 (\<^bold>\<forall>x y z. (C x (C y z)) \<approx> (C (C x y) z))"

abbreviation monoid where "monoid One Comp \<equiv>
 (\<^bold>\<forall>x. (Comp One x) \<approx> x) \<^bold>\<and>
 (\<^bold>\<forall>x. (Comp x One) \<approx> x) \<^bold>\<and>
 (\<^bold>\<forall>x y z. (Comp x (Comp y z)) \<approx> (Comp (Comp x y) z))"


consts One::e L::"e\<Rightarrow>e" R::"e\<Rightarrow>e" Comp::"e\<Rightarrow>e\<Rightarrow>e" 
lemma "((monoid One Comp) \<^bold>\<and> (\<^bold>\<forall>x. (L x \<approx> One)) \<^bold>\<and> (\<^bold>\<forall>x. (R x \<approx> One))) \<^bold>\<rightarrow> (category L R Comp)" 
sledgehammer[verbose, timeout = 600,overlord, remote_leo2, remote_satallax]


lemma "category source target composition" by (meson A1 A2b A3a A3b A4a A4b A5)

consts One :: "e" ("\<one>")

axiomatization Monoid where 
 M1: "\<one>\<cdot>x \<approx> x" and
 M2: "x\<cdot>\<one> \<approx> x" and
 M3: "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"


 M1: "(\<box>x) \<approx> \<one> \<^bold>\<and> (x\<box>) \<approx> \<one>"


consts 
 mor  :: "\<sigma>\<Rightarrow>\<tau>\<Rightarrow>\<sigma>\<Rightarrow>\<tau>" ("<_,_,_>")
 dom  :: "\<tau>\<Rightarrow>\<tau>"  
 cod  :: "\<tau>\<Rightarrow>\<tau>"  
 comp :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infix "\<^bold>\<circ>" 60)

abbreviation f_eq :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infixr "\<^bold>\<equiv>" 50)  where "x\<^bold>\<equiv>y \<equiv> (\<E>(x) \<^bold>\<or> \<E>(y)) \<^bold>\<rightarrow> x \<^bold>= y"



axiomatization where
 dom: "dom(<A,F,B>) = <A,(\<lambda>x. x),A>" and
 cod: "cod(<A,F,B>) = <B,(\<lambda>x. x),B>" and
 comp: "<B,G,C> \<^bold>\<circ> <A,F,B> = <A,(\<lambda>x. G(F(x))),C>" 

lemma A7: "dom(<A,F,B>) \<^bold>\<equiv> cod(dom(<A,F,B>))"
 by (metis dom cod)

lemma A8: "cod(<A,F,B>) \<^bold>\<equiv> dom(cod(<A,F,B>))" 
 by (metis dom cod)

lemma  A4: "x\<^bold>\<circ>(y\<^bold>\<circ>z) \<^bold>\<equiv> (x\<^bold>\<circ>y)\<^bold>\<circ>z" nitpick sledgehammer


axiomatization where
 A1: "\<E>(<A,F,B>) \<^bold>\<leftrightarrow> \<E>(dom(<A,F,B>))" and
 A2: "\<E>(<A,F,B>) \<^bold>\<leftrightarrow> \<E>(cod(<A,F,B>))" and
 A3: "\<E>(<A2,F2,B2>\<^bold>\<circ><A1,F1,B1>) \<^bold>\<leftrightarrow> dom(<A2,F2,B2>) \<^bold>= cod(<A1,F1,B1>)" and
 A4: "x\<^bold>\<circ>(y\<^bold>\<circ>z) \<^bold>\<equiv> (x\<^bold>\<circ>y)\<^bold>\<circ>z" and
 A5: "x\<^bold>\<circ>dom(x) \<^bold>\<equiv> x" and
 A6: "cod(x)\<^bold>\<circ>x \<^bold>\<equiv> x" 



lemma A9: "\<E>(x\<^bold>\<circ>y) \<^bold>\<leftrightarrow> dom(x\<^bold>\<circ>y) \<^bold>= dom(y)" nitpick

lemma A10: "\<E>(x\<^bold>\<circ>y) \<^bold>\<leftrightarrow> cod(x\<^bold>\<circ>y) \<^bold>= cod(y)" oops

lemma A11: "(\<E>(x\<^bold>\<circ>y) \<^bold>\<and> \<E>(y\<^bold>\<circ>x)) \<^bold>\<rightarrow> \<E>(x\<^bold>\<circ>(y\<^bold>\<circ>z))" nitpick


=======

consts source :: "e\<Rightarrow>e" ("\<box>_" [9]101) 
consts target :: "e\<Rightarrow>e" ("_\<box>" [10]102) 
consts composition :: "e\<Rightarrow>e\<Rightarrow>e" (infix "\<cdot>" 110)


abbreviation Definedness :: "e\<Rightarrow>bool" ("D_" [8]60) where "D x \<equiv> \<A> x" 
abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<approx>" 60) where "x \<approx> y \<equiv> ((D x) \<^bold>\<leftrightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

(* Axioms *)


end