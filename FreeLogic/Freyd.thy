theory Freyd 
imports FreeHOL 

begin

typedecl e  (* raw type of morphisms *)

consts source :: "e\<Rightarrow>e" ("\<box>_" [9]101) 
consts target :: "e\<Rightarrow>e" ("_\<box>" [9]101) 
consts composition :: "e\<Rightarrow>e\<Rightarrow>e" (infix "\<cdot>" 110)

abbreviation Definedness :: "e\<Rightarrow>bool" ("D_" [8]60) where "D x \<equiv> \<A> x" 
abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<approx>" 60) where "x \<approx> y \<equiv> ((D x) \<^bold>\<leftrightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

(* Axioms *)

axiomatization where
 A1:  "(D x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box> y))" and
 A2a: "((\<box>x)\<box>) \<approx> \<box>x" and
 A2b: "(\<box>(x\<box>)) \<approx> \<box>x" and
 A3a: "(\<box>x)\<cdot>x \<approx> x" and
 A3b: "x\<cdot>(x\<box>) \<approx> x" and
 A4a: "(\<box>(x\<cdot>y)) \<approx> \<box>(x\<cdot>(\<box>y))" and
 A4b: "(x\<cdot>y)\<box> \<approx> (((x\<box>)\<cdot>y)\<box>)" and
 A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"

abbreviation DirectedEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<greaterapprox>" 60) where "x \<greaterapprox> y \<equiv> ((D x) \<^bold>\<rightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

lemma L1_13: "((\<box>(x\<cdot>y)) \<approx> (\<box>(x\<cdot>(\<box>y)))) \<^bold>\<leftrightarrow> ((\<box>(x\<cdot>y)) \<greaterapprox> \<box>x)" by (metis A1 A2a A3a)

lemma "(\<^bold>\<exists>x. e \<approx> (\<box>x)) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))" by (metis A1 A2b A3b)
lemma "(\<^bold>\<exists>x. e \<approx> (x\<box>)) \<^bold>\<leftrightarrow> (e \<approx> \<box>e)" by (metis A1 A2a A3b)


abbreviation defined :: "e\<Rightarrow>bool" ("D_" [8]60) where "D x \<equiv> \<A> x"  

abbreviation f_E :: "'a\<Rightarrow>\<sigma>" ("\<E>")  where  "\<E> \<equiv> \<A>" (* \<E>,\<A> stand for Existence synonomously *)



abbreviation f_E :: "'a\<Rightarrow>\<sigma>" ("\<E>")  where  "\<E> \<equiv> \<A>" (* \<E>,\<A> stand for Existence synonomously *)

type_synonym \<sigma> = "(\<iota>\<Rightarrow>bool)" 
type_synonym \<tau> = "(\<iota>\<Rightarrow>\<iota>)" 

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
end