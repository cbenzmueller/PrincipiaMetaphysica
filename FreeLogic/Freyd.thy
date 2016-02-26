theory Freyd 
imports FreeHOL 

begin

typedecl e  (* raw type of morphisms *)


abbreviation Definedness :: "e\<Rightarrow>bool" ("D_" [8]60) 
 where "D x \<equiv> \<A> x" 
abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<approx>" 60) 
 where "x \<approx> y \<equiv> ((D x) \<^bold>\<leftrightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

(* Axioms *)

consts source :: "e\<Rightarrow>e" ("\<box>_" [108]109) 
consts target :: "e\<Rightarrow>e" ("_\<box>" [110]111) 
consts composition :: "e\<Rightarrow>e\<Rightarrow>e" (infix "\<cdot>" 110)

(*
axiomatization where
 Cat: "category source target composition"
*)

axiomatization Category where
 A1:  "(D x\<cdot>y) \<^bold>\<leftrightarrow> ((x\<box>) \<approx> (\<box>y))" and
(* A2a: "((\<box>x)\<box>) \<approx> \<box>x" \<and>*)
 A2b: "\<box>(x\<box>) \<approx> \<box>x" and
 A3a: "(\<box>x)\<cdot>x \<approx> x" and
 A3b: "x\<cdot>(x\<box>) \<approx> x" and
 A4a: "\<box>(x\<cdot>y) \<approx> \<box>(x\<cdot>(\<box>y))" and
 A4b: "(x\<cdot>y)\<box> \<approx> ((x\<box>)\<cdot>y)\<box>" and
 A5:  "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"


lemma L1:  "(\<box>\<box>x)\<cdot>((\<box>x)\<cdot>x) \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x"  using A5 by metis
lemma L2:  "(\<box>\<box>x)\<cdot>x \<approx> ((\<box>\<box>x)\<cdot>(\<box>x))\<cdot>x"         using L1 A3a by metis
lemma L3:  "(\<box>\<box>x)\<cdot>x \<approx> (\<box>x)\<cdot>x"                 using L2 A3a by metis
lemma L4:  "(\<box>\<box>x)\<cdot>x \<approx> x"                      using L3 A3a by metis
lemma L5:  "\<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>((\<box>\<box>x)\<cdot>(\<box>x))"      using A4a by auto
lemma L6:  "\<box>((\<box>\<box>x)\<cdot>x) \<approx> \<box>\<box>x"                using L5 A3a by metis
lemma L7:  "\<box>\<box>(x\<box>) \<approx> \<box>(\<box>\<box>(x\<box>))\<cdot>(x\<box>)"        using L6 by auto
lemma L8: "\<box>\<box>(x\<box>) \<approx> \<box>(x\<box>)"                   using L4 L7 by metis
lemma L9: "\<box>\<box>(x\<box>) \<approx> \<box>x"                      using A2b L8 by metis
lemma L10: "\<box>\<box>x \<approx> \<box>x"                         using A2b L9 by metis
lemma L11: "\<box>\<box>((\<box>x)\<box>) \<approx> \<box>\<box>(x\<box>)"             using A2b L10 by metis
lemma L12: "\<box>\<box>((\<box>x)\<box>) \<approx> \<box>x"                  using L11 L9 by metis
lemma L13: "(\<box>\<box>((\<box>x)\<box>))\<cdot>((\<box>x)\<box>) \<approx> ((\<box>x)\<box>)"  using L4 by auto   
lemma L14: "(\<box>x)\<cdot>((\<box>x)\<box>) \<approx> (\<box>x)\<box>"            using L12 L13 by metis
lemma LM10: "(\<box>x)\<box> \<approx> (\<box>x)\<cdot>((\<box>x)\<box>)"           using L14 by auto
lemma A2a: "(\<box>x)\<box> \<approx> \<box>x"                       using A3b LM10 by metis


abbreviation DirectedEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<greaterapprox>" 60) where "x \<greaterapprox> y \<equiv> ((D x) \<^bold>\<rightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

lemma L1_13: "((\<box>(x\<cdot>y)) \<approx> (\<box>(x\<cdot>(\<box>y)))) \<^bold>\<leftrightarrow> ((\<box>(x\<cdot>y)) \<greaterapprox> \<box>x)" 
sledgehammer
by (metis A1 A2a A3a)


lemma "(\<^bold>\<exists>x. e \<approx> (\<box>x)) \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))" 
 by (metis A1 A2b A3b)
lemma "(\<^bold>\<exists>x. e \<approx> (x\<box>)) \<^bold>\<leftrightarrow> e \<approx> (\<box>e)"
 by (metis A1 A2b A3a A3b)
lemma "e \<approx> (\<box>e) \<^bold>\<leftrightarrow> e \<approx> (e\<box>)"
 by (metis A1 A2b A3a A3b A4a)
lemma "e \<approx> (e\<box>) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)"
 by (metis A1 A2b A3a A3b A4a) 
lemma "(\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x)"
 by (metis A1 A2b A3a A3b)


abbreviation IdentityMorphism :: "e\<Rightarrow>bool" ("IdM_" [8]60) where "IdM x \<equiv> x \<approx> (\<box>x)"

lemma "(IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (\<box>x))) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<exists>x. e \<approx> (x\<box>))) \<^bold>\<and> 
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (\<box>e)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> e \<approx> (e\<box>)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. e\<cdot>x \<greaterapprox> x)) \<^bold>\<and>
       (IdM e \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. x\<cdot>e \<greaterapprox> x))"
 by (smt A1 A2a A3a A3b)

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
sledgehammer[verbose, timeout = 600] nitpick


lemma "category source target composition" by (meson A1 A2b A3a A3b A4a A4b A5)

consts One :: "e" ("\<one>")

axiomatization Monoid where 
 M1: "\<one>\<cdot>x \<approx> x" and
 M2: "x\<cdot>\<one> \<approx> x" and
 M3: "x\<cdot>(y\<cdot>z) \<approx> (x\<cdot>y)\<cdot>z"


 M1: "(\<box>x) \<approx> \<one> \<^bold>\<and> (x\<box>) \<approx> \<one>"




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


=======

consts source :: "e\<Rightarrow>e" ("\<box>_" [9]101) 
consts target :: "e\<Rightarrow>e" ("_\<box>" [10]102) 
consts composition :: "e\<Rightarrow>e\<Rightarrow>e" (infix "\<cdot>" 110)


abbreviation Definedness :: "e\<Rightarrow>bool" ("D_" [8]60) where "D x \<equiv> \<A> x" 
abbreviation OrdinaryEquality :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "\<approx>" 60) where "x \<approx> y \<equiv> ((D x) \<^bold>\<leftrightarrow> (D y)) \<^bold>\<and> x \<^bold>= y"  

(* Axioms *)


end