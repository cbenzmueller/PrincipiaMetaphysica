theory Categories3 imports FreeHOL 
begin

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
 A1: "dom(<A,F,B>) = (\<lambda>x.x)"
  
axiomatization where
 A1: "\<E>(x) \<^bold>\<leftrightarrow> \<E>(dom(x))" and
 A2: "\<E>(x) \<^bold>\<leftrightarrow> \<E>(cod(x))" and
 A3: "\<E>(x\<^bold>\<circ>y) \<^bold>\<leftrightarrow> dom(x) \<^bold>= cod(y)" and
 A4: "x\<^bold>\<circ>(y\<^bold>\<circ>z) \<^bold>\<equiv> (x\<^bold>\<circ>y)\<^bold>\<circ>z" and
 A5: "x\<^bold>\<circ>dom(x) \<^bold>\<equiv> x" and
 A6: "cod(x)\<^bold>\<circ>x \<^bold>\<equiv> x" 

lemma A7: "dom(x) \<^bold>\<equiv> cod(dom(x))" 
 sledgehammer
 by (metis A1 A2 A3 A5)

lemma A8: "cod(x) \<^bold>\<equiv> dom(cod(x))" 
 sledgehammer
 by (metis A2 A3 A5 A6 A7)

lemma A9: "\<E>(x\<^bold>\<circ>y) \<^bold>\<leftrightarrow> dom(x\<^bold>\<circ>y) \<^bold>= dom(y)" oops

lemma A10: "\<E>(x\<^bold>\<circ>y) \<^bold>\<leftrightarrow> cod(x\<^bold>\<circ>y) \<^bold>= cod(y)" oops

lemma A11: "(\<E>(x\<^bold>\<circ>y) \<^bold>\<and> \<E>(y\<^bold>\<circ>x)) \<^bold>\<rightarrow> \<E>(x\<^bold>\<circ>(y\<^bold>\<circ>z))" nitpick
end