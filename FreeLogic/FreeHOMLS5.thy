(*<*) 
theory FreeHOMLS5   
imports Main 

begin
(*>*)

typedecl \<iota>                     -- "the type for indiviuals" 
typedecl \<omega>                     -- "the type for possible worlds"     
type_synonym \<sigma> = "\<omega> \<Rightarrow> bool"   -- "the type for Booleans"   


consts f_A :: "'a\<Rightarrow>\<sigma>" ("\<A>")   (* Existence *)
consts f_star :: "'a" ("\<^bold>\<star>")   (* Undefinedness *)

axiomatization where f_star_axiom: "\<forall>w. \<not>\<A>(\<^bold>\<star>)(w)"

abbreviation f_not :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<not>_" [58] 59) 
  where "\<^bold>\<not> \<phi> \<equiv> (\<lambda>w. \<not>\<phi>(w))"    
abbreviation f_implies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<rightarrow>" 49)
  where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi>(w) \<longrightarrow> \<psi>(w))"  
abbreviation f_all :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<forall>")
  where "\<^bold>\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<A>(x)(w) \<longrightarrow>  \<Phi>(x)(w))"   
abbreviation f_all_bind :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<^bold>\<forall>" [8] 9) 
 where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"

abbreviation f_or :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<or>" 51)
  where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<lambda>w. \<phi>(w) \<or> \<psi>(w))"  
abbreviation f_and :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<and>" 52) 
  where "\<phi> \<^bold>\<and> \<psi> \<equiv> (\<lambda>w. \<phi>(w) \<and> \<psi>(w))"   
abbreviation f_equiv :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<leftrightarrow>" 50)     
 where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<lambda>w. \<phi>(w) \<longleftrightarrow> \<psi>(w))"   
abbreviation f_equals :: "'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "\<^bold>=" 56)
  where "x \<^bold>= y \<equiv> (\<lambda>w. x = y)"
  
abbreviation f_exi :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
 where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y))"                
(* where "\<^bold>\<exists>\<Phi> \<equiv> (\<lambda>w. \<forall>x. \<A>(x)(w) \<and> \<Phi>(x)(w))"   *)
abbreviation f_exi_b :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"  (binder "\<^bold>\<exists>" [8]9)  
 where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

abbreviation f_that :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<omega> \<Rightarrow> 'a" ("\<^bold>I")
  where "\<^bold>I\<Phi> \<equiv> (\<lambda>w. if \<exists>x. \<Phi>(x)(w) \<and> (\<forall>y. \<Phi>(y)(w) \<longrightarrow> y = x) 
                    then THE x. \<A>(x)(w) \<and> \<Phi>(x)(w) 
                    else \<^bold>\<star>)"
abbreviation f_that_b :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<omega> \<Rightarrow> 'a"  (binder "\<^bold>I" [8] 9) 
 where "\<^bold>Ix. \<phi>(x) \<equiv> \<^bold>I(\<phi>)"

abbreviation f_mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>_" [52] 53)
  where "\<^bold>\<box>\<phi> \<equiv> (\<lambda>w.\<forall>v. \<phi>(v))"
abbreviation f_mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<diamond>_" [52] 53) 
  where "\<^bold>\<diamond>\<phi> \<equiv> (\<lambda>w.\<exists>v. \<phi>(v))" 
  
abbreviation valid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>" [8] 9)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"



section {* Some Introductory Tests *} 
-- "See Scott, Existence and Description in Formal Logic, 1967, pages 183-184"

consts f_r  :: "\<iota>\<Rightarrow>\<iota>\<Rightarrow>\<sigma>" (infixr "\<^bold>r" 70)    (* Scott considers just one binary relation r *) 

lemma "\<lfloor>\<^bold>\<box>(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x)\<rfloor>" by auto  
 (* ... valid in all domains including the empty one *)

lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)\<rfloor>" nitpick oops    
 (* ... not valid in the empty domain; hence, the valid formulas formulas are not closed 
    under the rule of modus ponens when the empty domain is included *)

lemma "\<lfloor>\<^bold>\<box>((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y))\<rfloor>" nitpick oops
 (* not valid *)

lemma "\<lfloor>\<^bold>\<box>(((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> (\<^bold>\<exists>y::\<iota>. y \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y))\<rfloor>" by simp
 (* ... now the empty domain is excluded and the statement is valid *)


-- "See Scott 1967, page 185"
lemma S1_inst : "\<lfloor>\<^bold>\<box>((\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<Psi>(x))))\<rfloor>" by auto
lemma S2 :      "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>y.\<^bold>\<exists>x. x \<^bold>= y)\<rfloor>" by simp
lemma S3 :      "\<lfloor>\<^bold>\<box>(\<alpha> \<^bold>= \<alpha>)\<rfloor>" by simp
lemma S4_inst : "\<lfloor>\<^bold>\<box>((\<Phi>(\<alpha>) \<^bold>\<and> (\<alpha> \<^bold>= \<beta>)) \<^bold>\<rightarrow> \<Phi>(\<beta>))\<rfloor>" by auto
lemma UI_inst : "\<lfloor>\<^bold>\<box>(((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<and> (\<^bold>\<exists>x. x \<^bold>= \<alpha>)) \<^bold>\<rightarrow> \<Phi>(\<alpha>))\<rfloor>" by auto
lemma UI_test : "\<lfloor>\<^bold>\<box>((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(\<alpha>))\<rfloor>" nitpick [user_axioms] oops -- "Countermodel"
lemma UI_cor1 : "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>y.((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y)))\<rfloor>" by auto
lemma UI_cor2 : "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>y.((\<^bold>\<forall>x. \<^bold>\<not>(x \<^bold>= y)) \<^bold>\<rightarrow> \<^bold>\<not>(y \<^bold>= y)))\<rfloor>" by auto
lemma UI_cor3 : "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>y.((y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<exists>x. x \<^bold>= y)))\<rfloor>" by auto
lemma UI_cor4 : "\<lfloor>\<^bold>\<box>((\<^bold>\<forall>y. y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<forall>y.\<^bold>\<exists>x. x \<^bold>= y))\<rfloor>" by simp

lemma "(\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. x \<^bold>= \<alpha>)\<rfloor>) \<longrightarrow> \<A>(\<alpha>)(w)" by simp
 (* ... to say that (\<^bold>\<exists>x. x = \<alpha>) is true means that the value of \<alpha> exists (properly) *)

(*
lemma I1_inst : "\<lfloor>\<^bold>\<forall>y. ((y \<^bold>= (\<^bold>Ix. \<Phi>(x))(w)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))))\<rfloor>" nitpick

abbreviation star ("\<Otimes>") where "\<lfloor>\<^bold>\<box>()\<rfloor>\<Otimes> \<equiv> \<^bold>Iy. \<^bold>\<not> (y \<^bold>= y)"

lemma test : "\<lfloor>\<^bold>\<box>()\<rfloor>\<Otimes> = \<^bold>\<star>" by simp


lemma I2_inst : "\<lfloor>\<^bold>\<box>()\<rfloor>\<^bold>\<not>(\<^bold>\<exists>y. y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<rightarrow>  (\<Otimes> \<^bold>= (\<^bold>Ix. \<Phi>(x)))" by (metis (no_types, lifting) the_equality)

 (* Extensionality *)
lemma Ext_inst : "\<lfloor>\<^bold>\<box>()\<rfloor>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<leftrightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>Ix. \<Phi>(x)) \<^bold>= (\<^bold>Ix. \<Psi>(x)))" by (smt the1_equality)


 (* the following schema is not valid as intended *)
lemma I3 : "\<lfloor>\<^bold>\<box>()\<rfloor>(\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)" nitpick [user_axioms] oops


 (* The following is not valid, Problem? *)
lemma Russel_inst : 
 "\<lfloor>\<^bold>\<box>()\<rfloor>((\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)) 
  \<^bold>\<rightarrow> 
  ((\<alpha> \<^bold>r (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<exists>y.((\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))) \<^bold>\<and> (\<alpha> \<^bold>r y))))"
nitpick [user_axioms] oops




lemma "\<lfloor>\<^bold>\<box>()\<rfloor>\<^bold>\<not>(\<^bold>\<exists>x. (x \<^bold>= (\<^bold>Iy. \<^bold>\<not> (y \<^bold>= y))))" using f_star_axiom by auto
lemma "\<lfloor>\<^bold>\<box>()\<rfloor>(\<^bold>\<exists>x. x \<^bold>= a) \<^bold>\<rightarrow>  \<A>(a)" by simp


  (* Some further test *)
consts a::'a b::'a 
axiomatization where ax1: "\<lfloor>\<^bold>\<box>()\<rfloor>\<A>(a) \<^bold>\<and> \<A>(b) \<^bold>\<and> \<^bold>\<not> (a \<^bold>= b) \<^bold>\<and> \<^bold>\<not> (a \<^bold>= \<Otimes>) \<^bold>\<and> \<^bold>\<not> (b \<^bold>= \<Otimes>)"
lemma test2: "\<lfloor>\<^bold>\<box>()\<rfloor>\<Otimes> \<^bold>= (\<^bold>I (\<lambda>x. x  \<^bold>= a \<^bold>\<or> x \<^bold>= b))" by (metis ax1)

  
consts  f_r  :: "\<iota> \<Rightarrow> \<iota> \<Rightarrow> \<sigma>" (*<*)(infixr "\<^bold>r" 70)(*>*) 
consts  f_ar  :: "\<omega> \<Rightarrow> \<omega> \<Rightarrow> bool" (*<*)(infixr "\<^bold>a\<^bold>r" 70)(*>*)
  
*)
end