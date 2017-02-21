theory Functors2 imports Main begin 
declare [[ smt_solver = cvc4]]

abbreviation fNot ("\<^bold>\<not>") (* Free negation *)                        
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies (infixr "\<^bold>\<rightarrow>" 13) (* Free implication *)        
 where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
abbreviation fForall ("\<^bold>\<forall>") (* (Polymorphic) free universal quantification guarded by a set S *)                
 where "\<^bold>\<forall> S \<Phi> \<equiv> \<forall>x. S x \<longrightarrow> \<Phi> x"   
(* Note: I did not succeed to introduce binder notation for parameterized binders. 
   So below we have to write "(\<^bold>\<forall> S (\<lambda>x. \<phi>))" instead of "(\<^bold>\<forall>\<^sup>Sx. \<phi>)"  *)

(* Further free logic connectives can now be defined as usual. *)
abbreviation fOr (infixr "\<^bold>\<or>" 11)                                 
 where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 12)                                
 where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"    
abbreviation fImplied (infixr "\<^bold>\<leftarrow>" 13)       
 where "\<phi> \<^bold>\<leftarrow> \<psi> \<equiv> \<psi> \<^bold>\<rightarrow> \<phi>" 
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 15)                             
 where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"  
abbreviation fExists ("\<^bold>\<exists>") (* (Polymorphic) free universal quantification guarded by a set S *)               
 where "\<^bold>\<exists> S \<Phi> \<equiv> \<exists>x. S x \<^bold>\<and> \<Phi> x"   
(* Note: I did not succeed to introduce binder notation for parameterized binders. 
   So below we have to write "(\<^bold>\<exists> S (\<lambda>x. \<phi>))" instead of "(\<^bold>\<exists>\<^sup>Sx. \<phi>)"  *)

abbreviation KlEqS  (* (Polymorphic) Kleene equality on set S *)
  where "KlEqS S x y \<equiv> (S x \<^bold>\<or> S y) \<^bold>\<rightarrow> x = y"  
abbreviation ExIdS  (* (Polymorphic) existing identity on set S *)
  where "ExIdS S x y \<equiv> S x \<^bold>\<and> S y \<^bold>\<and> x = y"

abbreviation KlEq ("_\<cong>__") (* Mixfix notaion for Kleene equality on set S*)
  where "x \<cong>S y \<equiv> KlEqS S x y"  
abbreviation ExId ("_\<simeq>__") (* Mixfix notaion for Existing identity on set S *)  
  where "x \<simeq>S y \<equiv> ExIdS S x y"

consts (* Polymorphic versions of domain, codomain and composition *)
 domain::"'a\<Rightarrow>'a" ("dom _" [108] 109) 
 codomain:: "'a\<Rightarrow>'a" ("cod _" [110] 111) 
 composition:: "'a\<Rightarrow>'a\<Rightarrow>'a" (infix "\<cdot>" 110)

abbreviation ID (* (Polymorphic) predicate for identity morphisms on a set S *)
 where "ID S i \<equiv> (\<^bold>\<forall> S (\<lambda>x. S(i\<cdot>x) \<^bold>\<rightarrow> ((i\<cdot>x) \<cong>S x)) \<^bold>\<and> (\<^bold>\<forall> S (\<lambda>x. S(x\<cdot>i) \<^bold>\<rightarrow> ((x\<cdot>i) \<cong>S x))))"

abbreviation I ("I\<^sup>__") (* Mixfix notation: predicate for identity morphisms on a set S *)
 where "I\<^sup>S i \<equiv> ID S i"

definition CATEGORY (* (Polymorphic) definition of a category on a set S*) 
  where "CATEGORY \<equiv> \<lambda>S.
   ((\<forall>x. (S(dom x) \<^bold>\<rightarrow> S x)) \<^bold>\<and>
    (\<forall>y. S(cod y) \<^bold>\<rightarrow> S y) \<^bold>\<and>
    (\<forall>x y. S(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>S (cod y))) \<^bold>\<and>
    (\<forall>x y z. ((x\<cdot>(y\<cdot>z)) \<cong>S ((x\<cdot>y)\<cdot>z))) \<^bold>\<and>
    (\<forall>x. ((x\<cdot>(dom x)) \<cong>S x)) \<^bold>\<and>
    (\<forall>y. (((cod y)\<cdot>y) \<cong>S y)))"
(* Question to Dana: Is it correct to use \<simeq>S and \<cong>S here? *)

definition SUBCATEGORY 
(* (Polymorphic) definition of a subcategory A of category S:
  - dom and cod are total and strict functions on A
  - A is included in S *) 
  where "SUBCATEGORY \<equiv> \<lambda>A S. 
   (CATEGORY S \<^bold>\<and> 
    (\<forall>x. A(dom x) \<^bold>\<leftrightarrow> A x) \<^bold>\<and> 
    (\<forall>x. A(cod x) \<^bold>\<leftrightarrow> A x) \<^bold>\<and>
    (\<forall>x. A x \<^bold>\<rightarrow> S x))"

abbreviation CAT_E ("CAT\<^sup>__") (* Mixfix notation for A is a subcategory of S *)
  where "CAT\<^sup>S A \<equiv> SUBCATEGORY A S"

definition FUNCTOR 
(* (Polymorphic) definition of a Functor:
 - A and B are subcategories of E
 - f is a strict and total mapping from A to B
 - etc. (here I am not sure what exactly we need to assume) *)
  where "FUNCTOR \<equiv> \<lambda>A f B E.
   ((CAT\<^sup>E A) \<^bold>\<and>
    (CAT\<^sup>E B) \<^bold>\<and>
    (\<forall>x::'a. B(f x) \<^bold>\<leftrightarrow> A x) \<^bold>\<and>
    (\<forall>x::'a. \<forall>y::'a. A(x\<cdot>y) \<^bold>\<rightarrow> ((f(x\<cdot>y)) \<cong>B ((f x)\<cdot>(f y)))) \<^bold>\<and>
    (\<forall>x::'a. ((A x) \<^bold>\<and> (I\<^sup>A x)) \<^bold>\<rightarrow> I\<^sup>B(f x)) \<^bold>\<and>
    (\<forall>x::'a. \<forall>y::'a. \<forall>z::'a. ((x\<cdot>y) \<cong>A z) \<^bold>\<rightarrow> (((f x)\<cdot>(f y)) \<cong>B (f z))))" 
(* Remark: the last line is needed to prove Freyd and Scedrov's conditions for functors; see 
   below *)
    
typedecl i (* We fix a type i of morhisms *) 
consts 
  E:: "i\<Rightarrow>bool" (* Existence/definedness predicate on type i in free logic *)
  A:: "i\<Rightarrow>bool" (* Set A of morphisms of type i *)
  B:: "i\<Rightarrow>bool" (* Set B of morphisms of type i *)
  f::"i\<Rightarrow>i"     (* Mapping f from i to i *)


(* We postulate that f is functor for A to B (where A and B are subcategories of E) *)
axiomatization
  where 1: "FUNCTOR A f B E"

lemma True  (* Nitpick finds a model *)
  nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  (* Nitpick finds a model *)  
  nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops

lemma 2: "CAT\<^sup>E A" using 1 unfolding FUNCTOR_def by blast (* follows trivially from def of functor *)
lemma 3: "CAT\<^sup>E B" using 1 unfolding FUNCTOR_def by blast (* follows trivially from def of functor *)

(* Proving that E is a category; trivial since postulated in 1 via def of functor and subcatgeory *)
lemma 4: "CATEGORY E" using 1 unfolding FUNCTOR_def SUBCATEGORY_def by blast

(* We thus trivially also get the S axioms for E *)
lemma S1E: "E(dom x) \<^bold>\<rightarrow> E x" using 4 unfolding CATEGORY_def by blast 
lemma S2E: "E(cod y) \<^bold>\<rightarrow> E y" using 4 unfolding CATEGORY_def by blast 
lemma S3E: "E(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>E (cod y))" using 4 unfolding CATEGORY_def by blast 
lemma S4E: "(x\<cdot>(y\<cdot>z)) \<cong>E ((x\<cdot>y)\<cdot>z)" using 4 unfolding CATEGORY_def by blast 
lemma S5E: "(x\<cdot>(dom x)) \<cong>E x" using 4 unfolding CATEGORY_def by blast 
lemma S6E: "((cod y)\<cdot>y) \<cong>E y" using 4 unfolding CATEGORY_def by blast 

(* We prove that A is a category. This is not completely trivial anymore, e.g. for condition S3A. *)
lemma S1A: "A(dom x) \<^bold>\<rightarrow> A x" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson 
lemma S2A: "A(cod y) \<^bold>\<rightarrow> A y" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson
lemma S3A: "A(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>A (cod y))" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by smt
lemma S4A: "(x\<cdot>(y\<cdot>z)) \<cong>A ((x\<cdot>y)\<cdot>z)" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson 
lemma S5A: "(x\<cdot>(dom x)) \<cong>A x" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson
lemma S6A: "((cod y)\<cdot>y) \<cong>A y" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson

lemma 5: "CATEGORY A" unfolding CATEGORY_def using S1A S2A S3A S4A S5A S6A by blast

(* We prove that B is a category. This is not completely trivial anymore, e.g. for condition S3B. *)
lemma S1B: "B(dom x) \<^bold>\<rightarrow> B x" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson
lemma S2B: "B(cod y) \<^bold>\<rightarrow> B y" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson
lemma S3B: "B(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>B (cod y))" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by smt
lemma S4B: "(x\<cdot>(y\<cdot>z)) \<cong>B ((x\<cdot>y)\<cdot>z)" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson
lemma S5B: "(x\<cdot>(dom x)) \<cong>B x" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson
lemma S6B: "((cod y)\<cdot>y) \<cong>B y" using 1 unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by meson

lemma 6: "CATEGORY B" unfolding CATEGORY_def using S1B S2B S3B S4B S5B S6B by blast

(* We proving the functor conditions from Freyd and Scedrov, see p.5 of Categories, Allegories. *)
lemma "((dom x) \<cong>A y) \<^bold>\<rightarrow> ((dom (f x)) \<cong>B (f y))" 
  using 1 unfolding FUNCTOR_def by (smt S1A S1B S3A S3B S5A S5B S6A)
lemma "((cod x) \<cong>A y) \<^bold>\<rightarrow> ((cod (f x)) \<cong>B (f y))" 
  using 1 unfolding FUNCTOR_def by (smt S2A S2B S3A S3B S5A S5B S6A)
lemma "((x\<cdot>y) \<cong>A z) \<^bold>\<rightarrow> (((f x)\<cdot>(f y)) \<cong>B (f z))"
  using 1 unfolding FUNCTOR_def by blast
 
(* Some Tests *)
(* The polymorphic empty set is a category *)
lemma "CATEGORY (\<lambda>x::'a. False)" unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def by blast
(* The full set of objects of type i is not a category; countermodel by nitpick *)
lemma "CATEGORY (\<lambda>x::i. True)" unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def nitpick [user_axioms, show_all, format=2] oops


abbreviation CAT (* CAT stands for the collection of subcategories S of E *)
  where "CAT S \<equiv> CAT\<^sup>E S"

(* We try to prove that CAT is itself a category. However, we still fail; nitpick presents a countermodel. *)
lemma "CATEGORY CAT" nitpick [user_axioms, show_all, format=2] oops

(* We try to prove CAT satisfies the S-axioms for a category. However, we still fail; nitpick presents countermodels to all of them. *)
lemma S1: "CAT(dom x) \<^bold>\<rightarrow> CAT x" unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def nitpick [user_axioms, show_all, format=2] oops
lemma S2: "CAT(cod x) \<^bold>\<rightarrow> CAT x" unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def nitpick [user_axioms, show_all, format=2] oops
lemma S3: "CAT(x\<cdot>y) \<^bold>\<leftrightarrow> ((dom x) \<simeq>CAT (cod y))"  unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def nitpick [user_axioms, show_all, format=2] oops
lemma S4: "(x\<cdot>(y\<cdot>z)) \<cong>CAT ((x\<cdot>y)\<cdot>z)" unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def nitpick [user_axioms, show_all, format=2] oops
lemma S5B: "(x\<cdot>(dom x)) \<cong>CAT x" unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def nitpick [user_axioms, show_all, format=2] oops
lemma S6B: "((cod y)\<cdot>y) \<cong>CAT y" unfolding FUNCTOR_def SUBCATEGORY_def CATEGORY_def nitpick [user_axioms, show_all, format=2] oops











