theory BasicExamplePolynomials imports HOL Nitpick begin 

typedecl i                          (* U: The objects of type i form the universe U. *)
type_synonym pu = "(i \<Rightarrow> bool)"     (* P(U): The objects of type pu are the subsets of universe U. *)

consts E:: "pu\<Rightarrow>bool"   (* Existence predicate on P(U). *)

abbreviation fNot:: "bool\<Rightarrow>bool" ("\<^bold>\<not>")                           where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr "\<^bold>\<rightarrow>" 49)       where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 
abbreviation fForall:: "(pu\<Rightarrow>bool)\<Rightarrow>bool" ("\<^bold>\<forall>")                    where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E(x)\<longrightarrow>\<Phi>(x)"   
abbreviation fForallBinder:: "(pu\<Rightarrow>bool)\<Rightarrow>bool" (binder "\<^bold>\<forall>" [8] 9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"
abbreviation fOr (infixr "\<^bold>\<or>" 51)                                 where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 52)                                where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 50)                             where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation fExists ("\<^bold>\<exists>")                                       where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

consts fStar:: "pu" ("*")   \<comment> "Distinguished symbol for undefinedness"
axiomatization where fStarAxiom: "\<not>(E*)"
abbreviation fThat:: "(pu\<Rightarrow>bool)\<Rightarrow>pu" ("I") 
 where "I(\<Phi>) \<equiv>  if \<exists>x. E(x) \<and> \<Phi>(x) \<and> (\<forall>y. (E(y) \<and> \<Phi>(y)) \<longrightarrow> (y = x)) then THE x. E(x) \<and> \<Phi>(x) else *"
abbreviation fThatBinder:: "(pu\<Rightarrow>bool)\<Rightarrow>pu"  (binder "I" [8] 9) where "I x. \<phi>(x) \<equiv> I(\<phi>)"

abbreviation eq1 (infixr "\<^bold>=" 56)  where "x \<^bold>= y \<equiv> (E(x) \<^bold>\<and> E(y) \<^bold>\<and> (x = y))"
abbreviation eq2 (infixr "\<^bold>=\<^bold>=" 56) where "x \<^bold>=\<^bold>= y \<equiv> ((E(x) \<^bold>\<or> E(y)) \<^bold>\<rightarrow> (x\<^bold>=y))"

abbreviation intersection::"pu\<Rightarrow>pu\<Rightarrow>pu" ("_\<inter>_" [90,91] 100)  where "a\<inter>b \<equiv> \<lambda>x. a(x) \<and> b(x)"
abbreviation union::"pu\<Rightarrow>pu\<Rightarrow>pu" ("_\<union>_" [90,91] 100)  where "a\<union>b \<equiv> \<lambda>x. a(x) \<or> b(x)"
abbreviation setdifference::"pu\<Rightarrow>pu\<Rightarrow>pu" ("_\<setminus>_" [90,91] 100)  where "a\<setminus>b \<equiv> \<lambda>x. a(x) \<and> \<not>b(x)"
abbreviation subset::"pu\<Rightarrow>pu\<Rightarrow>bool" ("_\<subseteq>_" [90,91] 100)  where "a\<subseteq>b \<equiv> \<forall>x. a(x) \<longrightarrow> b(x)"

(* Boole's Partial Algebra  P(U):= *)
abbreviation zero::pu ("0") where "0 \<equiv> \<lambda>x. False"
abbreviation one::pu  ("1") where "1 \<equiv> \<lambda>x. True"
abbreviation comp::"pu\<Rightarrow>pu\<Rightarrow>pu" ("_\<cdot>_" [90,91] 100)   where "a\<cdot>b \<equiv> a \<inter> b"
abbreviation plus::"pu\<Rightarrow>pu\<Rightarrow>pu" ("_+_"  [92,93] 101)  where "a+b \<equiv> if a\<inter>b = 0 then a\<union>b else *"
abbreviation minus::"pu\<Rightarrow>pu\<Rightarrow>pu" ("_--_"  [92,93] 101)  where "a--b \<equiv> if a\<subseteq>b then a\<setminus>b else *"

axiomatization where
     A1: "E(0) \<^bold>\<and> E(1)" 
 and A2: "(p\<cdot>q \<^bold>=\<^bold>= 0) \<^bold>\<leftrightarrow> (p \<^bold>=\<^bold>= 0) \<^bold>\<and> (q \<^bold>=\<^bold>= 0)" 
 and A4: "(p\<cdot>q \<^bold>=\<^bold>= 1) \<^bold>\<leftrightarrow> (p \<^bold>=\<^bold>= 1) \<^bold>\<and> (q \<^bold>=\<^bold>= 1)" 

lemma True nitpick [satisfy, user_axioms] oops
lemma False sledgehammer

lemma "E(p+q) \<^bold>\<leftrightarrow> (p\<cdot>q \<^bold>=\<^bold>= 0)" sledgehammer nitpick [user_axioms, show_all, format = 2]

