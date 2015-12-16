theory QML_S4 imports Main 
begin
 typedecl i -- "type for possible worlds" 
 typedecl \<mu> -- "type for individuals"      
 type_synonym \<sigma> = "(i\<Rightarrow>bool)"

 consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)           -- "accessibility relation rr"   

 abbreviation mnot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not> _"[53]52)              where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)"    
 abbreviation mand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)           where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
 abbreviation mor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50)           where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
 abbreviation mimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49)           where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
 abbreviation mequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)           where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  
 abbreviation mall :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")                 where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
 abbreviation mallB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9)       where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
 abbreviation mexi :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>")                 where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
 abbreviation mexiB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)       where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
 abbreviation meq  :: "\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>" (infixr"\<^bold>="52)            where "x\<^bold>=y \<equiv> \<^bold>\<forall>\<phi>. \<phi>(x)\<^bold>\<rightarrow>\<phi>(y)"
 abbreviation mbox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>")                       where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. w r v \<longrightarrow> \<phi>(v)"
 abbreviation mdia :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>")                       where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. w r v \<and> \<phi>(v)" 

 abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>" [7] 8)         where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"


(*
 lemma M  : "\<lfloor>\<^bold>\<forall>p. \<^bold>\<box>p \<^bold>\<rightarrow> p\<rfloor>"        using refl_r by blast
 lemma IV : "\<lfloor>\<^bold>\<forall>p. \<^bold>\<box>p \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<box>p)\<rfloor>"   using trans_r by blast
*)

 abbreviation  mbbox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>\<^sup>b")                   where "\<^bold>\<box>\<^sup>b \<phi> \<equiv> \<^bold>\<exists>p. (p \<^bold>\<and> \<^bold>\<box>(\<^bold>\<diamond> p \<^bold>\<rightarrow> \<phi>))"
 abbreviation  mbdia :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>\<^sup>b")                   where "\<^bold>\<diamond>\<^sup>b \<phi> \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sup>b(\<^bold>\<not>\<phi>)"

 theorem FriedmanQuestion: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>b(\<^bold>\<diamond>\<^sup>b \<phi>)\<rfloor>"  
 sledgehammer [remote_leo2 remote_satallax,verbose,overlord]()

end
