(*<*) 
theory BasicTests1
imports AbstractObjects

begin
(*>*)

section {* Some Basic Tests *}

  text {* 
  The next two statements are not theorems; Nitpick reports countermodels
  *}

 lemma "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}
 lemma "[(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}

 lemma "[(\<^bold>\<forall>y. \<lparr>R\<^sup>T,y\<^sup>T\<rparr>)] = \<top>" apply simp nitpick oops

  text {* 
  However, the next two statements are of course valid.
  *}

 lemma "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp done

 subsection {* Verifying Necessitation *}

  text {* The next two lemmata show that neccessitation holds for arbitrary formulas 
  and arbitrary propositional formulas. We present the lemma in both variants. 
  *}
 
 lemma necessitationF: "[\<phi>\<^sup>F] = \<top> \<longrightarrow> [\<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp done
 lemma necessitationP: "[\<phi>\<^sup>P] = \<top> \<longrightarrow> [\<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp done

 subsection {* Modal Collapse is Countersatisfiable *}

  text {* 
  The modelfinder Nitpick constructs a finite countermodel to the assertion
  that modal collaps holds. 
  *}

 lemma modalCollapseF: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}
 lemma modalCollapseP: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}

 (*
 lemma modalCollapseFcsa: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F] = \<top>" sledgehammer [remote_leo2 remote_satallax]
 lemma modalCollapseFcsa: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<top>" sledgehammer [remote_leo2 remote_satallax]
 lemma modalCollapsePcsa: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<top>" sledgehammer [remote_leo2 remote_satallax]
 *)

 subsection {* Verifying S5 Principles \label{sec:S5} *} 

  text {* 
  @{text "\<box>"} could have been modeled by employing an equivalence relation @{text "r"} in a 
  guarding clause. This has been done in previous work. Our alternative, simpler definition of 
  @{text "\<box>"} above omits
  this clause (since all worlds are reachable from any world in an equivalence relation). The 
  following lemmata, which check various conditions for S5, confirm that we have indeed 
  obtain a correct modeling of S5.
  *}

 lemma axiom_T_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_T_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F] = \<top>" apply simp done

 lemma axiom_B_P: "[\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_B_F: "[\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma axiom_4_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp by auto
 lemma axiom_4_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp by auto

 lemma axiom_D_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_D_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma axiom_5_P: "[\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma axiom_5_F: "[\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma test_A_P: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma test_A_F: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done

 lemma test_B_P: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp by auto
 lemma test_B_F: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp by auto

 lemma test_C_P: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}
 lemma test_C_F: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}

 lemma test_D_P: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma test_D_F: "[\<^bold>\<diamond>\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F] = \<top>" apply simp done


 subsection {* Relations between  Meta-Logical Notions *}

 lemma  "[\<phi>\<^sup>P] = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>P]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>P]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>F] = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = \<bottom>" apply simp done
 lemma  "[\<phi>\<^sup>F]\<^sup>s\<^sup>a\<^sup>t = \<top> \<longleftrightarrow> [\<phi>\<^sup>F]\<^sup>i\<^sup>n\<^sup>v = \<bottom>" apply simp done

  text {* 
  However, for terms we have: 
  *}

 lemma  "[\<phi>\<^sup>T] = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>c\<^sup>s\<^sup>a\<^sup>t = *" apply simp done
 lemma  "[\<phi>\<^sup>T]\<^sup>i\<^sup>n\<^sup>v = *" apply simp done

 subsection {* Testing the Propagation of Syntactical Category Information *}

 lemma "\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>P \<and> \<not>(\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>F) \<and> \<not>(\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>T) \<and> \<not>(\<exists>X. \<lparr>R\<^sup>T,a\<^sup>T\<rparr> = X\<^sup>E)" apply simp done
 lemma "\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>F \<and> \<not>(\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>P) \<and> \<not>(\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>T) \<and> \<not>(\<exists>X. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> = X\<^sup>E)" apply simp done

  text {* 
  Most importantly, we have that the following language construct is evaluated as ineligible at validity
  level; @{text "error (*)"} is returned. 
  *}

 lemma "[\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr>] = *" apply simp done

  text {* 
  This is also confirmed as follows in Isabelle: Isabelle simplifies the following expression
  to @{text "dio\<^sup>E = X"} (simply move the curse on @{text "simp"} to see this). 
  *}

 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr> = X" apply simp oops     -- {* X is @{text "dio\<^sup>E"} *}
 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<not>\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr> = X" apply simp oops     -- {* X is @{text "dio\<^sup>E"} *}

 subsection {* Are Priorities Defined Correctly? *}

 lemma "\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P \<equiv> (\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<^bold>\<rightarrow> \<chi>\<^sup>P" apply simp done
 lemma "\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P \<equiv> \<phi>\<^sup>P \<^bold>\<and> (\<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P)" apply simp nitpick oops -- {* Countermodel by Nitpick *}

 lemma "(\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<equiv> \<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<equiv> ((\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<^bold>\<equiv> (\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P))" apply simp done
 lemma "(\<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P \<^bold>\<equiv> \<phi>\<^sup>P \<^bold>\<and> \<psi>\<^sup>P) \<equiv> (\<phi>\<^sup>P \<^bold>\<and> (\<psi>\<^sup>P \<^bold>\<equiv> \<phi>\<^sup>P) \<^bold>\<and> \<psi>\<^sup>P)" apply simp nitpick oops -- {* Countermodel by Nitpick *}


section {* E!, O!, A! and =E *}

  text {* 
  We introduce the distinguished 1-place relation constant: E (read: ‘being concrete’ or ‘concreteness’) 
  *}

 consts E::"(e\<Rightarrow>io)"
 
  text {* 
  Being ordinary is defined as being possibly concrete. 
  *}

 abbreviation ordinaryObject::"(e\<Rightarrow>io) opt" ("O!") where "O! \<equiv> \<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>"

 lemma "O! = X" apply simp oops       -- {* X is @{text "(\<lambda>x w. Ex (exe1 E x))\<^sup>T"} *}

  text {* 
  Being abstract is is defined as not possibly being concrete. 
  *}

 abbreviation abstractObject::"(e\<Rightarrow>io) opt" ("A!") where "A! \<equiv> \<^bold>\<lambda>x. \<^bold>\<not>(\<^bold>\<diamond>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)"

 lemma "A! = X" apply simp oops       -- {* X is @{text "(\<lambda>x w. \<forall>xa. \<not> exe1 E x xa)\<^sup>T"} *}


  text {* 
  Identity relations @{text "\<^bold>=\<^sub>E"} and @{text "\<^bold>="} are introduced. 
  *}

 abbreviation identityE::"e opt\<Rightarrow>e opt\<Rightarrow>io opt" (infixl "\<^bold>=\<^sub>E" 63) where "x \<^bold>=\<^sub>E y \<equiv> 
    \<lparr>O!,x\<rparr> \<^bold>\<and> \<lparr>O!,y\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F\<^sup>T,x\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>T,y\<rparr>)"

 lemma "a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T = X" apply simp oops      -- {* X is "@{text "(...)\<^sup>P"} *}


 subsection {* Identity on Individuals *}

 abbreviation identityI::"e opt\<Rightarrow>e opt\<Rightarrow>io opt" (infixl "\<^bold>=" 63) where "x \<^bold>= y \<equiv> 
    x \<^bold>=\<^sub>E y \<^bold>\<or> (\<lparr>A!,x\<rparr> \<^bold>\<and> \<lparr>A!,y\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<^sup>T\<rbrace>))"


 lemma "a\<^sup>T \<^bold>= a\<^sup>T = X" apply simp oops                                        -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "(\<lparr>A!,a\<^sup>T\<rparr> \<^bold>\<and> \<lparr>A!,a\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace>)) = X" apply simp oops   -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "(\<lparr>A!,a\<^sup>T\<rparr> \<^bold>\<and> \<lparr>A!,a\<^sup>T\<rparr>) = X" apply simp oops                             -- {* X is @{text "(...)\<^sup>P"} *}
 lemma "\<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace>) = X" apply simp oops                       -- {* X is @{text "(...)\<^sup>F"} *}

  text {* 
  As intended: the following two lambda-abstractions are not well-formed/eligible 
  and their evaluation reports in ERR-terms.
  *}

 lemma "\<^bold>\<lambda>\<^sup>2(\<lambda>x y. x\<^sup>T \<^bold>= y\<^sup>T) = X" apply simp oops   -- {* X is @{text "(\<lambda>x y. dio)\<^sup>E"} *}
 lemma "(\<^bold>\<lambda>x. x\<^sup>T \<^bold>= y\<^sup>T) = X" apply simp oops   -- {* X is @{text "(\<lambda>x. dio)\<^sup>E"} *}

 subsection {* Identitiy on Relations *}

 abbreviation identityRel1::" ((e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>1" 63) 
   where "F1 \<^bold>=\<^sup>1 G1 \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,F1\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>T,G1\<rbrace>)"

 abbreviation identityRel2::" ((e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>2" 63) 
   where "F2 \<^bold>=\<^sup>2 G2 \<equiv> \<^bold>\<forall>x1.(  (\<^bold>\<lambda>y.\<lparr>F2,y\<^sup>T,x1\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G2,y\<^sup>T,x1\<^sup>T\<rparr>)
                          \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F2,x1\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G2,x1\<^sup>T,y\<^sup>T\<rparr>))"

 abbreviation identityRel3::" ((e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>((e\<Rightarrow>e\<Rightarrow>e\<Rightarrow>io) opt)\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>3" 63) 
   where "F3 \<^bold>=\<^sup>3 G3 \<equiv> \<^bold>\<forall>x1 x2.(  (\<^bold>\<lambda>y.\<lparr>F3,y\<^sup>T,x1\<^sup>T,x2\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,y\<^sup>T,x1\<^sup>T,x2\<^sup>T\<rparr>)
                             \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F3,x1\<^sup>T,y\<^sup>T,x2\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,x1\<^sup>T,y\<^sup>T,x2\<^sup>T\<rparr>)
                             \<^bold>\<and> (\<^bold>\<lambda>y.\<lparr>F3,x1\<^sup>T,x2\<^sup>T,y\<^sup>T\<rparr>) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y.\<lparr>G3,x1\<^sup>T,x2\<^sup>T,y\<^sup>T\<rparr>))"

 lemma "F1\<^sup>T \<^bold>=\<^sup>1 G1\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "F2\<^sup>T \<^bold>=\<^sup>2 G2\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *} 
 lemma "F3\<^sup>T \<^bold>=\<^sup>3 G3\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}   
 lemma "\<lbrace>x\<^sup>T,F1\<^sup>T\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>T,G1\<^sup>T\<rbrace> = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}   
 lemma "\<lparr>F1\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<equiv> \<lparr>G1\<^sup>T,x\<^sup>T\<rparr> = X" apply simp oops -- {* X is @{text "(...)\<^sup>P"} *}   
 lemma "(\<^bold>\<lambda>y.\<lparr>F2\<^sup>T,y\<^sup>T,x1\<^sup>T\<rparr>)= X" apply simp oops -- {* X is @{text "(...)\<^sup>T"} *}  

 abbreviation equalityRel0::"io opt\<Rightarrow>io opt\<Rightarrow>io opt" (infixl "\<^bold>=\<^sup>0" 63) 
   where "F0 \<^bold>=\<^sup>0 G0 \<equiv> (\<^bold>\<lambda>y . F0) \<^bold>=\<^sup>1 (\<^bold>\<lambda>y. G0)"

 lemma "F1\<^sup>T \<^bold>=\<^sup>1 F1\<^sup>T = X" apply simp oops -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "[F1\<^sup>T \<^bold>=\<^sup>1 F1\<^sup>T] = \<top>" apply simp done 
 lemma "[F2\<^sup>T \<^bold>=\<^sup>2 F2\<^sup>T] = \<top>" apply simp done
 lemma "[F3\<^sup>T \<^bold>=\<^sup>3 F3\<^sup>T] = \<top>" apply simp done 

  text {* 
  Some further tests: 
  *}

  text {* 
  We discuss the example from \cite[pp.365-366]{zalta11:_relat_versus_funct_found_logic}:
  *}

 lemma "(\<^bold>\<lambda>x. \<^bold>\<exists>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>F\<^sup>T,x\<^sup>T\<rparr>) = X" apply simp  oops -- {*  X is @{text "(\<lambda>x. dio)\<^sup>E"} *}

 abbreviation K where "K \<equiv> \<^bold>\<lambda>x.\<^bold>\<exists>F.(\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>F\<^sup>T,x\<^sup>T\<rparr>)"
 
 lemma "[(\<^bold>\<exists>x. \<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> F\<^sup>T \<^bold>=\<^sup>1 K)))] = *" apply simp done
 lemma "(\<^bold>\<exists>x. \<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. (\<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> F\<^sup>T \<^bold>=\<^sup>1 K))) = X" apply simp oops -- {*  X is @{text "(dio)\<^sup>E"} *}
 

 text {* 
  Tests on identity:
  *}

 lemma "[a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T] = \<top>" apply simp nitpick oops -- {* Countermodel by Nitpick *}
 lemma "[\<lparr>O!,a\<^sup>T\<rparr> \<^bold>\<rightarrow> a\<^sup>T \<^bold>=\<^sub>E a\<^sup>T] = \<top>" apply simp done

 lemma "[(\<^bold>\<forall>F. \<lparr>F\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp done
 lemma "[\<lparr>O!,a\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>\<^bold>\<lambda>x. x\<^sup>T \<^bold>=\<^sub>E a\<^sup>T,a\<^sup>T\<rparr>] = \<top>" apply simp oops

 lemma "[(\<^bold>\<exists>F. \<lbrace>a\<^sup>T,F\<^sup>T\<rbrace>)] = \<top>" apply simp oops

 lemma "[(\<^bold>\<exists>\<phi>. \<phi>\<^sup>P)] = \<top>" apply simp by auto
 lemma "[(\<^bold>\<exists>\<phi>. \<phi>\<^sup>F)] = \<top>" apply simp by auto


 subsection {* Negation of Properties *}

 abbreviation notProp::"((e\<Rightarrow>io) opt)\<Rightarrow>(e\<Rightarrow>io) opt" ("\<^bold>\<sim>_" [58] 59) where "\<^bold>\<sim> \<Phi> \<equiv> case \<Phi> of 
    T(\<Psi>) \<Rightarrow> \<^bold>\<lambda>x.\<^bold>\<not>\<lparr>\<Phi>,x\<^sup>T\<rparr> | _ \<Rightarrow> ERR(deio)"  


 subsection {* Individual Constant @{text "\<^bold>a\<^sub>V"} and Function Term @{text "\<^bold>a\<^sub>G"} *}

 abbreviation a_V::"e opt" ("\<^bold>a\<^sub>V") where "\<^bold>a\<^sub>V \<equiv> \<^bold>\<iota>x. (\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> (F\<^sup>T \<^bold>=\<^sup>1 F\<^sup>T)))"

 abbreviation a_G::"(e\<Rightarrow>io) opt\<Rightarrow>e opt" ("\<^bold>a\<^sub>_" [58] 59) where "\<^bold>a\<^sub>G \<equiv> \<^bold>\<iota>x. (\<lparr>A!,x\<^sup>T\<rparr> \<^bold>\<and> (\<^bold>\<forall>F. \<lbrace>x\<^sup>T,F\<^sup>T\<rbrace> \<^bold>\<equiv> (F\<^sup>T \<^bold>=\<^sup>1 G)))"

 
section {* Axioms *}

 subsection {* Axioms for Negations and Conditionals *}

 lemma a21_1_P: "[\<phi>\<^sup>P \<^bold>\<rightarrow> (\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a21_1_F: "[\<phi>\<^sup>F \<^bold>\<rightarrow> (\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F)] = \<top>" apply simp done
 lemma a21_2_P: "[(\<phi>\<^sup>P \<^bold>\<rightarrow> (\<psi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P)) \<^bold>\<rightarrow> ((\<phi>\<^sup>P \<^bold>\<rightarrow> \<psi>\<^sup>P) \<^bold>\<rightarrow> (\<phi>\<^sup>P \<^bold>\<rightarrow> \<chi>\<^sup>P))] = \<top>" apply simp done
 lemma a21_2_F: "[(\<phi>\<^sup>F \<^bold>\<rightarrow> (\<psi>\<^sup>F \<^bold>\<rightarrow> \<chi>\<^sup>F)) \<^bold>\<rightarrow> ((\<phi>\<^sup>F \<^bold>\<rightarrow> \<psi>\<^sup>F) \<^bold>\<rightarrow> (\<phi>\<^sup>F \<^bold>\<rightarrow> \<chi>\<^sup>F))] = \<top>" apply simp done
 lemma a21_3_P: "[(\<^bold>\<not>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<not>\<psi>\<^sup>P) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi>\<^sup>P \<^bold>\<rightarrow> \<psi>\<^sup>P) \<^bold>\<rightarrow> \<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a21_3_F: "[(\<^bold>\<not>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<not>\<psi>\<^sup>F) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi>\<^sup>F \<^bold>\<rightarrow> \<psi>\<^sup>F) \<^bold>\<rightarrow> \<phi>\<^sup>F)] = \<top>" apply simp done

 subsection {* Axioms of Identity *}
  text {* todo *}

 subsection {* Axioms of Quantification *}
  text {* todo *}

 subsection {* Axioms of Actuality *}

 lemma a31_1_P: "[\<^bold>\<A>(\<^bold>\<not>\<phi>\<^sup>P) \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>(\<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a31_1_F: "[\<^bold>\<A>(\<^bold>\<not>\<phi>\<^sup>F) \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>(\<phi>\<^sup>F)] = \<top>" apply simp done
 lemma a31_2_P: "[\<^bold>\<A>(\<phi>\<^sup>P \<^bold>\<rightarrow> \<psi>\<^sup>P) \<^bold>\<equiv> (\<^bold>\<A>(\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<A>(\<psi>\<^sup>P))] = \<top>" apply simp done
 lemma a31_2_F: "[\<^bold>\<A>(\<phi>\<^sup>F \<^bold>\<rightarrow> \<psi>\<^sup>F) \<^bold>\<equiv> (\<^bold>\<A>(\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<A>(\<psi>\<^sup>F))] = \<top>" apply simp done
 lemma a31_3_P: "[\<^bold>\<A>(\<^bold>\<forall>x. \<phi>\<^sup>P) \<^bold>\<equiv> (\<^bold>\<forall>x. \<^bold>\<A>(\<phi>\<^sup>P))] = \<top>" apply simp done
 lemma a31_3_F: "[(\<^bold>\<A>(\<^bold>\<forall>x. \<phi>\<^sup>F) \<^bold>\<equiv> (\<^bold>\<forall>x. \<^bold>\<A>(\<phi>\<^sup>F)))] = \<top>" apply simp done
 lemma a31_4_P: "[\<^bold>\<A>(\<phi>\<^sup>P) \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<A>(\<phi>\<^sup>P))] = \<top>" apply simp done
 lemma a31_4_F: "[\<^bold>\<A>(\<phi>\<^sup>F) \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<A>(\<phi>\<^sup>F))] = \<top>" apply simp done

 subsection {* Axioms of Necessity *}

 lemma a32_1_P: "[(\<^bold>\<box>(\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>P)] = \<top>" apply simp done     (* K Schema *)
 lemma a32_1_F: "[(\<^bold>\<box>(\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<^sup>F)] = \<top>" apply simp done     (* K Schema *)
 lemma a32_2_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<rightarrow> \<phi>\<^sup>P] = \<top>" apply simp done                           (* T Schema *)
 lemma a32_2_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<rightarrow> \<phi>\<^sup>F] = \<top>" apply simp done                           (* T Schema *)

 lemma a32_3_P: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>P] = \<top>" apply simp done                       (* 5 Schema *)
 lemma a32_3_F: "[\<^bold>\<box>\<^bold>\<diamond>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<^sup>F] = \<top>" apply simp done                       (* 5 Schema *)
 lemma a32_4_P: "[(\<^bold>\<forall>x. \<^bold>\<box>\<phi>\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<forall>x. \<phi>\<^sup>P))] = \<top>" apply simp done         (* BF *)
 lemma a32_4_F: "[(\<^bold>\<forall>x. \<^bold>\<box>\<phi>\<^sup>F) \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<forall>x. \<phi>\<^sup>F))] = \<top>" apply simp done         (* BF *)

  text {* 
  The following needs to be an axiom; it does not follow for free: it is possible that there 
  are contingently concrete individuals and it is possible that there are not: 
  *}

 axiomatization where
   a32_5_P: "[\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)))] = \<top>"

   text {* 
   A brief check that this axiom is well-formed, i.e. does not return error 
   *}
 
 lemma "[\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)))] \<noteq> *" apply simp done
 lemma "\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>)) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E\<^sup>T,x\<^sup>T\<rparr>))) = X" apply simp oops -- {* X is @{text "(...)\<^sup>P"} *}

 subsection {* Axioms of Necessity and Actuality *}

 lemma a33_1_P: "[\<^bold>\<A>\<phi>\<^sup>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>\<^sup>P] = \<top>" apply simp done
 lemma a33_1_F: "[\<^bold>\<A>\<phi>\<^sup>F \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>\<^sup>F] = \<top>" apply simp done
 lemma a33_2_P: "[\<^bold>\<box>\<phi>\<^sup>P \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>\<^sup>P)] = \<top>" apply simp done
 lemma a33_2_F: "[\<^bold>\<box>\<phi>\<^sup>F \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>\<^sup>F)] = \<top>" apply simp done


 subsection {* Axioms for Descriptions *}

 lemma "(x\<^sup>T \<^bold>= (\<^bold>\<iota>x.\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)) = X" apply simp oops    -- {* X is @{text "(...)\<^sup>F"} *}
 lemma "(\<^bold>\<forall>z. (\<^bold>\<A>(\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) \<^bold>\<equiv> (z\<^sup>T \<^bold>= x\<^sup>T))) = X" apply simp oops    -- {* X is @{text "(...)\<^sup>F"} *} 

  text {* 
  For the following lemma cannot yet be automatically proved, since proof automation for definite
  descriptions is still not well enough developed in ATPs. 
  *}
 
  lemma a34_Inst_1: "[(x\<^sup>T \<^bold>= (\<^bold>\<iota>x.\<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)) \<^bold>\<equiv> (\<^bold>\<forall>z. (\<^bold>\<A>(\<lbrace>z\<^sup>T,R\<^sup>T\<rbrace>) \<^bold>\<equiv> (z\<^sup>T \<^bold>= x\<^sup>T)))] = \<top>" apply simp oops


(*<*)
section {* Various Further Test Examples *}

  text {* Todo: ... select, adapt, and explain some of examples below ... *}

 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>,a\<^sup>T\<rparr> = X" apply simp oops     -- {* X is @{text "(...)\<^sup>E"} *}

 lemma "[\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>,a\<^sup>T\<rparr>] = \<top>" apply simp oops

 lemma "\<lparr>\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>,a\<^sup>T\<rparr> = X\<^sup>P" apply simp oops
 lemma "(\<^bold>\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops

 lemma "[(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>)] = \<top>" apply simp done
 lemma "[(\<^bold>\<forall>R. \<^bold>\<forall>(\<lambda>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>))] = \<top>" apply simp done
 lemma "(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>) = X" apply simp oops

 lemma "[(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp done
 lemma "(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops

 lemma "[(\<^bold>\<exists>x y. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>y\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp done

 lemma "(\<^bold>\<forall>x. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops
 lemma "(\<^bold>\<forall>x. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lparr>R\<^sup>T,x\<^sup>T\<rparr>) = X" apply simp oops
 lemma "[(\<^bold>\<forall>R. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>)] = \<top>" apply simp oops
 lemma "(\<^bold>\<forall>R. \<lparr>R\<^sup>T,x\<^sup>T\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>) = X" apply simp oops

 lemma "[(\<^bold>\<forall>x. \<^bold>\<exists>(\<lambda>R. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>))] = \<top>" apply simp done
 lemma "[(\<^bold>\<exists>x. \<^bold>\<forall>(\<lambda>R. \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace> \<^bold>\<rightarrow> \<lbrace>x\<^sup>T,R\<^sup>T\<rbrace>))] = \<top>" apply simp done
(*>*)


(*<*)
end
(*>*)

