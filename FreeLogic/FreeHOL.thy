(*<*)
theory FreeHOL 
imports Main 

begin
(*>*)

text \<open>
\begin{abstract}
An embedding of free logic in classical higher-order logic is presented 
which has been formalized in Isabelle/HOL. Subsequently this 
work has been utilized as a foundation for the formalization of Peter Freyd's 
axiomatic category theory in Isabelle/HOL. Experiments with automated theorem provers integrated 
with Isabelle/HOL have been carried out, which revealed a previously unknown redundancy in 
Freyd's axiom system.
\end{abstract}
\<close>

section \<open>Free Logic\<close>

text \<open>
Motivated by problems and shortcomings in the handling of improper descriptions in the works of 
Russel, Frege and Hilbert-Bernays, the second author has proposed an alternative solution 
in his 1967 paper \emph{Existence and Description in Formal Logic} @{cite "scott67:_exist"}.

\begin{figure}
\newcommand\firstellipse{(2,-5) ellipse (6cm and 4cm)}
\newcommand\secondellipse{(0,-5) ellipse (4cm and 3cm)}
\begin{tikzpicture}
  \begin{scope}[fill opacity=0.4]
    \fill[red] \firstellipse;
    \fill[green] \secondellipse;
  \end{scope}
  \begin{scope}[very thick,font=\large]
    \draw \firstellipse node[font=\normalsize\bfseries] at (-1,-5) {\underline{Domain $\mathfrak{A}$ of defined objects}};
    \draw \firstellipse node[font=\small] at (-1,-5.5) {values of bound variables};
    \draw \secondellipse node[font=\normalsize\bfseries] at (4,-2) {\underline{All objects}};
    \draw \secondellipse node[font=\small] at (4.3,-2.5) {values of free variables};
  \end{scope}
  \node[font=\normalsize\bfseries] at (6,-5) {$\star$};
  \node[font=\normalsize\bfseries] at (6,-5.3) {undefined};
\end{tikzpicture}
\caption{Scott's Free Logic}
\end{figure}
\<close>

section \<open>Free Logic in HOL\<close>

text \<open>
In this section We present an embedding of the second authors \emph{Free Logic} in Isabelle/HOL. 
\<close>

type_synonym \<sigma> = "bool"   -- "the type for Booleans"   

consts f_A :: "'a\<Rightarrow>\<sigma>" ("\<A>")   (* Existence *)
consts f_star :: "'a" ("\<^bold>\<star>")   (* Undefinedness *)

axiomatization where f_star_axiom: "\<not>\<A>(\<^bold>\<star>)"

axiomatization where non_empty: "\<exists>x. \<A>(x) "

text \<open>Negation and implication in free logic are mapped to negation in HOl.\<close>
abbreviation f_not :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_" [58] 59)          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation f_implies :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<rightarrow>" 49)   
 where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<phi>\<longrightarrow>\<psi>" 

text \<open>Universal quantification in free logic is restricted to the domain of existing objects\<close>
abbreviation f_all :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")                 
 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. \<A>(x)\<longrightarrow>\<Phi>(x)"   
abbreviation f_all_bind :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<^bold>\<forall>" [8] 9) 
 where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"
abbreviation f_that :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>'a" ("\<^bold>I") 
 where "\<^bold>I \<Phi> \<equiv> if \<exists>x. \<A>(x) \<and> \<Phi>(x) \<and> (\<forall>y. (\<A>(y) \<and> \<Phi>(y)) \<longrightarrow> (y = x)) 
               then THE x. \<A>(x) \<and> \<Phi>(x) 
               else \<^bold>\<star>"
abbreviation f_that_b :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>'a"  (binder "\<^bold>I" [8] 9) 
 where "\<^bold>Ix. \<phi>(x) \<equiv> \<^bold>I(\<phi>)"



abbreviation f_or :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<or>" 51)         
 where "\<phi>\<^bold>\<or>\<psi> \<equiv> (\<^bold>\<not>\<phi>)\<^bold>\<rightarrow>\<psi>" 
abbreviation f_and :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<and>" 52)        
 where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi>\<^bold>\<or>\<^bold>\<not>\<psi>)"    
abbreviation f_equiv :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<leftrightarrow>" 50)     
 where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> (\<phi>\<^bold>\<rightarrow>\<psi>)\<^bold>\<and>(\<psi>\<^bold>\<rightarrow>\<phi>)"  
abbreviation f_equals :: "'a\<Rightarrow>'a\<Rightarrow>\<sigma>" (infixr "\<^bold>="56)       
 where "x\<^bold>=y \<equiv> x=y"
abbreviation f_exi :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>")                 
 where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>\<^bold>\<forall>(\<lambda>y.\<^bold>\<not>(\<Phi> y))"
abbreviation f_exi_b :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"  (binder "\<^bold>\<exists>" [8]9)  
 where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"


section \<open>Some Introductory Tests\<close> 
-- "See Scott, Existence and Description in Formal Logic, 1967, pages 183-184"

typedecl \<iota>                -- "the type for indiviuals"  
consts f_r  :: "\<iota>\<Rightarrow>\<iota>\<Rightarrow>\<sigma>" (infixr "\<^bold>r" 70)    (* Scott considers just one binary relation r *) 

lemma "x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x" by simp  
 (* ... valid in all domains including the empty one *)
lemma "\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y" nitpick oops    
 (* ... not valid in the empty domain; hence, the valid formulas formulas are not closed 
    under the rule of modus ponens when the empty domain is included *)
lemma "(x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" nitpick oops
 (* not valid *)
lemma "((x \<^bold>r x \<^bold>\<rightarrow> x \<^bold>r x) \<^bold>\<and> (\<^bold>\<exists>y::\<iota>. y \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>y. y \<^bold>r y \<^bold>\<rightarrow> y \<^bold>r y)" by simp
 (* ... now the empty domain is excluded and the statement is valid *)


-- "See Scott 1967, page 185"
lemma S1_inst : "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<Psi>(x)))" by auto
lemma S2 :      "\<^bold>\<forall>y. \<^bold>\<exists>x. x \<^bold>= y" by auto
lemma S3 :      "\<alpha> \<^bold>= \<alpha>" by auto
lemma S4_inst : "(\<Phi>(\<alpha>) \<^bold>\<and> (\<alpha> \<^bold>= \<beta>)) \<^bold>\<rightarrow> \<Phi>(\<beta>)" by auto
lemma UI_inst : "((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<and> (\<^bold>\<exists>x. x \<^bold>= \<alpha>)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" by auto
lemma UI_test : "(\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(\<alpha>)" nitpick [user_axioms] oops -- "Countermodel"
lemma UI_cor1 : "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<Phi>(x)) \<^bold>\<rightarrow> \<Phi>(y))" by auto
lemma UI_cor2 : "\<^bold>\<forall>y.((\<^bold>\<forall>x. \<^bold>\<not>(x \<^bold>= y)) \<^bold>\<rightarrow> \<^bold>\<not>(y \<^bold>= y))" by auto
lemma UI_cor3 : "\<^bold>\<forall>y.((y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<exists>x. x \<^bold>= y))" by auto
lemma UI_cor4 : "(\<^bold>\<forall>y. y \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<forall>y.\<^bold>\<exists>x. x \<^bold>= y)" by simp

lemma "(\<^bold>\<exists>x. x \<^bold>= \<alpha>) \<longrightarrow> \<A>(\<alpha>)" by simp
 (* ... to say that (\<^bold>\<exists>x. x = \<alpha>) is true means that the value of \<alpha> exists (properly) *)


lemma I1_inst : "\<^bold>\<forall>y. ((y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))))" by (smt f_star_axiom the_equality)


abbreviation star ("\<Otimes>") where "\<Otimes> \<equiv> \<^bold>Iy. \<^bold>\<not> (y \<^bold>= y)"

lemma test : "\<Otimes> = \<^bold>\<star>" by simp


lemma I2_inst : "\<^bold>\<not>(\<^bold>\<exists>y. y \<^bold>= (\<^bold>Ix. \<Phi>(x))) \<^bold>\<rightarrow>  (\<Otimes> \<^bold>= (\<^bold>Ix. \<Phi>(x)))" by (metis (no_types, lifting) the_equality)

 (* Extensionality *)
lemma Ext_inst : "(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<leftrightarrow> \<Psi>(x)) \<^bold>\<rightarrow> ((\<^bold>Ix. \<Phi>(x)) \<^bold>= (\<^bold>Ix. \<Psi>(x)))" by (smt the1_equality)


 (* the following schema is not valid as intended *)
lemma I3 : "(\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)" nitpick [user_axioms] oops


 (* The following is not valid, Problem? *)
lemma Russel_inst : 
 "((\<Otimes> \<^bold>= \<alpha> \<^bold>\<or> \<Otimes> \<^bold>= \<beta>) \<^bold>\<rightarrow> \<^bold>\<not>(\<alpha> \<^bold>r \<beta>)) 
  \<^bold>\<rightarrow> 
  ((\<alpha> \<^bold>r (\<^bold>Ix. \<Phi>(x))) \<^bold>\<leftrightarrow> (\<^bold>\<exists>y.((\<^bold>\<forall>x. ((x \<^bold>= y) \<^bold>\<leftrightarrow> \<Phi>(x))) \<^bold>\<and> (\<alpha> \<^bold>r y))))"
nitpick [user_axioms] oops




lemma "\<^bold>\<not>(\<^bold>\<exists>x. (x \<^bold>= (\<^bold>Iy. \<^bold>\<not> (y \<^bold>= y))))" using f_star_axiom by auto
lemma "(\<^bold>\<exists>x. x \<^bold>= a) \<^bold>\<rightarrow>  \<A>(a)" by simp


  (* Some further test *)
consts ca::'a cb::'a 
axiomatization where ax1: "\<A>(ca) \<^bold>\<and> \<A>(cb) \<^bold>\<and> \<^bold>\<not> (ca \<^bold>= cb) \<^bold>\<and> \<^bold>\<not> (ca \<^bold>= \<Otimes>) \<^bold>\<and> \<^bold>\<not> (cb \<^bold>= \<Otimes>)"
lemma test2: "\<Otimes> \<^bold>= (\<^bold>I (\<lambda>x. x  \<^bold>= ca \<^bold>\<or> x \<^bold>= cb))" by (metis ax1)

end
