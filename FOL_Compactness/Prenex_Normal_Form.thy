(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory Prenex_Normal_Form  
imports
    Ground_FOL_Compactness
begin


inductive is_prenex :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> is_prenex \<phi>\<close> 
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>

inductive_simps is_prenex_simps [simp]:
  "is_prenex Bot"
  "is_prenex (Atom p ts)"
  "is_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>)"
  "is_prenex (\<^bold>\<forall> x\<^bold>. \<phi>)" 

lemma prenex_formsubst1: \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
proof (induction \<phi> arbitrary: \<sigma> rule: is_prenex.induct)
  case 1
  then show ?case using is_prenex.intros(1) qfree_formsubst
    by blast
next
  case (2 \<phi> x)
  then show ?case
    using formsubst_def_switch by (metis (no_types, lifting) formsubst.simps(4) is_prenex.intros(2))
next
  case (3 \<phi> x)
  then show ?case
    using formsubst_def_switch is_prenex.intros(3)
    by (smt (verit, del_insts) formsubst.simps(1) formsubst.simps(3) formsubst.simps(4))
qed


thm is_prenex.induct
find_theorems is_prenex name: induct
thm is_prenex.cases

lemma prenex_formsubst2: \<open>is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<Longrightarrow> is_prenex \<phi>\<close>
proof (induction \<open>\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>\<close> arbitrary: \<phi> \<sigma> rule: is_prenex.induct)
  case 1
  then show ?case
    using is_prenex.intros(1) qfree_formsubst by auto
next
  case (2 \<psi> x \<phi>)
  then obtain y \<phi>' where phi_is: \<open>\<phi> = \<^bold>\<forall>y\<^bold>. \<phi>'\<close>
    using formsubst_structure_all by metis
  then have \<open>\<exists>\<sigma>'. \<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    using 2(3) by (metis (no_types, lifting) form.sel(6) formsubst.simps(4))
  then obtain \<sigma>' where \<open>\<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    by blast
  then have \<open>is_prenex \<phi>'\<close>
    using 2(2) by blast
  then show ?case
    using phi_is by (simp add: is_prenex.intros(2))
next
  case (3 \<psi> x \<phi>)
  then obtain y \<phi>' where phi_is: \<open>\<phi> = \<^bold>\<exists>y\<^bold>. \<phi>'\<close>
    using formsubst_structure_ex by metis
  then have \<open>\<exists>\<sigma>'. \<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    using 3(3) by (smt (verit, ccfv_threshold) form.inject(2) form.inject(3) formsubst.simps(3)
        formsubst.simps(4))
  then obtain \<sigma>' where \<open>\<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    by blast
  then have \<open>is_prenex \<phi>'\<close>
    using 3(2) by blast
  then show ?case
    using phi_is by (simp add: is_prenex.intros(3))
qed

lemma prenex_formsubst: \<open>is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<equiv> is_prenex \<phi>\<close>
  using prenex_formsubst1 prenex_formsubst2 by (smt (verit, ccfv_threshold))

lemma prenex_imp: \<open>is_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) \<Longrightarrow> 
  qfree (\<phi> \<^bold>\<longrightarrow> \<psi>) \<or> (\<psi> = \<^bold>\<bottom> \<and> (\<exists>x \<phi>'. is_prenex \<phi>' \<and> \<phi> = (\<^bold>\<forall>x\<^bold>. \<phi>' \<^bold>\<longrightarrow> \<^bold>\<bottom>)))\<close>
  by (metis form.distinct(11) form.inject(2) is_prenex.cases)

inductive universal :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> universal \<phi>\<close>
| \<open>universal \<phi> \<Longrightarrow> universal (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>

inductive_simps universal_simps [simp]:
  "universal Bot"
  "universal (Atom p ts)"
  "universal (\<phi> \<^bold>\<longrightarrow> \<psi>)"
  "universal (\<^bold>\<forall> x\<^bold>. \<phi>)" 

fun size :: "form \<Rightarrow> nat" where
  \<open>size \<^bold>\<bottom> = 1\<close>
| \<open>size (Atom p ts) = 1\<close>
| \<open>size (\<phi> \<^bold>\<longrightarrow> \<psi>) = size \<phi> + size \<psi>\<close>
| \<open>size (\<^bold>\<forall> x\<^bold>. \<phi>) = 1 + size \<phi>\<close>

lemma wf_size: \<open>wfP (\<lambda>\<phi> \<psi>. size \<phi> < size \<psi>)\<close>
  by (simp add: wfP_if_convertible_to_nat)

(*
instantiation form :: wellorder
begin

definition less_eq_form where less_eq_size: \<open>\<phi> \<le> \<psi> \<longleftrightarrow> (size \<phi> = size \<psi>) \<or> (size \<phi> < size \<psi>)\<close>

definition less_form where less_size: \<open>\<phi> < \<psi> \<longleftrightarrow> size \<phi> < size \<psi>\<close>

instance
proof
  fix \<phi> \<psi>::form
  show \<open>(\<phi> < \<psi>) = (\<phi> \<le> \<psi> \<and> \<not> \<psi> \<le> \<phi>)\<close>
    using less_eq_size less_size by presburger
next
  fix \<phi>::form
  show \<open>\<phi> \<le> \<phi>\<close> 
    using less_eq_size by simp
next
  fix \<phi> \<psi> \<xi>::form
  show \<open>\<phi> \<le> \<psi> \<Longrightarrow> \<psi> \<le> \<xi> \<Longrightarrow> \<phi> \<le> \<xi>\<close>
    using less_eq_size by auto
next
  fix \<phi> \<psi>::form
  show \<open>\<phi> \<le> \<psi> \<Longrightarrow> \<psi> \<le> \<phi> \<Longrightarrow> \<phi> = \<psi>\<close>
(* not true! ! ! *)
    oops
end
*)

lemma size_indep_subst: \<open>size (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = size \<phi>\<close>
proof (induction \<phi> arbitrary: \<sigma>)
  case (Forall x \<phi>)
  have \<open>\<exists>z \<sigma>'.(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
    by (meson formsubst.simps(4))
  then obtain z \<sigma>' where \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
    by blast
  then have \<open>size ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = size (\<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
    by argo
  also have \<open>... = size (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
    using Forall by auto
  finally show ?case .
qed auto


lemma prenex_distinct: \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<noteq> (\<^bold>\<exists>y\<^bold>. \<psi>)\<close>
  by auto

(*
inductive to_prenex to_prenex_left to_prenex_right where
  \<open>to_prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>to_prenex (Atom p ts) = Atom p ts\<close>
| \<open>to_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = to_prenex_left (to_prenex \<phi>) (to_prenex \<psi>)\<close>
| \<open>to_prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (to_prenex \<phi>)\<close>
| \<open>to_prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = \<^bold>\<forall>x\<^bold>. (to_prenex_left \<phi> \<psi>)\<close> (*TODO: just a test, to correct *)
| \<open>to_prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = \<^bold>\<exists>x\<^bold>. (to_prenex_right \<phi> \<psi>)\<close>
| \<open>qfree \<phi> \<Longrightarrow> to_prenex_left \<phi> \<psi> = \<phi> \<^bold>\<longrightarrow> \<psi>\<close>
| \<open>to_prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = \<^bold>\<forall>x\<^bold>. (to_prenex_right \<phi> \<psi>)\<close>
*)
(*   let y = VARIANT(FV(p) UNION FV(!!x q)) in
                   !!y (Prenex_right p (formsubst (valmod (x,V y) V) q)))  *)

lemma uniq_all_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)" (* necessaire pour décharger le "THE" *)
  using Uniq_def by blast

lemma uniq_all_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p))\<close>
  using uniq_all_x Uniq_def
  by (smt (verit, ccfv_threshold) form.inject(3))

lemma uniq_ex_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)"
  using Uniq_def by blast

lemma uniq_ex_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p))\<close>
  using uniq_ex_x Uniq_def
  by (smt (verit, best) form.inject(2) form.inject(3))

definition ppat :: "(nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> form" where
  \<open>ppat A B C r = (if (\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) then
    A (THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p) (THE p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p)
  else (if \<exists>x p. r = \<^bold>\<exists>x\<^bold>. p then
    B (THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p) (THE p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p) 
   else C r))\<close>

lemma ppat_simpA: \<open>\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p\<close>
  unfolding ppat_def by simp

lemma ppat_simpB: \<open>\<forall>x p. ppat A B C (\<^bold>\<exists>x\<^bold>. p) = B x p\<close>
  unfolding ppat_def by simp

(* simplified unneeded hypotheses: (\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p) \<Longrightarrow> (\<forall>x p. ppat A B C (\<^bold>\<exists>x\<^bold>. p) = B x p) *)
lemma ppat_last: \<open>(\<forall>r. \<not>(\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) \<and> \<not>(\<exists>x p. r = \<^bold>\<exists>x\<^bold>. p)) \<Longrightarrow> ppat A B C r = C r\<close>
  by blast

(* idem here *)
lemma ppat_last_qfree: \<open>qfree r \<Longrightarrow> ppat A B C r = C r\<close>
  using qfree_no_quantif ppat_last by (simp add: ppat_def)

(* holds but useless because not recursive *)
lemma ppat_to_ex_qfree:
  \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = ((A :: form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form) p) x q) \<and>
  (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = (B p) x q) \<and> 
  (\<forall>p q. qfree q \<longrightarrow> f p q = (C p) q))\<close>
proof
  define f where \<open>f = (\<lambda>p q. ppat (A p) (B p) (C p) q)\<close>
  have A_eq: \<open>(\<forall>x p q. ppat (A p) (B p) (C p) (\<^bold>\<forall>x\<^bold>. q) = (A p) x q)\<close> and 
    B_eq: \<open>(\<forall>x p q. ppat (A p) (B p) (C p) (\<^bold>\<exists>x\<^bold>. q) = (B p) x q)\<close>
    unfolding ppat_def by simp+
  have  C_eq: \<open>(\<forall>p q. qfree q \<longrightarrow> ppat (A p) (B p) (C p) q = (C p) q)\<close>
    using ppat_last_qfree by blast
  show \<open>(\<forall>x p q. f p (\<^bold>\<forall> x\<^bold>. q) = A p x q) \<and> (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B p x q) \<and> (\<forall>p q. qfree q \<longrightarrow> f p q = (C p) q)\<close>
    using A_eq B_eq C_eq unfolding f_def by blast
qed

term \<open>\<forall>\<phi>. \<exists>g. \<forall>\<psi>. g \<psi> = ppat (A g \<phi>) (B g \<phi>) (C \<phi>) \<psi>\<close> (* proven subgoal abstraction *)
term \<open>\<exists>f. \<forall>\<phi> \<psi>. f \<phi> \<psi> = ppat (prenex_right_forall f \<phi>) (prenex_right_exists f \<phi>) ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close> (* same after choice *)
term \<open>A g \<phi> = (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
term \<open>A = (\<lambda>g \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

(*
lemma ppat_to_ex_qfree_rec:
  assumes
    \<open>\<exists>(g :: form \<Rightarrow> form). \<forall>p q. g q = ppat (A g p) (B g p) (C p) q\<close>
  shows
    \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = A (f p) p x q) \<and>
      (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B (f p) p x q) \<and> 
      (\<forall>p q. qfree q \<longrightarrow> f p q = C p q))\<close>
  using assms ppat_last_qfree
sorry


lemma ppat_to_ex_qfree_rec2:
  assumes
    \<open>\<forall>(p :: form). \<exists>g. \<forall>q. g q = ppat (A p g) (B p g) (C p) q\<close>
  shows
    \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = (A p (f p) x q)) \<and>
      (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B p (f p) x q) \<and> 
      (\<forall>p q. qfree q \<longrightarrow> f p q = C p q))\<close>
sorry
*)

thm wf_induct

lemma "wfP ((<) :: (nat \<Rightarrow> nat \<Rightarrow> bool))"
  using wfP_less .

thm wfP_less

(*(!f g x. (!z. z << x ==> (f z = g z) /\ S z (f z))
                      ==> (H f x = H g x) /\ S x (H f x))
             ==> ?f:A->B. !x. (f x = H f x)`, *)

(*
WF_EQ = prove
 (`WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\ !y. y << x ==> ~P(y))`
*)

lemma wfP_eq: \<open>wfP ((<) :: ('a::ord \<Rightarrow> 'a \<Rightarrow> bool)) \<Longrightarrow> ((\<exists>(x::'a). P x) \<equiv> (\<exists>x. P x \<and> (\<forall>y. y < x \<longrightarrow> \<not>P y)))\<close>
  by (smt (verit) mem_Collect_eq wfP_eq_minimal)

(*
WF_IND = prove
 (`WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)`,
*)
lemma wfP_ind: \<open>wfP ((<) :: ('a::ord \<Rightarrow> 'a \<Rightarrow> bool)) \<Longrightarrow>
  (\<forall>(x::'a). (\<forall>y. y <  x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x)\<close>
  by (metis wfP_induct)

lemma size_wf_ind: \<open>(\<forall>x. (\<forall>y. size y <  size x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x)\<close>
  using wf_size by (smt (verit, best) wfP_induct)

lemma size_wf_induct: \<open>(\<And>x. (\<And>y. size y <  size x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P x\<close>
  using wf_size size_wf_ind by metis

lemma dependent_wfP_choice:
  fixes P :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "wfP R"
    and adm: "\<And>f g x r. (\<And>z. R z x \<Longrightarrow> f z = g z) \<Longrightarrow> P f x r = P g x r"
    and P: "\<And>x f. (\<And>y. R y x \<Longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r"
  shows "\<exists>f. \<forall>x. P f x (f x)"
proof -
  have wf_R: \<open>wf {(x,y). R x y}\<close> using assms(1) unfolding wfP_def .
  have eq_P: \<open>(\<forall>z. (z, x) \<in> {(x, y). R x y} \<longrightarrow> f z = g z) \<Longrightarrow> P f x r = P g x r\<close> for f g x r
    using assms(2) by blast
  have ex_P: \<open>(\<forall>y. (y, x) \<in> {(x, y). R x y} \<longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r\<close> for x f
    using assms(3) by blast
  show \<open>\<exists>f. \<forall>x. P f x (f x)\<close>
    using dependent_wf_choice[of "{(x,y). R x y}" P, OF wf_R] eq_P ex_P by blast
qed

lemma dependent_wfP_choice2:
  fixes P :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "wfP R"
    and adm: "\<And>f g x r. (\<And>z. R z x \<Longrightarrow> f z = g z) \<Longrightarrow> P f x = P g x"
  shows "\<exists>f. \<forall>x. P f x = (f x)"
proof -
  have adm_rel: \<open>(\<forall>z. R z x \<longrightarrow> f z = g z) \<Longrightarrow> (P f x = r) = (P g x = r)\<close> for f g x r
    using adm by fastforce
  have P_rel: \<open>(\<forall>y. R y x \<longrightarrow> P f y = (f y)) \<Longrightarrow> \<exists>r. P f x = r\<close> for x f
    by simp
  show "\<exists>f. \<forall>x. P f x = (f x)"
    using dependent_wfP_choice[of R \<open>\<lambda>f x r. P f x = r\<close>] assms(1) adm_rel P_rel by blast
qed

lemma size_rec: 
  \<open>\<forall>f g x. (\<forall>(z::form). size z < size x \<longrightarrow> (f z = g z)) \<longrightarrow> (H f x = H g x) \<Longrightarrow> (\<exists>f. \<forall>x. f x = H f x)\<close>
  using dependent_wfP_choice2[OF wf_size] by metis

abbreviation prenex_right_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_right_forall \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

abbreviation prenex_right_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_right_exists \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

lemma prenex_right_ex: 
  \<open>\<exists>prenex_right. (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  have \<open>\<forall>\<phi>. \<exists>prenex_right_only. \<forall>\<psi>. prenex_right_only \<psi> = ppat 
    (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. prenex_right_only (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. prenex_right_only (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
  proof
    fix \<phi>
    define A where \<open>A = (\<lambda>g x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    define B where \<open>B = (\<lambda>p x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    show \<open>\<exists>prenex_right_only. \<forall>\<psi>. prenex_right_only \<psi> = 
      ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
    proof (rule size_rec, (rule allI)+, (rule impI))
      fix prenex_right_only g:: "form \<Rightarrow> form" and \<psi>
      assume IH: \<open>\<forall>z. size z < size \<psi> \<longrightarrow> prenex_right_only z = g z\<close>
      show \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> =
        ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
      proof (cases "\<exists>x \<psi>'. \<psi> = \<^bold>\<forall>x\<^bold>. \<psi>'")
        case True
        then obtain x \<psi>' where psi_is: "\<psi> = \<^bold>\<forall>x\<^bold>. \<psi>'"
          by blast
        then have smaller: \<open>size (\<psi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<psi>\<close> for \<sigma>
          using size_indep_subst by simp
        have \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> = 
          A prenex_right_only x \<psi>'\<close>
          unfolding ppat_def by (simp add: psi_is)
        also have \<open>... = A g x \<psi>'\<close>
          unfolding A_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
          unfolding ppat_def by (simp add: psi_is)
        finally show ?thesis .
      next
        case False
        assume falseAll: \<open>\<not>(\<exists>x \<psi>'. \<psi> = \<^bold>\<forall> x\<^bold>. \<psi>')\<close>
        then show ?thesis
        proof (cases "\<exists>x \<psi>'. \<psi> = \<^bold>\<exists>x\<^bold>. \<psi>'")
          case True
          then obtain x \<psi>' where psi_is: "\<psi> = \<^bold>\<exists>x\<^bold>. \<psi>'"
            by blast
          then have smaller: \<open>size (\<psi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<psi>\<close> for \<sigma>
            using size_indep_subst by simp
        have \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> = 
          B prenex_right_only x \<psi>'\<close>
          unfolding ppat_def by (simp add: psi_is)
        also have \<open>... = B g x \<psi>'\<close>
          unfolding B_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
          unfolding ppat_def by (simp add: psi_is)
        finally show ?thesis .
        next
          case False
          then show ?thesis
            using falseAll ppat_last unfolding ppat_def by argo
        qed 
      qed
    qed
  qed
  then have \<open>\<exists>prenex_right. \<forall>\<phi> \<psi>. prenex_right \<phi> \<psi> = ppat
                (prenex_right_forall prenex_right \<phi>)
                (prenex_right_exists prenex_right \<phi>) 
                ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close>
    using choice[of "\<lambda>\<phi> p. \<forall>\<psi>. p \<psi> =
            ppat (\<lambda>x \<psi>. let y = variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in \<^bold>\<forall>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
              (\<lambda>x \<psi>. let y = variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
              ((\<^bold>\<longrightarrow>) \<phi>) \<psi>"] by blast
  then obtain prenex_right where prenex_right_is: \<open>\<forall>\<phi> \<psi>. prenex_right \<phi> \<psi> = 
    ppat (prenex_right_forall prenex_right \<phi>) (prenex_right_exists prenex_right \<phi>) ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close>
    by blast
(* then show each property separately *)
  have \<open>\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
    using prenex_right_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
    using prenex_right_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
    using prenex_right_is by (metis (no_types, lifting) ppat_last_qfree)
  ultimately show ?thesis
    by blast
qed

(* is it unique? \<rightarrow> No, it is undefined in the last case if \<not>qfree \<phi>. Use SOME, not THE  *)
consts prenex_right :: "form \<Rightarrow> form \<Rightarrow> form"
specification (prenex_right) \<open>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
  using prenex_right_ex by blast

find_theorems "SOME _. _ \<Longrightarrow> _"
thm some_eq_imp verit_sko_ex someI2_ex

thm someI2_ex
find_theorems is_prenex prenex_right

lemma prenex_right_qfree_case: \<open>qfree \<psi> \<Longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
  (* \<open>qfree \<phi> \<Longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close> *)
proof -
  assume qfree_psi: "qfree \<psi>"
  have \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow> (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close> (is "?P p \<Longrightarrow> ?Q p") for p 
    by argo
  then have \<open>(\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis
    using qfree_psi by blast
qed

lemma prenex_right_all_case: \<open>prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
proof -
  have all_cases_imp_all_case: \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow>
   (p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>)\<close> (is "?P p \<Longrightarrow> ?Q p") for p
    by meson
  then have \<open>prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis .
qed

lemma prenex_right_exist_case: \<open>prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
proof -
  have ex_cases_imp_ex_case: \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow>
   (p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>)\<close> (is "?P p \<Longrightarrow> ?Q p") for p
    by meson
  then have \<open>prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis .
qed

lemma prenex_right_exists_shape_case: 
  \<open>\<exists>x2 \<sigma>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = \<^bold>\<exists>x2\<^bold>. prenex_right \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
proof -
  have all_cases_imp_all_case: \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow>
   (\<exists>x2 \<sigma>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = \<^bold>\<exists>x2\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>))\<close> (is "?P p \<Longrightarrow> ?Q p") for p
    by meson
  then have \<open>\<exists>x2 \<sigma>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = \<^bold>\<exists>x2\<^bold>. prenex_right \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis .
qed


abbreviation prenex_left_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_left_forall \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

abbreviation prenex_left_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_left_exists \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

lemma prenex_left_ex:
  \<open>\<exists>prenex_left. (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>)\<close>
proof -
  have \<open>\<forall>\<psi>. \<exists>prenex_left_only. \<forall>\<phi>. prenex_left_only \<phi> = ppat
    (\<lambda>x \<phi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left_only (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>x \<phi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. prenex_left_only (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
  proof
    fix \<psi>
    define A where \<open>A = (\<lambda>g x \<phi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. g (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    define B where \<open>B = (\<lambda>p x \<phi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    show \<open>\<exists>prenex_left_only. \<forall>\<phi>. prenex_left_only \<phi> =
      ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    proof (rule size_rec, (rule allI)+, (rule impI))
      fix prenex_left_only g:: "form \<Rightarrow> form" and \<phi>
      assume IH: \<open>\<forall>z. size z < size \<phi> \<longrightarrow> prenex_left_only z = g z\<close>
      show \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> =
        ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
      proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'")
        case True
        then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'"
          by blast
        then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
          using size_indep_subst by simp
        have \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> = 
          A prenex_left_only x \<phi>'\<close>
          unfolding ppat_def by (simp add: phi_is)
        also have \<open>... = A g x \<phi>'\<close>
          unfolding A_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
          unfolding ppat_def by (simp add: phi_is)
        finally show ?thesis .
      next
        case False
        assume falseAll: \<open>\<not>(\<exists>x \<phi>'. \<phi> = \<^bold>\<forall> x\<^bold>. \<phi>')\<close>
        then show ?thesis
        proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'")
          case True
          then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'"
            by blast
          then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
            using size_indep_subst by simp
        have \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> = 
          B prenex_left_only x \<phi>'\<close>
          unfolding ppat_def by (simp add: phi_is)
        also have \<open>... = B g x \<phi>'\<close>
          unfolding B_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
          unfolding ppat_def by (simp add: phi_is)
        finally show ?thesis .
        next
          case False
          then show ?thesis
            using falseAll ppat_last unfolding ppat_def by argo
        qed 
      qed
    qed
  qed
  then have \<open>\<exists>prenex_left_argswap. \<forall>\<psi> \<phi>. prenex_left_argswap \<psi> \<phi> = ppat
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left_argswap \<psi> (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall> y\<^bold>. prenex_left_argswap \<psi> (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    using choice[of "\<lambda>\<psi> p. \<forall>\<phi>. p \<phi> =
            ppat (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
              (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
              (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>"] by blast
  then have \<open>\<exists>prenex_left. \<forall>\<phi> \<psi>. prenex_left \<phi> \<psi> = ppat
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>))
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall> y\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>)
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    by force
  then obtain prenex_left where prenex_left_is: \<open>\<forall>\<phi> \<psi>. prenex_left \<phi> \<psi> = ppat
    (\<lambda>x \<phi>. prenex_left_forall prenex_left \<phi> x \<psi>)
    (\<lambda>x \<phi>. prenex_left_exists prenex_left \<phi> x \<psi>)
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    by blast
  have \<open>\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> =  prenex_left_forall prenex_left \<phi> x \<psi>\<close>
    using prenex_left_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>\<close>
    using prenex_left_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>\<close>
    using prenex_left_is by (metis (no_types, lifting) ppat_last_qfree)
  ultimately show ?thesis
    by blast
qed

definition prenex_left where \<open>prenex_left = (SOME prenex_left.
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>))\<close>

lemma prenex_left_forall_case: \<open>prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>\<close>
  unfolding prenex_left_def by (smt (verit, del_insts) prenex_left_ex some_eq_ex)

lemma prenex_left_qfree_case: \<open>qfree \<phi> \<Longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>\<close>
  unfolding prenex_left_def by (smt (verit, del_insts) prenex_left_ex some_eq_ex)

lemma prenex_left_exists_case: \<open>prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>\<close>
  unfolding prenex_left_def by (smt (verit, del_insts) prenex_left_ex some_eq_ex)

lemma prenex_left_exists_shape_case: 
  \<open>\<exists>x2 \<sigma>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = \<^bold>\<forall>x2\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>\<close>
  using prenex_left_exists_case by metis


fun prenex where
  \<open>prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>prenex (Atom p ts) = Atom p ts\<close>
| \<open>prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = prenex_left (prenex \<phi>) (prenex \<psi>)\<close>
| \<open>prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (prenex \<phi>)\<close>

(*
let PRENEX_RIGHT_FORALL = prove
 (`~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> !!x q) <=>
        holds M v (!! (VARIANT (FV(p) UNION FV(!!x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q)))`
*)

lemma id_subst: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var x)) = \<phi>\<close>
  by (induction \<phi>) simp+

lemma holds_indep_forall: \<open>y \<notin> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<Longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<equiv> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
proof -
  assume y_notin: \<open>y \<notin> FV (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
  {
    assume \<open>y \<noteq> x\<close>
    then have y_notin_phi: \<open>y \<notin> FV \<phi>\<close> using y_notin by simp
    have beta_equiv: \<open>\<forall>w \<in> FV \<phi>. (\<lambda>v. eval_subst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close> for a
    proof
      fix w
      assume w_in: \<open>w \<in> FV \<phi>\<close>
      have \<open>w = x \<Longrightarrow> (\<lambda>v. eval_subst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close>
        by simp
      moreover have \<open>w \<noteq> x \<Longrightarrow> (\<lambda>v. eval_subst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close>
        using y_notin_phi by (metis w_in eval.simps(1) fun_upd_other subst_def)
      ultimately show \<open>(\<lambda>v. eval_subst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close>
        by argo
    qed
    have \<open>I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<equiv> (\<forall>a \<in> dom I. I\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
      by simp
    also have \<open>... \<equiv> (\<forall>a \<in> dom I. I\<^bold>,(\<lambda>v. eval_subst I (\<beta>(y := a)) (subst x (Var y)) v) \<Turnstile> \<phi>)\<close>
      using holds_indep_\<beta>_if[OF beta_equiv] by presburger
    also have \<open>... \<equiv> (\<forall>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
      using swap_subst_eval[of I _ \<phi> "subst x (Var y)"] by presburger
    also have \<open>... \<equiv> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
      by simp
    finally have \<open>(I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<equiv> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
      by argo
  }
  moreover {
    assume y_is_x: \<open>y = x\<close>
    then have \<open>(I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<equiv> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
      using id_subst by presburger
  }
 ultimately show \<open>(I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<equiv> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    by argo
qed

lemma forall_imp_commute: \<open>y \<notin> FV \<phi> \<Longrightarrow>
  ((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>y\<^bold>. \<psi>)) \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  assume y_notin: \<open>y \<notin> FV \<phi>\<close>
  then have \<open>(I\<^bold>, \<beta> \<Turnstile> \<phi>) \<longrightarrow> (\<forall>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>) \<equiv>
    (\<forall>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    by (smt (verit, del_insts) fun_upd_other holds_indep_\<beta>_if)
  then show \<open>(I\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>y\<^bold>. \<psi>)) \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close> by simp
qed

lemma forall_imp_exists: \<open>y \<notin> FV \<psi> \<Longrightarrow>
  ((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<forall>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>) \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
proof -
  assume y_notin: \<open>y \<notin> FV \<psi>\<close>
  have \<open>(\<forall>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi>) \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> \<psi>) \<equiv>
    (\<exists>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>))\<close>
    using empty_iff list.set(1)
    by (smt (verit, best) equals0I intrp_is_struct struct_def)
  also have \<open>... \<equiv> (\<exists>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    using holds_indep_\<beta>_if by (smt (verit, del_insts) fun_upd_other y_notin)
  finally show \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<forall>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>) \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
    by simp
qed

lemma exists_imp_forall: \<open>y \<notin> FV \<psi> \<Longrightarrow>
  ((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<exists>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>) \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
proof -
  assume y_notin: \<open>y \<notin> FV \<psi>\<close>
  have \<open>(\<exists>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi>) \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> \<psi>) \<equiv>
    (\<forall>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>))\<close>
    using empty_iff list.set(1) by (smt (verit, ccfv_threshold))
  also have \<open>... \<equiv> (\<forall>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    using holds_indep_\<beta>_if by (smt (verit, del_insts) fun_upd_other y_notin)
  finally show \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<exists>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>) \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
    by simp
qed

lemma exists_imp_commute: \<open>y \<notin> FV \<phi> \<Longrightarrow> ((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>y\<^bold>. \<psi>)) \<equiv>
   I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  assume y_notin: \<open>y \<notin> FV \<phi>\<close>
  have \<open>(I\<^bold>, \<beta> \<Turnstile> \<phi>) \<longrightarrow> (\<exists>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>) \<equiv>
   (\<exists>a \<in> dom I. (I\<^bold>, \<beta> \<Turnstile> \<phi>) \<longrightarrow> (I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    by (smt (verit) equals0I intrp_is_struct struct_def)
  also have \<open>... \<equiv> (\<exists>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    using y_notin by (smt (verit, ccfv_threshold) fun_upd_other holds_indep_\<beta>_if)
  finally show \<open>(I\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>y\<^bold>. \<psi>)) \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
    using holds_exists by simp
qed

lemma holds_indep_exists: \<open>y \<notin> FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<Longrightarrow> 
  (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>) \<equiv> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
  using holds_indep_forall by (smt (verit, ccfv_threshold) FV.simps(1) FV.simps(3)
    formsubst.simps(1) formsubst.simps(3) holds.simps(3) sup_bot.right_neutral) 

(* sublemmas for is_prenex(prenex _)*)

(* holds M (v:num->A) (p --> !!y (formsubst (valmod (x,V y) V) q)) *)
lemma prenex_right_forall_is:
  assumes \<open>\<not>(dom (I :: 'a intrp) = {})\<close> 
  shows \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>)) \<equiv>
  (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. 
             (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))))))))))\<close> (is "?lhs \<equiv> ?rhs")
proof -
  define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))\<close>
  then have y_notin1: \<open>y \<notin> FV \<phi>\<close> and y_notin2: \<open>y \<notin> FV (\<^bold>\<forall>x\<^bold>. \<psi>)\<close>
  using variant_finite finite_FV by (meson UnCI finite_UnI)+
  have \<open>?lhs \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>y\<^bold>. \<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using holds_indep_forall y_notin2
    by (smt (verit, ccfv_SIG) holds.simps(3))
  also have \<open>... \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using forall_imp_commute[OF y_notin1, of I \<beta> "\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))"] .
  finally show \<open>?lhs \<equiv> ?rhs\<close>
    unfolding y_def .
qed

(*`~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> ??x q) <=>
        holds M v (?? (VARIANT (FV(p) UNION FV(??x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q)))`,*)
lemma prenex_right_exists_is:
  assumes \<open>\<not>(dom (I :: 'a intrp) = {})\<close> 
  shows \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>)) \<equiv>
  (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. 
             (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))))))))))\<close> (is "?lhs \<equiv> ?rhs")
proof -
  define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))\<close>
  then have y_notin1: \<open>y \<notin> FV \<phi>\<close> and y_notin2: \<open>y \<notin> FV (\<^bold>\<exists>x\<^bold>. \<psi>)\<close>
  using variant_finite finite_FV by (meson UnCI finite_UnI)+
  have \<open>?lhs \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>y\<^bold>. \<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using holds_indep_exists y_notin2 holds_exists by (smt (verit) holds.simps(3))
  also have \<open>... \<equiv> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using exists_imp_commute[OF y_notin1, of I \<beta> "\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))"] .
  finally show \<open>?lhs \<equiv> ?rhs\<close>
    unfolding y_def .
qed

lemma prenex_left_forall_is:
  assumes \<open>\<not>(dom (I :: 'a intrp) = {})\<close> 
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>)) \<equiv> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>.
               ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)))\<close>
  using forall_imp_exists holds_indep_forall holds.simps(3)
  by (smt (verit, del_insts) FV.simps(3) UnI2 sup.commute variant_form)

lemma prenex_left_exists_is:
  assumes \<open>\<not>(dom (I :: 'a intrp) = {})\<close> 
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>)) \<equiv> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>.
               ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)))\<close>
  using exists_imp_forall holds_indep_exists holds.simps(3)
  by (smt (verit, ccfv_SIG) FV.simps(3) UnCI finite_FV variant_finite)

(* sublemmas for prenex prop on FV *)
lemma prenex_right_forall_FV: \<open>FV (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>)) =
  FV (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))))))))\<close>
  using formsubst_rename
  by (metis Diff_empty Diff_insert0 FV.simps(3) FV.simps(4) Un_Diff finite_FV variant_finite)

lemma prenex_right_exists_FV: \<open>FV (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>)) =
  FV (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))))))))\<close>
  using formsubst_rename prenex_right_forall_FV by force

lemma prenex_left_forall_FV: \<open>FV ((\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>) =
  FV (\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>))\<close>
  using formsubst_rename
  by (metis Diff_idemp Diff_insert_absorb FV.simps(3) FV.simps(4) Un_Diff finite_FV variant_finite FV_exists)

lemma prenex_left_exists_FV: \<open>FV ((\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>) =
  FV (\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>))\<close>
  using formsubst_rename FV_exists prenex_left_forall_FV by auto

(* sublemmas for prenex prop on language *)
lemma prenex_right_forall_language: \<open>language {\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>)} =
  language {\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))))))}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

lemma prenex_right_exists_language: \<open>language {\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>)} =
  language {\<^bold>\<exists>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))))))}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

lemma prenex_left_forall_language: \<open>language {(\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>} =
  language {\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

lemma prenex_left_exists_language: \<open>language {(\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>} =
  language {\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

(* prenex properties lemmas *)
lemma prenex_props_forall: \<open>P \<and> FV \<phi> = FV \<psi> \<and> language {\<phi>} = language {\<psi>} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)) \<Longrightarrow>
  P \<and> FV (\<^bold>\<forall>x\<^bold>. \<phi>) = FV (\<^bold>\<forall>x\<^bold>. \<psi>) \<and> language {(\<^bold>\<forall>x\<^bold>. \<phi>)} = language {(\<^bold>\<forall>x\<^bold>. \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<psi>)))
\<close>
  using lang_singleton by simp

lemma prenex_props_exists: \<open>P \<and> FV \<phi> = FV \<psi> \<and> language {\<phi>} = language {\<psi>} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)) \<Longrightarrow>
  P \<and> FV (\<^bold>\<exists>x\<^bold>. \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<psi>) \<and> language {(\<^bold>\<exists>x\<^bold>. \<phi>)} = language {(\<^bold>\<exists>x\<^bold>. \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<psi>)))
\<close>
  using lang_singleton by simp

thm is_prenex.induct

(* val num_WF : thm = |- !P. (!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n) *)
find_theorems " _ < _ " "_::nat" name: ind

thm prenex_right_forall_is 
prenex_right_forall_FV
prenex_right_forall_language
prenex_props_forall

find_theorems wfP name: induct 
find_theorems wfP "(<)"
thm wfP_ind
find_theorems prenex_right name: "case"

lemma prenex_right_props_imp0:
  \<open>qfree \<phi> \<Longrightarrow> is_prenex \<psi> \<longrightarrow> is_prenex (prenex_right \<phi> \<psi>)\<close>
proof -
  (* Is it possible to use the induction tactic here instead? *)
  assume qfree_phi: \<open>qfree \<phi>\<close>
  have \<open>(\<forall>\<psi>. (\<forall>\<psi>'. size \<psi>' < size \<psi> \<longrightarrow> 
    (is_prenex \<psi>'  \<longrightarrow> is_prenex (prenex_right \<phi> \<psi>'))) \<longrightarrow> 
    (is_prenex \<psi> \<longrightarrow> is_prenex (prenex_right \<phi> \<psi>)))\<close>
  proof clarsimp
    fix \<xi>
    assume IH: \<open>\<forall>\<psi>'. size \<psi>' < size \<xi> \<longrightarrow> is_prenex \<psi>' \<longrightarrow> is_prenex (prenex_right \<phi> \<psi>')\<close> and
      prenex_xi: \<open>is_prenex \<xi>\<close>
    show \<open>is_prenex (prenex_right \<phi> \<xi>)\<close>
    proof (cases rule: is_prenex.cases[OF prenex_xi])
      case (1 \<xi>')
      then show ?thesis
        using prenex_right_qfree_case qfree_phi is_prenex.intros(1) qfree.simps(3) by presburger
    next
      case (2 \<xi>' x)
      then have \<open>prenex_right \<phi> \<xi> = prenex_right_forall prenex_right \<phi> x \<xi>'\<close>
        using prenex_right_all_case by blast
      then show \<open>is_prenex (prenex_right \<phi> \<xi>)\<close>
        using IH 2 by (metis One_nat_def bot_nat_0.extremum is_prenex.intros(2) le_add_same_cancel2
            le_imp_less_Suc plus_nat.simps(2) prenex_formsubst1 size.simps(4) size_indep_subst)
    next
      case (3 \<xi>' x)
      then have \<open>\<exists>y \<sigma>. prenex_right \<phi> \<xi> = \<^bold>\<exists>y\<^bold>. prenex_right \<phi> (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
        using prenex_right_exists_shape_case by presburger
      then obtain y \<sigma> where pr_is: \<open>prenex_right \<phi> \<xi> = \<^bold>\<exists>y\<^bold>. prenex_right \<phi> (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
        by blast
      have size_xp: \<open>size (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<xi>\<close> 
        using 3(1) size_indep_subst by auto
      have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
        using 3(2) prenex_formsubst1 by blast
      then have \<open>is_prenex (prenex_right \<phi> (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>))\<close>
        using IH size_xp by blast
      then show ?thesis
        using is_prenex.intros(3) pr_is by presburger
    qed
  qed
  then show ?thesis
    using size_wf_ind[of "\<lambda>\<psi>. is_prenex \<psi> \<longrightarrow> is_prenex (prenex_right \<phi> \<psi>)"]
    by blast
qed

lemma prenex_right_props_imp:  \<open>qfree \<phi> \<Longrightarrow> is_prenex \<psi> \<longrightarrow> is_prenex (prenex_right \<phi> \<psi>) \<and> 
  FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
  language {prenex_right \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_right \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>))))\<close>
proof -
  (* Is it possible to use the induction tactic here instead? *)
  define P where \<open>P = (\<lambda>\<psi>. is_prenex (prenex_right \<phi> \<psi>)  \<and> 
    FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
    language {prenex_right \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
    (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_right \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>)))))\<close>
  assume qfree_phi: \<open>qfree \<phi>\<close>
  have \<open>(\<forall>\<psi>. (\<forall>\<psi>'. size \<psi>' < size \<psi> \<longrightarrow> 
    (is_prenex \<psi>'  \<longrightarrow> P \<psi>')) \<longrightarrow> 
    (is_prenex \<psi> \<longrightarrow> P \<psi>))\<close>
  proof clarsimp
    fix \<xi>
    assume IH: \<open>\<forall>\<psi>'. size \<psi>' < size \<xi> \<longrightarrow> is_prenex \<psi>' \<longrightarrow> P \<psi>'\<close> and
      prenex_xi: \<open>is_prenex \<xi>\<close>
    show \<open>P \<xi>\<close>
    proof (cases rule: is_prenex.cases[OF prenex_xi])
      case (1 \<xi>')
      then show ?thesis
        unfolding P_def
        using prenex_right_qfree_case qfree_phi is_prenex.intros(1) qfree.simps(3) by presburger
    next
      case (2 \<xi>' x)
      have pr_is1:\<open>prenex_right \<phi> \<xi> = prenex_right_forall prenex_right \<phi> x \<xi>'\<close>
        using 2 prenex_right_all_case by blast
      define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<forall> x\<^bold>. \<xi>'))\<close>
      then have pr_is2: \<open>prenex_right \<phi> \<xi> = \<^bold>\<forall>y\<^bold>. prenex_right \<phi> (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using qfree_phi 2(2) pr_is1  unfolding y_def by meson
      have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using prenex_formsubst1 2(2) by presburger
      then have p_xps: \<open>P (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using IH 2(1) less_Suc_eq plus_1_eq_Suc size.simps(4) size_indep_subst by presburger
      have \<open>is_prenex (prenex_right \<phi> \<xi>)\<close>
        using prenex_right_props_imp0 prenex_xi qfree_phi by blast
      moreover have \<open>FV (prenex_right \<phi> \<xi>) = FV (\<phi> \<^bold>\<longrightarrow> \<xi>)\<close>
        using prenex_right_forall_FV[of \<phi> x \<xi>'] by (metis 2(1) FV.simps(4) P_def p_xps pr_is1 y_def)
      moreover have \<open>language {prenex_right \<phi> \<xi>} = language {\<phi> \<^bold>\<longrightarrow> \<xi>}\<close>
        using prenex_right_forall_language by (smt (verit, ccfv_threshold) 2(1) P_def p_xps pr_is1
            prenex_props_forall y_def)
      moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> 
        I\<^bold>,\<beta> \<Turnstile> prenex_right \<phi> \<xi> = I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<xi>)\<close>
      proof clarsimp
        fix I :: "'a intrp" and \<beta>
        assume \<open>dom I \<noteq> {}\<close>
        then show \<open>I\<^bold>,\<beta> \<Turnstile> prenex_right \<phi> \<xi> = (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<xi>)\<close>
          using prenex_right_forall_is by (smt (verit, del_insts) 2(1) P_def holds.simps(3) p_xps
              pr_is1 prenex_props_forall y_def)
      qed
      ultimately show \<open>P \<xi>\<close>
        unfolding P_def by blast
    next
      case (3 \<xi>' x)
      have pr_is1:\<open>prenex_right \<phi> \<xi> = prenex_right_exists prenex_right \<phi> x \<xi>'\<close>
        using 3 prenex_right_exist_case by blast
      define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<exists> x\<^bold>. \<xi>'))\<close>
      then have pr_is2: \<open>prenex_right \<phi> \<xi> = \<^bold>\<exists>y\<^bold>. prenex_right \<phi> (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using qfree_phi 3(2) pr_is1  unfolding y_def by meson
      have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using prenex_formsubst1 3(2) by presburger
      then have p_xps: \<open>P (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using IH 3(1) less_Suc_eq plus_1_eq_Suc size.simps size_indep_subst by simp
      have \<open>is_prenex (prenex_right \<phi> \<xi>)\<close>
        using prenex_right_props_imp0 prenex_xi qfree_phi by blast
      moreover have \<open>FV (prenex_right \<phi> \<xi>) = FV (\<phi> \<^bold>\<longrightarrow> \<xi>)\<close>
        using prenex_right_exists_FV[of \<phi> x \<xi>'] by (metis 3(1) FV.simps(4) FV_exists P_def p_xps
            pr_is1 y_def)
      moreover have \<open>language {prenex_right \<phi> \<xi>} = language {\<phi> \<^bold>\<longrightarrow> \<xi>}\<close>
        using prenex_right_forall_language by (smt (verit) "3"(1) P_def p_xps pr_is1 
            prenex_props_exists prenex_right_exists_language y_def)
      moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> 
        I\<^bold>,\<beta> \<Turnstile> prenex_right \<phi> \<xi> = I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<xi>)\<close>
      proof clarsimp
        fix I :: "'a intrp" and \<beta>
        assume \<open>dom I \<noteq> {}\<close>
        then show \<open>I\<^bold>,\<beta> \<Turnstile> prenex_right \<phi> \<xi> = (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<xi>)\<close>
          using prenex_right_exists_is by (smt (verit) 3(1) P_def holds.simps(3) p_xps pr_is1
              prenex_props_exists y_def)
      qed
      ultimately show \<open>P \<xi>\<close>
        unfolding P_def by blast
    qed
  qed
  then show ?thesis
    using size_wf_ind[of "\<lambda>\<psi>. is_prenex \<psi> \<longrightarrow> P \<psi>"]
    unfolding P_def by blast
qed

lemma prenex_right_props: \<open>qfree \<phi> \<and> is_prenex \<psi> \<Longrightarrow>
  is_prenex (prenex_right \<phi> \<psi>) \<and>
  FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
  language {prenex_right \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_right \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>))))\<close>
  using prenex_right_props_imp by meson


lemma prenex_left_props_imp0: \<open>is_prenex \<psi> \<Longrightarrow> is_prenex \<phi> \<longrightarrow> is_prenex (prenex_left \<phi> \<psi>)\<close>
proof -
  assume prenex_psi: \<open>is_prenex \<psi>\<close>
  have \<open>(\<forall>\<phi>. (\<forall>\<phi>'. size \<phi>' < size \<phi> \<longrightarrow> 
    (is_prenex \<phi>'  \<longrightarrow> is_prenex (prenex_left \<phi>' \<psi>))) \<longrightarrow> 
    (is_prenex \<phi> \<longrightarrow> is_prenex (prenex_left \<phi> \<psi>)))\<close>
  proof clarsimp
    fix \<xi>
    assume IH: \<open>\<forall>\<phi>'. size \<phi>' < size \<xi> \<longrightarrow> is_prenex \<phi>' \<longrightarrow> is_prenex (prenex_left \<phi>' \<psi>)\<close> and
      prenex_xi: \<open>is_prenex \<xi>\<close>
    show \<open>is_prenex (prenex_left \<xi> \<psi>)\<close>
    proof (cases rule: is_prenex.cases[OF prenex_xi])
      case (1 \<xi>')
      then show ?thesis
         using prenex_xi prenex_right_props prenex_left_qfree_case prenex_psi by presburger
    next
      case (2 \<xi>' x)
      then have \<open>prenex_left \<xi> \<psi> = prenex_left_forall prenex_left \<xi>' x \<psi>\<close>
        using prenex_left_forall_case by blast
      then show \<open>is_prenex (prenex_left \<xi> \<psi>)\<close>
        using IH 2 by (metis is_prenex.intros(3) lessI plus_1_eq_Suc prenex_formsubst1 size.simps(4)
            size_indep_subst)
    next
      case (3 \<xi>' x)
      then have \<open>\<exists>y \<sigma>. prenex_left \<xi> \<psi> = \<^bold>\<forall>y\<^bold>. prenex_left (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>\<close>
        using prenex_left_exists_shape_case by presburger
      then obtain y \<sigma> where pr_is: \<open>prenex_left \<xi> \<psi> = \<^bold>\<forall>y\<^bold>. prenex_left (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>\<close>
        by blast
      have size_xp: \<open>size (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<xi>\<close> 
        using 3(1) size_indep_subst by auto
      have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
        using 3(2) prenex_formsubst1 by blast
      then have \<open>is_prenex (prenex_left (\<xi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>)\<close>
        using IH size_xp by blast
      then show ?thesis
        using is_prenex.intros pr_is by presburger
    qed
  qed
  then show ?thesis
    using size_wf_ind[of "\<lambda>\<phi>. is_prenex \<phi> \<longrightarrow> is_prenex (prenex_left \<phi> \<psi>)"]
    by blast
qed


lemma prenex_left_props_imp: \<open>is_prenex \<psi> \<Longrightarrow> is_prenex \<phi> \<longrightarrow> 
        is_prenex (prenex_left \<phi> \<psi>) \<and>
        FV (prenex_left \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
        (language {(prenex_left \<phi> \<psi>)} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)}) \<and>
        (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> prenex_left \<phi> \<psi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  (* Is it possible to use the induction tactic here instead? *)
  define P where \<open>P = (\<lambda>\<phi>. is_prenex (prenex_left \<phi> \<psi>)  \<and> 
    FV (prenex_left \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
    language {prenex_left \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
    (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_left \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>)))))\<close>
  assume is_prenex_psi: \<open>is_prenex \<psi>\<close>
  have \<open>(\<forall>\<phi>. (\<forall>\<phi>'. size \<phi>' < size \<phi> \<longrightarrow> (is_prenex \<phi>'  \<longrightarrow> P \<phi>')) \<longrightarrow> (is_prenex \<phi> \<longrightarrow> P \<phi>))\<close>
  proof clarsimp
    fix \<xi>
    assume IH: \<open>\<forall>\<phi>'. size \<phi>' < size \<xi> \<longrightarrow> is_prenex \<phi>' \<longrightarrow> P \<phi>'\<close> and
      prenex_xi: \<open>is_prenex \<xi>\<close>
    show \<open>P \<xi>\<close>
    proof (cases rule: is_prenex.cases[OF prenex_xi])
      case (1 \<xi>')
      then show ?thesis
        unfolding P_def
        using prenex_right_qfree_case is_prenex_psi 
        by (simp add: prenex_left_qfree_case prenex_right_props)
    next
      case (2 \<xi>' x)
      have pr_is1:\<open>prenex_left \<xi> \<psi> = prenex_left_forall prenex_left \<xi>' x \<psi>\<close>
        using 2 prenex_left_forall_case by blast
      define y where \<open>y = variant (FV (\<^bold>\<forall>x\<^bold>. \<xi>') \<union> FV \<psi>)\<close>
      then have pr_is2: \<open>prenex_left \<xi> \<psi> = \<^bold>\<exists>y\<^bold>. prenex_left (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>\<close>
        using is_prenex_psi 2(2) pr_is1  unfolding y_def by meson
      have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using prenex_formsubst1 2(2) by presburger
      then have p_xps: \<open>P (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using IH 2(1) less_Suc_eq plus_1_eq_Suc size.simps(4) size_indep_subst by presburger
      have \<open>is_prenex (prenex_left \<xi> \<psi>)\<close>
        using prenex_left_props_imp0 prenex_xi is_prenex_psi by blast
      moreover have \<open>FV (prenex_left \<xi> \<psi>) = FV (\<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
        using prenex_left_forall_FV[of x \<xi>' \<psi>] by (metis 2(1) FV_exists P_def p_xps pr_is1 y_def)
      moreover have \<open>language {prenex_left \<xi> \<psi>} = language {\<xi> \<^bold>\<longrightarrow> \<psi>}\<close>
        using prenex_left_forall_language 
        by (smt (verit, ccfv_threshold) 2(1) P_def p_xps pr_is1 prenex_props_exists y_def)
      moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> 
        I\<^bold>,\<beta> \<Turnstile> prenex_left \<xi> \<psi> = I\<^bold>,\<beta> \<Turnstile> \<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
      proof clarsimp
        fix I :: "'a intrp" and \<beta>
        assume \<open>dom I \<noteq> {}\<close>
        then show \<open>I\<^bold>,\<beta> \<Turnstile> prenex_left \<xi> \<psi> = (I\<^bold>,\<beta> \<Turnstile> \<xi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)\<close>
          using prenex_left_forall_is
          by (smt (verit) "2"(1) P_def holds.simps(3) p_xps pr_is1 prenex_props_exists y_def)
      qed
      ultimately show \<open>P \<xi>\<close>
        unfolding P_def by blast
    next
      case (3 \<xi>' x)
      have pr_is1:\<open>prenex_left \<xi> \<psi> = prenex_left_exists prenex_left \<xi>' x \<psi>\<close>
        using 3 prenex_left_exists_case by blast
      define y where \<open>y = variant (FV (\<^bold>\<exists> x\<^bold>. \<xi>') \<union> FV \<psi>)\<close>
      then have pr_is2: \<open>prenex_left \<xi> \<psi> = \<^bold>\<forall>y\<^bold>. prenex_left (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>\<close>
        using is_prenex_psi 3(2) pr_is1  unfolding y_def by meson
      have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using prenex_formsubst1 3(2) by presburger
      then have p_xps: \<open>P (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
        using IH 3(1) less_Suc_eq plus_1_eq_Suc size.simps size_indep_subst by simp
      have \<open>is_prenex (prenex_left \<xi> \<psi>)\<close>
        using prenex_left_props_imp0 prenex_xi is_prenex_psi by blast
      moreover have \<open>FV (prenex_left \<xi> \<psi>) = FV (\<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
        using prenex_left_exists_FV[of x \<xi>' \<psi>] by (metis 3(1) FV.simps(4) P_def p_xps
            pr_is1 y_def)
      moreover have \<open>language {prenex_left \<xi> \<psi>} = language {\<xi> \<^bold>\<longrightarrow> \<psi>}\<close>
        using prenex_left_exists_language[of x \<xi>' \<psi>] 
        by (smt (verit) 3(1) P_def p_xps pr_is2 prenex_props_forall y_def)
      moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> 
        I\<^bold>,\<beta> \<Turnstile> prenex_left \<xi> \<psi> = I\<^bold>,\<beta> \<Turnstile> \<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
      proof clarsimp
        fix I :: "'a intrp" and \<beta>
        assume \<open>dom I \<noteq> {}\<close>
        then show \<open>I\<^bold>,\<beta> \<Turnstile> prenex_left \<xi> \<psi> = (I\<^bold>,\<beta> \<Turnstile> \<xi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)\<close>
          using prenex_left_exists_is by (smt (verit, del_insts) 3(1) P_def holds.simps(3) p_xps
              pr_is1 prenex_props_forall y_def)
      qed
      ultimately show \<open>P \<xi>\<close>
        unfolding P_def by blast
    qed
  qed
  then show ?thesis
    using size_wf_ind[of "\<lambda>\<psi>. is_prenex \<psi> \<longrightarrow> P \<psi>"]
    unfolding P_def by blast
qed

(* 
(`!p q. prenex p /\ prenex q
         ==> prenex (Prenex_left p q) /\
             (FV(Prenex_left p q) = FV(p --> q)) /\
             (language {(Prenex_left p q)} = language {(p --> q)}) /\
             (!M v. ~(Dom M :A->bool = EMPTY)
                    ==> (holds M v (Prenex_left p q) <=> holds M v (p --> q)))`,
*)
lemma prenex_left_props: \<open>is_prenex \<phi> \<and> is_prenex \<psi> \<Longrightarrow> 
        is_prenex (prenex_left \<phi> \<psi>) \<and>
        FV (prenex_left \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
        (language {(prenex_left \<phi> \<psi>)} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)}) \<and>
        (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> prenex_left \<phi> \<psi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
  using prenex_left_props_imp by meson

theorem prenex_props: \<open>is_prenex (prenex \<phi>) \<and> (FV (prenex \<phi>) = FV \<phi>) \<and> 
  (language {prenex \<phi>} = language {\<phi>}) \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I\<^bold>, \<beta> \<Turnstile> \<phi>))\<close>
proof (induction \<phi> rule: form.induct)
  case Bot
  then show ?case
    by (metis is_prenex.simps prenex.simps(1) qfree.simps(1))
next
  case (Atom p ts)
  then show ?case
    using is_prenex.intros(1) prenex.simps(2) qfree.simps(2) by presburger
next
  case (Implies \<phi> \<psi>)
  have \<open>is_prenex (prenex (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
    using Implies prenex_left_props prenex.simps(3) by presburger
  moreover have \<open>FV (prenex (\<phi> \<^bold>\<longrightarrow> \<psi>)) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
    using Implies prenex_left_props prenex.simps(3) FV.simps(3) by presburger
  moreover have \<open>language {prenex (\<phi> \<^bold>\<longrightarrow> \<psi>)} = language {\<phi> \<^bold>\<longrightarrow> \<psi>}\<close>
    using Implies prenex_left_props prenex.simps(3) lang_singleton 
      functions_form.simps(3) predicates_form.simps(3) by (metis prod.inject)
  moreover have \<open>\<forall>(I::'a intrp) \<beta>. FOL_Semantics.dom I \<noteq> {} \<longrightarrow>
    I\<^bold>,\<beta> \<Turnstile> prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>\<close>
    using Implies prenex_left_props holds.simps(3) prenex.simps(3) by metis
  ultimately show ?case by blast
next
  case (Forall x \<phi>)
  have \<open>is_prenex (prenex (\<^bold>\<forall>x\<^bold>. \<phi>))\<close>
    using Forall using is_prenex.intros(2) prenex.simps(4) by presburger
  moreover have fv_indep_prenex: \<open>FV (prenex (\<^bold>\<forall>x\<^bold>. \<phi>)) = FV (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
    using Forall FV.simps(4) prenex.simps(4) by presburger
  moreover have \<open>language {prenex (\<^bold>\<forall>x\<^bold>. \<phi>)} = language {\<^bold>\<forall>x\<^bold>. \<phi>}\<close>
    using Forall prenex.simps(4) functions_form.simps(4) predicates_form.simps(4)
    unfolding language_def functions_forms_def predicates_def by simp
  moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>))\<close>
    using Forall holds.simps(4) by simp
  ultimately show ?case by blast
qed

corollary is_prenex_prenex [simp]: \<open>is_prenex (prenex \<phi>)\<close> 
  and FV_prenex [simp]: \<open>FV (prenex \<phi>) = FV \<phi>\<close>
  and language_prenex [simp]: \<open>language {prenex \<phi>} = language {\<phi>}\<close>
  by (auto simp: prenex_props)

corollary prenex_holds [simp]: \<open>dom I \<noteq> {} \<Longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
  by (simp add: prenex_props)

lemma prenex_satisfies [simp]:
  assumes "dom M \<noteq> {}" 
  shows "satisfies M {prenex \<phi>} \<longleftrightarrow> satisfies M {\<phi>}"
  using assms prenex_holds by (fastforce simp: satisfies_def)

end
