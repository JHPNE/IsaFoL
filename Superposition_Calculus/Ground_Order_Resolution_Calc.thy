theory Ground_Order_Resolution_Calc
  imports
    Main

    (* Theories from the AFP *)
    "Saturation_Framework.Calculus"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "Abstract-Rewriting.Abstract_Rewriting"

    Multiset_Extra
    Clausal_Calculus_Extra
    Selection_Function
    Ground_Order
begin

subsection \<open>Helper\<close>


section \<open>Resolution Calculus\<close>

locale ground_order_resolution_calculus =
  ground_order_base where less\<^sub>t = less\<^sub>t +
  selection_function select 
for
  less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" and
  select :: "'f gterm clause \<Rightarrow> 'f gterm clause"
begin

subsection \<open>Resolution Calculus\<close>

inductive resolution ::
  "'f gterm clause \<Rightarrow> 'f gterm clause \<Rightarrow> 'f gterm clause \<Rightarrow> bool"
where
  resolutionI: "
    C = add_mset L\<^sub>C C' \<Longrightarrow>
    D = add_mset L\<^sub>D D' \<Longrightarrow>
    L\<^sub>D = (Pos t) \<Longrightarrow>
    L\<^sub>C = (Neg t) \<Longrightarrow>
    L\<^sub>C \<prec>\<^sub>l L\<^sub>D \<Longrightarrow>
    (select C = {#} \<and> is_maximal L\<^sub>C C) \<or> (is_maximal L\<^sub>C (select C)) \<Longrightarrow>
    select D = {#} \<Longrightarrow>    
    is_strictly_maximal L\<^sub>D D \<Longrightarrow>
    R = (C' + D') \<Longrightarrow>
    resolution C D R"

inductive factoring ::
  "'f gterm clause \<Rightarrow> 'f gterm clause \<Rightarrow> bool"
where
  factoringI: "
  C = add_mset L\<^sub>1 (add_mset L\<^sub>1 C') \<Longrightarrow>
  L\<^sub>1 = (Pos t) \<Longrightarrow>
  select C = {#} \<Longrightarrow>
  is_maximal L\<^sub>1 C \<Longrightarrow>
  D = add_mset L\<^sub>1 C' \<Longrightarrow>
  factoring C D"

abbreviation factoring_inferences where
"factoring_inferences \<equiv> {Infer [C] D | C D. factoring C D}"

abbreviation resolution_inferences where
  "resolution_inferences \<equiv> {Infer [D, C] R | D C R. resolution D C R}"

subsection \<open>Ground Layer\<close>

definition G_Inf :: "'f gterm clause inference set" where
  "G_Inf =
    {Infer [P\<^sub>2, P\<^sub>1] C | P\<^sub>2 P\<^sub>1 C. resolution P\<^sub>2 P\<^sub>1 C} \<union>
    {Infer [P] C | P C. factoring P C}"

abbreviation G_Bot :: "'f gterm clause set" where
  "G_Bot \<equiv> {{#}}"


definition G_entails :: "'f gterm clause set \<Rightarrow> 'f gterm clause set \<Rightarrow> bool" where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall> I. I \<TTurnstile>s N\<^sub>1 \<longrightarrow> I \<TTurnstile>s N\<^sub>2)"
end

subsection \<open>Smaller Conclussions\<close>

context ground_order_resolution_calculus
begin

lemma test_ordering: "C \<prec>\<^sub>c D \<Longrightarrow> C \<prec>\<^sub>c D"
  by simp

end

subsection \<open>Sublocales\<close>

sublocale ground_order_resolution_calculus \<subseteq> consequence_relation where
  Bot = G_Bot and
  entails = G_entails
proof unfold_locales
  show "G_Bot \<noteq> {}"
    by simp
next
  show "\<And>B N. B \<in> G_Bot \<Longrightarrow> G_entails {B} N"
    by (simp add: G_entails_def)
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> G_entails N1 N2"
    by (auto simp: G_entails_def elim!: true_clss_mono[rotated])
next
  fix N1 N2 assume ball_G_entails: "\<forall>C \<in> N2. G_entails N1 {C}"
  show "G_entails N1 N2"
    unfolding G_entails_def
    by (meson G_entails_def all_formulas_entailed ball_G_entails)
next
  show "\<And>N1 N2 N3. G_entails N1 N2 \<Longrightarrow> G_entails N2 N3 \<Longrightarrow> G_entails N1 N3"
    using G_entails_def
    by simp
qed

sublocale ground_order_resolution_calculus \<subseteq> calculus_with_finitary_standard_redundancy where
  Inf = G_Inf and
  Bot = G_Bot and
  entails = G_entails and
  less = "(\<prec>\<^sub>c)"
  defines GRed_I = Red_I and GRed_F = Red_F
proof unfold_locales