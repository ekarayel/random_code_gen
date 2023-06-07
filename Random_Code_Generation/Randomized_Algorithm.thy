theory Randomized_Algorithm
  imports Randomized_Algorithm_Internal
begin

lemma pmf_eq_iff_le:
  fixes p q :: "'a pmf"
  assumes "\<And>x. pmf p x \<le> pmf q x"
  shows "p = q"
proof -
  have "(\<integral>x. pmf q x - pmf p x \<partial>count_space UNIV) = 0"
    by (simp_all add:integrable_pmf integral_pmf)
  moreover have "integrable (count_space UNIV) (\<lambda>x. pmf q x - pmf p x)"
    by (simp add:integrable_pmf)
  moreover  have "AE x in count_space UNIV. 0 \<le> pmf q x - pmf p x"
    using assms unfolding AE_count_space by auto
  ultimately have "AE x in count_space UNIV. pmf q x - pmf p x = 0"
    using integral_nonneg_eq_0_iff_AE by blast
  hence "\<And>x. pmf p x = pmf q x" unfolding AE_count_space by simp
  thus ?thesis by (intro pmf_eqI) auto
qed

lemma eq_iff_ord_spmf:
  assumes "weight_spmf p \<ge> weight_spmf q"
  assumes "ord_spmf (=) p q"
  shows "p = q"
proof -
  have "\<And>x. spmf p x \<le> spmf q x"
    using ord_spmf_eq_leD[OF assms(2)] by simp
  moreover have "pmf p None \<le> pmf q None"
    using assms(1) unfolding pmf_None_eq_weight_spmf by auto
  ultimately have "pmf p x \<le> pmf q x" for x by (cases x) auto
  thus ?thesis using pmf_eq_iff_le by auto
qed

lemma wf_empty: "wf_random (\<lambda>_. None)"
  unfolding wf_random_def by auto

typedef 'a random_alg = "{(r :: 'a random_monad). wf_random r}"
  using wf_empty by (intro exI[where x="\<lambda>_. None"]) auto

setup_lifting type_definition_random_alg

lift_definition return_ra :: "'a \<Rightarrow> 'a random_alg" is return_rm
  by (rule wf_return) 

lift_definition coin_ra :: "bool random_alg" is coin_rm
  by (rule wf_coin) 

lift_definition bind_ra :: "'a random_alg \<Rightarrow> ('a \<Rightarrow> 'b random_alg) \<Rightarrow> 'b random_alg" is bind_rm
  by (rule wf_bind)

adhoc_overloading Monad_Syntax.bind bind_ra

lift_definition lub_ra :: "'a random_alg set \<Rightarrow> 'a random_alg" is 
  "(\<lambda>F. if Complete_Partial_Order.chain ord_rm F then lub_rm F else (\<lambda>x. None))"
  using wf_lub wf_empty by auto

lift_definition ord_ra :: "'a random_alg \<Rightarrow> 'a random_alg \<Rightarrow> bool" is "ord_rm" .

context
begin

interpretation pmf_as_measure .

lemma measure_rm_is_pmf:
  assumes "wf_random f"
  shows 
    "prob_space (measure_rm f)" (is "?A")
    "sets (measure_rm f) = UNIV" (is "?B")
    "AE x in measure_rm f. measure (measure_rm f) {x} \<noteq> 0" (is "?C")
proof -
  show "prob_space (measure_rm f)"
    using prob_space_measure_rm[OF assms] by simp
  then interpret p: prob_space "measure_rm f"
    by auto
  show ?B
    unfolding measure_rm_def by simp

  have "AE bs in \<B>. map_option fst (f bs) \<in> Some ` range_rm f \<union> {None}"
    unfolding range_rm_def
    by (intro AE_I2) (auto simp:image_iff split:option.split)
  hence "AE x in measure_rm f. x \<in> Some ` range_rm f \<union> {None}"
    unfolding measure_rm_def using measure_rm_measurable[OF assms]
    by (subst AE_distr_iff) auto
  moreover have "countable (Some ` range_rm f \<union> {None})"
    using countable_range[OF assms] by simp
  moreover have "p.events = UNIV" 
    unfolding measure_rm_def by simp
  ultimately show ?C
    by (intro iffD2[OF p.AE_support_countable] exI[where x= "Some ` range_rm f \<union> {None}"]) auto
qed

lift_definition spmf_of_ra :: "'a random_alg \<Rightarrow> 'a spmf" is "measure_rm"
  using measure_rm_is_pmf by metis

lemma used_bits_distr_is_pmf:
  assumes "wf_random f"
  shows 
    "prob_space (used_bits_distr f)" (is "?A")
    "sets (used_bits_distr f) = UNIV" (is "?B")
    "AE x in used_bits_distr f. measure (used_bits_distr f) {x} \<noteq> 0" (is "?C")
proof -
  show "prob_space (used_bits_distr f)"
    unfolding used_bits_distr_def
    by (intro coin_space.prob_space_distr consumed_bits_measurable)
  then interpret p: prob_space "used_bits_distr f"
    by auto
  show ?B
    unfolding used_bits_distr_def by simp
  have "p.events = UNIV" 
    unfolding used_bits_distr_def by simp
  thus ?C
    by (intro iffD2[OF p.AE_support_countable] exI[where x= "UNIV"]) auto
qed

lift_definition coin_usage_of_ra_aux :: "'a random_alg \<Rightarrow> nat spmf" is "used_bits_distr"
  using used_bits_distr_is_pmf by auto

definition coin_usage_of_ra
  where "coin_usage_of_ra p = map_pmf (case_option \<infinity> enat) (coin_usage_of_ra_aux p)"

end

lemma rep_rand_alg:
  "wf_random (Rep_random_alg f)"
  using Rep_random_alg by auto

lemma set_pmf_spmf_of_ra: 
  "set_pmf (spmf_of_ra f) \<subseteq> Some ` range_rm (Rep_random_alg f) \<union> {None}"
proof
  let ?f = "Rep_random_alg f"

  fix x assume "x \<in> set_pmf (spmf_of_ra f)"
  hence "pmf (spmf_of_ra f) x > 0"
    using pmf_positive by metis
  hence "measure (measure_rm ?f) {x} > 0"
    by (subst spmf_of_ra.rep_eq[symmetric]) (simp add: pmf.rep_eq)
  hence "0 < measure \<B> {\<omega>. map_option fst (?f \<omega>) = x}"
    using measure_rm_measurable[OF rep_rand_alg] unfolding measure_rm_def 
    by (subst (asm) measure_distr) (simp_all add:vimage_def space_coin_space)
  moreover have "{\<omega>. map_option fst (?f \<omega>) = x} = {}" if "x \<notin> range (map_option fst \<circ> ?f)"
    using that by (auto simp:set_eq_iff image_iff)
  hence "measure \<B> {\<omega>. map_option fst (?f \<omega>) = x} = 0" if "x \<notin> range (map_option fst \<circ> ?f)"
    using that by simp
  ultimately have "x \<in> range (map_option fst \<circ> ?f)"
    by auto
  thus "x \<in> Some ` range_rm (Rep_random_alg f) \<union> {None}"
    unfolding range_rm_def by (cases x) auto 
qed

lemma spmf_of_ra_return: "spmf_of_ra (return_ra x) = return_spmf x"
proof -
  have "measure_pmf (spmf_of_ra (return_ra x)) = measure_pmf (return_spmf x)"
    unfolding  spmf_of_ra.rep_eq measure_rm_return'[symmetric]
    by (simp add: return_ra.rep_eq)
  thus ?thesis
    using measure_pmf_inject by blast
qed

lemma spmf_of_ra_coin: "spmf_of_ra coin_ra = coin_spmf"
proof -
  have "measure_pmf (spmf_of_ra coin_ra) = measure_pmf coin_spmf"
    unfolding  spmf_of_ra.rep_eq measure_rm_coin[symmetric]
    by (simp add: coin_ra.rep_eq)
  thus ?thesis
    using measure_pmf_inject by blast
qed

lemma spmf_of_ra_bind: 
  "spmf_of_ra (bind_ra f g) = bind_spmf (spmf_of_ra f) (\<lambda>x. spmf_of_ra (g x))" (is "?L = ?R")
proof -
  let ?f = "Rep_random_alg f"
  let ?g = "\<lambda>x. Rep_random_alg (g x)"

  have 0: "x \<in> Some ` range_rm ?f \<or> x = None" if "x \<in> set_pmf (spmf_of_ra f)" for x
    using that set_pmf_spmf_of_ra by auto

  have "measure_pmf ?L = measure_rm (?f \<bind> ?g)"
    unfolding spmf_of_ra.rep_eq bind_ra.rep_eq by (simp add:comp_def)
  also have "... = measure_rm ?f \<bind> 
    (\<lambda>x. if x \<in> Some ` range_rm ?f then measure_rm (?g (the x)) else return \<D> None)"
    by (intro measure_rm_bind rep_rand_alg)  
  also have "... = measure_pmf (spmf_of_ra f) \<bind>
    (\<lambda>x. measure_pmf (if x \<in> Some ` range_rm ?f then spmf_of_ra (g (the x)) else return_pmf None))"
    by (intro arg_cong2[where f="bind"] ext) (auto simp:spmf_of_ra.rep_eq return_discrete)
  also have "... = measure_pmf (spmf_of_ra f \<bind> 
    (\<lambda>x. if x \<in> Some ` range_rm ?f then spmf_of_ra (g (the x)) else return_pmf None))"
    unfolding bind_pmf.rep_eq by (simp add:comp_def id_def)
  also have "... = measure_pmf ?R"
    using 0 unfolding bind_spmf_def 
    by (intro arg_cong[where f="measure_pmf"] bind_pmf_cong refl) (auto split:option.split)
  finally have "measure_pmf ?L = measure_pmf ?R" by simp
  thus ?thesis
    using measure_pmf_inject by blast
qed

lemma spmf_of_ra_mono:
  assumes "ord_ra f g"
  shows "ord_spmf (=) (spmf_of_ra f) (spmf_of_ra g)"
proof -
  have "ord_rm (Rep_random_alg f) (Rep_random_alg g)"
    using assms unfolding ord_ra.rep_eq by simp
  hence "ennreal (spmf (spmf_of_ra f) x) \<le> ennreal (spmf (spmf_of_ra g) x)" for x
    unfolding emeasure_pmf_single[symmetric] spmf_of_ra.rep_eq 
    by (intro measure_rm_ord_rm_mono rep_rand_alg) auto
  hence "spmf (spmf_of_ra f) x \<le> spmf (spmf_of_ra g) x" for x
    by simp
  thus ?thesis
    by (intro ord_pmf_increaseI) auto
qed

lemma spmf_of_ra_lub_ra_empty:
  "spmf_of_ra (lub_ra {}) = return_pmf None" (is "?L = ?R")
proof -
  have "measure_pmf ?L = measure_rm (lub_rm {})"
    unfolding spmf_of_ra.rep_eq lub_ra.rep_eq Complete_Partial_Order.chain_def by auto
  also have "... = measure_rm (\<lambda>_. None)"
    unfolding lub_rm_def fun_lub_def flat_lub_def by auto
  also have "... = measure_pmf ?R"
    unfolding measure_rm_None by simp
  finally have "measure_pmf ?L = measure_pmf ?R"
    by simp
  thus ?thesis
    using measure_pmf_inject by auto
qed

lemma spmf_of_ra_lub_ra:
  fixes A :: "'a random_alg set"
  assumes "Complete_Partial_Order.chain ord_ra A"
  shows "spmf_of_ra (lub_ra A) = lub_spmf (spmf_of_ra ` A)" (is "?L = ?R")
proof (cases "A \<noteq> {}")
  case True
  have 0:"Complete_Partial_Order.chain ord_rm (Rep_random_alg ` A)"
    using assms unfolding ord_ra.rep_eq Complete_Partial_Order.chain_def by auto
  have 1:"Complete_Partial_Order.chain (ord_spmf (=)) (spmf_of_ra ` A)"
    using spmf_of_ra_mono by (intro chain_imageI[OF assms]) auto

  show ?thesis
  proof (rule spmf_eqI)
    fix x :: "'a"  
    have "ennreal (spmf ?L x) = emeasure (measure_rm (lub_rm (Rep_random_alg ` A))) {Some x}"
      using 0 unfolding emeasure_pmf_single[symmetric] spmf_of_ra.rep_eq lub_ra.rep_eq by simp
    also have "... = (SUP f\<in>Rep_random_alg ` A. emeasure (measure_rm f) {Some x})"
      using True rep_rand_alg by (intro measure_rm_lub 0) auto
    also have "... = (SUP p\<in>A. ennreal (spmf (spmf_of_ra p) x))"
      unfolding emeasure_pmf_single[symmetric] spmf_of_ra.rep_eq by (simp add:image_image)
    also have "... = (SUP p\<in>spmf_of_ra ` A. ennreal (spmf p x))"
      by (simp add:image_image)
    also have "... = ennreal (spmf ?R x)"
      using True by (intro ennreal_spmf_lub_spmf[symmetric] 1) auto
    finally have "ennreal (spmf ?L x) = ennreal (spmf ?R x)"
      by simp 
    thus "spmf ?L x = spmf ?R x"
      by simp
  qed
next
  case False
  thus ?thesis using spmf_of_ra_lub_ra_empty by simp
qed

lemma rep_lub_ra:
  assumes "Complete_Partial_Order.chain ord_ra F"
  shows "Rep_random_alg (lub_ra F) = lub_rm (Rep_random_alg ` F)"
proof -
  have "Complete_Partial_Order.chain ord_rm (Rep_random_alg ` F)"
    using assms unfolding ord_ra.rep_eq Complete_Partial_Order.chain_def by auto
  thus ?thesis
    unfolding lub_ra.rep_eq by simp
qed

lemma partial_function_image_improved:
  fixes ord
  assumes "\<And>A. Complete_Partial_Order.chain ord (f ` A) \<Longrightarrow> l1 (f ` A) = f (l2 A)"
  assumes "partial_function_definitions ord l1"
  assumes "inj f"
  shows "partial_function_definitions (img_ord f ord) l2"
proof -
  interpret pd: partial_function_definitions ord l1
    using assms(2) by auto
  have "img_ord f ord x x" for x
    unfolding img_ord_def using pd.leq_refl by simp
  moreover have "img_ord f ord x z" if "img_ord f ord x y" "img_ord f ord y z"  for x y z
    using that pd.leq_trans unfolding img_ord_def by blast
  moreover have "x = y" if "img_ord f ord x y" "img_ord f ord y x"  for x y
  proof -
    have "f x = f y"
      using that pd.leq_antisym unfolding img_ord_def by blast
    thus ?thesis
      using inj_onD[OF assms(3)] by simp
  qed
  moreover have "img_ord f ord x (l2 A)" 
    if "x \<in> A" "Complete_Partial_Order.chain (img_ord f ord) A" for x A
  proof -
    have 0:"Complete_Partial_Order.chain ord (f ` A)"
      using that(2) unfolding chain_def img_ord_def by auto
    have "ord (f x) (l1 (f ` A))"
      using that by (intro pd.lub_upper[OF 0]) auto
    thus ?thesis
      unfolding img_ord_def assms(1)[OF 0] by auto
  qed
  moreover have "img_ord f ord (l2 A) z"
    if "Complete_Partial_Order.chain (img_ord f ord) A" "(\<forall>x. x \<in> A \<longrightarrow> img_ord f ord x z)" 
    for z A
  proof -
    have 0:"Complete_Partial_Order.chain ord (f ` A)"
      using that(1) unfolding chain_def img_ord_def by auto
    have "ord (l1 (f ` A)) (f z)"
      using that(2) by (intro pd.lub_least[OF 0]) (auto simp:img_ord_def)
    thus ?thesis
      unfolding img_ord_def assms(1)[OF 0] by auto
  qed
  ultimately show ?thesis
    unfolding partial_function_definitions_def by blast
qed

lemma random_alg_pfd: "partial_function_definitions ord_ra lub_ra"
proof -
  have 0: "inj Rep_random_alg"
    using Rep_random_alg_inject unfolding inj_on_def by auto

  have 1:"partial_function_definitions ord_rm lub_rm"
    using random_monad_pd_fact by simp

  have 2:"ord_ra = img_ord Rep_random_alg ord_rm"
    unfolding ord_ra.rep_eq img_ord_def by auto

  show ?thesis
    unfolding 2 by (intro partial_function_image_improved[OF _ 1 0]) (auto simp: lub_ra.rep_eq)
qed

interpretation random_alg_pf: partial_function_definitions "ord_ra" "lub_ra"
  using random_alg_pfd by auto

abbreviation "mono_ra \<equiv> monotone (fun_ord ord_ra) ord_ra"

lemma bind_mono_aux_ra:
  assumes "ord_ra f1 f2" "\<And>y. ord_ra (g1 y) (g2 y)"
  shows "ord_ra (bind_ra f1 g1) (bind_ra f2 g2)"
  using assms unfolding ord_ra.rep_eq bind_ra.rep_eq 
  by (intro bind_mono_aux) auto

lemma bind_mono_ra [partial_function_mono]:
  assumes "mono_ra B" and "\<And>y. mono_ra (C y)"
  shows "mono_ra (\<lambda>f. bind_ra (B f) (\<lambda>y. C y f))"
  using assms by (intro monotoneI bind_mono_aux_ra) (auto simp:monotone_def)

definition map_ra :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a random_alg \<Rightarrow> 'b random_alg"
  where "map_ra f p = p \<bind> (\<lambda>x. return_ra (f x))"

lemma spmf_of_ra_map_ra: "spmf_of_ra (map_ra f p) = map_spmf f (spmf_of_ra p)"
  unfolding map_ra_def map_spmf_conv_bind_spmf spmf_of_ra_bind spmf_of_ra_return by simp

lemma map_mono_ra [partial_function_mono]:
  assumes "mono_ra B" 
  shows "mono_ra (\<lambda>f. map_ra g (B f))"
  using assms unfolding map_ra_def by (intro bind_mono_ra) auto

definition rel_spmf_of_ra :: "'a spmf \<Rightarrow> 'a random_alg \<Rightarrow> bool" where
  "rel_spmf_of_ra q p \<longleftrightarrow> q = spmf_of_ra p"

lemma admissible_rel_spmf_of_ra:
  "ccpo.admissible (prod_lub lub_spmf lub_ra) (rel_prod (ord_spmf (=)) ord_ra) (case_prod rel_spmf_of_ra)"
  (is "ccpo.admissible ?lub ?ord ?P")
proof (rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and R: "\<forall>(p, q) \<in> Y. rel_spmf_of_ra p q"
  from R have R: "\<And>p q. (p, q) \<in> Y \<Longrightarrow> rel_spmf_of_ra p q" by auto
  have chain1: "Complete_Partial_Order.chain (ord_spmf (=)) (fst ` Y)"
    and chain2: "Complete_Partial_Order.chain (ord_ra) (snd ` Y)"
    using chain by(rule chain_imageI; clarsimp)+
  from Y have Y1: "fst ` Y \<noteq> {}" and Y2: "snd ` Y \<noteq> {}" by auto
 
  have "lub_spmf (fst ` Y) = lub_spmf (spmf_of_ra ` snd ` Y)"
    unfolding image_image using R
    by (intro arg_cong[of _ _ lub_spmf] image_cong) (auto simp: rel_spmf_of_ra_def)
  also have "\<dots> = spmf_of_ra (lub_ra (snd ` Y))"
    by (intro spmf_of_ra_lub_ra[symmetric] chain2)
  finally have "rel_spmf_of_ra (lub_spmf (fst ` Y)) (lub_ra (snd ` Y))"
    unfolding rel_spmf_of_ra_def .
  then show "?P (?lub Y)"
    by (simp add: prod_lub_def)
qed

lemma admissible_rel_spmf_of_ra_cont [cont_intro]:
  fixes ord
  shows "\<lbrakk> mcont lub ord lub_spmf (ord_spmf (=)) f; mcont lub ord lub_ra ord_ra g \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. rel_spmf_of_ra (f x) (g x))"
  by (rule admissible_subst[OF admissible_rel_spmf_of_ra, where f="\<lambda>x. (f x, g x)", simplified]) 
     (rule mcont_Pair)

lemma mcont2mcont_spmf_of_ra[THEN spmf.mcont2mcont, cont_intro]:
  shows mcont_spmf_of_sampler: "mcont lub_ra ord_ra lub_spmf (ord_spmf (=)) spmf_of_ra"
  unfolding mcont_def monotone_def cont_def
  by (auto simp: spmf_of_ra_mono spmf_of_ra_lub_ra)

(*
lemma (in ccpo) ccpo: "class.ccpo Sup (\<le>) (mk_less (\<le>))"
proof -
  have "class.ccpo Sup (\<le>) ((<) :: 'a \<Rightarrow> _)"
    by (rule ccpo_axioms)
  also have "((<) :: 'a \<Rightarrow> _) = mk_less (\<le>)"
    by (auto simp: fun_eq_iff mk_less_def)
  finally show ?thesis .
qed
*)
context includes lifting_syntax
begin

lemma fixp_ra_parametric[transfer_rule]:
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_ra (\<lambda>f. G f x)"
  and param: "((A ===> rel_spmf_of_ra) ===> A ===> rel_spmf_of_ra) F G"
  shows "(A ===> rel_spmf_of_ra) (spmf.fixp_fun F) (random_alg_pf.fixp_fun G)"
  using f g 
proof(rule parallel_fixp_induct_1_1[OF 
      partial_function_definitions_spmf random_alg_pfd _ _ reflexive reflexive, 
        where P="(A ===> rel_spmf_of_ra)"])
  show "ccpo.admissible (prod_lub (fun_lub lub_spmf) (fun_lub lub_ra)) 
        (rel_prod (fun_ord (ord_spmf (=))) (fun_ord ord_ra)) 
        (\<lambda>x. (A ===> rel_spmf_of_ra) (fst x) (snd x))"
    unfolding rel_fun_def
    by(rule admissible_all admissible_imp cont_intro)+
  show "(A ===> rel_spmf_of_ra) (\<lambda>_. lub_spmf {}) (\<lambda>_. lub_ra {})"
    by (auto simp: rel_fun_def rel_spmf_of_ra_def spmf_of_ra_lub_ra_empty)
  show "(A ===> rel_spmf_of_ra) (F f) (G g)" if "(A ===> rel_spmf_of_ra) f g" for f g
    using that by(rule rel_funD[OF param])
qed

lemma return_ra_tranfer[transfer_rule]: "((=) ===> rel_spmf_of_ra) return_spmf return_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_return by simp

lemma bind_ra_tranfer[transfer_rule]:
  "(rel_spmf_of_ra ===> ((=) ===> rel_spmf_of_ra) ===> rel_spmf_of_ra) bind_spmf bind_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_bind by simp presburger

lemma coin_ra_tranfer[transfer_rule]: 
  "rel_spmf_of_ra coin_spmf coin_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_coin by simp

lemma map_ra_tranfer[transfer_rule]:
  "((=) ===> rel_spmf_of_ra ===> rel_spmf_of_ra) map_spmf map_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_map_ra by simp

end

declare [[function_internals]]

declaration \<open>Partial_Function.init "random_alg" \<^term>\<open>random_alg_pf.fixp_fun\<close>
  \<^term>\<open>random_alg_pf.mono_body\<close> 
  @{thm random_alg_pf.fixp_rule_uc} @{thm random_alg_pf.fixp_induct_uc}
  NONE\<close>

end