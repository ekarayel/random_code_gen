theory Consumption_SPMF
  imports Tracking_Randomized_Algorithm
begin

type_synonym 'a rspmf = "('a \<times> nat) spmf"

definition return_rspmf :: "'a \<Rightarrow> 'a rspmf" where
  "return_rspmf x = return_spmf (x,0)"

definition coin_rspmf :: "bool rspmf" where
  "coin_rspmf = pair_spmf coin_spmf (return_spmf 1)"

definition bind_rspmf :: "'a rspmf \<Rightarrow> ('a \<Rightarrow> 'b rspmf) \<Rightarrow> 'b rspmf" where
  "bind_rspmf f g = bind_spmf f (\<lambda>(r,c). map_spmf (apsnd ((+) c)) (g r))"

adhoc_overloading Monad_Syntax.bind bind_rspmf

lemma bind_mono_rspmf_aux:
  assumes "ord_spmf (=) f1 f2" "\<And>y. ord_spmf (=) (g1 y) (g2 y)"
  shows "ord_spmf (=) (bind_rspmf f1 g1) (bind_rspmf f2 g2)"
  using assms unfolding bind_rspmf_def map_spmf_conv_bind_spmf 
  by (auto intro!: bind_spmf_mono' simp add:case_prod_beta')

lemma bind_mono_rspmf [partial_function_mono]:
  assumes "mono_spmf B" and "\<And>y. mono_spmf (C y)"
  shows "mono_spmf (\<lambda>f. bind_rspmf (B f) (\<lambda>y. C y f))"
  using assms by (intro monotoneI bind_mono_rspmf_aux) (auto simp:monotone_def) 

definition ord_rspmf :: "'a rspmf \<Rightarrow> 'a rspmf \<Rightarrow> bool" where 
  "ord_rspmf = ord_spmf (\<lambda>x y. fst x = fst y \<and> snd x \<ge> snd y)"

notation
  ord_rspmf  ("(_/ \<le>\<^sub>R _)"  [51, 51] 50) 

definition consumption :: "'a rspmf \<Rightarrow> enat pmf"
  where "consumption = map_pmf (\<lambda>x. case x of None \<Rightarrow> \<infinity> | Some y \<Rightarrow> enat (snd y))"

definition consumption_real :: "'a rspmf \<Rightarrow> ennreal pmf"
  where "consumption_real p = map_pmf ennreal_of_enat (consumption p)"

definition expected_consumption :: "'a rspmf \<Rightarrow> ennreal"
  where "expected_consumption p = (\<integral>\<^sup>+x. x \<partial>(consumption_real p))"

definition result :: "'a rspmf \<Rightarrow> 'a spmf"
  where "result = map_spmf fst"

lemma consumption_alt_def:
  "consumption p = map_pmf (\<lambda>x. case x of None \<Rightarrow> \<infinity> | Some y \<Rightarrow> enat y) (map_spmf snd p)"
  unfolding consumption_def map_pmf_comp map_option_case 
  by (metis enat_def infinity_enat_def option.case_eq_if option.sel)

lemma consumption_mono:
  assumes "ord_rspmf p q"
  shows "measure (consumption p) {..k} \<le> measure (consumption q) {..k}"
proof -
  define p' where "p' = map_spmf snd p" 
  define q' where "q' = map_spmf snd q" 
  have 0:"ord_spmf (\<ge>) p' q'"
    using assms(1) ord_spmf_mono unfolding p'_def q'_def ord_rspmf_def ord_spmf_map_spmf12 by fastforce

  have cp:"consumption p = map_pmf (case_option \<infinity> enat) p'"
    unfolding consumption_alt_def p'_def by simp
  have cq:"consumption q = map_pmf (case_option \<infinity> enat) q'"
    unfolding consumption_alt_def q'_def by simp

  have 0:"rel_pmf (\<ge>) (consumption p) (consumption q)"
    unfolding cp cq map_pmf_def by (intro rel_pmf_bindI[OF 0]) (auto split:option.split)
  show ?thesis
    unfolding atMost_def by (intro measure_Ici[OF 0] transp_ge) (simp add:reflp_def) 
qed

lemma consumption_mono_rev:
  assumes "ord_rspmf p q"
  shows "measure (consumption q) {x. x > k} \<le> measure (consumption p) {x. x > k}" (is "?L \<le> ?R")
proof -
  have 0:"UNIV - {x. x > k} = {..k}"
    by (auto simp add:set_diff_eq set_eq_iff)
  have "1 - ?R \<le> 1 - ?L"
    using consumption_mono[OF assms]
    by (subst (1 2) measure_pmf.prob_compl[symmetric]) (auto simp:0)
  thus ?thesis
    by simp
qed

lemma expected_consumption:
  "expected_consumption p = (\<Sum>k. ennreal (measure (consumption p) {x. x > enat k}))" (is "?L = ?R")
proof -
  have "?L = integral\<^sup>N (measure_pmf (consumption p)) ennreal_of_enat"
    unfolding expected_consumption_def consumption_real_def by simp
  also have "... = (\<Sum>k. emeasure (measure_pmf (consumption p)) {x. enat k < x})"
    by (subst nn_integral_enat_function) auto
  also have "... = ?R"
    by (subst measure_pmf.emeasure_eq_measure) simp
  finally show ?thesis
    by simp
qed

lemma ord_rspmf_min: "ord_rspmf (return_pmf None) p"
  unfolding ord_rspmf_def by (simp add: ord_spmf_reflI)

lemma ord_rspmf_refl: "ord_rspmf p p"
  unfolding ord_rspmf_def by (simp add: ord_spmf_reflI)

lemma ord_rspmf_trans[trans]: 
  assumes "ord_rspmf p q" "ord_rspmf q r"
  shows "ord_rspmf p r"
proof -
  have 0:"transp (ord_rspmf)"
    unfolding ord_rspmf_def
    by (intro transp_rel_pmf transp_ord_option) (auto simp:transp_def) 
  thus ?thesis
    using assms transpD[OF 0] by auto
qed

lemma ord_rspmf_map_spmf: 
  assumes "\<And>x. x \<le> f x"
  shows "ord_rspmf (map_spmf (apsnd f) p) p"
  using assms unfolding ord_rspmf_def ord_spmf_map_spmf1 
  by (intro ord_spmf_reflI) auto

lemma ord_rspmf_bind_pmf:
  assumes "\<And>x. ord_rspmf (f x) (g x)"
  shows "ord_rspmf (bind_pmf p f) (bind_pmf p g)"
  using assms unfolding ord_rspmf_def
  by (intro rel_pmf_bindI[where R="(=)"]) (auto simp add: pmf.rel_refl)

lemma ord_rspmf_bind_rspmf:
  assumes "\<And>x. ord_rspmf (f x) (g x)"
  shows "ord_rspmf (bind_rspmf p f) (bind_rspmf p g)"
  using assms unfolding bind_rspmf_def ord_rspmf_def
  by (intro ord_spmf_bind_reflI) (simp add:case_prod_beta ord_spmf_map_spmf12)

definition consume :: "nat  \<Rightarrow> 'a rspmf \<Rightarrow> 'a rspmf"
  where "consume k = map_spmf (apsnd ((+) k))"

lemma consume_add:
  "consume k (consume s f) = consume (k+s) f"
  unfolding consume_def spmf.map_comp 
  by (simp add:comp_def apsnd_def map_prod_def case_prod_beta' algebra_simps)

lemma coin_rspmf_split:
  fixes f :: "bool \<Rightarrow> 'b rspmf"
  shows "(coin_rspmf \<bind> f) = consume 1 (coin_spmf \<bind> f)"
  unfolding coin_rspmf_def consume_def map_spmf_conv_bind_spmf pair_spmf_alt_def bind_rspmf_def
  by (simp)

lemma ord_rspmf_consume:
  "ord_rspmf (consume k p) p"
  unfolding consume_def by (intro ord_rspmf_map_spmf) auto

lemma ord_rspmf_consume_2:
  assumes "ord_rspmf p q"
  shows  "ord_rspmf (consume k p) (consume k q)"
  using assms unfolding consume_def ord_rspmf_def ord_spmf_map_spmf12 by auto

lemma result_mono:
  assumes "ord_rspmf p q"
  shows "ord_spmf (=) (result p) (result q)"
  using assms ord_spmf_mono unfolding result_def ord_rspmf_def ord_spmf_map_spmf12 by force

lemma result_bind:
  "result (bind_rspmf f g) = result f \<bind> (\<lambda>x. result (g x))"
  unfolding bind_rspmf_def result_def map_spmf_conv_bind_spmf by (simp add:case_prod_beta')

lemma result_return:
  "result (return_rspmf x) = return_spmf x"
  unfolding return_rspmf_def result_def map_spmf_conv_bind_spmf by (simp add:case_prod_beta')

lemma result_coin:
  "result (coin_rspmf) = coin_spmf"
  unfolding coin_rspmf_def result_def pair_spmf_alt_def map_spmf_conv_bind_spmf by (simp add:case_prod_beta')

definition rspmf_of_ra :: "'a random_alg \<Rightarrow> 'a rspmf" where
  "rspmf_of_ra = spmf_of_ra \<circ> track_coin_use"

lemma rspmf_of_ra_coin: "rspmf_of_ra coin_ra = coin_rspmf"
  unfolding rspmf_of_ra_def comp_def track_coin_use_coin coin_rac_def coin_rspmf_def 
    spmf_of_ra_bind spmf_of_ra_coin spmf_of_ra_return pair_spmf_alt_def
  by simp

lemma rspmf_of_ra_return: "rspmf_of_ra (return_ra x) = return_rspmf x"
  unfolding rspmf_of_ra_def comp_def track_coin_use_return return_rac_def return_rspmf_def 
     spmf_of_ra_return by simp

lemma rspmf_of_ra_bind:
  "rspmf_of_ra (bind_ra m f) = bind_rspmf (rspmf_of_ra m) (\<lambda>x. rspmf_of_ra (f x))"
  unfolding rspmf_of_ra_def comp_def track_coin_use_bind bind_rac_def bind_rspmf_def 
    map_spmf_conv_bind_spmf
  by (simp add:case_prod_beta' spmf_of_ra_bind spmf_of_ra_return apsnd_def map_prod_def)

lemma rspmf_of_ra_mono:
  assumes "ord_ra f g"
  shows "ord_spmf (=) (rspmf_of_ra f) (rspmf_of_ra g)"
  unfolding rspmf_of_ra_def comp_def
  by (intro spmf_of_ra_mono track_coin_use_mono assms)

lemma rspmf_of_ra_lub:
  assumes "Complete_Partial_Order.chain ord_ra A"
  shows "rspmf_of_ra (lub_ra A) = lub_spmf (rspmf_of_ra ` A)" (is "?L = ?R")
proof -
  have 0:"Complete_Partial_Order.chain ord_ra (track_coin_use ` A)"
    by (intro chain_imageI[OF assms] track_coin_use_mono)

  have "?L = spmf_of_ra (lub_ra (track_coin_use ` A))"
    unfolding rspmf_of_ra_def comp_def 
    by (intro arg_cong[where f="spmf_of_ra"] track_coin_use_lub assms)
  also have "... = lub_spmf (spmf_of_ra ` track_coin_use ` A)"
    by (intro spmf_of_ra_lub_ra 0)
  also have "... = ?R"
    unfolding image_image rspmf_of_ra_def by simp
  finally show "?thesis" by simp
qed

definition rel_rspmf_of_ra :: "'a rspmf \<Rightarrow> 'a random_alg \<Rightarrow> bool" where
  "rel_rspmf_of_ra q p \<longleftrightarrow> q = rspmf_of_ra p"

lemma admissible_rel_rspmf_of_ra:
  "ccpo.admissible (prod_lub lub_spmf lub_ra) (rel_prod (ord_spmf (=)) ord_ra) (case_prod rel_rspmf_of_ra)"
  (is "ccpo.admissible ?lub ?ord ?P")
proof (rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and R: "\<forall>(p, q) \<in> Y. rel_rspmf_of_ra p q"
  from R have R: "\<And>p q. (p, q) \<in> Y \<Longrightarrow> rel_rspmf_of_ra p q" by auto
  have chain1: "Complete_Partial_Order.chain (ord_spmf (=)) (fst ` Y)"
    and chain2: "Complete_Partial_Order.chain ord_ra (snd ` Y)"
    using chain by(rule chain_imageI; clarsimp)+
  from Y have Y1: "fst ` Y \<noteq> {}" and Y2: "snd ` Y \<noteq> {}" by auto
 
  have "lub_spmf (fst ` Y) = lub_spmf (rspmf_of_ra ` snd ` Y)"
    unfolding image_image using R
    by (intro arg_cong[of _ _ lub_spmf] image_cong) (auto simp: rel_rspmf_of_ra_def)
  also have "\<dots> = rspmf_of_ra (lub_ra (snd ` Y))"
    by (intro rspmf_of_ra_lub[symmetric] chain2)
  finally have "rel_rspmf_of_ra (lub_spmf (fst ` Y)) (lub_ra (snd ` Y))"
    unfolding rel_rspmf_of_ra_def .
  then show "?P (?lub Y)"
    by (simp add: prod_lub_def)
qed

lemma admissible_rel_rspmf_of_ra_cont [cont_intro]:
  fixes ord
  shows "\<lbrakk> mcont lub ord lub_spmf (ord_spmf (=)) f; mcont lub ord lub_ra ord_ra g \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. rel_rspmf_of_ra (f x) (g x))"
  by (rule admissible_subst[OF admissible_rel_rspmf_of_ra, where f="\<lambda>x. (f x, g x)", simplified]) 
     (rule mcont_Pair)

lemma mcont_rspmf_of_ra:
  "mcont lub_ra ord_ra lub_spmf (ord_spmf (=)) rspmf_of_ra"
  unfolding mcont_def monotone_def cont_def
  by (auto simp: rspmf_of_ra_mono rspmf_of_ra_lub)

lemmas mcont2mcont_rspmf_of_ra = mcont_rspmf_of_ra[THEN spmf.mcont2mcont]

context includes lifting_syntax
begin

lemma fixp_rel_rspmf_of_ra_parametric[transfer_rule]:
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_ra (\<lambda>f. G f x)"
  and param: "((A ===> rel_rspmf_of_ra) ===> A ===> rel_rspmf_of_ra) F G"
  shows "(A ===> rel_rspmf_of_ra) (spmf.fixp_fun F) (random_alg_pf.fixp_fun G)"
  using f g 
proof(rule parallel_fixp_induct_1_1[OF 
      partial_function_definitions_spmf random_alg_pfd _ _ reflexive reflexive, 
        where P="(A ===> rel_rspmf_of_ra)"])
  show "ccpo.admissible (prod_lub (fun_lub lub_spmf) (fun_lub lub_ra)) 
        (rel_prod (fun_ord (ord_spmf (=))) (fun_ord ord_ra)) 
        (\<lambda>x. (A ===> rel_rspmf_of_ra) (fst x) (snd x))"
    unfolding rel_fun_def 
    by(rule admissible_all admissible_imp cont_intro)+
  have 0:"rspmf_of_ra (lub_ra {}) = return_pmf None"
    using rspmf_of_ra_lub[where A="{}"]
    by (simp add:Complete_Partial_Order.chain_def)
  show "(A ===> rel_rspmf_of_ra) (\<lambda>_. lub_spmf {}) (\<lambda>_. lub_ra {})"
    by (auto simp: rel_fun_def rel_rspmf_of_ra_def 0) 
  show "(A ===> rel_rspmf_of_ra) (F f) (G g)" if "(A ===> rel_rspmf_of_ra) f g" for f g
    using that by(rule rel_funD[OF param])
qed

lemma return_ra_tranfer[transfer_rule]: "((=) ===> rel_rspmf_of_ra) return_rspmf return_ra"
  unfolding rel_fun_def rel_rspmf_of_ra_def rspmf_of_ra_return by simp

lemma bind_ra_tranfer[transfer_rule]:
  "(rel_rspmf_of_ra ===> ((=) ===> rel_rspmf_of_ra) ===> rel_rspmf_of_ra) bind_rspmf bind_ra"
  unfolding rel_fun_def rel_rspmf_of_ra_def rspmf_of_ra_bind by simp presburger

lemma coin_ra_tranfer[transfer_rule]: 
  "rel_rspmf_of_ra coin_rspmf coin_ra"
  unfolding rel_fun_def rel_rspmf_of_ra_def rspmf_of_ra_coin by simp

end

lemma spmf_of_rspmf:
  "result (rspmf_of_ra f) = spmf_of_ra f"
  unfolding rspmf_of_ra_def result_def 
  by (simp add: untrack_coin_use spmf_of_ra_map_ra[symmetric])

lemma consumption_correct:
  "consumption (rspmf_of_ra p) = map_pmf (case_option \<infinity> enat) (track_ra p)" (is "?L = ?R")
proof -
  let ?p = "Rep_random_alg p"

  have "measure_pmf (map_spmf snd (rspmf_of_ra p)) =
    distr (measure_rm (track_random_bits ?p)) \<D> (map_option snd)"
    unfolding rspmf_of_ra_def map_pmf_rep_eq spmf_of_ra.rep_eq comp_def track_coin_use.rep_eq 
    by simp
  also have "... = distr \<B> \<D> (map_option snd \<circ> (map_option fst \<circ> track_random_bits ?p))"
    unfolding measure_rm_def 
    by (intro distr_distr measure_rm_measurable wf_track_random_bits rep_rand_alg) simp 
  also have "... = distr \<B> \<D> (\<lambda>x. ?p x \<bind> (\<lambda>xa. consumed_bits ?p x))"
    unfolding track_random_bits_def by (simp add:comp_def map_option_bind case_prod_beta)
  also have "... = distr \<B> \<D> (\<lambda>x. consumed_bits ?p x)"
    by (intro arg_cong[where f="distr \<B> \<D>"] ext)
     (auto simp:consumed_bits_inf_iff[OF rep_rand_alg] split:bind_split)
  also have "... = measure_pmf (track_ra p)"
    unfolding track_ra.rep_eq track_rm_def by simp
  finally have "measure_pmf (map_spmf snd (rspmf_of_ra p)) = measure_pmf (track_ra p)"
    by simp
  hence 0:"map_spmf snd (rspmf_of_ra p) = track_ra p"
    using measure_pmf_inject by auto
  show ?thesis
    unfolding consumption_def 0[symmetric] map_pmf_comp 
    by (intro map_pmf_cong) (auto split:option.split)
qed

end