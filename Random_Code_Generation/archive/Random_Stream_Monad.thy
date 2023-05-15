theory Random_Stream_Monad
  imports 
    "HOL-Library.Stream" 
    "HOL-Library.While_Combinator"
    "HOL-Library.Log_Nat" 
    "HOL-Probability.Stream_Space" 
    "HOL-Probability.Probability_Mass_Function"
    "HOL-Probability.Giry_Monad"
begin

text \<open>Abbreviation for the discrete $\sigma$-algebra. (Do not use, if the measure is important.)\<close>

abbreviation discrete where "discrete \<equiv> count_space UNIV"

text \<open>Preliminary measure theoretic results:\<close>

lemma (in sigma_finite_measure) restrict_space_pair_lift: 
  assumes "A' \<in> sets A"
  shows "restrict_space A A' \<Otimes>\<^sub>M M = restrict_space (A \<Otimes>\<^sub>M M) (A' \<times> space M)" (is "?L = ?R")
proof -
  let ?X = "((\<inter>) (A' \<times> space M) ` {a \<times> b |a b. a \<in> sets A \<and> b \<in> sets M})"
  have 0: "A' \<subseteq> space A"
    using assms sets.sets_into_space by blast

  have "?X \<subseteq> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
  proof (rule image_subsetI)
    fix x assume "x \<in> {a \<times> b |a b. a \<in> sets A \<and> b \<in> sets M}"
    then obtain u v where uv_def: "x = u \<times> v" "u \<in> sets A" "v \<in> sets M"
      by auto
    have 8:"u \<inter> A' \<in> sets (restrict_space A A')" 
      using uv_def(2) unfolding sets_restrict_space by auto
    have "v \<subseteq> space M"
      using uv_def(3) sets.sets_into_space by auto
    hence "A' \<times> space M \<inter> x = (u \<inter> A') \<times> v"
      unfolding uv_def(1) by auto
    also have "... \<in> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
      using 8 uv_def(3) by auto

    finally show "A' \<times> space M \<inter> x \<in> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
      by simp
  qed
  moreover have "{a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M} \<subseteq> ?X"
  proof (rule subsetI)
    fix x assume "x \<in> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
    then obtain u v where uv_def: "x = u \<times> v" "u \<in> sets (restrict_space A A')" "v \<in> sets M"
      by auto

    have "x = (A' \<times> space M) \<inter> x"
      unfolding uv_def(1) using uv_def(2,3) sets.sets_into_space
      by (intro Int_absorb1[symmetric]) (auto simp add:sets_restrict_space)
    moreover have "u \<in> sets A" using uv_def(2) assms unfolding sets_restrict_space by blast
    hence "x \<in> {a \<times> b |a b. a \<in> sets A \<and> b \<in> sets M}"
      unfolding uv_def(1) using uv_def(3) by auto
    ultimately show "x \<in> ?X" 
      by simp
  qed
  ultimately have 1: "?X = {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}" by simp

  have "sets ?R = sigma_sets (A'\<times>space M) ((\<inter>) (A'\<times>space M) ` {a\<times>b |a b. a \<in> sets A\<and>b \<in> sets M})"
    unfolding sets_restrict_space sets_pair_measure using assms  sets.sets_into_space
    by (intro sigma_sets_Int sigma_sets.Basic) auto
  also have "... = sets (restrict_space A A' \<Otimes>\<^sub>M M)"
    unfolding sets_pair_measure space_restrict_space Int_absorb2[OF 0] sets_restrict_space 1
    by auto
  finally have 2:"sets (restrict_space (A \<Otimes>\<^sub>M M) (A' \<times> space M)) = sets (restrict_space A A' \<Otimes>\<^sub>M M)"
    by simp

  have 3: "emeasure (restrict_space A A'\<Otimes>\<^sub>MM) S = emeasure (restrict_space (A\<Otimes>\<^sub>MM) (A'\<times>space M)) S"
    (is "?L1 = ?R1") if 4:"S \<in> sets (restrict_space A A' \<Otimes>\<^sub>M M)" for S
  proof -
    have "Pair x -` S = {}" if "x \<notin> A'" "x \<in> space A" for x
      using that 4 by (auto simp add:2[symmetric] sets_restrict_space)
    hence 5: "emeasure M (Pair x -` S) = 0" if "x \<notin> A'" "x \<in> space A" for x
      using that by auto
    have "?L1 = (\<integral>\<^sup>+ x. emeasure M (Pair x -` S) \<partial>restrict_space A A')"
      by (intro emeasure_pair_measure_alt[OF that]) 
    also have "... = (\<integral>\<^sup>+x\<in>A'. emeasure M (Pair x -` S) \<partial>A)"
      using assms by (intro nn_integral_restrict_space) auto
    also have "... = (\<integral>\<^sup>+x. emeasure M (Pair x -` S) \<partial>A)"
      using 5 by (intro nn_integral_cong) force
    also have "... = emeasure (A \<Otimes>\<^sub>M M) S"
      using that assms by (intro emeasure_pair_measure_alt[symmetric]) 
        (auto simp add:2[symmetric] sets_restrict_space) 
    also have "... = ?R1"
      using assms that by (intro emeasure_restrict_space[symmetric]) 
        (auto simp add:2[symmetric] sets_restrict_space)
    finally show ?thesis by simp
  qed

  show ?thesis using 2 3
    by (intro measure_eqI) auto 
qed

lemma pair_prob_spaceI:
  assumes "prob_space M" "prob_space N"
  shows "pair_prob_space M N"
  using assms 
  by (simp add: pair_prob_space.intro pair_sigma_finite_def prob_space_imp_sigma_finite)

text \<open>
  The following is highly experimental.

  It probably makes sense to abstract over the stream type, or use a more general interface
  for randomness sources.
\<close>

type_synonym 'a random_monad = "bool stream \<Rightarrow> 'a \<times> bool stream"

definition rm_return :: "'a \<Rightarrow> 'a random_monad"
  where "rm_return x f = (x, f)"

definition rm_bind :: "'a random_monad \<Rightarrow> ('a \<Rightarrow> 'b random_monad) \<Rightarrow> 'b random_monad"
  where "rm_bind x y f = case_prod y (x f)"

adhoc_overloading Monad_Syntax.bind rm_bind

definition rm_coin :: "bool random_monad"
  where "rm_coin f = (shd f, stl f)"

definition coin :: "bool pmf"
  where "coin = pmf_of_set UNIV"

definition coin_space :: "bool stream measure"
  where "coin_space = stream_space (measure_pmf (pmf_of_set UNIV))"

lemma coin_space: "prob_space coin_space"
  unfolding coin_space_def
  by (intro prob_space.prob_space_stream_space prob_space_measure_pmf)

lemma space_coin_space: "space coin_space = UNIV"
  unfolding coin_space_def space_stream_space by simp

text \<open>This is the relation expressing that a randomized algorithm is a sampler for a given pmf.\<close>

definition sampler_for where
  "sampler_for r m = (                  
    distr coin_space (discrete \<Otimes>\<^sub>M coin_space) r = measure_pmf m \<Otimes>\<^sub>M coin_space \<and>
    r \<in> coin_space \<rightarrow>\<^sub>M discrete \<Otimes>\<^sub>M coin_space \<and> countable (range (fst \<circ> r)))"

lemma rm_range_intro:
  assumes "sampler_for r m"
  assumes "x \<in> set_pmf m"
  shows "x \<in> range (fst \<circ> r)"
proof (rule ccontr)
  assume "x \<notin> range (fst \<circ> r)"
  hence "False " if  "y \<in> r -` ({x} \<times> UNIV)" for y
    by (metis rangeI set.compositionality that vimage_fst vimage_singleton_eq)
  hence a:"r -` ({x} \<times> UNIV) = {}"
    by blast

  have "0 < emeasure (measure_pmf m) {x} * 1"
    using assms(2) by (simp add: emeasure_pmf_single_eq_zero_iff order_less_le)
  also have "... = emeasure (measure_pmf m) {x} * emeasure (coin_space) (space coin_space)"
    using coin_space
    by (intro arg_cong2[where f="(*)"] refl prob_space.emeasure_space_1[symmetric]) 
  also have "... = emeasure (measure_pmf m \<Otimes>\<^sub>M coin_space) ({x} \<times> space coin_space)" 
    using prob_space_imp_sigma_finite[OF coin_space] 
    by (intro sigma_finite_measure.emeasure_pair_measure_Times[symmetric]) simp_all
  also have "... = emeasure (distr coin_space (discrete \<Otimes>\<^sub>M coin_space) r) ({x} \<times> space coin_space)"
    using assms(1) unfolding sampler_for_def by simp
  also have "... = emeasure coin_space (r -` ({x} \<times> space coin_space) \<inter> space coin_space)"
    using assms(1) unfolding sampler_for_def by (intro emeasure_distr pair_measureI) auto
  also have "... = emeasure coin_space {}"
    using a by (intro arg_cong2[where f="emeasure"]) auto 
  also have "... = 0"
    by simp
  finally show "False" by simp
qed

lemma sampler_for_bind:
  assumes "sampler_for f' f"  (* TODO: Rename args r for randomized algorith, m for measure *)
  assumes "\<And>x. x \<in> range (fst \<circ> f') \<Longrightarrow> sampler_for (g' x) (g x)" 
  shows "sampler_for (rm_bind f' g') (f \<bind> g) "
proof -
  let ?M = "measure_pmf f"
  let ?N = "\<lambda>x. measure_pmf (g x)"
  let ?C = "coin_space"
  let ?D = "discrete"
  let ?R = "restrict_space ?M (range (fst \<circ> f'))"

  have m_g: "case_prod g' \<in> ?R \<Otimes>\<^sub>M ?C \<rightarrow>\<^sub>M ?D \<Otimes>\<^sub>M ?C"
    using assms unfolding sampler_for_def
    by (intro measurable_pair_restrict_pmf1) simp_all

  have "g \<in> ?R \<rightarrow>\<^sub>M ?D"
    by (intro measurable_restrict_space1) simp
  hence m_g_2: "(\<lambda>x. measure_pmf (g x)) \<in> ?R \<rightarrow>\<^sub>M subprob_algebra discrete"
    by measurable

  have 3:"x \<in> range (fst \<circ> f')" if "x \<in> set_pmf f" for x
    using rm_range_intro[OF assms(1) that] by simp

  have 2:"prob_space ?R" using 3 
    by (intro Probability_Measure.prob_space_restrict_space measure_pmf.emeasure_eq_1_AE AE_pmfI)
     simp_all 
  hence 0:"prob_space (?R \<bind> ?N)"
    by (intro prob_space.prob_space_bind[where S="discrete"] AE_I2 m_g_2 prob_space_measure_pmf)
      auto

  have m_f_3: "f' x \<in> range (\<lambda>x. fst (f' x)) \<times> space coin_space" for x
    unfolding space_coin_space using vimage_fst by fastforce
  hence m_f: "f' \<in> ?C \<rightarrow>\<^sub>M ?R \<Otimes>\<^sub>M ?C"
    using coin_space prob_space_imp_sigma_finite assms(1) unfolding sampler_for_def
    by (subst sigma_finite_measure.restrict_space_pair_lift)
       (auto intro: measurable_restrict_space2)

  have "f' \<in> coin_space \<rightarrow>\<^sub>M discrete \<Otimes>\<^sub>M coin_space"
    using assms(1) unfolding sampler_for_def by auto
  hence m_f_2: "f' \<in> ?C \<rightarrow>\<^sub>M ?M \<Otimes>\<^sub>M ?C"
    by measurable 

  have "distr ?C (?R \<Otimes>\<^sub>M ?C) f' = distr ?C (restrict_space (?M\<Otimes>\<^sub>M?C) (range (fst\<circ>f')\<times>space ?C)) f'"
    using prob_space_imp_sigma_finite[OF coin_space]
    by (subst sigma_finite_measure.restrict_space_pair_lift) auto 
  also have "... = restrict_space (distr ?C (?M \<Otimes>\<^sub>M ?C) f') (range (fst \<circ> f') \<times> space coin_space)"
    using m_f_2 m_f_3 
    by (intro restrict_distr[symmetric]) (simp_all add: Pi_def)
  also have "... = restrict_space (distr ?C (?D \<Otimes>\<^sub>M ?C) f') (range (fst \<circ> f') \<times> space coin_space)"
    by (intro arg_cong2[where f="restrict_space"] distr_cong refl) (simp add:sets_pair_measure)
  also have "... = restrict_space (?M \<Otimes>\<^sub>M ?C) (range (fst \<circ> f') \<times> space coin_space)"
    using assms(1) unfolding sampler_for_def by simp
  also have "... = ?R \<Otimes>\<^sub>M ?C"
    using prob_space_imp_sigma_finite[OF coin_space]
    by (intro sigma_finite_measure.restrict_space_pair_lift[symmetric]) simp_all
  finally have 1: "distr ?C (?R \<Otimes>\<^sub>M ?C) f' = ?R \<Otimes>\<^sub>M ?C"
    by simp

  have "distr ?C (?D \<Otimes>\<^sub>M ?C) (rm_bind f' g') = distr ?C (?D \<Otimes>\<^sub>M ?C) (\<lambda>\<omega>. case_prod g' (f' \<omega>))"
    unfolding rm_bind_def by simp
  also have "... =  distr (distr ?C (?R \<Otimes>\<^sub>M ?C) f') (?D \<Otimes>\<^sub>M ?C) (case_prod g')"
    using m_g m_f by (subst distr_distr) (simp_all add:comp_def)
  also have "... = distr (?R \<Otimes>\<^sub>M ?C) (?D \<Otimes>\<^sub>M ?C) (case_prod g')"
    unfolding 1 by simp
  also have "... = distr (?R \<bind> (\<lambda>x. ?C \<bind> (\<lambda>\<omega>. return(?R\<Otimes>\<^sub>M?C) (x,\<omega>)))) (?D\<Otimes>\<^sub>M?C) (case_prod g')"
    using pair_prob_spaceI[OF 2 coin_space]
    by (subst pair_prob_space.pair_measure_eq_bind) simp_all
  also have "... = ?R \<bind>(\<lambda>x. distr(?C \<bind>(\<lambda>\<omega>. return(?R\<Otimes>\<^sub>M?C)(x, \<omega>)))(?D \<Otimes>\<^sub>M ?C)(\<lambda>(x, y). g' x y))"
    using prob_space_imp_subprob_space[OF coin_space] 
    by (intro distr_bind[where K="?R \<Otimes>\<^sub>M ?C"] m_g measurable_bind[where N="?C"] measurable_const)
       (simp_all add:space_subprob_algebra)
  also have "... =?R \<bind>(\<lambda>x.?C \<bind>(\<lambda>y. distr (return(?R\<Otimes>\<^sub>M?C)(x, y))(?D \<Otimes>\<^sub>M ?C)(\<lambda>(x, y). g' x y)))"
    using m_g
    by (intro bind_cong ext distr_bind[where K="?R \<Otimes>\<^sub>M ?C"] refl) (simp_all add:space_coin_space)
  also have "... =?R \<bind> (\<lambda>x. ?C \<bind> (\<lambda>y. return (?D \<Otimes>\<^sub>M ?C) (case (x, y) of (x, y) \<Rightarrow> g' x y))) "
    using m_g
    by (intro bind_cong distr_return) (simp_all add:space_restrict_space space_pair_measure) 
  also have "... = ?R \<bind> (\<lambda>x. ?C \<bind> (\<lambda>y. return (?D \<Otimes>\<^sub>M ?C) (g' x y)))"
    by simp
  also have "... = ?R \<bind> (\<lambda>x. distr ?C (?D \<Otimes>\<^sub>M ?C) (g' x))"
    using assms(2) unfolding sampler_for_def
    by (intro bind_cong bind_return_distr' refl) (simp_all add:space_coin_space)
  also have "... = ?R \<bind> (\<lambda>x. ?N x \<Otimes>\<^sub>M ?C)"
    using assms(2) unfolding sampler_for_def
    by (intro bind_cong refl) simp
  also have "... = ?R \<bind> (\<lambda>x. ?N x \<bind> (\<lambda>y. ?C \<bind> (\<lambda>\<omega>. return (?N x \<Otimes>\<^sub>M ?C) (y,\<omega>))))"
   using coin_space prob_space_measure_pmf by (intro arg_cong2[where f="bind"] 
     pair_prob_space.pair_measure_eq_bind ext pair_prob_space.intro)
     (auto simp add: pair_sigma_finite.intro prob_space_imp_sigma_finite)
  also have "... = ?R \<bind> (\<lambda>x. ?N x \<bind> (\<lambda>y. ?C \<bind> (\<lambda>\<omega>. return (?D \<Otimes>\<^sub>M ?C) (y,\<omega>))))"
    by (intro arg_cong2[where f="bind"] ext refl return_cong sets_pair_measure_cong) simp
  also have "... = (?R \<bind> ?N) \<bind> (\<lambda>y. ?C \<bind> (\<lambda>\<omega>. return (?D \<Otimes>\<^sub>M ?C) (y, \<omega>)))"
    using prob_space_imp_subprob_space[OF coin_space]
    by (intro bind_assoc[symmetric, where N="discrete" and R="discrete \<Otimes>\<^sub>M coin_space"] m_g_2)
      (auto intro!:subprob_space.bind_in_space simp add:Pi_def)
  also have "... = (?R \<bind> ?N) \<bind> (\<lambda>y. ?C \<bind> (\<lambda>\<omega>. return ((?R \<bind> ?N) \<Otimes>\<^sub>M ?C) (y, \<omega>)))"
    by (intro arg_cong2[where f="bind"] ext refl return_cong sets_pair_measure_cong) auto
  also have "... = (?R \<bind> ?N) \<Otimes>\<^sub>M ?C"
    using pair_prob_spaceI[OF 0 coin_space] 
    by (subst (2) pair_prob_space.pair_measure_eq_bind) simp_all
  also have "... = (?M \<bind> (\<lambda>x. if x \<in> range (fst \<circ> f') then ?N x else 
    null_measure (measure_pmf (g (SOME x. x \<in> range (fst \<circ> f') \<and> x \<in> space ?M))))) \<Otimes>\<^sub>M ?C"
    using m_g_2 by (subst bind_restrict_space[where N="discrete"]) auto
  also have "... = (?M \<bind> ?N)  \<Otimes>\<^sub>M ?C"
    using 3 by (intro bind_cong_AE[where B="discrete"] arg_cong2[where f="(\<Otimes>\<^sub>M)"] refl AE_pmfI)
      (simp_all add:space_subprob_algebra Pi_def subprob_spaceI)+
  also have "... = measure_pmf (bind_pmf f g) \<Otimes>\<^sub>M coin_space"
    unfolding measure_pmf_bind by simp
  finally have 4:"distr coin_space (?D \<Otimes>\<^sub>M ?C) (rm_bind f' g') = measure_pmf (bind_pmf f g) \<Otimes>\<^sub>M ?C"
    by simp

  have 5:"(\<lambda>\<omega>. rm_bind f' g' \<omega>) \<in> ?C \<rightarrow>\<^sub>M (?D \<Otimes>\<^sub>M ?C)"
    using m_f m_g unfolding rm_bind_def by simp

  have "range (fst \<circ> rm_bind f' g') = range (\<lambda>x. fst (g' (fst (f' x)) (snd (f' x))))"
    unfolding rm_bind_def by (simp add:case_prod_beta)
  also have "... \<subseteq> (\<Union>x \<in> range (fst \<circ> f'). range (fst \<circ> g' x))"
    by (intro subsetI) auto
  finally have "range (fst \<circ> rm_bind f' g') \<subseteq> (\<Union>x \<in> range (fst \<circ> f'). range (fst \<circ> g' x))"
    by simp
  moreover have "countable (\<Union>x \<in> range (fst \<circ> f'). range (fst \<circ> g' x))"
    using assms unfolding sampler_for_def by (intro countable_UN) auto

  ultimately have 6:"countable (range (fst \<circ> rm_bind f' g'))"
    using countable_subset by auto

  show ?thesis using 4 5 6
    unfolding sampler_for_def by blast
qed

lemma sampler_for_coin: "sampler_for rm_coin coin"
proof -
  let ?C = "coin_space"
  let ?D = "discrete"
  let ?M = "measure_pmf (pmf_of_set (UNIV :: bool set))"

  have "emeasure (distr ?C (?D \<Otimes>\<^sub>M ?C) rm_coin) A = emeasure (measure_pmf coin \<Otimes>\<^sub>M ?C) A"
    (is "?L = ?R") if "A \<in> sets (distr ?C (?D \<Otimes>\<^sub>M ?C) rm_coin)" for A
  proof -
    have "A \<in> sets (?D \<Otimes>\<^sub>M ?C)" 
      using that by simp 
    moreover have "(\<lambda>x. (shd x, stl x)) \<in> ?C \<rightarrow>\<^sub>M ?D \<Otimes>\<^sub>M ?C"
      unfolding coin_space_def by simp
    ultimately have 0: "{x. (shd x, stl x) \<in> A} \<in> sets ?C"
      unfolding measurable_def space_coin_space vimage_def by auto

    have "?L = emeasure ?C (rm_coin -` A \<inter> space ?C)"
      using that unfolding rm_coin_def coin_space_def by (subst emeasure_distr) simp_all
    also have "... = emeasure ?C {x. (shd x, stl x) \<in> A}"
      unfolding rm_coin_def vimage_def space_coin_space by simp
    also have "... = \<integral>\<^sup>+ t. emeasure ?C {x \<in> space ?C. t ## x \<in> {x. (shd x, stl x) \<in> A}} \<partial>?M"
      using 0 unfolding coin_space_def
      by (intro prob_space.emeasure_stream_space prob_space_measure_pmf) simp
    also have "... = \<integral>\<^sup>+ t. emeasure ?C {x. (t,x) \<in> A} \<partial>?M"
      unfolding space_coin_space by simp
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space (Pair x -` A) \<partial>measure_pmf coin"
      unfolding coin_def vimage_def by simp
    also have "... = ?R"
      using prob_space_imp_sigma_finite[OF coin_space] that
      by (intro sigma_finite_measure.emeasure_pair_measure_alt[symmetric]) simp_all
    finally show ?thesis 
      by simp
  qed
  hence "distr ?C (?D \<Otimes>\<^sub>M ?C) rm_coin = measure_pmf coin \<Otimes>\<^sub>M ?C"
    by (intro measure_eqI) (auto simp add:sets_pair_measure)

  thus ?thesis
    unfolding sampler_for_def coin_space_def rm_coin_def by simp
qed

lemma sampler_for_return: "sampler_for (rm_return x) (return_pmf x) "
proof -
  let ?C = "coin_space"
  let ?D = "discrete"

  have "emeasure (distr ?C (?D \<Otimes>\<^sub>M ?C) (Pair x)) A = emeasure (measure_pmf (return_pmf x) \<Otimes>\<^sub>M ?C) A"
    (is "?L = ?R") if "A \<in> sets (distr ?C (?D \<Otimes>\<^sub>M ?C) (Pair x))" for A
  proof -
    have "?L = emeasure ?C (Pair x -` A \<inter> space ?C)"
      using that by (intro emeasure_distr) simp_all
    also have "... = \<integral>\<^sup>+ x. emeasure ?C (Pair x -` A) \<partial>measure_pmf (return_pmf x)"
      unfolding space_coin_space by simp
    also have "... = ?R"
      using prob_space_imp_sigma_finite[OF coin_space] that
      by (intro sigma_finite_measure.emeasure_pair_measure_alt[symmetric]) simp_all
    finally show ?thesis
      by simp
  qed
  hence "distr coin_space (?D \<Otimes>\<^sub>M ?C) (Pair x) = measure_pmf (return_pmf x) \<Otimes>\<^sub>M ?C"
    by (intro measure_eqI)  (simp_all add:sets_pair_measure)
  thus ?thesis
    unfolding sampler_for_def rm_return_def by simp
qed

lemmas sampler_for_simps = sampler_for_return sampler_for_bind sampler_for_coin

subsection \<open>Sampler for numbers in {0..<2^n}\<close>

fun rm_uniform_pow :: "nat \<Rightarrow> nat random_monad"
  where 
    "rm_uniform_pow 0 = rm_return 0" | 
    "rm_uniform_pow (Suc n) = 
      do {
        x \<leftarrow> rm_uniform_pow n;
        y \<leftarrow> rm_coin;
        rm_return (of_bool y + 2*x)
      }"

fun pmf_uniform_pow :: "nat \<Rightarrow> nat pmf"
  where 
    "pmf_uniform_pow 0 = return_pmf 0" | 
    "pmf_uniform_pow (Suc n) = 
      do {
        x \<leftarrow> pmf_uniform_pow n;
        y \<leftarrow> coin;
        return_pmf (of_bool y + 2*x)
      }"

lemma "sampler_for (rm_uniform_pow n) (pmf_uniform_pow n)"
  by (induction n) (simp_all add:sampler_for_simps)

text \<open>Sampler for pmf_of_set {0..n} *inclusive*\<close>

function rm_uniform :: "nat \<Rightarrow> nat random_monad"
  where "rm_uniform n = 
    do {
      x \<leftarrow> rm_uniform_pow (floorlog 2 n);
      if x \<le> n then rm_return x else rm_uniform n
    }"
    by pat_completeness auto

(* TODO: Write this using the while combinator or a counter-part of it in the random_monad, the
above variant does not allow code-gen. *)

end