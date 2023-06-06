theory Coin_Space
  imports 
    "HOL-Probability.Probability" 
begin

text \<open>Stream version of @{term "prefix"}\<close>

definition sprefix where "sprefix xs ys = (stake (length xs) ys = xs)"

lemma sprefix_iff: "sprefix x y \<longleftrightarrow> (\<forall>i < length x. y !! i = x ! i)" (is "?L \<longleftrightarrow> ?R")
proof -
  have "?L \<longleftrightarrow> stake (length x) y = x"
    unfolding sprefix_def by simp
  also have "... \<longleftrightarrow> (\<forall>i < length x . (stake (length x) y) ! i = x ! i)"
    by (simp add: list_eq_iff_nth_eq)
  also have "... \<longleftrightarrow> ?R"
    by (intro all_cong) simp
  finally show ?thesis by simp
qed

text \<open>Stream version of @{thm [source] prefix_length_prefix}\<close>

lemma sprefix_length_prefix:
  assumes "length x \<le> length y"
  assumes "sprefix x bs" "sprefix y bs"
  shows "prefix x y"
proof -
  have "take (length x) y = take (length x) (stake (length y) bs)"
    using assms(3) unfolding sprefix_def by simp
  also have "... = stake (length x) bs"
    unfolding take_stake using assms by simp
  also have "... = x"
    using assms(2) unfolding sprefix_def by simp
  finally have "take (length x) y = x"
    by simp
  thus ?thesis
    by (metis take_is_prefix)
qed

lemma same_prefix_not_parallel:
  assumes "sprefix x bs" "sprefix y bs"
  shows "\<not>(x \<parallel> y)"
  using assms sprefix_length_prefix
  by (cases "length x \<le> length y") auto

text \<open>A non-empty shift is not idempotent:\<close>

lemma empty_if_shift_idem:
  fixes h :: "bool list"
  assumes "\<And>cs. h@- cs = cs"
  shows "h = []"
proof (cases h)
  case Nil
  then show ?thesis by simp
next
  case (Cons hh ht)
  have "[hh] = stake 1 ((hh#ht) @- sconst (\<not> hh))"
    by simp
  also have "... = stake 1 (sconst (\<not> hh))"
    using assms unfolding Cons by simp
  also have "... = [\<not> hh]" by simp
  finally show ?thesis by simp
qed

lemma stake_shift:
  "stake m (xs @- ys) = (if m \<le> length xs then take m xs else xs @ stake (m - length xs) ys)"
proof (induction m arbitrary: xs)
  case (Suc m xs)
  thus ?case
    by (cases xs) auto
qed auto

lemma stake_shift_small [simp]: "m \<le> length xs \<Longrightarrow> stake m (xs @- ys) = take m xs"
  and stake_shift_big [simp]: "m \<ge> length xs \<Longrightarrow> stake m (xs @- ys) = xs @ stake (m - length xs) ys"
  by (subst stake_shift; simp)+

lemma sdrop_shift:
  "sdrop m (xs @- ys) = (if m \<le> length xs then drop m xs @- ys else sdrop (m - length xs) ys)"
proof (induction m arbitrary: xs)
  case (Suc m xs)
  thus ?case
    by (cases xs) auto
qed auto

lemma sdrop_shift_small [simp]: "m \<le> length xs \<Longrightarrow> sdrop m (xs @- ys) = drop m xs @- ys"
  and sdrop_shift_big [simp]: "m \<ge> length xs \<Longrightarrow> sdrop m (xs @- ys) = sdrop (m - length xs) ys"
  by (subst sdrop_shift; simp)+

lemma map_prod_measurable[measurable]:
  assumes "f \<in> M \<rightarrow>\<^sub>M M'"
  assumes "g \<in> N \<rightarrow>\<^sub>M N'"
  shows "map_prod f g \<in> M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M M' \<Otimes>\<^sub>M N'"
  using assms by (subst measurable_pair_iff) simp

lemma measurable_sigma_sets_with_exception:
  fixes f :: "'a \<Rightarrow> 'b :: countable" 
  assumes "\<And>x. x \<noteq> d \<Longrightarrow> f -` {x} \<inter> space M \<in> sets M"
  shows "f \<in> M \<rightarrow>\<^sub>M count_space UNIV"
proof -
  define A :: "'b set set" where "A = (\<lambda>x. {x}) ` UNIV"

  have 0: "sets (count_space UNIV) = sigma_sets (UNIV :: 'b set) A"
    unfolding A_def by (subst sigma_sets_singletons) auto

  have 1: "f -` {x} \<inter> space M \<in> sets M" for x
  proof (cases "x = d")
    case True
    have "f -` {d} \<inter> space M = space M - (\<Union>y \<in> UNIV - {d}. f -` {y} \<inter> space M)"
      by (auto simp add:set_eq_iff)
    also have "... \<in> sets M"
      using assms
      by (intro sets.compl_sets sets.countable_UN) auto
    finally show ?thesis 
      using True by simp
  next
    case False
    then show ?thesis using assms by simp
  qed
  hence 1: "\<And>y. y \<in> A \<Longrightarrow> f -` y \<inter> space M \<in> sets M"
    unfolding A_def by auto

  thus ?thesis
    by (intro measurable_sigma_sets[OF 0]) simp_all
qed

lemma restr_empty_eq: "restrict_space M {} = restrict_space N {}"
  by (intro measure_eqI) (auto simp add:sets_restrict_space)

lemma (in sigma_finite_measure) restrict_space_pair_lift':
  assumes "sigma_finite_measure A"
  assumes "A' \<in> sets A"
  shows "restrict_space A A' \<Otimes>\<^sub>M M = restrict_space (A \<Otimes>\<^sub>M M) (A' \<times> space M)" (is "?L = ?R")
proof -



  show ?thesis
    apply (intro pair_measure_eqI)
    sorry
qed

lemma (in prob_space) distr_stream_space_snth [simp]:
  assumes "sets M = sets N"
  shows   "distr (stream_space M) N (\<lambda>xs. snth xs n) = M"
proof -
  have "distr (stream_space M) N (\<lambda>xs. snth xs n) = distr (stream_space M) M (\<lambda>xs. snth xs n)"
    by (rule distr_cong) (use assms in auto)
  also have "\<dots> = distr (Pi\<^sub>M UNIV (\<lambda>i. M)) M (\<lambda>f. f n)"
    by (subst stream_space_eq_distr, subst distr_distr) (auto simp: to_stream_def o_def)
  also have "\<dots> = M"
    by (intro distr_PiM_component prob_space_axioms) auto
  finally show ?thesis .
qed

lemma (in prob_space) distr_stream_space_shd [simp]:
  assumes "sets M = sets N"
  shows   "distr (stream_space M) N shd = M"
  using distr_stream_space_snth[OF assms, of 0] by (simp del: distr_stream_space_snth)

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



text \<open>Measure spaces and notation for them:\<close>

abbreviation discrete_sigma_algebra 
  where "discrete_sigma_algebra \<equiv> count_space UNIV"

definition coin_space :: "bool stream measure"
  where "coin_space = stream_space (measure_pmf (pmf_of_set UNIV))"

bundle random_monad_notation
begin
  notation discrete_sigma_algebra ("\<D>")
  notation coin_space ("\<B>")
end

bundle no_random_monad_notation
begin
  no_notation discrete_sigma_algebra ("\<D>")
  no_notation coin_space ("\<B>")
end

unbundle random_monad_notation

lemma space_coin_space: "space \<B> = UNIV"
  unfolding coin_space_def space_stream_space by simp

interpretation coin_space: prob_space coin_space
  unfolding coin_space_def
  by (intro prob_space.prob_space_stream_space prob_space_measure_pmf)

lemma distr_shd: "distr \<B> \<D> shd = pmf_of_set UNIV"
  using coin_space.distr_stream_space_shd unfolding coin_space_def  by auto

lemma append_measurable:
  "(\<lambda>bs. x @- bs) \<in> \<B> \<rightarrow>\<^sub>M \<B>"
proof -
  have "(\<lambda>bs. (x @- bs) !! n) \<in> coin_space \<rightarrow>\<^sub>M \<D>" for n
  proof (cases "n < length x")
    case True
    have "(\<lambda>bs. (x @- bs) !! n) = (\<lambda>bs. x ! n)"
      using True by simp
    also have "... \<in> coin_space \<rightarrow>\<^sub>M \<D>"
      by simp
    finally show ?thesis by simp
  next
    case False
    have "(\<lambda>bs. (x @- bs) !! n) = (\<lambda>bs. bs !! (n - length x))"
      using False by simp
    also have "... \<in> \<B> \<rightarrow>\<^sub>M (measure_pmf (pmf_of_set UNIV))"
      unfolding coin_space_def by (intro measurable_snth)
    also have "... = \<B> \<rightarrow>\<^sub>M \<D>"
      by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding coin_space_def by (intro measurable_stream_space2) auto
qed

lemma bool_list_set:
  "card {xs :: bool list. length xs = k} = 2^k"
  "{xs :: bool list. length xs = k} \<noteq> {}"
  "finite {xs :: bool list. length xs = k}"
proof -
  have "card {xs :: bool list. length xs = k} = card {xs. set xs \<subseteq> (UNIV::bool set)\<and>length xs = k}"
    by simp
  also have "... = card (UNIV::bool set) ^ k"
    by (intro card_lists_length_eq) auto
  finally show "card {xs :: bool list. length xs = k} = 2^k" by simp
  hence "card {xs :: bool list. length xs = k} \<noteq> 0"
    by simp
  thus "{xs :: bool list. length xs = k} \<noteq> {}" "finite {xs :: bool list. length xs = k}"
    unfolding card_eq_0_iff by auto
qed

lemma split_coin_space:
  "distr (pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M \<B>) \<B> (\<lambda>(x,y). x@-y) = \<B>"
  (is "?L = ?R")
proof (rule measure_eqI)
  show "sets ?L = sets ?R" by simp
next
  fix A assume "A \<in> sets ?L"

  hence a:"A \<in> sets coin_space"
    by simp

  have 0: "(\<lambda>(x, y). x @- y) \<in> pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M coin_space \<rightarrow>\<^sub>M coin_space"
    using append_measurable by measurable

  have 1:"{bs. x @- bs \<in> A} \<in> sets coin_space" for x
    using a append_measurable unfolding measurable_def space_coin_space vimage_def by simp

  have "{x. fst x @- snd x \<in> A} =
    (\<lambda>(x, y). x @- y) -` A \<inter> space (pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M coin_space)"
    unfolding space_pair_measure by (simp add:space_coin_space vimage_def case_prod_beta)
  also have "... \<in> sets (pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M coin_space)"
    by (intro measurable_sets[OF 0] a)
  finally have 2:"{x. fst x @- snd x \<in> A} \<in> sets (pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M coin_space)"
    by simp

  have "emeasure ?L A = emeasure (pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M coin_space){x. fst x@-snd x\<in>A}"
    using 0 a by (subst emeasure_distr)
      (simp_all add:space_pair_measure space_coin_space vimage_def case_prod_beta)
  also have "... =
    \<integral>\<^sup>+ x. emeasure coin_space (Pair x -` {x. fst x @- snd x \<in> A}) \<partial>pmf_of_set {xs. length xs = k}"
    using 2 by (intro coin_space.emeasure_pair_measure_alt)
  also have "... = \<integral>\<^sup>+ x. emeasure coin_space {bs. x @- bs \<in> A} \<partial>pmf_of_set {xs. length xs = k}"
    unfolding vimage_def by simp
  also have "... = (\<Sum>x\<in>set_pmf (pmf_of_set {xs. length xs = k}).
    emeasure coin_space {bs. x @- bs \<in> A} * ennreal (pmf (pmf_of_set {xs. length xs = k}) x))"
    using bool_list_set by (intro nn_integral_measure_pmf_finite) (simp_all)
  also have "... = (\<Sum>xs| length xs = k. emeasure coin_space {bs. xs @- bs \<in> A} * ennreal (1/2^k))"
    using bool_list_set by (intro sum.cong set_pmf_of_set) simp_all
  also have "... = emeasure ?R A"
  proof (induction k)
    case 0
    then show ?case by (simp_all)
  next
    case (Suc k)
    have "length y = Suc k \<Longrightarrow> take k y @ [y ! k] = y" for y :: "bool list"
      by (metis lessI less_eq_Suc_le take_Suc_conv_app_nth take_all)

    hence "(\<Sum>xs | length xs = Suc k. emeasure coin_space {bs. xs @- bs \<in> A}* ennreal (1/2^Suc k))=
      (\<Sum>x|length (fst x)=k. emeasure coin_space {bs. (fst x@[snd x])@-bs\<in>A}*ennreal (1/2^Suc k))"
      by (intro sum.reindex_bij_betw[symmetric] bij_betwI[where g="(\<lambda>x. (take k x, x!k))"]) auto
    also have "... = (\<Sum>xs | length xs = k.
      (\<Sum>x\<in>UNIV. emeasure coin_space {bs. (xs@[x]) @- bs \<in> A} * ennreal ((1/2) * (1/2^k))))"
      unfolding sum.cartesian_product by (intro sum.cong) auto
    also have "... = (\<Sum>xs | length xs = k.
      (\<Sum>x\<in>UNIV. emeasure coin_space {bs. (xs@[x]) @- bs \<in> A}) * inverse 2 * ennreal (1/2^k))"
      by (subst ennreal_mult') (simp_all add:sum_distrib_right sum_distrib_left algebra_simps)
    also have "... = (\<Sum>xs | length xs = k.
      (\<Sum>x\<in>UNIV. emeasure coin_space {xa. xs @- x ## xa \<in> A}) * inverse 2 * ennreal (1 / 2 ^ k))"
      by (intro sum.cong arg_cong2[where f="(*)"] refl arg_cong2[where f="emeasure"]) simp_all
    also have "... = (\<Sum>xs | length xs = k.
      (\<integral>\<^sup>+ t. emeasure coin_space {x. xs @- t ## x \<in> A} \<partial>pmf_of_set UNIV) * ennreal (1 / 2 ^ k))"
      by (subst nn_integral_measure_pmf_finite) (simp_all add:sum_distrib_right)
    also have "... = (\<Sum>xs | length xs = k. (\<integral>\<^sup>+ t. emeasure coin_space {x \<in> space coin_space.
          t ## x \<in> {bs. xs @- bs \<in> A}} \<partial>pmf_of_set UNIV) * ennreal (1 / 2 ^ k))"
      unfolding space_coin_space by simp
    also have "... = (\<Sum>xs|length xs=k. emeasure coin_space {bs. xs @- bs \<in> A} * ennreal (1/2^k))"
      using 1 unfolding coin_space_def by (intro sum.cong arg_cong2[where f="(*)"]
          prob_space.emeasure_stream_space[symmetric] prob_space_measure_pmf refl) auto
    also have "... = emeasure ?R A"
      by (intro Suc)
    finally show ?case by simp
  qed
  finally show "emeasure ?L A = emeasure ?R A"
    by simp
qed

lemma distr_stake:
  "distr \<B> \<D> (stake n) = pmf_of_set {bs. length bs = n}" (is "?L = ?R")
proof -
  have 1: "stake n \<in> coin_space \<rightarrow>\<^sub>M \<D>"
    unfolding coin_space_def by simp

  have "{x \<in> space (?R \<Otimes>\<^sub>M coin_space). (stake n \<circ> (\<lambda>(x, y). x @- y)) x = fst x} =
    (\<lambda>(x,y). stake n (x @- y) = x) -` {True} \<inter> space (?R \<Otimes>\<^sub>M coin_space)"
    by (auto simp add:set_eq_iff comp_def)
  also have "... \<in> sets (?R \<Otimes>\<^sub>M coin_space)"
    using append_measurable 1 by (intro measurable_sets[where A="\<D>"]) auto
  finally have 2: "{x \<in> space (?R \<Otimes>\<^sub>M coin_space). (stake n \<circ> (\<lambda>(x, y). x @- y)) x = fst x} \<in>
    sets (?R \<Otimes>\<^sub>M coin_space)"
    by simp

  have 0: "AE x in ?R \<Otimes>\<^sub>M coin_space. (stake n \<circ> (\<lambda>(x, y). x @- y)) x = fst x"
    using  coin_space.sigma_finite_measure bool_list_set
    by (intro pair_sigma_finite.AE_pair_measure AE_pmfI 2 AE_I2)
     (simp_all add:pair_sigma_finite_def measure_pmf.sigma_finite_measure_axioms)

  have "?L = distr (distr (?R  \<Otimes>\<^sub>M coin_space) coin_space (\<lambda>(x,y). x@-y)) \<D> (stake n)"
    by (subst split_coin_space)  simp
  also have "... = distr (?R \<Otimes>\<^sub>M coin_space) \<D> (stake n \<circ> (\<lambda>(x, y). x @- y))"
    using append_measurable 1 by (intro distr_distr) simp_all
  also have "... = distr (?R \<Otimes>\<^sub>M coin_space) \<D> fst"
    using append_measurable 0 1
    by (intro distr_cong_AE refl measurable_comp[where N="coin_space"]) simp_all
  also have "... = distr (?R \<Otimes>\<^sub>M coin_space) ?R fst"
    by (intro distr_cong refl) simp
  also have "... = ?R"
    by (intro coin_space.distr_pair_fst)
  finally show ?thesis
    by simp
qed

lemma branch_coin_space:
  "(\<lambda>(x, y). stake n x @- y) \<in> \<B> \<Otimes>\<^sub>M \<B> \<rightarrow>\<^sub>M \<B>"
  "distr (\<B> \<Otimes>\<^sub>M \<B>) \<B> (\<lambda>(x,y). stake n x@-y) = \<B>" (is "?L = ?R")
proof -
  have 1:"stake n \<in> \<B> \<rightarrow>\<^sub>M \<D>"
    unfolding coin_space_def using measurable_stake by simp
  hence "case_prod (@-) \<circ> map_prod (stake n) id \<in> \<B> \<Otimes>\<^sub>M \<B> \<rightarrow>\<^sub>M \<B>"
    using append_measurable
    by (intro measurable_comp[where N="\<D> \<Otimes>\<^sub>M \<B>"] map_prod_measurable) simp_all
  thus 0:"(\<lambda>(x, y). stake n x @- y) \<in> \<B> \<Otimes>\<^sub>M \<B> \<rightarrow>\<^sub>M \<B>"
    by (simp add:comp_def map_prod_def case_prod_beta)

  have "?L = distr (distr (\<B> \<Otimes>\<^sub>M \<B>) (\<D> \<Otimes>\<^sub>M \<B>) (map_prod (stake n) id)) \<B> (\<lambda>(x,y). x@-y)"
    using append_measurable 1
    by (subst distr_distr) (auto intro!:map_prod_measurable simp:comp_def case_prod_beta')
  also have "... = distr (distr \<B> \<D> (stake n) \<Otimes>\<^sub>M distr \<B> \<B> id) \<B> (\<lambda>(x,y). x@-y)"
    using 1 coin_space.sigma_finite_measure
    by (subst pair_measure_distr) (simp_all add:map_prod_def id_def)
  also have "... = distr (pmf_of_set {xs. length xs = n} \<Otimes>\<^sub>M \<B>)  \<B> (\<lambda>(x,y). x@-y)"
    by (subst distr_stake) (simp add:id_def)
  also have "... = \<B>"
    by (intro split_coin_space)
  finally show "?L = ?R" 
    by simp
qed

end