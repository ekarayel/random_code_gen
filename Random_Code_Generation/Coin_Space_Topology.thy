theory Coin_Space_Topology
  imports 
    Coin_Space 
    "HOL-Analysis.Function_Topology" 
    "HOL-Probability.Discrete_Topology"
begin

lemma stream_eq_iff: 
  assumes "\<And>i. x !! i = y !! i"
  shows "x = y"
proof -
  have "x = smap id x"
    by (simp add: stream.map_id)
  also have "... = y"
    using assms unfolding smap_alt by auto
  finally show ?thesis by simp
qed

definition from_coins :: "bool stream \<Rightarrow> (nat \<Rightarrow> bool discrete)" 
  where "from_coins s i = discrete (s !! i)"

definition to_coins :: "(nat \<Rightarrow> bool discrete) \<Rightarrow> bool stream"
  where "to_coins x = (to_stream (of_discrete \<circ> x))"

definition \<B>\<^sub>t where "\<B>\<^sub>t = embed_measure coin_space from_coins"

lemma from_to_coins: "from_coins (to_coins x) = x"
  unfolding to_coins_def from_coins_def to_stream_def
  by (intro ext) (simp add:of_discrete_inverse) 

lemma to_from_coins: "to_coins (from_coins x) = x"
proof -
  have "smap (of_discrete \<circ> from_coins x) nats = x"
    by (intro stream_eq_iff) (simp add:from_coins_def discrete_inverse)
  thus ?thesis
    by (simp add:from_coins_def to_coins_def to_stream_def)
qed

lemma inj_from_coins: "inj from_coins"
  using to_from_coins by (metis injI)

lemma surj_from_coins: "surj from_coins"
  using from_to_coins by (metis surjI)

lemma B_t_eq_distr: "\<B>\<^sub>t = distr \<B> \<B>\<^sub>t from_coins"
  unfolding \<B>\<^sub>t_def by (intro embed_measure_eq_distr inj_from_coins)

lemma from_coins_measurable: "from_coins \<in> \<B> \<rightarrow>\<^sub>M \<B>\<^sub>t"
  unfolding \<B>\<^sub>t_def by (intro measurable_embed_measure2 inj_from_coins)

lemma to_coins_measurable: "to_coins \<in> \<B>\<^sub>t \<rightarrow>\<^sub>M \<B>"
  unfolding \<B>\<^sub>t_def by (intro measurable_embed_measure1) (simp add:to_from_coins)

lemma B_eq_distr: "\<B> = distr \<B>\<^sub>t \<B> to_coins" (is "?L = ?R")
proof -
  have "?R = distr (distr \<B> \<B>\<^sub>t from_coins) \<B> to_coins"
    using B_t_eq_distr by simp
  also have "... = distr \<B> \<B> (to_coins \<circ> from_coins)"
    by (intro distr_distr to_coins_measurable from_coins_measurable)
  also have "... = distr \<B> \<B> id"
    unfolding id_def comp_def to_from_coins by simp
  also have "... = ?L"
    unfolding id_def by simp
  finally show ?thesis
    by simp
qed

lemma B_t_finite: "emeasure \<B>\<^sub>t (space \<B>\<^sub>t) = 1"
proof -
  have "1 = emeasure \<B> (space \<B>)"
    by (simp add: coin_space.emeasure_space_1)
  also have "... = emeasure \<B>\<^sub>t (to_coins -` space \<B> \<inter> space \<B>\<^sub>t)"
    by (subst B_eq_distr) (intro emeasure_distr to_coins_measurable sets.top)
  also have "... = emeasure \<B>\<^sub>t (space \<B>\<^sub>t)"
    unfolding space_coin_space by simp
  finally show ?thesis by simp
qed

lemma space_B_t: "space \<B>\<^sub>t = UNIV"
  unfolding \<B>\<^sub>t_def space_embed_measure space_coin_space using surj_from_coins by simp

lemma at_least_borelI:
  assumes "topological_basis K" 
  assumes "countable K"
  assumes "K \<subseteq> sets M"
  assumes "open U"
  shows "U \<in> sets M"
proof -
  obtain K' where K'_range: "K' \<subseteq> K" and "\<Union>K' = U"
    using assms(1,4) unfolding topological_basis_def by blast
  hence "U = \<Union>K'" by simp
  also have "... \<in> sets M"
    using K'_range assms(2,3) countable_subset
    by (intro sets.countable_Union) auto
  finally show ?thesis
    by simp
qed

lemma coin_space_is_borel_measure:
  assumes "open U"
  shows "U \<in> sets \<B>\<^sub>t"
proof -
  obtain K :: "(nat \<Rightarrow> bool discrete) set set" where 
    K_countable: "countable K" and K_top_basis: "topological_basis K" and
    K_cylinder: "\<forall>k\<in>K. \<exists>X. (k = Pi\<^sub>E UNIV X) \<and> (\<forall>i. open (X i)) \<and> finite {i. X i \<noteq> UNIV}"
    using product_topology_countable_basis by auto

  have "k \<in> sets \<B>\<^sub>t" if k_in_K: "k \<in> K" for k
  proof -
    obtain X where k_def: "k = Pi\<^sub>E UNIV X" and "\<And>i. open (X i)" and fin_X: "finite {i. X i \<noteq> UNIV}" 
      using K_cylinder k_in_K by auto
    define Z where "Z i = (X i \<noteq> UNIV)" for i
    define n where "n = (if {i. X i \<noteq> UNIV} \<noteq> {} then Suc (Max {i. X i \<noteq> UNIV}) else 0)"
    have "i < n" if "Z i" for i
      using fin_X that less_Suc_eq_le unfolding n_def Z_def[symmetric] by (auto split:if_split_asm)
    hence "X i = UNIV" if "i \<ge> n" for i
      using that leD unfolding Z_def by auto

    hence "{xs. \<forall>i. discrete (xs !! i) \<in> X i} = {xs. \<forall>i < n. discrete (xs !! i) \<in> X i}"
      using not_le_imp_less by auto
    also have "... = stake n -` {xs. length xs  = n \<and> (\<forall>i < n. discrete (xs ! i) \<in> X i)}" 
      unfolding vimage_def by (intro Collect_cong) auto
    also have "... = stake n -` {xs. length xs  = n \<and> (\<forall>i < n. discrete (xs ! i) \<in> X i)} \<inter> space \<B>"
      unfolding space_coin_space by simp
    also have "... \<in> sets \<B>" 
      using measurable_stake by (intro measurable_sets[where A="\<D>"]) (auto simp:coin_space_def)
    finally have 0: "{xs. \<forall>i. discrete (xs !! i) \<in> X i} \<in> sets \<B>"
      by simp

    have "k = to_coins -` {xs. \<forall>i. discrete (xs !! i) \<in> X i} \<inter> space \<B>\<^sub>t"
      unfolding k_def to_coins_def vimage_def PiE_def Pi_def
      by (simp add:to_stream_def of_discrete_inverse space_B_t)
    also have "... \<in> sets \<B>\<^sub>t"
      by (intro measurable_sets[OF to_coins_measurable] 0)
    finally show ?thesis by simp
  qed

  thus ?thesis
    by (intro at_least_borelI[OF K_top_basis K_countable] assms) auto
qed

definition option_ud :: "'a option topology"
  where "option_ud = topology (\<lambda>S. S=UNIV \<or> None \<notin> S)"

lemma option_ud_topology: "istopology (\<lambda>S. S=UNIV \<or> None \<notin> S)" (is "istopology ?T")
proof -
  have "?T (U \<inter> V)" if "?T U" "?T V" for U V
    using that by auto
  moreover have "?T (\<Union>K)" if "\<And>U. U \<in> K \<Longrightarrow> ?T U" for K
    using that by auto
  ultimately show ?thesis
    unfolding istopology_def by auto
qed

lemma openin_option_ud: "openin option_ud S \<longleftrightarrow> (S = UNIV \<or> None \<notin> S)"
  unfolding option_ud_def by (subst topology_inverse'[OF option_ud_topology]) auto

lemma topspace_option_ud: "topspace option_ud = UNIV"
proof -
  have "UNIV \<subseteq> topspace option_ud"
    by (intro openin_subset) (simp add:openin_option_ud)
  thus ?thesis by auto
qed

lemma contionuos_into_option_udI: 
  assumes "\<And>x. openin X (f -` {Some x} \<inter> topspace X)"
  shows "continuous_map X option_ud f"
proof -
  have "openin X {x \<in> topspace X. f x \<in> U}" if "openin option_ud U" for U
  proof (cases "U = UNIV")
    case True
    then show ?thesis by simp
  next
    case False
    define V where "V = the ` U"
    have "None \<notin> U"
      using that False unfolding openin_option_ud by simp
    hence "Some ` V = id ` U"
      unfolding V_def image_image id_def
      by (intro image_cong refl) (metis option.exhaust_sel)
    hence "U = Some ` V" by simp
    hence "{x \<in> topspace X. f x \<in> U} = (\<Union>v \<in> V. f -` {Some v} \<inter> topspace X)" by auto
    moreover have "openin X (\<Union>v \<in> V. f -` {Some v} \<inter> topspace X)" 
      using assms by (intro openin_Union) auto
    ultimately show ?thesis by auto
  qed
  thus ?thesis
    unfolding continuous_map topspace_option_ud by auto
qed

lemma map_option_continuous:
  "continuous_map option_ud option_ud (map_option f)"
  by (intro contionuos_into_option_udI) 
    (simp add:topspace_option_ud vimage_def openin_option_ud)

end