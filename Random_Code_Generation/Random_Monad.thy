theory Random_Monad
  imports 
    "HOL-Probability.Probability" 
    "HOL-Library.Extended_Nat"
    "Permuted_Congruential_Generator"
    "Coin_Space"
    "Zeta_Function.Zeta_Library"
    (* The last import is to pull set_nn_integral_cong which should be in
    HOL-Analysis.Set_Integral. *)
begin

text \<open>This is the inverse of @{term "set_option"}\<close>

definition the_elem_opt :: "'a set \<Rightarrow> 'a option"
  where "the_elem_opt S = (if Set.is_singleton S then Some (the_elem S) else None)"

lemma the_elem_opt_empty[simp]: "the_elem_opt {} = None"
  unfolding the_elem_opt_def is_singleton_def by (simp split:if_split_asm)

lemma the_elem_opt_single[simp]: "the_elem_opt {x} = Some x"
  unfolding the_elem_opt_def by simp

definition at_most_one :: "'a set \<Rightarrow> bool"
  where "at_most_one S \<longleftrightarrow> (\<forall>x y. x \<in> S \<and> y \<in> S \<longrightarrow> x = y)"

lemma at_most_one_cases[consumes 1]:
  assumes "at_most_one S"
  assumes "P {the_elem S}"
  assumes "P {}"
  shows "P S"
proof (cases "S = {}")
  case True
  then show ?thesis using assms by auto
next
  case False
  then obtain x where "x \<in> S" by auto
  hence "S = {x}" using assms(1) unfolding at_most_one_def by auto
  thus ?thesis using assms(2) by simp
qed

lemma the_elem_opt_Some_iff[simp]: "at_most_one S \<Longrightarrow> the_elem_opt S = Some x \<longleftrightarrow> S = {x}"
  by (induction S rule:at_most_one_cases) auto

lemma the_elem_opt_None_iff[simp]: "at_most_one S \<Longrightarrow> the_elem_opt S = None \<longleftrightarrow> S = {}"
  by (induction S rule:at_most_one_cases) auto

type_synonym 'a random_monad = "bool stream \<Rightarrow> ('a \<times> bool stream) option"

definition return_rm :: "'a \<Rightarrow> 'a random_monad"
  where "return_rm x bs = Some (x, bs)"

definition bind_rm :: "'a random_monad \<Rightarrow> ('a \<Rightarrow> 'b random_monad) \<Rightarrow> 'b random_monad"
  where "bind_rm m f bs = 
    do {
      (r, bs') \<leftarrow> m bs;
      f r bs' 
    }"

definition coin_rm :: "bool random_monad"
  where "coin_rm bs = Some (shd bs, stl bs)"

adhoc_overloading Monad_Syntax.bind bind_rm

definition wf_on_prefix :: "'a random_monad \<Rightarrow> bool list \<Rightarrow> 'a \<Rightarrow> bool" where
  "wf_on_prefix f p r = (\<forall>cs. f (p@-cs) = Some (r,cs))"

definition wf_random :: "'a random_monad \<Rightarrow> bool" where
  "wf_random f \<longleftrightarrow> (\<forall>bs. 
      case f bs of 
        None \<Rightarrow> True | 
        Some (r,bs') \<Rightarrow> (\<exists>p. sprefix p bs \<and> wf_on_prefix f p r))"

definition range_rm :: "'a random_monad \<Rightarrow> 'a set"
  where "range_rm f = Some -` (range (map_option fst \<circ> f))"

lemma in_range_rmI:
  assumes "r bs = Some (y, n)"
  shows   "y \<in> range_rm r"
proof -
  have "Some (y, n) \<in> range r"
    using assms[symmetric] by auto
  thus ?thesis
    unfolding range_rm_def using fun.set_map by force
qed

definition measure_rm :: "'a random_monad \<Rightarrow> 'a option measure"
  where "measure_rm f = distr \<B> \<D> (map_option fst \<circ> f)"

lemma wf_randomI:
  assumes "\<And>bs. f bs \<noteq> None \<Longrightarrow> (\<exists>p r. sprefix p bs \<and> wf_on_prefix f p r)"
  shows "wf_random f"
proof -
  have "\<exists>p. sprefix p bs \<and> wf_on_prefix f p r" if 0:"f bs = Some (r, bs')"  for bs r bs'
  proof -
    obtain p r' where 1:"sprefix p bs" and 2:"wf_on_prefix f p r'"
      using assms 0 by force
    have "f bs = f (p@-(sdrop (length p) bs))" 
      using 1 unfolding sprefix_def by (metis stake_sdrop)
    also have "... = Some (r', sdrop (length p) bs)"
      using 2 unfolding wf_on_prefix_def by auto
    finally have "f bs = Some (r', sdrop (length p) bs)"
      by simp
    hence "r = r'" using 0 by simp
    thus ?thesis using 1 2 by auto
  qed
  thus ?thesis
    unfolding wf_random_def by (auto split:option.split)
qed

lemma wf_bind:
  assumes "wf_random m"
  assumes "\<And>x. x \<in> range_rm m \<Longrightarrow> wf_random (f x)"
  shows "wf_random (m \<bind> f)"
proof (rule wf_randomI)
  fix bs
  assume 0:"(m \<bind> f) bs \<noteq> None"
  obtain x bs' y bs'' where 1: "m bs = Some (x,bs')" and 5:"f x bs' = Some (y, bs'')"
    using 0 unfolding bind_rm_def by (cases "m bs") auto
  hence wf: "wf_random (f x)"
    by (intro assms(2) in_range_rmI) auto 
  obtain p where 2:"wf_on_prefix m p x" and 3:"sprefix p bs"
    using assms(1) 1 unfolding wf_random_def by (auto split:option.split_asm)
  have 4:"bs = p@- (sdrop (length p) bs)"
    using 3 unfolding sprefix_def by (metis stake_sdrop)
  hence "m bs = Some (x, sdrop (length p) bs)"
    using 2 unfolding wf_on_prefix_def by metis
  hence "bs' = sdrop (length p) bs"
    using 1 by auto
  hence 6:"bs = p @- bs'"
    using 4 by auto

  obtain q where 7:"wf_on_prefix (f x) q y" and 8:"sprefix q bs'"
    using wf 5 unfolding wf_random_def by (auto split:option.split_asm)

  have "sprefix (p@q) bs"
    unfolding 6 using 8 unfolding sprefix_def by auto

  moreover have "(m \<bind> f) ((p@q)@-cs) = Some (y, cs)" for cs 
  proof -
    have "(m \<bind> f) ((p@q)@-cs) = (m \<bind> f) (p@-(q@-cs))"
      by simp
    also have "... = (f x) (q@-cs)"
      using 2 unfolding wf_on_prefix_def bind_rm_def by simp
    also have "... = Some (y,cs)"
      using 7 unfolding wf_on_prefix_def by simp
    finally show ?thesis by simp
  qed

  hence "wf_on_prefix (m \<bind> f) (p@q) y"
    unfolding wf_on_prefix_def by auto
  ultimately show "\<exists>p r. sprefix p bs \<and> wf_on_prefix (m \<bind> f) p r"
    by auto
qed

lemma wf_return:
  "wf_random (return_rm x)"
proof (rule wf_randomI)
  fix bs assume "return_rm x bs \<noteq> None"
  have "wf_on_prefix (return_rm x) [] x" 
    unfolding wf_on_prefix_def return_rm_def by auto
  moreover have "sprefix [] bs"
    unfolding sprefix_def by auto
  ultimately show "\<exists>p r. sprefix p bs \<and> wf_on_prefix (return_rm x) p r"
    by auto
qed

lemma wf_coin:
  "wf_random (coin_rm)"
proof (rule wf_randomI)
  fix bs assume "coin_rm bs \<noteq> None"
  have "wf_on_prefix coin_rm [shd bs] (shd bs)" 
    unfolding wf_on_prefix_def coin_rm_def by auto
  moreover have "sprefix [shd bs] bs"
    unfolding sprefix_def by auto
  ultimately show "\<exists>p r. sprefix p bs \<and> wf_on_prefix coin_rm p r"
    by auto
qed

definition ptree_rm :: "'a random_monad \<Rightarrow> bool list set"
  where "ptree_rm f = {p. \<exists>r. wf_on_prefix f p r}"

definition eval_rm :: "'a random_monad \<Rightarrow> bool list \<Rightarrow> 'a" where 
  "eval_rm f p = fst (the (f (p@-sconst False)))"

lemma eval_rmD:
  assumes "wf_on_prefix f p r"
  shows "eval_rm f p = r"
  using assms unfolding wf_on_prefix_def eval_rm_def by auto

lemma wf_on_prefixD:
  assumes "wf_on_prefix f p r"
  assumes "sprefix p bs"
  shows "f bs = Some (eval_rm f p, sdrop (length p) bs)"
proof -
  have 0:"bs = p@-(sdrop (length p) bs)"
    using assms(2) unfolding sprefix_def by (metis stake_sdrop)
  hence "f bs = Some (r, sdrop (length p) bs)"
    using assms(1) 0 unfolding wf_on_prefix_def by metis
  thus ?thesis
    using eval_rmD[OF assms(1)] by simp
qed

lemma prefixes_parallel_helper:
  assumes "p \<in> ptree_rm f"
  assumes "q \<in> ptree_rm f"
  assumes "prefix p q"
  shows "p = q"
proof -
  obtain h where 0:"q = p@h"
    using assms(3) prefixE that by auto
  obtain r1 where 1:"wf_on_prefix f p r1"
    using assms(1) unfolding ptree_rm_def by auto
  obtain r2 where 2:"wf_on_prefix f q r2"
    using assms(2) unfolding ptree_rm_def by auto
  have "x = h@-x" for x :: "bool stream"
  proof -
    have "Some (r2, x) = f (q@-x)"
      using 2 unfolding wf_on_prefix_def by auto
    also have "... = f (p@-(h@-x))"
      using 0 by auto
    also have "... = Some (r1, h@-x)"
      using 1 unfolding wf_on_prefix_def by auto
    finally show "x = h@-x"
      by simp
  qed
  hence "h = []"
    using empty_if_shift_idem by simp
  thus ?thesis using 0 by simp
qed

lemma prefixes_parallel:
  assumes "p \<in> ptree_rm f"
  assumes "q \<in> ptree_rm f"
  shows "p = q \<or> p \<parallel> q"
  using prefixes_parallel_helper assms by blast

lemma prefixes_singleton:
  assumes "p \<in> {p. p \<in> ptree_rm f \<and> sprefix p bs}"
  shows "{p \<in> ptree_rm f. sprefix p bs} = {p}"
proof
  have "q = p" if "q \<in> ptree_rm f" "sprefix q bs" for q
    using same_prefix_not_parallel assms prefixes_parallel that by blast    
  thus "{p \<in> ptree_rm f. sprefix p bs} \<subseteq> {p}"
    by (intro subsetI) simp
next
  show "{p} \<subseteq> {p \<in> ptree_rm f. sprefix p bs}"
    using assms by auto
qed

lemma prefixes_at_most_one: 
  "at_most_one {p \<in> ptree_rm f. sprefix p x}"
  unfolding at_most_one_def using same_prefix_not_parallel prefixes_parallel by blast

lemma wf_random_alt:
  assumes "wf_random f"
  shows "f bs = (case the_elem_opt {p \<in> ptree_rm f. sprefix p bs} of
      None \<Rightarrow> None | Some p \<Rightarrow> Some (eval_rm f p, sdrop (length p) bs))"
proof (cases "f bs")
  case None
  have "False" if p_in: "p \<in> ptree_rm f" and p_pref: "sprefix p bs" for p
  proof -
    obtain r where wf: "wf_on_prefix f p r" using that p_in unfolding ptree_rm_def by auto
    have "bs = p@-(sdrop (length p) bs)"
      using p_pref unfolding sprefix_def by (metis stake_sdrop)
    hence "f bs \<noteq> None"
      using wf unfolding wf_on_prefix_def 
      by (metis option.simps(3))
    thus "False" using  None by simp
  qed
  hence 0:"{p \<in> ptree_rm f. sprefix p bs} = {}"
    by auto
  show ?thesis unfolding 0 None by simp
next
  case (Some a)
  moreover obtain r cs where "a = (r, cs)" by (cases a) auto
  ultimately have "f bs = Some (r, cs)" by simp
  hence "\<exists>p. sprefix p bs \<and> wf_on_prefix f p r"
    using assms(1) unfolding wf_random_def by (auto split:option.split_asm)
  then obtain p where sp: "sprefix p bs" and wf: "wf_on_prefix f p r"
    by auto
  hence "p \<in> {p \<in> ptree_rm f. sprefix p bs}" 
    unfolding ptree_rm_def by auto
  hence 0:"{p \<in> ptree_rm f. sprefix p bs} = {p}"
    using prefixes_singleton by auto
  show ?thesis unfolding 0 wf_on_prefixD[OF wf sp] by simp
qed

definition consumed_bits where 
  "consumed_bits f bs = (case the_elem_opt {p. p \<in> ptree_rm f \<and> sprefix p bs}
    of None \<Rightarrow> \<infinity> | Some p \<Rightarrow> enat (length p))"

lemma wf_random_alt2:
  assumes "wf_random f"
  shows "f bs = (
    case consumed_bits f bs of
      \<infinity> \<Rightarrow> None | 
      enat n \<Rightarrow> Some (eval_rm f (stake n bs), sdrop n bs))"
proof (cases "consumed_bits f bs")
  case (enat n)
  then obtain p where p_def:
    "the_elem_opt {p. p \<in> ptree_rm f \<and> sprefix p bs} = Some p" "length p = n"
    unfolding consumed_bits_def by (simp split:option.split_asm)

  have "p \<in> {p. p \<in> ptree_rm f \<and> sprefix p bs}"
    using p_def(1) unfolding the_elem_opt_Some_iff[OF prefixes_at_most_one] by auto
  hence 0: "p = stake n bs"
    using p_def(2) by (simp add:set_eq_iff sprefix_def)

  have "f bs = Some (eval_rm f p, sdrop (length p) bs)"
    by (subst wf_random_alt[OF assms]) (simp add:p_def)
  also have "... = Some (eval_rm f (stake n bs), sdrop n bs)"
    unfolding p_def(1) by (simp add:0)
  finally have "f bs = Some (eval_rm f (stake n bs), sdrop n bs)" 
    by simp
  then show ?thesis using enat by simp 
next
  case infinity
  hence 0:"the_elem_opt {p. p \<in> ptree_rm f \<and> sprefix p bs} = None"
    unfolding consumed_bits_def by (simp split:option.split_asm)
  have "f bs = None"
    by (subst wf_random_alt[OF assms]) (simp add:0)
  then show ?thesis using infinity by simp
qed

lemma consumed_bits_inf_iff: 
  assumes "wf_random f"
  shows "f bs = None \<longleftrightarrow> consumed_bits f bs = \<infinity>"
    using wf_random_alt2[OF assms] by (simp split:enat.split)

lemma consumed_bits_enat_iff:
  "consumed_bits f bs = enat n \<longleftrightarrow> stake n bs \<in> ptree_rm f" (is "?L = ?R")
proof 
  assume "consumed_bits f bs = enat n"
  then obtain p where "the_elem_opt {p \<in> ptree_rm f. sprefix p bs} = Some p" and 0: "length p = n"
    unfolding consumed_bits_def by (auto split:option.split_asm) 
  hence "p \<in> ptree_rm f" "sprefix p bs"
    unfolding the_elem_opt_Some_iff[OF prefixes_at_most_one] by auto 
  thus "stake n bs \<in> ptree_rm f"
    using 0 unfolding sprefix_def by auto
next
  assume "stake n bs \<in> ptree_rm f"
  hence "stake n bs \<in> {p \<in> ptree_rm f. sprefix p bs}"
    unfolding sprefix_def by auto
  hence "{p \<in> ptree_rm f. sprefix p bs} = {stake n bs}"
    using prefixes_singleton by auto
  thus "consumed_bits f bs = enat n"
    unfolding consumed_bits_def by simp
qed

lemma 
  assumes "wf_random f"
  assumes "consumed_bits f bs = enat n"
  assumes "stake n bs = stake n bs'" 
  shows "f bs = f bs'"
  sorry

(*
lemma wf_randomD:
  assumes "wf_random f"
  assumes "f bs = Some (r, bs')"
  obtains p where "sprefix p bs" "wf_on_prefix f p r"
proof -
  have "\<exists>p. sprefix p bs \<and> wf_on_prefix f p r"
    using assms unfolding wf_random_def by (auto split:option.split_asm)
  thus ?thesis using that by auto
qed

lemma consumed_prefix_unique_helper:
  assumes "length p \<le> length q"
  assumes "sprefix p bs" "sprefix q bs"
  assumes "wf_on_prefix f p r" "wf_on_prefix f q r"
  shows "p = q"
proof -
  have "prefix p q"
    using sprefix_length_prefix[OF assms(1-3)] by simp
  then obtain h where h_def:"q = p@h"
    using prefixE by auto

  have "h@-cs = cs" for cs
  proof-
    have "Some (r,cs) =  f ((p@h)@-cs)"
      using assms(5) unfolding h_def[symmetric] wf_on_prefix_def by auto
    also have "... = f (p@-(h@-cs))"
      by simp
    also have "... = Some (r, h@-cs)"
      using assms(4) unfolding wf_on_prefix_def by auto
    finally have "Some (r,cs) = Some (r, h@-cs)"
      by simp
    thus ?thesis by simp
  qed
  hence "h = []"
    by (intro empty_if_shift_idem) simp
  thus "p = q"
    using h_def by simp
qed

lemma consumed_prefix_unique:
  assumes "sprefix p bs" "sprefix q bs"
  assumes "wf_on_prefix f p r" "wf_on_prefix f q r"
  shows "p = q"
proof (cases "length p \<le> length q")
  case True
  show ?thesis 
    using consumed_prefix_unique_helper[OF True assms(1,2,3,4)] by simp
next
  case False
  hence 0:"length q \<le> length p" 
    by simp
  show ?thesis 
    using consumed_prefix_unique_helper[OF 0 assms(2,1,4,3)] by simp
qed

definition consumed_prefix :: "'a random_monad \<Rightarrow> bool stream \<Rightarrow> bool list" where
  "consumed_prefix f bs = (THE p. sprefix p bs \<and> wf_on_prefix f p (fst (the (f bs))))"

lemma consumed_prefixD:
  assumes "wf_random f"
  assumes "f bs = Some (r, bs')"
  shows 
    "sprefix (consumed_prefix f bs) bs" (is "?A") 
    "wf_on_prefix f (consumed_prefix f bs) r" (is "?B")
proof -
  have 0:"fst (the (f bs)) = r"
    using assms by simp

  obtain p where p_def: "sprefix p bs \<and> wf_on_prefix f p r"
    using wf_randomD[OF assms] by auto
  hence p_eq_q: "q = p" if "sprefix q bs \<and> wf_on_prefix f q r" for q
    using consumed_prefix_unique that by metis

  have "sprefix (consumed_prefix f bs) bs \<and> wf_on_prefix f (consumed_prefix f bs) r"
    unfolding 0 consumed_prefix_def by (rule theI2, use p_def p_eq_q in auto)
  thus ?A ?B by auto
qed

definition consumed_bits'
  where "consumed_bits' f bs = (
    case f bs of 
        None \<Rightarrow> \<infinity> 
      | Some (r,bs') \<Rightarrow> length (consumed_prefix f bs))"
*)

locale wf_random_fun =
  fixes f :: "'a random_monad"
  assumes wf: "wf_random f"
begin

definition R where "R = restrict_space \<B> {bs. f bs \<noteq> None}"

lemma consumed_bits_measurable: "consumed_bits f \<in> \<B> \<rightarrow>\<^sub>M \<D>"
proof -
  have 0: "consumed_bits f -` {x} \<inter> space \<B> \<in> sets \<B>" (is "?L \<in> _") 
    if x_ne_inf: "x \<noteq> \<infinity>" for x
  proof -
    obtain n where x_def: "x = enat n"
      using x_ne_inf that by auto

    have "?L = {bs. \<exists>p. sprefix p bs \<and> length p = n \<and> p \<in> ptree_rm f}"
      unfolding vimage_def space_coin_space consumed_bits_def x_def
      by (simp add:set_eq_iff prefixes_at_most_one split:option.split) metis
    also have "... = {bs. stake n bs \<in> ptree_rm f}"
      unfolding sprefix_def by (intro Collect_cong) (metis length_stake)
    also have "... = stake n -` ptree_rm f \<inter> space \<B>"
      unfolding vimage_def space_coin_space by simp
    also have "... \<in> sets \<B>"
      unfolding coin_space_def by (intro measurable_sets[where A="\<D>"]) simp_all
    finally show ?thesis 
      by simp
  qed

  thus ?thesis
    by (intro measurable_sigma_sets_with_exception[where d="\<infinity>"])
qed

lemma R_sets: 
  "{bs. f bs = None} \<in> sets \<B>"
  "{bs. f bs \<noteq> None} \<in> sets \<B>"
proof -
  have "{bs. f bs = None} \<inter> space \<B> = consumed_bits f -` {\<infinity>} \<inter> space \<B>"
    using consumed_bits_inf_iff[OF wf] by auto
  also have "... \<in> sets \<B>"
    by (intro measurable_sets[OF consumed_bits_measurable]) auto
  finally have "{bs. f bs = None} \<inter> space \<B> \<in> sets \<B>"
    by simp
  thus 0: "{bs. f bs = None} \<in> sets \<B>"
    unfolding space_coin_space by simp
  have "{bs. f bs \<noteq> None} = space \<B> - {bs. f bs = None}"
    unfolding space_coin_space by (simp add:set_eq_iff del:not_None_eq) 
  also have "... \<in> sets \<B>"
    by (intro sets.compl_sets 0)
  finally show "{bs. f bs \<noteq> None} \<in> sets \<B>" 
    by simp
qed

(*
lemma indep_rem:
  assumes "consumed_bits f bs = enat n"
  assumes "stake n bs = stake n bs'"
  shows "map_option fst (f bs) = map_option fst (f bs')"
proof -
  have nn: "f bs \<noteq> None" and lp: "length (consumed_prefix f bs) = n"
    using assms(1) unfolding consumed_bits_def by (auto split:option.split_asm)

  define r where "r = fst (the (f bs))"

  have c1:"wf_on_prefix f (consumed_prefix f bs) r" and c2: "sprefix (consumed_prefix f bs) bs"
    using nn consumed_prefixD[OF wf] r_def by auto
  have "bs' = (consumed_prefix f bs)@-sdrop n bs'"
    using assms(2) by (metis c2 lp sprefix_def stake_sdrop)
  hence "f bs' = Some (r, sdrop n bs')"
    using c1 unfolding wf_on_prefix_def by metis
  thus ?thesis
    using r_def nn by auto
qed

lemma "countable (range (map_option fst \<circ> f))"
proof -
  have 0:"(range (map_option fst \<circ> f)) = (\<Union>k. (map_option fst \<circ> f) ` {bs. consumed_bits f bs = k})"
    by auto

  have 1: "finite ((map_option fst \<circ> f) ` {bs. consumed_bits f bs = k})" (is "finite ?T") for k
  proof (cases k)
    case (enat n)

    define drp where "drp bs = stake n bs @- sconst False" for bs

    have 2:"drp ` {bs. consumed_bits f bs = k} \<subseteq> 
      (\<lambda>x. x@- sconst False) ` {p. set p \<subseteq> UNIV \<and> length p = n}"
      unfolding drp_def by (auto simp add:image_iff)

    have "?T = (map_option fst \<circ> f \<circ> drp) ` {bs. consumed_bits f bs = k}"
    proof (rule image_cong[OF refl])
      fix bs assume "bs \<in> {bs. consumed_bits f bs = k}"

      hence "map_option fst (f bs) = map_option fst (f (drp bs))"
        unfolding drp_def enat
        by (intro indep_rem) (auto simp add: stake_shift)
      thus "(map_option fst \<circ> f) bs = (map_option fst \<circ> f \<circ> drp) bs"
        by simp
    qed
    also have "... = (map_option fst \<circ> f) ` (drp ` {bs. consumed_bits f bs = k})"
      unfolding image_image by simp
    finally have "?T = (map_option fst \<circ> f) ` (drp ` {bs. consumed_bits f bs = k})"
      by simp
    moreover have "finite (drp ` {bs. consumed_bits f bs = k})"
      by (intro finite_subset[OF 2] finite_imageI finite_lists_length_eq) auto
    ultimately show ?thesis by simp
  next
    case infinity
    hence "{bs. consumed_bits f bs = k} \<subseteq> {bs. f bs = None}"
      unfolding consumed_bits_def by (intro subsetI) (simp split:option.split_asm) 
    hence "(map_option fst \<circ> f) ` {bs. consumed_bits f bs = k} \<subseteq> {None}"
      by auto
    with finite_subset[OF this] show ?thesis 
      by simp
  qed

  thus ?thesis
    using countable_finite unfolding 0 by (intro countable_UN) auto
qed
*)

lemma countable_range: "countable (range_rm f)"
proof -
  have "countable (eval_rm f ` UNIV)"
    by (intro countable_image) simp
  moreover have "range_rm f \<subseteq> eval_rm f ` UNIV"
    unfolding range_rm_def comp_def 
    by (subst wf_random_alt[OF wf]) (auto split:option.split_asm)
  ultimately show ?thesis using countable_subset by blast
qed

lemma the_f_measurable: "the \<circ> f \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
proof -
  define h where "h = the_enat \<circ> consumed_bits f"
  define g where "g bs = (stake (h bs) bs, sdrop (h bs) bs)" for bs

  have "consumed_bits f bs \<noteq> \<infinity>" if "bs \<in> space R" for bs
    using that consumed_bits_inf_iff[OF wf] unfolding R_def space_restrict_space space_coin_space
    by (simp del:not_infinity_eq not_None_eq)

  hence 0:"the (f bs) = map_prod (eval_rm f) id (g bs)" if "bs \<in> space R" for bs
    unfolding g_def h_def using that 
    by (subst wf_random_alt2[OF wf]) (simp split:enat.split del:not_infinity_eq)

  have 1:"h \<in> R \<rightarrow>\<^sub>M \<D>"
    unfolding R_def h_def
    by (intro measurable_restrict_space1 measurable_comp[OF consumed_bits_measurable]) simp

  have "stake k \<in> R \<rightarrow>\<^sub>M \<D>" for k
    unfolding R_def coin_space_def
    by (intro measurable_restrict_space1) simp
  moreover have "sdrop k \<in> R \<rightarrow>\<^sub>M \<B>" for k
    unfolding R_def coin_space_def
    by (intro measurable_restrict_space1) simp
  ultimately have "g \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
    unfolding g_def 
    by (intro measurable_Pair measurable_Pair_compose_split[OF  _ 1 measurable_id]) simp_all
  hence "(map_prod (eval_rm f) id \<circ> g) \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
    by (intro measurable_comp[where N="\<D> \<Otimes>\<^sub>M \<B>"] map_prod_measurable) auto
  moreover have "(the \<circ> f) \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B> \<longleftrightarrow> (map_prod  (eval_rm f) id \<circ> g) \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
    using 0 by (intro measurable_cong) (simp add:comp_def)
  ultimately show ?thesis
    by auto
qed

lemma measure_rm_measurable: "map_option fst \<circ> f \<in> \<B> \<rightarrow>\<^sub>M \<D>"
proof -
  have 0:"countable {{bs. f bs \<noteq> None}, {bs. f bs = None}}"
    by simp

  have 1: "\<Omega> \<in> sets \<B> \<and> map_option fst \<circ> f \<in> restrict_space \<B> \<Omega> \<rightarrow>\<^sub>M \<D>" 
    if "\<Omega> \<in> {{bs. f bs \<noteq> None}, {bs. f bs = None}}" for \<Omega>
  proof (cases "\<Omega> = {bs. f bs \<noteq> None}")
    case True
    have "Some \<circ> fst \<circ> (the \<circ> f) \<in> R \<rightarrow>\<^sub>M \<D>"
      by (intro measurable_comp[OF the_f_measurable]) auto
    hence "map_option fst \<circ> f \<in> R \<rightarrow>\<^sub>M \<D>"
      unfolding R_def by (subst measurable_cong[where g="Some \<circ> fst \<circ> (the \<circ> f)"]) 
        (auto simp add: space_restrict_space space_coin_space) 
    thus "\<Omega> \<in> sets \<B> \<and> map_option fst \<circ> f \<in> restrict_space \<B> \<Omega> \<rightarrow>\<^sub>M \<D>" 
      unfolding R_def True using R_sets by auto
  next
    case False
    hence 2:"\<Omega> = {bs. f bs = None}"
      using that by simp

    have "map_option fst \<circ> f \<in> restrict_space \<B> {bs. f bs = None} \<rightarrow>\<^sub>M \<D>"
      by (subst measurable_cong[where g="\<lambda>_. None"])
       (simp_all add:space_restrict_space)

    thus "\<Omega> \<in> sets \<B> \<and> map_option fst \<circ> f \<in> restrict_space \<B> \<Omega> \<rightarrow>\<^sub>M \<D>" 
      unfolding 2 using R_sets by auto
  qed

  have 3: "space \<B> \<subseteq> \<Union> {{bs. f bs \<noteq> None}, {bs. f bs = None}}"
    unfolding space_coin_space by auto

  show ?thesis
    by (rule measurable_piecewise_restrict[OF 0]) (use 1 3 space_coin_space in \<open>auto\<close>)
qed

lemma measure_rm_subprob_space:
  "measure_rm f \<in> space (subprob_algebra \<D>)"
proof -
  have "prob_space (measure_rm f)"
    unfolding measure_rm_def using measure_rm_measurable
    by (intro coin_space.prob_space_distr ) auto 
  moreover have "sets (measure_rm f) = \<D>"
    unfolding measure_rm_def by simp
  ultimately show ?thesis
    unfolding space_subprob_algebra using prob_space_imp_subprob_space
    by auto
qed

lemma none_measure_subprob_algebra:
  "return \<D> None \<in> space (subprob_algebra \<D>)"
  by (metis measure_subprob return_pmf.rep_eq)

lemma fst_the_f_measurable: "fst \<circ> the \<circ> f \<in> R \<rightarrow>\<^sub>M \<D>"
proof -
  have "fst \<circ> (the \<circ> f) \<in> R \<rightarrow>\<^sub>M \<D>"
    by (intro measurable_comp[OF the_f_measurable]) simp
  thus ?thesis by (simp add:comp_def)
qed

lemma remainder_indep: 
  "distr R (\<D> \<Otimes>\<^sub>M \<B>) (the \<circ> f) = distr R \<D> (fst \<circ> the \<circ> f) \<Otimes>\<^sub>M \<B>"
proof -
  define C where "C k = consumed_bits f -` {enat k}" for k

  have 2: "(\<exists>k. x \<in> C k) \<longleftrightarrow> f x \<noteq> None" for x 
    using consumed_bits_inf_iff[OF wf] unfolding C_def
    by auto

  hence 5: "C k \<subseteq> space R" for k
    unfolding R_def space_restrict_space space_coin_space
    by auto

  have 1:"{bs. f bs \<noteq> None} \<inter> space \<B> \<in> sets \<B>"
    using R_sets by simp

  have 6: "C k \<in> sets \<B>" for k
  proof -
    have "C k = consumed_bits f -` {enat k} \<inter> space \<B>"
      unfolding C_def space_coin_space by simp
    also have "... \<in> sets \<B>"
      by (intro measurable_sets[OF consumed_bits_measurable]) auto
    finally show ?thesis by simp
  qed

  have 8: "x \<in> C k \<longleftrightarrow> stake k x \<in> ptree_rm f" for x k
    unfolding C_def using consumed_bits_enat_iff by auto

  have 7: "the (f (stake k x @- y)) = (fst (the (f x)), y)" (is "?L = ?R") if "x \<in> C k" for x y k 
  proof -
    have "stake k x @- y \<in> C k"
      using 8 that by simp
    hence "the (f (stake k x @- y)) = (eval_rm f (stake k x), y)"
      using wf_random_alt2[OF wf] unfolding C_def by simp
    also have "... = (fst (the (f x)), y)"
      using that wf_random_alt2[OF wf] unfolding C_def by simp
    finally show ?thesis by simp
  qed

  have C_disj: "disjoint_family C"
    unfolding disjoint_family_on_def C_def by auto 

  have 0:
    "emeasure (distr R (\<D> \<Otimes>\<^sub>M \<B>) (the \<circ> f)) (A \<times> B) = 
     emeasure (distr R \<D> (fst \<circ> the \<circ> f)) A * emeasure \<B> B"
    (is "?L = ?R") if "A \<in> sets \<D>" "B \<in> sets \<B>" for A B 
  proof -
    have 3: "{bs. fst (the (f bs)) \<in> A \<and> bs \<in> C k} \<in> sets \<B>" (is "?L1 \<in> _") for k
    proof -
      have "?L1 = (fst \<circ> the \<circ> f) -` A \<inter> space (restrict_space R (C k))"
        using 5 unfolding vimage_def space_restrict_space R_def space_coin_space by auto 
      also have "... \<in> sets (restrict_space R (C k))"
        by (intro measurable_sets[OF _ that(1)] measurable_restrict_space1 fst_the_f_measurable)
      also have "... = sets (restrict_space \<B> (C k))"
        using 5 unfolding R_def sets_restrict_restrict_space space_restrict_space space_coin_space
        by (intro arg_cong2[where f="restrict_space"] arg_cong[where f="sets"] refl) auto
      finally have "?L1 \<in> sets (restrict_space \<B> (C k))"
        by simp
      thus "?L1 \<in> sets \<B>"
        using 6 space_coin_space sets_restrict_space_iff[where M="\<B>" and \<Omega>="C k"] by auto
    qed

    have 4: "{bs. the (f bs) \<in> A \<times> B \<and> bs \<in> C k} \<in> sets \<B>" (is "?L1 \<in> _") for k
    proof -
      have "?L1 = (the \<circ> f) -` (A \<times> B) \<inter> space (restrict_space R (C k))"
        using 5 unfolding vimage_def space_restrict_space R_def space_coin_space by auto 
      also have "... \<in> sets (restrict_space R (C k))"
        using that by (intro measurable_sets[where A="\<D> \<Otimes>\<^sub>M \<B>"] measurable_restrict_space1 
                       the_f_measurable) auto
      also have "... = sets (restrict_space \<B> (C k))"
        using 5 unfolding R_def sets_restrict_restrict_space space_restrict_space space_coin_space
        by (intro arg_cong2[where f="restrict_space"] arg_cong[where f="sets"] refl) auto
      finally have "?L1 \<in> sets (restrict_space \<B> (C k))"
        by simp
      thus "?L1 \<in> sets \<B>"
        using 6 space_coin_space sets_restrict_space_iff[where M="\<B>" and \<Omega>="C k"] by auto
    qed

    have "?L = emeasure R ((the \<circ> f) -` (A \<times> B) \<inter> space R)"
      using that the_f_measurable by (intro emeasure_distr) auto
    also have "... = emeasure R {x. the (f x) \<in> A \<times> B \<and> f x \<noteq> None}"
      unfolding vimage_def R_def Int_def
      by (simp add:space_restrict_space space_coin_space)
    also have "... = emeasure \<B> {x. the (f x) \<in> A \<times> B \<and> (\<exists>k. x \<in> C k)}"
      unfolding R_def 2 using 1 by (intro emeasure_restrict_space) auto
    also have "... = emeasure \<B> (\<Union>k. {x. the (f x) \<in> A \<times> B \<and> x \<in> C k})"
      by (intro arg_cong2[where f="emeasure"]) auto
    also have "... = (\<Sum>k. emeasure \<B> {x. the (f x) \<in> A \<times> B \<and> x \<in> C k})"
      using 4 C_disj
      by (intro suminf_emeasure[symmetric] subsetI) (auto simp:disjoint_family_on_def)
    also have "... = (\<Sum>k. emeasure (distr (\<B> \<Otimes>\<^sub>M \<B>) \<B> (\<lambda>(x,y). (stake k x@-y))) 
      {x. the (f x) \<in> A \<times> B \<and> x \<in> C k})"
      by (intro suminf_cong arg_cong2[where f="emeasure"] branch_coin_space(2)[symmetric] refl)
    also have "... = (\<Sum>k. emeasure (\<B> \<Otimes>\<^sub>M \<B>) 
      {x. the (f (stake k (fst x)@-snd x)) \<in> A \<times> B \<and> (stake k (fst x)@-snd x) \<in> C k})"
      using branch_coin_space(1) 4 by (subst emeasure_distr) 
        (simp_all add:case_prod_beta Int_def space_pair_measure space_coin_space)
    also have "... = (\<Sum>k. emeasure (\<B> \<Otimes>\<^sub>M \<B>) 
      {x. the (f (stake k (fst x)@-snd x)) \<in> A \<times> B \<and> fst x \<in> C k})"
      using 8 by (intro suminf_cong arg_cong2[where f="emeasure"] refl Collect_cong) auto
    also have "... = (\<Sum>k. emeasure (\<B> \<Otimes>\<^sub>M \<B>) ({x. fst (the (f x)) \<in> A \<and> x \<in> C k} \<times> B))"
      using 7 by (intro suminf_cong arg_cong2[where f="emeasure"] refl)
        (auto simp add:mem_Times_iff set_eq_iff) 
    also have "... = (\<Sum>k. emeasure \<B> {x. fst (the (f x)) \<in> A \<and> x \<in> C k} * emeasure \<B> B)"
      using 3 that(2)
      by (intro suminf_cong coin_space.emeasure_pair_measure_Times) auto
    also have "... = (\<Sum>k. emeasure \<B> {x. fst (the (f x)) \<in> A \<and> x \<in> C k}) * emeasure \<B> B"
      by simp
    also have "... = emeasure \<B> (\<Union>k. {x. fst (the (f x)) \<in> A \<and> x \<in> C k}) * emeasure \<B> B"
      using 3 C_disj
      by (intro arg_cong2[where f="(*)"] suminf_emeasure refl image_subsetI)
       (auto simp add:disjoint_family_on_def)
    also have "... = emeasure \<B> {x. fst (the (f x)) \<in> A \<and> (\<exists>k. x \<in> C k)} * emeasure \<B> B"
      by (intro arg_cong2[where f="emeasure"] arg_cong2[where f="(*)"]) auto
    also have "... = emeasure R {x. fst (the (f x)) \<in> A \<and> f x \<noteq> None} * emeasure \<B> B"
      unfolding R_def 2 using 1
      by (intro arg_cong2[where f="(*)"] emeasure_restrict_space[symmetric] subsetI) simp_all
    also have "... = emeasure R ((fst \<circ> the \<circ> f) -` A \<inter> space R) * emeasure \<B> B"
      unfolding vimage_def R_def Int_def by (simp add:space_restrict_space space_coin_space)
    also have "... = ?R" 
      using that
      by (intro arg_cong2[where f="(*)"] emeasure_distr[symmetric] fst_the_f_measurable) auto
    finally show ?thesis by simp
  qed

  have "finite_measure R"
    using 1 unfolding R_def space_coin_space 
    by (intro finite_measure_restrict_space) simp_all
  hence "finite_measure (distr R \<D> (fst \<circ> the \<circ> f))" 
    by (intro finite_measure.finite_measure_distr fst_the_f_measurable)
  hence 1:"sigma_finite_measure (distr R \<D> (fst \<circ> the \<circ> f))" 
    unfolding finite_measure_def by auto

  have 2:"sigma_finite_measure \<B>" 
    using prob_space_imp_sigma_finite[OF coin_space.prob_space_axioms] by simp

  show ?thesis
    using 0 by (intro pair_measure_eqI[symmetric] 1 2) (simp_all add:sets_pair_measure)
qed

end

lemma measure_rm_bind:
  assumes wf_m: "wf_random m"
  assumes wf_f: "\<And>x. x \<in> range_rm m \<Longrightarrow> wf_random (f x)"
  shows "measure_rm (m \<bind> f) = measure_rm m \<bind>
    (\<lambda>x. if x \<in> Some ` range_rm m then measure_rm (f (the x)) else return \<D> None)"
    (is "?L = ?R")
proof (rule measure_eqI)
  have "sets ?L = UNIV"
    unfolding measure_rm_def by simp
  also have "... = sets ?R"
    unfolding measure_rm_def by (subst sets_bind[where N="\<D>"])
      (simp_all add:option.case_distrib option.case_eq_if)
  finally show "sets ?L = sets ?R" by simp
next
  let ?m = "measure_rm"
  let ?H = "count_space (range_rm m)"

  fix A assume "A \<in> sets (measure_rm (m \<bind> f))"
  define N where "N = {x. m x \<noteq> None}"

  interpret wf_random_fun m
    unfolding wf_random_fun_def using wf_m by simp

  have ran_f: "wf_random_fun (f x)" if "x \<in> range_rm m" for x
    unfolding wf_random_fun_def using that wf_f by simp

  have N_meas: "N \<in> sets coin_space"
    unfolding N_def using R_sets by simp

  hence N_meas': "-N \<in> sets coin_space"
    unfolding Compl_eq_Diff_UNIV using space_coin_space by (metis sets.compl_sets)

  have wf_bind: "wf_random (m \<bind> f)"
    using wf_bind[OF assms] by auto

  interpret ran_bind: wf_random_fun "m \<bind> f"
    unfolding wf_random_fun_def using wf_bind by simp

  have 0: "(map_option fst \<circ> (m \<bind> f)) \<in> coin_space \<rightarrow>\<^sub>M \<D>"
    using ran_bind.measure_rm_measurable by auto
  have "(map_option fst \<circ> (m \<bind> f)) -` A = (map_option fst \<circ> (m \<bind> f)) -` A \<inter> space coin_space"
    unfolding space_coin_space by simp
  also have "... \<in> sets \<B>"
    by (intro measurable_sets[where A="\<D>"] 0) simp
  finally have 1: "(map_option fst \<circ> (m \<bind> f)) -` A \<in> sets coin_space"
    by simp

  have "{(v, bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m} =
    (map_option fst \<circ> case_prod f) -` A \<inter> space (?H \<Otimes>\<^sub>M \<B>)"
    unfolding vimage_def space_pair_measure space_coin_space by auto
  also have "... \<in> sets (?H \<Otimes>\<^sub>M \<B>)"
    using wf_random_fun.measure_rm_measurable[OF ran_f]
    by (intro measurable_sets[where A="\<D>"] measurable_pair_measure_countable1 countable_range)
      (simp_all add:comp_def)
  also have "... = sets (restrict_space \<D> (range_rm m) \<Otimes>\<^sub>M \<B>)"
    unfolding restrict_count_space inf_top_right by simp
  also have "... = sets (restrict_space (\<D> \<Otimes>\<^sub>M \<B>) (range_rm m \<times> space coin_space))"
    by (subst coin_space.restrict_space_pair_lift) auto
  finally have "{(v, bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m} \<in>
    sets (restrict_space (\<D> \<Otimes>\<^sub>M \<B>) (range_rm m \<times> UNIV))"
    unfolding space_coin_space by simp
  moreover have "range_rm m \<times> space coin_space \<in> sets (\<D> \<Otimes>\<^sub>M \<B>)"
    by (intro pair_measureI sets.top) auto
  ultimately have 2: "{(v, bs). map_option fst (f v bs) \<in> A \<and> v\<in> range_rm m} \<in> sets (\<D> \<Otimes>\<^sub>M \<B>)"
    by (subst (asm) sets_restrict_space_iff) (auto simp: space_coin_space)

  have space_R: "space R = {x. m x \<noteq> None}"
    unfolding R_def by (simp add:space_restrict_space space_coin_space)

  have 3: "measure_rm (f (the x)) \<in> space (subprob_algebra \<D>)"
    if "x \<in> Some ` range_rm m" for x
    using wf_random_fun.measure_rm_subprob_space[OF ran_f] wf_f that by fastforce

  have "(\<lambda>x. emeasure (measure_rm (f (fst (the (m x))))) A * indicator N x) =
    (\<lambda>x. emeasure (if m x \<noteq> None then measure_rm (f (fst (the (m x)))) else null_measure \<D>) A)"
    unfolding N_def by (intro ext) simp
  also have "... = (\<lambda>v. emeasure (if v\<in>Some`range_rm m then ?m (f (the v)) else null_measure \<D>) A)
    \<circ> (map_option fst \<circ> m)"
    unfolding comp_def by (intro ext arg_cong2[where f="emeasure"] refl if_cong)
      (auto intro:in_range_rmI simp add:vimage_def image_iff)
  also have "... \<in> borel_measurable coin_space"
    using 3 by (intro measurable_comp[where N="\<D>"]
        measurable_emeasure_kernel[where N="\<D>"] measure_rm_measurable) simp_all
  finally have 4:"(\<lambda>x. emeasure (measure_rm (f (fst (the (m x))))) A * indicator N x)
    \<in> coin_space \<rightarrow>\<^sub>M borel" by simp

  let ?N = "emeasure \<B> {bs. bs \<notin> N \<and> None \<in> A}"

  have "emeasure ?L A = emeasure \<B> ((map_option fst \<circ> (m \<bind> f)) -` A)"
    unfolding measure_rm_def using 0 by (subst emeasure_distr) (simp_all add:space_coin_space)
  also have "... =
    emeasure \<B> ((map_option fst\<circ>(m\<bind>f))-`A \<inter> -N) + emeasure \<B> ((map_option fst\<circ>(m\<bind>f))-`A \<inter> N)"
    using N_meas N_meas' 1
    by (subst emeasure_Un'[symmetric]) (simp_all add:Int_Un_distrib[symmetric])
  also have "... =
    emeasure \<B> ((map_option fst\<circ>(m\<bind>f))-`A\<inter> -N) + emeasure R ((map_option fst\<circ>(m\<bind>f))-`A\<inter> N)"
    using N_meas unfolding R_def N_def
    by (intro arg_cong2[where f="(+)"] refl emeasure_restrict_space[symmetric]) simp_all
  also have "... =?N + emeasure R ((the \<circ> m) -`
    {(v, bs). map_option fst (f v bs) \<in> A \<and> v\<in> range_rm m} \<inter> space R)"
    unfolding bind_rm_def N_def space_R apfst_def
    by (intro arg_cong2[where f="(+)"] arg_cong2[where f="emeasure"])
     (simp_all add: set_eq_iff in_range_rmI split:option.split bind_splits)
  also have "... = ?N + emeasure (distr R (\<D>\<Otimes>\<^sub>M\<B>) (the \<circ> m))
    {(v,bs). map_option fst (f v bs)\<in>A \<and> v\<in> range_rm m}"
    using 2 by (intro arg_cong2[where f="(+)"] emeasure_distr[symmetric]
          the_f_measurable map_prod_measurable) simp_all
  also have "... = ?N + emeasure (distr R \<D> (fst \<circ> the \<circ> m) \<Otimes>\<^sub>M \<B>)
    {(v,bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m}"
    unfolding N_def remainder_indep by simp
  also have "... =  ?N + \<integral>\<^sup>+ v. emeasure \<B>
    {bs. map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m} \<partial>distr R \<D> (fst \<circ> (the \<circ> m))"
    using 2 by (subst coin_space.emeasure_pair_measure_alt) (simp_all add:vimage_def comp_assoc)
  also have "... =  ?N + \<integral>\<^sup>+ x. emeasure \<B>
    {bs. map_option fst (f ((fst \<circ> (the \<circ> m)) x) bs) \<in> A \<and> (fst \<circ> (the \<circ> m)) x \<in> range_rm m} \<partial>R"
    using the_f_measurable by (intro arg_cong2[where f="(+)"] refl nn_integral_distr) simp_all
  also have "... = ?N + (\<integral>\<^sup>+x\<in>{bs. m bs \<noteq> None}. emeasure \<B>
    {bs. map_option fst (f (fst (the (m x))) bs) \<in> A \<and> fst (the (m x)) \<in> range_rm m} \<partial>\<B>)"
    using N_meas unfolding R_def N_def using nn_integral_restrict_space
    by (subst nn_integral_restrict_space) simp_all
  also have "... = ?N + (\<integral>\<^sup>+x\<in>{bs. m bs \<noteq> None}.
    emeasure \<B> ((map_option fst \<circ> f (fst (the (m x)))) -` A \<inter> space \<B>) \<partial>\<B>)"
    by (intro arg_cong2[where f="(+)"] set_nn_integral_cong refl arg_cong2[where f="emeasure"])
     (auto intro:in_range_rmI simp:space_coin_space)
  also have "... = ?N + (\<integral>\<^sup>+x\<in>N. emeasure (measure_rm(f(fst(the(m x))))) A \<partial>\<B>)"
    unfolding measure_rm_def N_def
    by (intro arg_cong2[where f="(+)"] set_nn_integral_cong refl emeasure_distr[symmetric]
        wf_random_fun.measure_rm_measurable[OF ran_f]) (auto intro:in_range_rmI)
  also have "... = (\<integral>\<^sup>+x. (indicator {bs. bs \<notin> N \<and> None \<in> A}) x  \<partial>\<B>) +
    (\<integral>\<^sup>+x\<in>N. emeasure (measure_rm(f(fst(the(m x))))) A \<partial>\<B>)"
    using N_meas N_meas'
    by (intro arg_cong2[where f="(+)"] nn_integral_indicator[symmetric] refl)
     (cases "None \<in> A"; auto simp:Collect_neg_eq)
  also have "... = \<integral>\<^sup>+ x. indicator {bs. bs \<notin> N \<and> None \<in> A} x +
           emeasure (measure_rm (f (fst (the (m x))))) A * indicator N x \<partial>\<B>"
    using N_meas' N_meas by (intro nn_integral_add[symmetric] 4) simp
  also have "... =  \<integral>\<^sup>+ x. indicator (-N) x * indicator A None +
    indicator N x * emeasure (measure_rm (f (fst (the (m x))))) A \<partial>\<B>"
    unfolding N_def by (intro arg_cong2[where f="nn_integral"] ext refl arg_cong2[where f="(+)"])
      (simp_all split:split_indicator)
  also have "... =
    \<integral>\<^sup>+ x. emeasure (case m x of None \<Rightarrow> return \<D> None | Some x \<Rightarrow> measure_rm (f (fst x))) A \<partial>\<B>"
    unfolding N_def by (intro arg_cong2[where f="nn_integral"] ext)
      (auto split:split_indicator option.split)
  also have "... = \<integral>\<^sup>+ x. emeasure (if (map_option fst \<circ> m) x \<in> Some ` range_rm m
    then measure_rm (f (the ((map_option fst \<circ> m) x)))
    else return \<D> None) A \<partial>\<B>"
    by (intro arg_cong2[where f="nn_integral"] arg_cong2[where f="emeasure"] refl ext)
     (auto simp add: in_range_rmI vimage_def split:option.splits)
  also have "... =
    \<integral>\<^sup>+ x. emeasure (if x \<in> Some ` range_rm m then ?m (f (the x)) else return \<D> None) A \<partial>?m m"
    unfolding measure_rm_def using measure_rm_measurable
    by (intro nn_integral_distr[symmetric]) (simp_all add:comp_def)
  also have "... = emeasure ?R A"
    using 3 none_measure_subprob_algebra
    by (intro emeasure_bind[symmetric, where N="\<D>"]) (auto simp add:measure_rm_def Pi_def)
  finally show "emeasure ?L A = emeasure ?R A"
    by simp
qed



(*
  f1 \<le> f2 \<le> ... 
  chain F \<Longrightarrow> wf_lub F    hmm

  lub_pmf (rm_pmf ` F) = rm_pmf (lub_rm F)

  lub_spmf (\<lambda>f. distr B discrete (map_opt fst o f)) ` F = distr B discrete (map_opt fst o lub_rm F)
  
  we already know that the RHS is well defined
  we can even go to the Abs_pmf

  lub_spmf (\<lambda>f. distr B discrete (map_opt fst o f)) ` F x
  = Sup f in F (Abs_pmf (distr B discrete (map_opt fst o f)) x) 
  = Sup f in F (measure {bs. map_opt fst (f bs) = Some x})   
        -- should be trivial because of the chain property
  \<le> (straightforward)
  \<ge> (because the fixed point is in the iterates?)
  
  =? measure {bs. map_opt fst (lub_rm F bs) = Some x}
  = .. 
  

*)

lemma "lub_spmf = undefined"
  sorry

definition run :: "'a random_monad \<Rightarrow> 'a option" 
    where "run f = map_option fst (f (random_bits 0))"

definition rm_measure :: "'a random_monad \<Rightarrow> 'a option measure" 
  where "rm_measure f = distr \<B> \<D> (map_option fst \<circ> f)"

definition rm_pmf :: "'a  random_monad \<Rightarrow> 'a spmf"
  where "rm_pmf f = Abs_pmf (rm_measure f)"

(*
  Better to use typedef
*)
lemma rm_pmf_bind:
  "rm_pmf (f \<bind> g) = rm_pmf f \<bind> (\<lambda>x. rm_pmf (g x))"
  sorry

lemma rm_pmf_coin:
  "rm_pmf coin = coin_spmf"
  sorry

lemma rm_pmf_return:
  "rm_pmf (return_rm x) = return_spmf x"
  sorry

definition weight :: "'a random_monad \<Rightarrow> real"
  where "weight f = weight_spmf (rm_pmf f)"

lemma hurd_rm_interp: 
  "partial_function_definitions (fun_ord (flat_ord None)) (fun_lub (flat_lub None))"
  by (intro partial_function_lift flat_interpretation)

definition rord  :: "'a random_monad \<Rightarrow> 'a random_monad \<Rightarrow> bool"
  where "rord = fun_ord (flat_ord None)"

definition rlub  :: "'a random_monad set \<Rightarrow> 'a random_monad"
  where "rlub = fun_lub (flat_lub None)"

interpretation random_monad_pd: 
  partial_function_definitions "rord" "rlub"
  unfolding rord_def rlub_def using hurd_rm_interp by auto

lemma wf_lub_helper:
  assumes "rord f g"
  assumes "wf_on_prefix f p r"
  shows "wf_on_prefix g p r"
proof -
  have "g (p@-cs) = Some (r, cs)" for cs
  proof -
    have "f (p@-cs) = Some (r,cs)"
      using assms(2) unfolding wf_on_prefix_def by auto
    moreover have "flat_ord None (f (p@-cs)) (g (p@-cs))"
      using assms(1) unfolding rord_def fun_ord_def by simp
    ultimately show ?thesis
      unfolding flat_ord_def by auto
  qed
  thus ?thesis
    unfolding wf_on_prefix_def by auto
qed

lemma wf_lub:
  assumes "Complete_Partial_Order.chain rord R"
  assumes "\<And>r. r \<in> R \<Longrightarrow> wf_random r"
  shows "wf_random (rlub R)"
proof (rule wf_randomI)
  fix bs
  assume a:"rlub R bs \<noteq> None"
  define S where "S = ((\<lambda>x. x bs) ` R)"
  have 0:"rlub R bs = flat_lub None S"
    unfolding S_def rlub_def fun_lub_def 
    by (intro arg_cong2[where f="flat_lub"]) auto

  have "rlub R bs = None" if "S \<subseteq> {None}"
    using that unfolding 0 flat_lub_def by auto
  hence "\<not> (S \<subseteq> {None})"
    using a by auto
  then obtain r where 1:"r \<in> R" and 2: "r bs \<noteq> None"
    unfolding S_def by blast 
  then obtain p y where 3:"sprefix p bs" and 4:"wf_on_prefix r p y"
    using assms(2)[OF 1] 2 unfolding wf_random_def by (auto split:option.split_asm)
  have "wf_on_prefix (rlub R) p y"
    by (intro wf_lub_helper[OF _ 4] random_monad_pd.lub_upper 1 assms(1))
  thus "\<exists>p r. sprefix p bs \<and> wf_on_prefix (rlub R) p r "
    using 3 by auto
qed

abbreviation "mono_rm \<equiv> monotone (fun_ord rord) (rord)"

lemma bind_mono_aux:
  assumes "rord f1 f2" "\<And>y. rord (g1 y) (g2 y)"
  shows "rord (bind_rm f1 g1) (bind_rm f2 g2)"
proof -
  have "flat_ord None (bind_rm f1 g1 bs) (bind_rm f2 g2 bs)" for bs
  proof (cases "(f1 \<bind> g1) bs")
    case None
    then show ?thesis by (simp add:flat_ord_def)
  next
    case (Some a)
    then obtain y bs' where 0: "f1 bs = Some (y,bs')" and 1:"g1 y bs' \<noteq> None" and "f1 bs \<noteq> None"
      by (cases "f1 bs", auto simp:bind_rm_def)
    hence "f2 bs = f1 bs"
      using assms(1) unfolding rord_def fun_ord_def flat_ord_def by metis
    hence "f2 bs = Some (y,bs')"
      using 0 by auto
    moreover have "g1 y bs' = g2 y bs'"
      using assms(2) 1 unfolding rord_def fun_ord_def flat_ord_def by metis
    ultimately have "(f1 \<bind> g1) bs = (f2 \<bind> g2) bs"
      unfolding bind_rm_def 0 by auto
    thus ?thesis unfolding flat_ord_def by auto
  qed
  thus ?thesis
    unfolding rord_def fun_ord_def by simp
qed

lemma bind_mono [partial_function_mono]:
  assumes "mono_rm B" and "\<And>y. mono_rm (C y)"
  shows "mono_rm (\<lambda>f. bind_rm (B f) (\<lambda>y. C y f))"
  using assms by (intro monotoneI bind_mono_aux) (auto simp:monotone_def)

declaration \<open>Partial_Function.init "random_monad" \<^term>\<open>random_monad_pd.fixp_fun\<close>
  \<^term>\<open>random_monad_pd.mono_body\<close> 
  @{thm random_monad_pd.fixp_rule_uc} @{thm random_monad_pd.fixp_induct_uc}
  NONE\<close>

declare [[function_internals]]

partial_function (option) testo :: "nat \<Rightarrow> nat option"
  where "testo x = Some x"

declare testo.simps[code]

partial_function (random_monad) test1 :: "nat \<Rightarrow> nat random_monad"
  where "test1 n = return_rm n"

partial_function (random_monad) test2 :: "bool \<Rightarrow> bool random_monad"
  where "test2 x = bind_rm coin_rm return_rm"

partial_function (random_monad) test3 :: "unit \<Rightarrow> unit random_monad"
  where
    "test3 _ = do {
      c \<leftarrow> coin_rm;
      if c then test3 () else return_rm ()
    }"


partial_function (random_monad) test :: "nat \<Rightarrow> nat random_monad"
  where
    "test n = do {
      c \<leftarrow> coin_rm;
      if c then (test (n+1)) else return_rm n
    }"

declare test.simps[code]
print_theorems

definition test1d :: "nat \<Rightarrow> nat random_monad"
  where "test1d = return_rm"

definition run_test where "run_test = run (test 1)"

export_code testo test in Haskell
print_theorems


partial_function (spmf) test_spmf :: "nat \<Rightarrow> nat spmf"
  where
    "test_spmf n = do {
      c \<leftarrow> coin_spmf;
      if c then (test_spmf (n+1)) else return_spmf n
    }"


print_theorems

thm test_spmf_def

lemma "rm_pmf (test n) = test_spmf n"
  using test1_def test3_def
  unfolding test_spmf_def test_def
  sorry


end
