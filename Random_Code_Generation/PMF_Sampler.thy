theory PMF_Sampler
  imports Main
    "HOL-Probability.Probability"
    "HOL-Library.Code_Lazy"
    "Zeta_Function.Zeta_Library"
    (* The last import is to pull set_nn_integral_cong which should be in
    HOL-Analysis.Set_Integral. *)
begin

hide_const (open) ord

text \<open>Abbreviation for the discrete $\sigma$-algebra. (Do not use, if the measure is important.)\<close>

abbreviation discrete where "discrete \<equiv> count_space UNIV"

lemma Option_bind_conv_case: "Option.bind x f = (case x of None \<Rightarrow> None | Some x \<Rightarrow> f x)"
  by (auto split: option.splits)

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

definition coin_space :: "bool stream measure" where
  "coin_space = stream_space (measure_pmf (pmf_of_set UNIV))"

lemma space_coin_space: "space coin_space = UNIV"
  by (simp add: coin_space_def space_stream_space)

interpretation coin_space: prob_space coin_space
  unfolding coin_space_def
  by (intro prob_space.prob_space_stream_space prob_space_measure_pmf)

definition options :: "'a set \<Rightarrow> 'a option set" where
  "options X = insert None (Some ` X)"

lemma None_in_options [simp]: "None \<in> options X"
  by (auto simp: options_def)

lemma Some_in_options_iff [simp]: "Some x \<in> options X \<longleftrightarrow> x \<in> X"
  by (auto simp: options_def)

lemma range_Some: "range Some = -{None}"
  using notin_range_Some by blast

lemma vimage_Some_insert_None [simp]: "Some -` insert None X = Some -` X"
  by auto

lemma countable_options [intro]:
  assumes "countable A"
  shows   "countable (options A)"
  using assms unfolding options_def by blast

type_synonym 'a pmfsr = "bool stream \<Rightarrow> ('a \<times> nat) option"

definition range_pmfsr where "range_pmfsr r = fst ` Some -` range r"

definition wf_pmfsr :: "'a pmfsr \<Rightarrow> bool" where
  "wf_pmfsr p \<longleftrightarrow>
     (\<forall>bs. case p bs of None \<Rightarrow> True | Some (x, n) \<Rightarrow>
       (\<forall>bs'. stake n bs' = stake n bs \<longrightarrow> p bs' = p bs))"

lemma wf_pmfsr_const_None [simp, intro]: "wf_pmfsr (\<lambda>_. None)"
  by (auto simp: wf_pmfsr_def)

lemma in_range_pmfsrI:
  assumes "r bs = Some (y, n)"
  shows   "y \<in> range_pmfsr r"
proof -
  have "Some (y, n) \<in> range r"
    by (rule range_eqI[of _ _ bs]) (use assms in auto)
  thus ?thesis
    unfolding range_pmfsr_def
    by (intro image_eqI[of _ _ "(y, n)"]) (use assms in auto)
qed

lemma in_range_pmfsr: "r bs \<in> options (range_pmfsr r \<times> UNIV)"
proof (cases "r bs")
  case [simp]: (Some z)
  obtain y n where [simp]: "z = (y, n)"
    by (cases z)
  have "y \<in> range_pmfsr r"
    by (rule in_range_pmfsrI[of _ bs _ n]) auto
  thus ?thesis
    by auto
qed auto

lemma wf_pmfsrI:
  assumes "\<And>bs bs' x n. r bs = Some (x, n) \<Longrightarrow> stake n bs' = stake n bs \<Longrightarrow> r bs' = Some (x, n)"
  shows "wf_pmfsr r"
  unfolding wf_pmfsr_def
proof
  fix bs :: "bool stream"
  show "case r bs of None \<Rightarrow> True
          | Some (xa, n) \<Rightarrow> \<forall>bs'. stake n bs' = stake n bs \<longrightarrow> r bs' = r bs"
  proof (cases "r bs")
    case (Some xn)
    thus ?thesis
      using assms[of bs "fst xn" "snd xn"] by auto
  qed auto
qed


lemma wf_pmfsrD:
  assumes "wf_pmfsr r" "r bs = Some (x, n)" "stake n bs' = stake n bs"
  shows   "r bs' = Some (x, n)"
proof -
  have "(case r bs of None \<Rightarrow> True
         | Some (xa, n) \<Rightarrow> \<forall>bs'. stake n bs' = stake n bs \<longrightarrow> r bs' = r bs)"
    using assms(1) unfolding wf_pmfsr_def by blast
  thus ?thesis using assms(2-)
    by auto
qed

lemma countable_range_pmfsr:
  assumes "wf_pmfsr r"
  shows   "countable (range_pmfsr r)"
proof -
  define f where "f = (\<lambda>bs. fst (the (r (bs @- sconst False))))"
  have "range_pmfsr r \<subseteq> range f"
  proof
    fix x assume "x \<in> range_pmfsr r"
    then obtain bs n where bs: "r bs = Some (x, n)"
      by (auto simp: range_pmfsr_def eq_commute)
    have "r (stake n bs @- sconst False) = Some (x, n)"
      by (rule wf_pmfsrD[OF assms bs]) auto
    hence "f (stake n bs) = x"
      by (auto simp: f_def)
    thus "x \<in> range f"
      by blast
  qed
  thus ?thesis
    by (rule countable_subset) auto
qed

lemma range_pmfsr_subset: "range r \<subseteq> options (range_pmfsr r \<times> UNIV)"
proof
  fix xn assume "xn \<in> range r"
  then obtain bs where [simp]: "r bs = xn"
    by (auto simp: eq_commute)
  show "xn \<in> options (range_pmfsr r \<times> UNIV)"
  proof (cases xn)
    case [simp]: (Some xn')
    obtain x n where [simp]: "xn' = (x, n)"
      by (cases xn')
    have "x \<in> range_pmfsr r"
      by (rule in_range_pmfsrI[of _ bs _ n]) auto
    thus ?thesis
      by auto
  qed auto
qed

lemma countable_range_pmfsr':
  assumes "wf_pmfsr r"
  shows   "countable (range r)"
proof (rule countable_subset)
  show "range r \<subseteq> options (range_pmfsr r \<times> UNIV)"
    by (rule range_pmfsr_subset)
  show "countable (options (range_pmfsr r \<times> (UNIV :: nat set)))"
    using countable_range_pmfsr[OF assms] by blast
qed

lemma measurable_pmfsr:
  assumes "wf_pmfsr r"
  shows   "r \<in> coin_space \<rightarrow>\<^sub>M count_space UNIV"
proof -
  have *: "r -` Some ` X \<in> sets coin_space" if X: "X \<subseteq> range_pmfsr r \<times> UNIV" for X
  proof -
    define A where "A = {bs |bs x. r (bs @- sconst False) = Some (x, length bs) \<and> (x, length bs) \<in> X}"
    have "(\<Union>bs\<in>A. stake (length bs) -` {bs} \<inter> space coin_space) \<in> sets coin_space"
    proof (rule sets.countable_UN'')
      show "stake (length bs) -` {bs} \<inter> space coin_space \<in> coin_space.events" for bs
        unfolding coin_space_def by measurable
    qed auto
    also have "(\<Union>bs\<in>A. stake (length bs) -` {bs} \<inter> space coin_space) = (\<Union>bs\<in>A. stake (length bs) -` {bs})"
      by (simp add: space_coin_space)
    also have "\<dots> = r -` Some ` X"
    proof safe
      fix bs x n
      assume *: "r bs = Some (x, n)" "(x, n) \<in> X"
      define bs' where "bs' = stake n bs"
      have **: "r (bs' @- sconst False) = Some (x, n)"
        by (rule wf_pmfsrD[OF assms *(1)]) (auto simp: bs'_def)
      from ** have "bs' \<in> A"
        using * by (auto simp: A_def bs'_def)
      moreover have "bs \<in> stake (length bs') -` {bs'}"
        by (auto simp: bs'_def)
      ultimately show "bs \<in> (\<Union>bs\<in>A. stake (length bs) -` {bs})"
        by blast
    next
      fix bs' bs
      assume bs': "bs' \<in> A" "stake (length bs') bs = bs'"
      define n where "n = length bs'"
      from bs'(1) obtain x where xn: "r (bs' @- sconst False) = Some (x, n)" "(x, n) \<in> X"
        unfolding A_def by (auto simp: n_def)
      have "r bs = Some (x, n)"
        by (rule wf_pmfsrD[OF assms xn(1)]) (use bs'(2) in \<open>auto simp: n_def\<close>)
      thus "bs \<in> r -` Some ` X"
        using xn by auto
    qed
    finally show ?thesis .
  qed

  have **: "r -` Some ` X \<in> sets coin_space" for X
  proof -
    have "r -` Some ` (X \<inter> (range_pmfsr r \<times> UNIV)) \<in> sets coin_space"
      by (intro *) auto
    also have "r -` Some ` (X \<inter> (range_pmfsr r \<times> UNIV)) = r -` Some ` X"
      by (auto simp add: in_range_pmfsrI)
    finally show ?thesis .
  qed

  have ***: "r -` X \<in> sets coin_space" if "None \<notin> X" for X
  proof -
    have "r -` Some ` Some -` X \<in> sets coin_space"
      by (intro **)
    also have "Some ` Some -` X = X"
      using that by (subst image_vimage_eq) (auto simp: range_Some)
    finally show ?thesis .
  qed

  show ?thesis
  proof (rule measurableI)
    show "r -` X \<inter> space coin_space \<in> sets coin_space" for X
    proof (cases "None \<in> X")
      case False
      thus ?thesis using *** by blast
    next
      case True
      hence "r -` (-X) \<in> sets coin_space"
        by (intro ***) auto
      hence "space coin_space - r -` (-X) \<in> sets coin_space"
        by blast
      also have "space coin_space - r -` (-X) = r -` X"
        by (auto simp: space_coin_space)
      finally show ?thesis
        by (simp add: space_coin_space)
    qed
  qed auto
qed


definition return_pmfsr :: "'a \<Rightarrow> 'a pmfsr" where
  "return_pmfsr x bs = Some (x, 0)"

definition coin_pmfsr :: "bool pmfsr" where
  "coin_pmfsr bs = Some (shd bs, 1)"

definition bind_pmfsr :: "'a pmfsr \<Rightarrow> ('a \<Rightarrow> 'b pmfsr) \<Rightarrow> 'b pmfsr" where
  "bind_pmfsr r f bs =
     do {(x, m) \<leftarrow> r bs; (y, n) \<leftarrow> f x (sdrop m bs); Some (y, m + n)}"

definition consumption_pmfsr :: "'a pmfsr \<Rightarrow> nat pmfsr" where
  "consumption_pmfsr r bs = map_option (\<lambda>(_, n). (n, n)) (r bs)"


adhoc_overloading Monad_Syntax.bind bind_pmfsr

definition map_pmfsr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pmfsr \<Rightarrow> 'b pmfsr" where
  "map_pmfsr f r bs = map_option (map_prod f id) (r bs)"

lemma map_pmfsr_id [simp]: "map_pmfsr id r = r"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

lemma map_pmfsr_id' [simp]: "map_pmfsr (\<lambda>x. x) r = r"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

lemma map_pmfsr_return [simp]: "map_pmfsr f (return_pmfsr x) = return_pmfsr (f x)"
  by (auto simp: map_pmfsr_def return_pmfsr_def)

lemma map_pmfsr_comp: "map_pmfsr (f \<circ> g) r = map_pmfsr f (map_pmfsr g r)"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

lemma map_pmfsr_conv_bind_pmfsr: "map_pmfsr f r = bind_pmfsr r (\<lambda>x. return_pmfsr (f x))"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def map_pmfsr_def Option_bind_conv_case
           split: option.splits)

lemma bind_return_pmfsr': "bind_pmfsr r return_pmfsr = r"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def Option_bind_conv_case
           split: option.splits)

lemma bind_return_pmfsr: "bind_pmfsr (return_pmfsr x) r = r x"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def  Option_bind_conv_case
           split: option.splits)

lemma bind_assoc_pmfsr: "(A :: 'a pmfsr) \<bind> B \<bind> C = A \<bind> (\<lambda>x. B x \<bind> C)"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def Option_bind_conv_case
           split: option.splits)

lemma bind_pmfsr_cong:
  "p = q \<Longrightarrow> (\<And>x. x \<in> range_pmfsr q \<Longrightarrow> f x = g x) \<Longrightarrow> bind_pmfsr p f = bind_pmfsr q g"
  by (auto simp: bind_pmfsr_def fun_eq_iff Option_bind_conv_case in_range_pmfsrI split: option.splits)


lemma range_return_pmfsr [simp]: "range_pmfsr (return_pmfsr x) = {x}"
  by (auto simp: return_pmfsr_def range_pmfsr_def)

lemma wf_return_pmfsr: "wf_pmfsr (return_pmfsr x)"
proof -
  have "fst ` Some -` range (\<lambda>bs::bool stream. Some (x, 0 :: nat)) = {x}"
    by auto
  moreover have "wf_pmfsr (return_pmfsr x)"
    by (auto simp: wf_pmfsr_def return_pmfsr_def)
  ultimately show ?thesis
    unfolding wf_pmfsr_def return_pmfsr_def[abs_def] range_pmfsr_def by auto
qed

lemma range_coin_pmfsr [simp]: "range_pmfsr coin_pmfsr = UNIV"
proof safe
  fix b :: bool
  show "b \<in> range_pmfsr coin_pmfsr"
    by (rule in_range_pmfsrI[of _ "sconst b" _ 1]) (auto simp: coin_pmfsr_def)
qed auto

lemma wf_coin_pmfsr: "wf_pmfsr coin_pmfsr"
proof -
  have "coin_space.random_variable (count_space UNIV) (\<lambda>bs. Some (shd bs, 1::nat))"
    unfolding coin_space_def by measurable
  moreover have "wf_pmfsr coin_pmfsr"
    by (auto simp: wf_pmfsr_def coin_pmfsr_def)
  ultimately show ?thesis
    unfolding wf_pmfsr_def coin_pmfsr_def range_pmfsr_def by auto
qed

lemma wf_consumption_pmfsr:
  assumes "wf_pmfsr r"
  shows   "wf_pmfsr (consumption_pmfsr r)"
proof (rule wf_pmfsrI)
  fix bs bs' x n
  assume "consumption_pmfsr r bs = Some (x, n)" "stake n bs' = stake n bs"
  thus "consumption_pmfsr r bs' = Some (x, n)"
    unfolding consumption_pmfsr_def using assms by (auto dest: wf_pmfsrD)
qed

lemma range_bind_pmfsr_subset:
  "range_pmfsr (bind_pmfsr r f) \<subseteq> (\<Union>x\<in>range_pmfsr r. range_pmfsr (f x))"
proof safe
  fix x assume "x \<in> range_pmfsr (bind_pmfsr r f)"
  then obtain bs y m n where *: "r bs = Some (y, m)" "f y (sdrop m bs) = Some (x, n)"
    by (auto simp: range_pmfsr_def bind_pmfsr_def split: Option.bind_splits)
  have "Some (y, m) \<in> range r"
    by (rule range_eqI[of _ _ bs]) (use * in auto)
  hence "y \<in> fst ` Some -` range r"
    by (intro image_eqI[of _ _ "(y, m)"]) (use * in auto)
  hence "y \<in> range_pmfsr r"
    by (auto simp: range_pmfsr_def)
  moreover have "Some (x, n) \<in> range (f y)"
    by (rule range_eqI[of _ _ "sdrop m bs"]) (use * in auto)
  hence "x \<in> fst ` Some -` range (f y)"
    by (intro image_eqI[of _ _ "(x, n)"]) auto
  hence "x \<in> range_pmfsr (f y)"
    by (auto simp: range_pmfsr_def)
  ultimately show "x \<in> (\<Union>y\<in>range_pmfsr r. range_pmfsr (f y))"
    by blast
qed

lemma range_bind_pmfsr_eq:
  assumes "wf_pmfsr r"
  shows   "range_pmfsr (bind_pmfsr r f) = (\<Union>x\<in>range_pmfsr r. range_pmfsr (f x))"
proof
  show "range_pmfsr (bind_pmfsr r f) \<subseteq> (\<Union>x\<in>range_pmfsr r. range_pmfsr (f x))"
    by (rule range_bind_pmfsr_subset)
next
  show "(\<Union>x\<in>range_pmfsr r. range_pmfsr (f x)) \<subseteq> range_pmfsr (bind_pmfsr r f)"
  proof safe
    fix y x
    assume y: "y \<in> range_pmfsr r" and x: "x \<in> range_pmfsr (f y)"
    from y obtain m bs where y': "r bs = Some (y, m)"
      unfolding range_pmfsr_def by (auto simp: eq_commute)
    from x obtain n bs' where x': "f y bs' = Some (x, n)"
      by (auto simp: range_pmfsr_def eq_commute)
    define bs'' where "bs'' = Stream.shift (stake m bs) bs'"
    have y'': "r bs'' = Some (y, m)"
      by (rule wf_pmfsrD[where bs = bs])
         (use y' assms(1) in \<open>auto simp: bs''_def\<close>)
    have bs'': "sdrop m bs'' = bs'"
      by (auto simp: bs''_def)
    have "Some (x, m+n) \<in> range (bind_pmfsr r f)"
      by (rule range_eqI[of _ _ bs'']) (auto simp: bind_pmfsr_def bs'' y'' x')
    hence "x \<in> fst ` Some -` range (bind_pmfsr r f)"
      by (intro image_eqI[of _ _ "(x, m+n)"]) auto
    thus "x \<in> range_pmfsr (bind_pmfsr r f)"
      using y'' x' bs'' unfolding range_pmfsr_def by blast
  qed
qed

lemma range_map_pmfsr: "range_pmfsr (map_pmfsr f r) = f ` range_pmfsr r"
proof safe
  fix y assume "y \<in> range_pmfsr (map_pmfsr f r)"
  then obtain n bs where bs: "Some (y, n) = map_option (map_prod f id) (r bs)"
    unfolding map_pmfsr_def range_pmfsr_def by auto
  then obtain x where x: "r bs = Some (x, n)" "y = f x"
    by (cases "r bs") auto
  thus "y \<in> f ` range_pmfsr r"
    by (auto simp: x bs intro!: imageI intro: in_range_pmfsrI[of _ bs _ n])
next
  fix x assume "x \<in> range_pmfsr r"
  then obtain bs n where "r bs = Some (x, n)"
    by (auto simp: range_pmfsr_def eq_commute)
  thus "f x \<in> range_pmfsr (map_pmfsr f r)"
    by (intro in_range_pmfsrI[of _ bs _ n]) (auto simp: map_pmfsr_def)
qed


lemma wf_bind_pmfsr:
  assumes "wf_pmfsr r"
  assumes "\<And>x. x \<in> range_pmfsr r \<Longrightarrow> wf_pmfsr (f x)"
  shows   "wf_pmfsr (bind_pmfsr r f)"
proof -
  define A where "A = range_pmfsr (bind_pmfsr r f)"
  define B where "B = options (A \<times> (UNIV :: nat set))"
  have "countable A" unfolding A_def using assms
    by (intro countable_subset [OF range_bind_pmfsr_subset] countable_UN countable_range_pmfsr)
       (use assms in \<open>auto simp: wf_pmfsr_def\<close>)

  show ?thesis
  proof (rule wf_pmfsrI)
    fix bs bs' :: "bool stream" and x :: 'b and n :: nat
    assume *: "bind_pmfsr r f bs = Some (x, n)" "stake n bs' = stake n bs"
    have r: "wf_pmfsr r"
      using assms(1) by (simp add: wf_pmfsr_def)
    from * obtain y m where ym: "r bs = Some (y, m)" "m \<le> n" "f y (sdrop m bs) = Some (x, n-m)"
      by (auto simp: bind_pmfsr_def Option_bind_conv_case split: option.splits)
    have stake_eq': "stake m bs' = stake m bs"
      using \<open>m \<le> n\<close> * by (metis length_stake stake_sdrop stake_shift_small)
    have ym': "r bs' = Some (y, m)"
      by (rule wf_pmfsrD[OF r, of bs]) (use * ym stake_eq' in auto)

    have "y \<in> range_pmfsr r"
      using ym(1) by (blast intro: in_range_pmfsrI)
    hence fy: "wf_pmfsr (f y)"
      using assms by (auto simp: wf_pmfsr_def)
    have stake_eq'': "stake (n - m) (sdrop m bs') = stake (n - m) (sdrop m bs)"
      by (metis "*"(2) drop_stake)
    have "f y (sdrop m bs') = Some (x, n-m)"
      by (rule wf_pmfsrD[OF fy, of "sdrop m bs"]) (use ym stake_eq'' in auto)
    thus "bind_pmfsr r f bs' = Some (x, n)"
      by (auto simp: ym ym' bind_pmfsr_def)
  qed
qed

lemma wf_map_pmfsr:
  assumes "wf_pmfsr r"
  shows   "wf_pmfsr (map_pmfsr f r)"
  using assms unfolding map_pmfsr_conv_bind_pmfsr
  by (intro wf_bind_pmfsr wf_return_pmfsr)

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

definition loss_pmfsr :: "'a pmfsr \<Rightarrow> real" where
  "loss_pmfsr r = coin_space.prob (r -` {None})"

definition measure_pmfsr :: "'a pmfsr \<Rightarrow> 'a option measure" where
  "measure_pmfsr p = distr coin_space (count_space UNIV) (map_option fst \<circ> p)"

lemma append_measurable:
  "(\<lambda>bs. x @- bs) \<in> coin_space \<rightarrow>\<^sub>M coin_space"
proof -
  have "(\<lambda>bs. (x @- bs) !! n) \<in> coin_space \<rightarrow>\<^sub>M discrete" for n
  proof (cases "n < length x")
    case True
    have "(\<lambda>bs. (x @- bs) !! n) = (\<lambda>bs. x ! n)"
      using True by simp
    also have "... \<in> coin_space \<rightarrow>\<^sub>M discrete"
      by simp
    finally show ?thesis by simp
  next
    case False
    have "(\<lambda>bs. (x @- bs) !! n) = (\<lambda>bs. bs !! (n - length x))"
      using False by simp
    also have "... \<in> coin_space \<rightarrow>\<^sub>M (measure_pmf (pmf_of_set UNIV))"
      unfolding coin_space_def by (intro measurable_snth)
    also have "... = coin_space \<rightarrow>\<^sub>M discrete"
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
  "distr (pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M coin_space) coin_space (\<lambda>(x,y). x@-y) = coin_space"
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
  "distr coin_space discrete (stake n) = pmf_of_set {bs. length bs = n}" (is "?L = ?R")
proof -
  have 1: "stake n \<in> coin_space \<rightarrow>\<^sub>M discrete"
    unfolding coin_space_def by simp

  have "{x \<in> space (?R \<Otimes>\<^sub>M coin_space). (stake n \<circ> (\<lambda>(x, y). x @- y)) x = fst x} =
    (\<lambda>(x,y). stake n (x @- y) = x) -` {True} \<inter> space (?R \<Otimes>\<^sub>M coin_space)"
    by (auto simp add:set_eq_iff comp_def)
  also have "... \<in> sets (?R \<Otimes>\<^sub>M coin_space)"
    using append_measurable 1 by (intro measurable_sets[where A="discrete"]) auto
  finally have 2: "{x \<in> space (?R \<Otimes>\<^sub>M coin_space). (stake n \<circ> (\<lambda>(x, y). x @- y)) x = fst x} \<in>
    sets (?R \<Otimes>\<^sub>M coin_space)"
    by simp

  have 0: "AE x in ?R \<Otimes>\<^sub>M coin_space. (stake n \<circ> (\<lambda>(x, y). x @- y)) x = fst x"
    using  coin_space.sigma_finite_measure bool_list_set
    by (intro pair_sigma_finite.AE_pair_measure AE_pmfI 2 AE_I2)
     (simp_all add:pair_sigma_finite_def measure_pmf.sigma_finite_measure_axioms)

  have "?L = distr (distr (?R  \<Otimes>\<^sub>M coin_space) coin_space (\<lambda>(x,y). x@-y)) discrete (stake n)"
    by (subst split_coin_space)  simp
  also have "... = distr (?R \<Otimes>\<^sub>M coin_space) discrete (stake n \<circ> (\<lambda>(x, y). x @- y))"
    using append_measurable 1 by (intro distr_distr) simp_all
  also have "... = distr (?R \<Otimes>\<^sub>M coin_space) discrete fst"
    using append_measurable 0 1
    by (intro distr_cong_AE refl measurable_comp[where N="coin_space"]) simp_all
  also have "... = distr (?R \<Otimes>\<^sub>M coin_space) ?R fst"
    by (intro distr_cong refl) simp
  also have "... = ?R"
    by (intro coin_space.distr_pair_fst)
  finally show ?thesis
    by simp
qed

lemma map_prod_measurable[measurable]:
  assumes "f \<in> M \<rightarrow>\<^sub>M M'"
  assumes "g \<in> N \<rightarrow>\<^sub>M N'"
  shows "map_prod f g \<in> M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M M' \<Otimes>\<^sub>M N'"
  using assms by (subst measurable_pair_iff) simp


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

lemma measure_pmfsr_subprob_space:
  assumes "wf_pmfsr p"
  shows "measure_pmfsr p \<in> space (subprob_algebra discrete)"
proof -
  have "prob_space (measure_pmfsr p)"
    unfolding measure_pmfsr_def using measurable_pmfsr[OF assms]
    by (intro coin_space.prob_space_distr measurable_comp[where N="discrete"]) auto
  moreover have "sets (measure_pmfsr p) = discrete"
    unfolding measure_pmfsr_def by simp
  ultimately show ?thesis
    unfolding space_subprob_algebra using prob_space_imp_subprob_space
    by auto
qed

context
  fixes m :: "'a pmfsr"
  fixes f :: "'a \<Rightarrow> 'b pmfsr"
  assumes wf_m: "wf_pmfsr m"
  assumes wf_f: "\<And>x. x \<in> range_pmfsr m \<Longrightarrow> wf_pmfsr (f x)"
begin

private definition R where "R = restrict_space coin_space {bs. m bs \<noteq> None}"

text \<open>This function \<mu> attaches the remaining coins to the result. It is only well-defined on
the @{term "restrict_space coin_space {bs. m bs \<noteq> None}"}.\<close>

private definition \<mu> where "\<mu> bs = (the (m bs), sdrop (snd (the (m bs))) bs)"

lemma none_measure_subprob_algebra:
  "return discrete None \<in> space (subprob_algebra discrete)"
  by (metis measure_subprob return_pmf.rep_eq)

lemma measure_bind_pmfsr_helper_2:
  shows
    "\<mu> \<in> R \<rightarrow>\<^sub>M (discrete \<Otimes>\<^sub>M coin_space)"
    "(\<lambda>x. the (m x)) \<in> R \<rightarrow>\<^sub>M discrete" "the \<circ> m  \<in> R \<rightarrow>\<^sub>M discrete"
    "distr R (discrete \<Otimes>\<^sub>M coin_space) \<mu> = distr R discrete (the \<circ> m) \<Otimes>\<^sub>M coin_space"
    (is "?L = ?R")
proof -
  have [measurable]: "sdrop i \<in> R \<rightarrow>\<^sub>M coin_space" for i
    unfolding R_def coin_space_def
    by (intro measurable_restrict_space1 measurable_sdrop)

  have "(\<lambda>x. snd (the (m x))) \<in> R \<rightarrow>\<^sub>M discrete"
    unfolding R_def
    by (intro measurable_restrict_space1 measurable_compose[OF measurable_pmfsr[OF wf_m]]) simp

  hence 0:"(\<lambda>x. sdrop (snd (the (m x))) x) \<in> R \<rightarrow>\<^sub>M coin_space"
    by measurable

  show 1:"(\<lambda>x. the (m x)) \<in> R \<rightarrow>\<^sub>M discrete"
    unfolding R_def
    by (intro measurable_restrict_space1 measurable_compose[OF measurable_pmfsr[OF wf_m]]) simp
  thus "the \<circ> m  \<in> R \<rightarrow>\<^sub>M discrete"
    unfolding comp_def by simp

  have 4:"{bs. m bs \<noteq> None} \<inter> space coin_space \<in> coin_space.events"
    using measurable_pmfsr[OF wf_m] by measurable

  show 2: "\<mu> \<in> R \<rightarrow>\<^sub>M (discrete \<Otimes>\<^sub>M coin_space)"
    unfolding \<mu>_def by (intro measurable_Pair 0 1)

  define B :: "nat \<Rightarrow> (('a \<times> nat) \<times> bool stream) set"
    where "B k = {(x,bs). snd x = k}" for k :: nat

  have B_sets: "B k \<in> sets (discrete \<Otimes>\<^sub>M coin_space)" for k
  proof -
    have "B k = (snd -` {k}) \<times> space coin_space"
      unfolding B_def vimage_def space_coin_space by auto
    also have "... \<in> sets (discrete \<Otimes>\<^sub>M coin_space)"
      by (intro pair_measureI) auto
    finally show ?thesis by simp
  qed

  have 3:"emeasure ?L A = emeasure ?R A" if "A \<in> sets ?L" and a3: "A \<subseteq> B k" for k A
  proof -
    let ?S = "(measure_pmf (pmf_of_set {xs. length xs = k}) \<Otimes>\<^sub>M coin_space)"

    have "{bs. (the (m bs), sdrop k bs) \<in> A \<and> (m bs \<noteq> None)} =
      ((\<lambda>bs. (the (m bs), sdrop k bs)) -` A \<inter> space R)"
      unfolding R_def by (simp add: vimage_def space_restrict_space Int_def space_coin_space)
    also have "... \<in> sets R"
      using 1 that(1) by (intro measurable_sets[where A="discrete \<Otimes>\<^sub>M coin_space"]) simp_all
    finally have "{bs. (the (m bs), sdrop k bs) \<in> A \<and> (m bs \<noteq> None)} \<in> sets R"
      by simp
    hence 5:"{bs. (the (m bs), sdrop k bs) \<in> A \<and> (m bs \<noteq> None)} \<in> sets coin_space"
      unfolding R_def using 4
      by (subst (asm) sets_restrict_space_iff) auto

    have "{x. (the (m (fst x@-snd x)), sdrop k (fst x@-snd x)) \<in> A \<and> m (fst x @- snd x) \<noteq> None} =
      (\<lambda>x. fst x@-snd x) -` {bs. (the (m bs), sdrop k bs) \<in> A \<and> (m bs \<noteq> None)} \<inter> space ?S"
      unfolding space_pair_measure space_coin_space by simp
    also have "... \<in> sets ?S"
      using append_measurable
      by (intro measurable_sets[where A="coin_space"] 5) simp
    finally have 6:
      "{x. (the (m (fst x@-snd x)), sdrop k (fst x@-snd x)) \<in> A \<and> m (fst x @- snd x) \<noteq> None}
      \<in> sets ?S"
      by simp

    have 9:"m x = m y" if "(the (m x), bs) \<in> A \<and> m x \<noteq> None" "stake k x = stake k y" for x y bs
    proof -
      have "snd (the (m x)) = k" "m x \<noteq> None"
        using a3 that(1) unfolding B_def by auto
      then obtain v where "m x  = Some (v,k)"
        by auto
      thus ?thesis
        using wf_pmfsrD[OF wf_m _ that(2)[symmetric]] by simp
    qed

    have "(the (m (stake k x @- bs)), bs) \<in> A \<and> m (stake k x @- bs) \<noteq> None \<longleftrightarrow>
      (the (m x), bs) \<in> A \<and> m x \<noteq> None" (is "?L1 = ?R1") for x bs
    proof
      have a9: "stake k (stake k x @- bs) = stake k x" by simp
      assume ?L1
      thus ?R1 using 9[OF _ a9, of "bs"] by simp
    next
      have a9: "stake k x = stake k (stake k x @- bs)" by simp
      assume ?R1
      thus ?L1 using 9[OF _ a9, of "bs"] by simp
    qed

    hence 7: "{bs. (the (m (stake k x @- bs)), bs) \<in> A \<and> m (stake k x @- bs) \<noteq> None} =
      {bs. (the (m x), bs) \<in> A \<and> m x \<noteq> None}"  for x
      by simp

    have "emeasure ?L A = emeasure R (\<mu> -` A \<inter> space R)"
      using that by (intro emeasure_distr 2) auto
    also have "... = emeasure R {bs. (the (m bs), sdrop (snd (the (m bs))) bs) \<in> A \<and> m bs \<noteq> None}"
      unfolding \<mu>_def R_def
      by (simp add:space_restrict_space space_coin_space vimage_def Int_def)
    also have "... = emeasure R {bs. (the (m bs), sdrop k bs)\<in>A \<and> m bs \<noteq> None}"
      using that(2) unfolding B_def by (intro arg_cong2[where f="emeasure"] refl) auto
    also have "... =
      emeasure coin_space {bs. (the (m bs), sdrop k bs)\<in>A \<and> m bs \<noteq> None}"
      using 4 unfolding R_def by (intro emeasure_restrict_space subsetI) simp_all
    also have "... =
      emeasure (distr ((pmf_of_set {xs. length xs = k}) \<Otimes>\<^sub>M coin_space) coin_space (\<lambda>(x, y). x@-y))
        {bs. (the (m bs), sdrop k bs) \<in> A \<and> m bs \<noteq> None}"
      by (subst split_coin_space[symmetric, of k]) simp
    also have "... = emeasure (pmf_of_set {xs. length xs = k} \<Otimes>\<^sub>M coin_space)
      {x. (the (m (fst x @- snd x)), sdrop k (fst x @- snd x)) \<in> A \<and> m (fst x @- snd x) \<noteq> None}"
      using append_measurable 5 by (subst emeasure_distr)
        (simp_all add:space_pair_measure space_coin_space vimage_def case_prod_beta)
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space (Pair x -` {x. (the (m (fst x@-snd x)),
        sdrop k (fst x @- snd x))\<in>A \<and> m (fst x@-snd x)\<noteq>None}) \<partial>(pmf_of_set {xs. length xs = k})"
      by (intro coin_space.emeasure_pair_measure_alt 6)
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space
      {bs. (the (m (x@-bs)), sdrop k (x@-bs)) \<in> A \<and> m (x@-bs) \<noteq> None} \<partial>pmf_of_set{xs. length xs=k}"
      unfolding vimage_def by simp
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space {bs. (the (m (x@-bs)), bs) \<in> A \<and> m (x@-bs) \<noteq> None}
      \<partial>pmf_of_set{xs. length xs=k}"
      using bool_list_set by (intro nn_integral_cong_AE AE_pmfI) auto
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space
      {bs. (the (m (stake k x @- bs)), bs) \<in> A \<and> m (stake k x @- bs) \<noteq> None} \<partial>coin_space"
      unfolding distr_stake[symmetric] coin_space_def by (intro nn_integral_distr) auto
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space {bs. (the (m x), bs) \<in> A \<and> m x \<noteq> None} \<partial>coin_space"
      by (subst 7)  simp
    also have "... = \<integral>\<^sup>+x\<in>{bs. m bs \<noteq> None}. emeasure coin_space {bs. (the (m x),bs)\<in>A}\<partial>coin_space"
      by (intro arg_cong2[where f="nn_integral"] refl ext) (simp split:split_indicator)
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space {bs. (the (m x), bs) \<in> A} \<partial>R"
      unfolding R_def by (intro nn_integral_restrict_space[symmetric] 4)
    also have "... =  \<integral>\<^sup>+ x. emeasure coin_space (Pair ((the \<circ> m) x) -` A) \<partial>R"
      unfolding vimage_def comp_def by simp
    also have "... = \<integral>\<^sup>+ x. emeasure coin_space (Pair x -` A) \<partial>distr R discrete (the \<circ> m)"
      using 1 by (intro nn_integral_distr[symmetric]) simp_all
    also have "... = emeasure ?R A"
      using that by (intro sigma_finite_measure.emeasure_pair_measure_alt[symmetric]
          coin_space.sigma_finite_measure_axioms) (simp add:sets_pair_measure)
    finally show ?thesis
      by simp
  qed

  have "emeasure ?L A = emeasure ?R A" if "A \<in> sets ?L" for A
  proof -
    define A' where "A' k = A \<inter> B k" for k
    have df: "disjoint_family A'"
      unfolding A'_def B_def disjoint_family_on_def by auto

    have "emeasure ?L A = emeasure ?L (\<Union>k. A' k)"
      unfolding A'_def B_def by (intro arg_cong2[where f="emeasure"] refl) auto
    also have "... = (\<Sum>k. emeasure ?L (A' k))"
      using that df B_sets unfolding A'_def
      by (intro suminf_emeasure[symmetric] image_subsetI sets.Int) auto
    also have "... = (\<Sum>k. emeasure ?R (A' k))"
      unfolding A'_def using that B_sets
      by (intro suminf_cong 3 sets.Int) auto
    also have "... = emeasure ?R (\<Union>k. A' k)"
      using that B_sets df unfolding A'_def
      by (intro suminf_emeasure) auto
    also have "... = emeasure ?R A"
      unfolding A'_def B_def by (intro arg_cong2[where f="emeasure"] refl) auto

    finally show ?thesis by simp
  qed

  moreover have "sets ?L = sets ?R"
    unfolding sets_distr sets_pair_measure by simp

  ultimately show "?L = ?R"
    by (intro measure_eqI) auto
qed

(*
  Central theorem: running the sampler and returning the stream of unused coins is equivalent
  to running the sampler and returning a fresh stream of random coins.

  In other words: if the sampler terminates with result (x, n) then it really did "use" only the
  first n coins and the remaining ones are still "as good as fresh ones".
*)

lemma measure_bind_pmfsr_helper:
  "distr R (discrete \<Otimes>\<^sub>M coin_space) (apfst fst\<circ>\<mu>) = distr R discrete (fst\<circ>the\<circ>m) \<Otimes>\<^sub>M coin_space"
  (is "?L = ?R")
proof -
  let ?C = "coin_space"
  let ?D = "discrete"
  have 0: "(\<lambda>x. the (m x)) \<in> R \<rightarrow>\<^sub>M ?D"
    using measure_bind_pmfsr_helper_2(2) unfolding R_def by simp

  have "?L = distr (distr R (?D \<Otimes>\<^sub>M ?C) \<mu>) (?D \<Otimes>\<^sub>M ?C) (apfst fst)"
    unfolding  apfst_def by (intro distr_distr[symmetric] measure_bind_pmfsr_helper_2) measurable
  also have "... = distr (distr R ?D (the \<circ> m) \<Otimes>\<^sub>M coin_space) (?D \<Otimes>\<^sub>M ?C) (apfst fst)"
    by (subst measure_bind_pmfsr_helper_2) simp
  also have "... = distr (distr R ?D (the \<circ> m) \<Otimes>\<^sub>M distr ?C ?C id) (?D \<Otimes>\<^sub>M ?C) (apfst fst)"
    unfolding id_def by simp
  also have "... =  distr (distr (R \<Otimes>\<^sub>M ?C) (?D \<Otimes>\<^sub>M ?C) (apfst (the \<circ> m))) (?D \<Otimes>\<^sub>M ?C) (apfst fst)"
    using 0 coin_space.sigma_finite_measure
    by (subst pair_measure_distr) (simp_all add:comp_def id_def map_prod_def apfst_def)
  also have "... = distr (R \<Otimes>\<^sub>M ?C) (?D \<Otimes>\<^sub>M ?C) (apfst fst \<circ> apfst (the \<circ> m))"
    using 0 unfolding apfst_def
    by (intro distr_distr map_prod_measurable) (simp_all add:comp_def)
  also have "... = distr (R \<Otimes>\<^sub>M ?C) (?D \<Otimes>\<^sub>M ?C) ((\<lambda>(bs, bs'). (fst (the (m bs)), bs')))"
    by (intro arg_cong2[where f="distr (R \<Otimes>\<^sub>M ?C)"] refl)
      (simp add:apfst_def map_prod_def comp_def case_prod_beta')
  also have "... = distr R ?D (\<lambda>bs. (fst (the (m bs)))) \<Otimes>\<^sub>M distr ?C ?C (\<lambda>x. x)"
    using coin_space.sigma_finite_measure
    by (intro pair_measure_distr[symmetric] measurable_compose[OF 0]) simp_all
  also have "... = ?R"
    by (simp add:comp_def)
  finally show ?thesis by simp
qed

lemma measure_bind_pmfsr:
  "measure_pmfsr (bind_pmfsr m f) = measure_pmfsr m \<bind>
    (\<lambda>x. if x \<in> Some ` range_pmfsr m then measure_pmfsr (f (the x)) else return discrete None)"
    (is "?L = ?R")
proof (rule measure_eqI)
  have "sets ?L = UNIV"
    unfolding measure_pmfsr_def by simp
  also have "... = sets ?R"
    unfolding measure_pmfsr_def by (subst sets_bind[where N="discrete"])
      (simp_all add:option.case_distrib option.case_eq_if)
  finally show "sets ?L = sets ?R" by simp
next
  let ?C = "coin_space"
  let ?D = "discrete"
  let ?m = "measure_pmfsr"
  let ?H = "count_space (range_pmfsr m)"
  fix A assume "A \<in> sets (measure_pmfsr (m \<bind> f))"
  define N where "N = {x. m x \<noteq> None}"

  have "N = m -` (Some ` UNIV) \<inter> space coin_space"
    unfolding N_def space_coin_space vimage_def by auto
  also have "... \<in> sets coin_space"
    by (intro measurable_sets[where A="discrete"] measurable_pmfsr[OF wf_m]) simp
  finally have N_meas: "N \<in> sets coin_space"
    by simp

  hence N_meas': "-N \<in> sets coin_space"
    unfolding Compl_eq_Diff_UNIV using space_coin_space by (metis sets.compl_sets)

  have wf_bind: "wf_pmfsr (m \<bind> f)"
    using wf_bind_pmfsr[OF wf_m wf_f] by auto

  have 0: "(map_option fst \<circ> (m \<bind> f)) \<in> coin_space \<rightarrow>\<^sub>M discrete"
    by (intro measurable_comp[OF measurable_pmfsr[OF wf_bind]]) simp
  have "(map_option fst \<circ> (m \<bind> f)) -` A = (map_option fst \<circ> (m \<bind> f)) -` A \<inter> space coin_space"
    unfolding space_coin_space by simp
  also have "... \<in> sets coin_space"
    by (intro measurable_sets[where A="discrete"] 0) simp
  finally have 1: "(map_option fst \<circ> (m \<bind> f)) -` A \<in> sets coin_space"
    by simp

  have "{(v, bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_pmfsr m} =
    (map_option fst \<circ> case_prod f) -` A \<inter> space (?H \<Otimes>\<^sub>M ?C)"
    unfolding vimage_def space_pair_measure space_coin_space by auto
  also have "... \<in> sets (?H \<Otimes>\<^sub>M coin_space)"
    using measurable_compose[OF measurable_pmfsr[OF wf_f], where L="discrete"]
    by (intro measurable_sets[where A="discrete"] measurable_pair_measure_countable1
        countable_range_pmfsr[OF wf_m]) auto
  also have "... = sets (restrict_space discrete (range_pmfsr m) \<Otimes>\<^sub>M coin_space)"
    unfolding restrict_count_space inf_top_right by simp
  also have "... = sets (restrict_space (discrete \<Otimes>\<^sub>M coin_space) (range_pmfsr m \<times> space coin_space))"
    by (subst coin_space.restrict_space_pair_lift) auto
  finally have "{(v, bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_pmfsr m} \<in>
    sets (restrict_space (discrete \<Otimes>\<^sub>M coin_space) (range_pmfsr m \<times> UNIV))"
    unfolding space_coin_space by simp
  moreover have "range_pmfsr m \<times> space coin_space \<in> sets (discrete \<Otimes>\<^sub>M coin_space)"
    by (intro pair_measureI sets.top) auto
  ultimately have 2: "{(v, bs). map_option fst (f v bs) \<in> A \<and> v\<in>range_pmfsr m} \<in> sets (?D \<Otimes>\<^sub>M ?C)"
    by (subst (asm) sets_restrict_space_iff) (auto simp: space_coin_space)

  have space_R: "space R = {x. m x \<noteq> None}"
    unfolding R_def by (simp add:space_restrict_space space_coin_space)

  have 3: "measure_pmfsr (f (the x)) \<in> space (subprob_algebra discrete)"
    if "x \<in> Some ` range_pmfsr m" for x
    using measure_pmfsr_subprob_space wf_f that by fastforce

  have "(\<lambda>x. emeasure (measure_pmfsr (f (fst (the (m x))))) A * indicator N x) =
    (\<lambda>x. emeasure (if m x \<noteq> None then measure_pmfsr (f (fst (the (m x)))) else null_measure discrete) A)"
    unfolding N_def by (intro ext) simp
  also have "... = (\<lambda>v. emeasure
    (if v \<in> Some ` range_pmfsr m then ?m (f (the v)) else null_measure discrete) A)
    \<circ> (map_option fst \<circ> m)"
    unfolding comp_def by (intro ext arg_cong2[where f="emeasure"] refl if_cong)
      (auto intro:in_range_pmfsrI simp add:vimage_def image_iff)
  also have "... \<in> borel_measurable coin_space"
    using 3 by (intro measurable_comp[where N="discrete"]
        measurable_emeasure_kernel[where N="discrete"] measurable_pmfsr[OF wf_m]) simp_all
  finally have 4:"(\<lambda>x. emeasure (measure_pmfsr (f (fst (the (m x))))) A * indicator N x)
    \<in> coin_space \<rightarrow>\<^sub>M borel" by simp

  let ?N = "emeasure ?C {bs. bs \<notin> N \<and> None \<in> A}"

  have "emeasure ?L A = emeasure ?C ((map_option fst \<circ> (m \<bind> f)) -` A)"
    unfolding measure_pmfsr_def using 0 by (subst emeasure_distr) (simp_all add:space_coin_space)
  also have "... =
    emeasure ?C ((map_option fst\<circ>(m\<bind>f))-`A \<inter> -N) + emeasure ?C ((map_option fst\<circ>(m\<bind>f))-`A \<inter> N)"
    using N_meas N_meas' 1
    by (subst emeasure_Un'[symmetric]) (simp_all add:Int_Un_distrib[symmetric])
  also have "... =
    emeasure ?C ((map_option fst\<circ>(m\<bind>f))-`A\<inter> -N) + emeasure R ((map_option fst\<circ>(m\<bind>f))-`A\<inter> N)"
    using N_meas unfolding R_def N_def
    by (intro arg_cong2[where f="(+)"] refl emeasure_restrict_space[symmetric]) simp_all
  also have "... =?N + emeasure R ((apfst fst \<circ> \<mu>) -`
    {(v, bs). map_option fst (f v bs) \<in> A \<and> v\<in> range_pmfsr m} \<inter> space R)"
    unfolding bind_pmfsr_def map_conv_bind_option N_def space_R apfst_def \<mu>_def
    by (intro arg_cong2[where f="(+)"] arg_cong2[where f="emeasure"])
     (simp_all add: Option_bind_conv_case set_eq_iff in_range_pmfsrI split:option.split)
  also have "... = ?N + emeasure (distr R (?D\<Otimes>\<^sub>M?C) (apfst fst \<circ> \<mu>))
    {(v,bs). map_option fst (f v bs)\<in>A \<and> v\<in> range_pmfsr m}"
    using 2 unfolding apfst_def by (intro arg_cong2[where f="(+)"] emeasure_distr[symmetric]
         measurable_comp[OF measure_bind_pmfsr_helper_2(1)] map_prod_measurable) simp_all
  also have "... = ?N + emeasure (distr R ?D (fst \<circ> the \<circ> m) \<Otimes>\<^sub>M ?C)
    {(v,bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_pmfsr m}"
    unfolding N_def measure_bind_pmfsr_helper by simp
  also have "... =  ?N + \<integral>\<^sup>+ v. emeasure ?C
    {bs. map_option fst (f v bs) \<in> A \<and> v \<in> range_pmfsr m} \<partial>distr R ?D (fst \<circ> (the \<circ> m))"
    using 2 by (subst coin_space.emeasure_pair_measure_alt) (simp_all add:vimage_def comp_assoc)
  also have "... =  ?N + \<integral>\<^sup>+ x. emeasure ?C
    {bs. map_option fst (f ((fst \<circ> (the \<circ> m)) x) bs) \<in> A \<and> (fst \<circ> (the \<circ> m)) x \<in> range_pmfsr m} \<partial>R"
    by (intro arg_cong2[where f="(+)"] refl nn_integral_distr
        measurable_comp[OF measure_bind_pmfsr_helper_2(3)]) simp_all
  also have "... = ?N + (\<integral>\<^sup>+x\<in>{bs. m bs \<noteq> None}. emeasure ?C
    {bs. map_option fst (f (fst (the (m x))) bs) \<in> A \<and> fst (the (m x)) \<in> range_pmfsr m} \<partial>?C)"
    using N_meas unfolding R_def N_def using nn_integral_restrict_space
    by (subst nn_integral_restrict_space) simp_all
  also have "... = ?N + (\<integral>\<^sup>+x\<in>{bs. m bs \<noteq> None}.
    emeasure ?C ((map_option fst \<circ> f (fst (the (m x)))) -` A \<inter> space coin_space) \<partial>?C)"
    by (intro arg_cong2[where f="(+)"] set_nn_integral_cong refl arg_cong2[where f="emeasure"])
     (auto intro:in_range_pmfsrI simp:space_coin_space)
  also have "... = ?N + (\<integral>\<^sup>+x\<in>N. emeasure (measure_pmfsr(f(fst(the(m x))))) A \<partial>?C)"
    unfolding measure_pmfsr_def N_def
    by (intro arg_cong2[where f="(+)"] set_nn_integral_cong refl emeasure_distr[symmetric]
        measurable_comp[OF measurable_pmfsr[OF wf_f]]) (auto intro:in_range_pmfsrI)
  also have "... = (\<integral>\<^sup>+x. (indicator {bs. bs \<notin> N \<and> None \<in> A}) x  \<partial>?C) +
    (\<integral>\<^sup>+x\<in>N. emeasure (measure_pmfsr(f(fst(the(m x))))) A \<partial>?C)"
    using N_meas N_meas'
    by (intro arg_cong2[where f="(+)"] nn_integral_indicator[symmetric] refl)
     (cases "None \<in> A"; auto simp:Collect_neg_eq)
  also have "... = \<integral>\<^sup>+ x. indicator {bs. bs \<notin> N \<and> None \<in> A} x +
           emeasure (measure_pmfsr (f (fst (the (m x))))) A * indicator N x \<partial>?C"
    using N_meas' N_meas by (intro nn_integral_add[symmetric] 4) simp
  also have "... =  \<integral>\<^sup>+ x. indicator (-N) x * indicator A None +
    indicator N x * emeasure (measure_pmfsr (f (fst (the (m x))))) A \<partial>?C"
    unfolding N_def by (intro arg_cong2[where f="nn_integral"] ext refl arg_cong2[where f="(+)"])
      (simp_all split:split_indicator)
  also have "... =
    \<integral>\<^sup>+ x. emeasure (case m x of None \<Rightarrow> return discrete None | Some x \<Rightarrow> measure_pmfsr (f (fst x))) A \<partial>?C"
    unfolding N_def by (intro arg_cong2[where f="nn_integral"] ext)
      (auto split:split_indicator option.split)
  also have "... = \<integral>\<^sup>+ x. emeasure (if (map_option fst \<circ> m) x \<in> Some ` range_pmfsr m
    then measure_pmfsr (f (the ((map_option fst \<circ> m) x)))
    else return discrete None) A \<partial>?C"
    by (intro arg_cong2[where f="nn_integral"] arg_cong2[where f="emeasure"] refl ext)
     (auto simp add: in_range_pmfsrI vimage_def split:option.splits)
  also have "... =
    \<integral>\<^sup>+ x. emeasure (if x \<in> Some ` range_pmfsr m then ?m (f (the x)) else return discrete None) A \<partial>?m m"
    unfolding measure_pmfsr_def using measurable_pmfsr[OF wf_m]
    by (intro nn_integral_distr[symmetric] measurable_comp[where N="discrete"]) simp_all
  also have "... = emeasure ?R A"
    using 3 none_measure_subprob_algebra
    by (intro emeasure_bind[symmetric, where N="discrete"]) (auto simp add:measure_pmfsr_def Pi_def)
  finally show "emeasure ?L A = emeasure ?R A"
    by simp
qed

end

context
begin

interpretation pmf_as_measure .

lift_definition spmf_of_pmfsr :: "'a pmfsr \<Rightarrow> 'a spmf" is
  "\<lambda>r. if wf_pmfsr r then measure_pmfsr r
       else return (count_space UNIV) None"
proof goal_cases
  case (1 r)
  define M where "M = (if wf_pmfsr r then
                         measure_pmfsr r
                       else return (count_space UNIV) None)"
  have "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> r)" if "wf_pmfsr r"
    by (rule measurable_comp[OF measurable_pmfsr[OF that]]) auto
  then interpret M: prob_space M
    by (auto simp: M_def measure_pmfsr_def intro!: coin_space.prob_space_distr prob_space_return)
  show ?case
    unfolding M_def [symmetric]
  proof (intro conjI)
    show "prob_space M"
      by (fact M.prob_space_axioms)
  next
    show "sets M = UNIV"
      by (simp add: M_def measure_pmfsr_def)
  next
    show "AE x in M. Sigma_Algebra.measure M {x} \<noteq> 0"
    proof (cases "wf_pmfsr r")
      case True
      have meas: "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> r)"
        by (rule measurable_comp[OF measurable_pmfsr[OF True]]) auto
      show ?thesis
      proof (subst M.AE_support_countable)
        have "AE x in coin_space. map_option fst (r x) \<in> options (range_pmfsr r)"
          by (intro always_eventually)
             (auto simp: options_def map_option_case intro: imageI in_range_pmfsrI split: option.splits)
        hence "AE x in M. x \<in> options (range_pmfsr r)"
          unfolding M_def measure_pmfsr_def using True meas by (simp add: AE_distr_iff)
        thus "\<exists>S. countable S \<and> (AE x in M. x \<in> S)"
          by (intro exI[of _ "options (range_pmfsr r)"]) (use True countable_range_pmfsr in auto)
      qed (auto simp: M_def measure_pmfsr_def)
    next
      case False
      thus ?thesis
        unfolding M_def by (auto simp: AE_return measure_return)
    qed
  qed
qed

end

lemma loss_pmfsr_altdef:
  assumes "wf_pmfsr r"
  shows   "loss_pmfsr r = pmf (spmf_of_pmfsr r) None"
proof -
  have "(map_option fst \<circ> r) -` {None} = r -` {None}"
    by auto
  moreover have "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> r)"
    by (intro measurable_comp[OF measurable_pmfsr] assms) auto
  ultimately show ?thesis
    using assms
    by (auto simp: loss_pmfsr_def pmf.rep_eq spmf_of_pmfsr.rep_eq measure_pmfsr_def
                   measure_distr space_coin_space)
qed

lemma weight_pmfsr: "wf_pmfsr r \<Longrightarrow> weight_spmf (spmf_of_pmfsr r) = 1 - loss_pmfsr r"
  by (simp add: weight_spmf_conv_pmf_None loss_pmfsr_altdef)

lemma spmf_of_return_pmfsr [simp]:
  "spmf_of_pmfsr (return_pmfsr x) = return_spmf x"
proof -
  have "measure_pmf (spmf_of_pmfsr (return_pmfsr x)) =
          distr coin_space (count_space UNIV) (map_option fst \<circ> return_pmfsr x)"
    by (subst spmf_of_pmfsr.rep_eq) (auto simp: wf_return_pmfsr measure_pmfsr_def)
  also have "map_option fst \<circ> return_pmfsr x = (\<lambda>_. Some x)"
    by (auto simp: fun_eq_iff return_pmfsr_def)
  also have "distr coin_space (count_space UNIV) \<dots> = return (count_space UNIV) (Some x)"
    by simp
  also have "\<dots> = measure_pmf (return_spmf x)"
    by (simp add: return_pmf.rep_eq)
  finally show ?thesis
    using measure_pmf_inject by auto
qed

lemma loss_return_pmfsr [simp]: "loss_pmfsr (return_pmfsr x) = 0"
  by (simp add: loss_pmfsr_altdef wf_return_pmfsr)

lemma spmf_of_coin_pmfsr [simp]:
  "spmf_of_pmfsr coin_pmfsr = coin_spmf"
proof -
  have "measure_pmf (spmf_of_pmfsr coin_pmfsr) =
          distr coin_space (count_space UNIV) (map_option fst \<circ> coin_pmfsr)"
    by (subst spmf_of_pmfsr.rep_eq) (auto simp: wf_coin_pmfsr measure_pmfsr_def)
  also have "map_option fst \<circ> coin_pmfsr = Some \<circ> shd"
    by (auto simp: fun_eq_iff coin_pmfsr_def)
  also have "distr coin_space (count_space UNIV) \<dots> =
               distr (distr coin_space (count_space UNIV) shd) (count_space UNIV) Some"
    by (subst distr_distr) (auto simp: coin_space_def)
  also have "distr coin_space (count_space UNIV) shd = measure_pmf (pmf_of_set UNIV)"
    unfolding coin_space_def by simp
  also have "distr (measure_pmf (pmf_of_set UNIV)) (count_space UNIV) Some =
             measure_pmf (map_pmf Some (pmf_of_set UNIV))"
    by (rule map_pmf_rep_eq [symmetric])
  also have "\<dots> = measure_pmf coin_spmf"
    unfolding spmf_of_set_def spmf_of_pmf_def by simp
  finally show ?thesis
    using measure_pmf_inject by auto
qed

lemma loss_coin_pmfsr [simp]: "loss_pmfsr coin_pmfsr = 0"
  by (simp add: loss_pmfsr_altdef wf_coin_pmfsr)

lemma set_spmf_of_pmfsr:
  assumes  "wf_pmfsr r"
  shows    "set_spmf (spmf_of_pmfsr r) \<subseteq> range_pmfsr r"
proof -
  have "x \<notin> set_spmf (spmf_of_pmfsr r)" if "x \<notin> range_pmfsr r" for x
  proof -
    have "spmf (spmf_of_pmfsr r) x = Sigma_Algebra.measure (measure_pmfsr r) {Some x}"
      unfolding pmf.rep_eq spmf_of_pmfsr.rep_eq using assms by auto
    also have "\<dots> = coin_space.prob ((map_option fst \<circ> r) -` {Some x})"
      unfolding measure_pmfsr_def
      by (subst measure_distr)
         (auto intro: measurable_comp[OF measurable_pmfsr[OF assms]] simp: space_coin_space)
    also have "(map_option fst \<circ> r) -` {Some x} = {}"
      using \<open>x \<notin> range_pmfsr r\<close> in_range_pmfsrI[of r _ x] by fastforce
    finally have "spmf (spmf_of_pmfsr r) x = 0"
      by simp
    thus "x \<notin> set_spmf (spmf_of_pmfsr r)"
      by (simp add: spmf_eq_0_set_spmf)
  qed
  thus ?thesis
    by blast
qed

lemma spmf_of_bind_pmfsr:
  assumes "wf_pmfsr r"
  assumes "\<And>x. x \<in> range_pmfsr r \<Longrightarrow> wf_pmfsr (f x)"
  shows   "spmf_of_pmfsr (bind_pmfsr r f) = bind_spmf (spmf_of_pmfsr r) (spmf_of_pmfsr \<circ> f)"
      (is "?L = ?R")
proof -
  have 0: "wf_pmfsr (f (the x))" if "x \<in> Some ` range_pmfsr r" for x
    using assms(2) that by (cases x) auto

  have 1: "return discrete None = measure_pmf (return_pmf None)"
    by (intro measure_eqI) auto

  have "measure_pmf ?L = measure_pmfsr (bind_pmfsr r f)"
    using assms wf_bind_pmfsr by (subst spmf_of_pmfsr.rep_eq) auto
  also have "... =  measure_pmfsr r \<bind> (\<lambda>x. if x \<in> Some ` range_pmfsr r then
    measure_pmfsr (f (the x)) else return discrete None)"
    by (intro measure_bind_pmfsr[OF assms])
  also have "... = measure_pmf (spmf_of_pmfsr r) \<bind> (\<lambda>x. if x \<in> Some ` range_pmfsr r then
    measure_pmf (spmf_of_pmfsr (f (the x))) else measure_pmf (return_pmf None))"
    using 0 assms(1) unfolding spmf_of_pmfsr.rep_eq 1 by (simp cong:if_cong)
  also have "... = measure_pmf (spmf_of_pmfsr r) \<bind> measure_pmf \<circ>
    (\<lambda>x. (if x \<in> Some ` range_pmfsr r then spmf_of_pmfsr (f (the x)) else return_pmf None)) \<circ> id"
    by (simp add:comp_def id_def if_distrib)
  also have "... = measure_pmf (spmf_of_pmfsr r \<bind>
      (\<lambda>x. if x \<in> Some ` range_pmfsr r then spmf_of_pmfsr (f (the x)) else return_pmf None))"
    by (subst bind_pmf.rep_eq[symmetric]) simp
  also have "... = measure_pmf (spmf_of_pmfsr r \<bind>
      (\<lambda>x. case x of None \<Rightarrow> return_pmf None | Some y \<Rightarrow> spmf_of_pmfsr (f y)))"
    using subsetD[OF set_spmf_of_pmfsr[OF assms(1)]]
    by (intro arg_cong[where f="measure_pmf"] bind_pmf_cong refl)
      (auto simp: in_set_spmf split:option.split)
  also have "... = measure_pmf ?R"
    unfolding bind_spmf_def case_option_def by simp
  finally have "measure_pmf ?L = measure_pmf ?R"
    by simp
  thus ?thesis
    using measure_pmf_inject by auto
qed

lemma loss_bind_pmfsr:
  assumes "wf_pmfsr r"
  assumes "\<And>x. x \<in> range_pmfsr r \<Longrightarrow> wf_pmfsr (f x)"
  shows   "loss_pmfsr (bind_pmfsr r f) = loss_pmfsr r +
             (LINT x|measure_spmf (spmf_of_pmfsr r). loss_pmfsr (f x))"
proof -
  have "loss_pmfsr (bind_pmfsr r f) = pmf (spmf_of_pmfsr (r \<bind> f)) None"
    by (subst loss_pmfsr_altdef) (auto intro!: wf_bind_pmfsr assms)
  also have "spmf_of_pmfsr (r \<bind> f) = spmf_of_pmfsr r \<bind> (spmf_of_pmfsr \<circ> f)"
    by (rule spmf_of_bind_pmfsr) (auto intro!: assms)
  also have "pmf \<dots> None = loss_pmfsr r +
               (LINT x|measure_spmf (spmf_of_pmfsr r). pmf (spmf_of_pmfsr (f x)) None)"
    by (subst pmf_bind_spmf_None) (auto simp: assms loss_pmfsr_altdef o_def)
  also have "(LINT x|measure_spmf (spmf_of_pmfsr r). pmf (spmf_of_pmfsr (f x)) None) =
             (LINT x|measure_spmf (spmf_of_pmfsr r). loss_pmfsr (f x))"
  proof (intro Bochner_Integration.integral_cong_AE)
    have "AE x in measure_spmf (spmf_of_pmfsr r). x \<in> set_spmf (spmf_of_pmfsr r)"
      using AE_measure_spmf_iff by blast
    hence "AE x in measure_spmf (spmf_of_pmfsr r). x \<in> range_pmfsr r"
      by eventually_elim (use assms(1) set_spmf_of_pmfsr in blast)
    thus "AE x in measure_spmf (spmf_of_pmfsr r).
            pmf (spmf_of_pmfsr (f x)) None = loss_pmfsr (f x)"
      by eventually_elim (auto simp: loss_pmfsr_altdef assms)
  qed auto
  finally show ?thesis .
qed

lemma spmf_of_map_pmfsr:
  assumes "wf_pmfsr r"
  shows   "spmf_of_pmfsr (map_pmfsr f r) = map_spmf f (spmf_of_pmfsr r)"
  using assms
  by (simp add: map_pmfsr_conv_bind_pmfsr spmf_of_bind_pmfsr wf_return_pmfsr
                o_def map_spmf_conv_bind_spmf)

lemma loss_map_pmfsr [simp]: "loss_pmfsr (map_pmfsr f r) = loss_pmfsr r"
proof -
  have "map_pmfsr f r -` {None} = r -` {None}"
    by (auto simp: map_pmfsr_def)
  thus ?thesis
    by (simp add: loss_pmfsr_def)
qed



definition ord_pmfsr :: "'a pmfsr \<Rightarrow> 'a pmfsr \<Rightarrow> bool" where
  "ord_pmfsr = rel_fun (=) (ord_option (=))"

context fixes Y :: "'a pmfsr set" begin

definition lub_pmfsr :: "'a pmfsr" where
  "lub_pmfsr bs =
     (let X = {xn |xn r. r \<in> Y \<and> r bs = Some xn}
      in  if Set.is_singleton X then Some (the_elem X) else None)"

lemma lub_pmfsr_eq_SomeI:
  assumes "r \<in> Y" "r bs = Some xn"
  assumes "\<And>r' xn'. r' \<in> Y \<Longrightarrow> r' bs = Some xn' \<Longrightarrow> xn' = xn"
  shows   "lub_pmfsr bs = Some xn"
proof -
  have *: "{xn |xn r. r \<in> Y \<and> r bs = Some xn} = {xn}"
    using assms by blast
  show ?thesis
    unfolding Let_def lub_pmfsr_def * by auto
qed

lemma lub_pmfsr_eq_SomeE:
  assumes "lub_pmfsr bs = Some xn"
  obtains r where "r \<in> Y" "r bs = Some xn"
  using assms
  by (auto simp: lub_pmfsr_def Let_def is_singleton_def split: if_splits)

lemma lub_pmfsr_eq_SomeD:
  assumes "lub_pmfsr bs = Some xn" "r \<in> Y" "r bs = Some xn'"
  shows   "xn' = xn"
proof -
  let ?X = "{xn |xn r. r \<in> Y \<and> r bs = Some xn}"
  from assms(1) have "is_singleton ?X"
    by (auto simp: lub_pmfsr_def Let_def split: if_splits)
  then obtain xn'' where xn'': "?X = {xn''}"
    by (auto simp: is_singleton_def)
  moreover have "xn' \<in> ?X"
    using assms by auto
  ultimately show "xn' = xn"
    using assms unfolding lub_pmfsr_def Let_def xn'' by auto
qed

end

lemma wf_lub_pmfsr:
  assumes "Complete_Partial_Order.chain ord_pmfsr Y" "\<And>r. r \<in> Y \<Longrightarrow> wf_pmfsr r"
  shows   "wf_pmfsr (lub_pmfsr Y)"
proof (rule wf_pmfsrI)
  fix bs bs' x n
  assume *: "lub_pmfsr Y bs = Some (x, n)" "stake n bs' = stake n bs"
  from *(1) obtain r where r: "r \<in> Y" "r bs = Some (x, n)"
    by (auto elim!: lub_pmfsr_eq_SomeE)
  show "lub_pmfsr Y bs' = Some (x, n)"
  proof (rule lub_pmfsr_eq_SomeI)
    show "r \<in> Y"
      by fact
    show "r bs' = Some (x, n)"
      by (rule wf_pmfsrD[where bs = bs]) (use assms r * in auto)
    fix r' xn'
    assume r': "r' \<in> Y" "r' bs' = Some xn'"
    have "ord_pmfsr r' r \<or> ord_pmfsr r r'"
      using assms r r' by (auto simp: Complete_Partial_Order.chain_def)
    hence "ord_option (=) (r' bs') (r bs') \<or> ord_option (=) (r bs') (r' bs')"
      by (auto simp: ord_pmfsr_def rel_fun_def)
    thus "xn' = (x, n)"
      using \<open>r bs' = Some (x, n)\<close> r' by (cases "r' bs'") auto
  qed
qed


lemma lub_pmfsr_empty [simp]: "lub_pmfsr {} = (\<lambda>_. None)"
  by (auto simp: lub_pmfsr_def fun_eq_iff is_singleton_def)

lemma lub_pmfsr_const [simp]: "lub_pmfsr {p} = p"
proof
  fix bs :: "bool stream"
  show "lub_pmfsr {p} bs = p bs"
  proof (cases "p bs")
    case None
    hence *: "{xn |xn r. r \<in> {p} \<and> r bs = Some xn} = {}"
      by auto
    show ?thesis
      unfolding lub_pmfsr_def Let_def * by (auto simp: is_singleton_def None)
  next
    case (Some xn)
    hence *: "{xn |xn r. r \<in> {p} \<and> r bs = Some xn} = {xn}"
      by auto
    show ?thesis
      unfolding lub_pmfsr_def Let_def * by (auto simp: is_singleton_def Some)
  qed
qed

lemma partial_function_definitions_pmfsr:
  "partial_function_definitions ord_pmfsr lub_pmfsr"
  (is "partial_function_definitions ?R _")
proof
  fix x show "?R x x"
    by (auto simp: ord_pmfsr_def rel_fun_def intro: ord_option_reflI)
next
  fix x y z
  assume "?R x y" "?R y z"
  with transp_ord_option[OF transp_equality] show "?R x z"
    unfolding ord_pmfsr_def by (fastforce simp: rel_fun_def transp_def)
next
  fix x y
  assume "?R x y" "?R y x"
  thus "x = y"
    using antisymp_ord_option[of "(=)"]
    by (fastforce simp: ord_pmfsr_def rel_fun_def antisymp_def)
next
  fix Y r
  assume Y: "Complete_Partial_Order.chain ?R Y" "r \<in> Y"
  show "?R r (lub_pmfsr Y)"
    unfolding ord_pmfsr_def rel_fun_def
  proof safe
    fix bs :: "bool stream"
    show "ord_option (=) (r bs) (lub_pmfsr Y bs)"
    proof (cases "r bs")
      case None
      thus ?thesis
        by auto
    next
      case [simp]: (Some xn)
      have "{xn |xn r. r \<in> Y \<and> r bs = Some xn} = {xn}"
      proof (intro equalityI subsetI)
        fix xn' assume "xn' \<in> {xn |xn r. r \<in> Y \<and> r bs = Some xn}"
        then obtain r' where *: "r' \<in> Y" "r' bs = Some xn'"
          by auto
        from Y * have "ord_pmfsr r r' \<or> ord_pmfsr r' r"
          unfolding Complete_Partial_Order.chain_def by blast
        hence "ord_option (=) (r bs) (r' bs) \<or> ord_option (=) (r' bs) (r bs)"
          unfolding ord_pmfsr_def rel_fun_def by blast
        with * have "xn = xn'"
          by auto
        thus "xn' \<in> {xn}"
          by simp
      qed (use Y(2) in auto)
      hence "lub_pmfsr Y bs = Some xn"
        by (simp add: lub_pmfsr_def)
      thus ?thesis
        by simp
    qed
  qed
next
  fix Y r
  assume Y: "Complete_Partial_Order.chain ?R Y" and upper: "\<And>r'. r' \<in> Y \<Longrightarrow> ?R r' r"
  show "?R (lub_pmfsr Y) r"
    unfolding ord_pmfsr_def rel_fun_def
  proof safe
    fix bs :: "bool stream"
    show "ord_option (=) (lub_pmfsr Y bs) (r bs)"
    proof (cases "lub_pmfsr Y bs")
      case None
      thus ?thesis
        by auto
    next
      case (Some xn)
      then obtain r' where r': "r' \<in> Y" "r' bs = Some xn"
        by (elim lub_pmfsr_eq_SomeE)
      have "?R r' r"
        by (rule upper) fact+
      hence "ord_option (=) (r' bs) (r bs)"
        by (auto simp: ord_pmfsr_def rel_fun_def)
      with r' Some show ?thesis
        by auto
    qed
  qed
qed

lemma ccpo_pmfsr: "class.ccpo lub_pmfsr ord_pmfsr (mk_less ord_pmfsr)"
  by (rule ccpo partial_function_definitions_pmfsr)+

interpretation pmfsr: partial_function_definitions "ord_pmfsr" "lub_pmfsr"
  rewrites "lub_pmfsr {} \<equiv> (\<lambda>_. None)"
  by (rule partial_function_definitions_pmfsr) simp



typedef 'a pmfs = "{r :: 'a pmfsr. wf_pmfsr r}"
proof -
  obtain x :: 'a where True
    by auto
  show "\<exists>r::'a pmfsr. r \<in> {r. wf_pmfsr r}"
    by (rule exI[of _ "return_pmfsr x"]) (auto intro: wf_return_pmfsr)
qed

setup_lifting type_definition_pmfs

lift_definition run_pmfs :: "'a pmfs \<Rightarrow> bool stream \<Rightarrow> 'a option" is
  "\<lambda>r bs. map_option fst (r bs)" .

lift_definition run_pmfs' :: "'a pmfs \<Rightarrow> bool stream \<Rightarrow> ('a \<times> nat) option" is
  "\<lambda>r. r" .

lift_definition return_pmfs :: "'a \<Rightarrow> 'a pmfs" is return_pmfsr
  by (rule wf_return_pmfsr)

lift_definition coin_pmfs :: "bool pmfs" is coin_pmfsr
  by (rule wf_coin_pmfsr)

lift_definition bind_pmfs :: "'a pmfs \<Rightarrow> ('a \<Rightarrow> 'b pmfs) \<Rightarrow> 'b pmfs" is bind_pmfsr
  by (rule wf_bind_pmfsr)

lift_definition loss_pmfs :: "'a pmfs \<Rightarrow> real" is loss_pmfsr .

lift_definition consumption_pmfs :: "'a pmfs \<Rightarrow> nat pmfs" is consumption_pmfsr
  by (rule wf_consumption_pmfsr)


adhoc_overloading Monad_Syntax.bind bind_pmfs

lift_definition map_pmfs :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pmfs \<Rightarrow> 'b pmfs" is map_pmfsr
  by (rule wf_map_pmfsr)

lift_definition range_pmfs :: "'a pmfs \<Rightarrow> 'a set" is range_pmfsr .

lift_definition spmf_of_pmfs :: "'a pmfs \<Rightarrow> 'a spmf" is spmf_of_pmfsr .

lift_definition bot_pmfs :: "'a pmfs" is "\<lambda>_. None" by auto

primrec replicate_pmfs :: "nat \<Rightarrow> 'a pmfs \<Rightarrow> 'a list pmfs" where
  "replicate_pmfs 0 r = return_pmfs []"
| "replicate_pmfs (Suc n) r = do {x \<leftarrow> r; map_pmfs (\<lambda>xs. x # xs) (replicate_pmfs n r)}"

lemma map_pmfs_id [simp]: "map_pmfs id r = r"
  by transfer (rule map_pmfsr_id)

lemma map_pmfs_id' [simp]: "map_pmfs (\<lambda>x. x) r = r"
  by transfer (rule map_pmfsr_id')

lemma map_pmfs_return [simp]: "map_pmfs f (return_pmfs x) = return_pmfs (f x)"
  by transfer auto

lemma map_pmfs_comp: "map_pmfs (f \<circ> g) r = map_pmfs f (map_pmfs g r)"
  by transfer (rule map_pmfsr_comp)

lemma map_pmfs_conv_bind_pmfs: "map_pmfs f r = bind_pmfs r (\<lambda>x. return_pmfs (f x))"
  by transfer (rule map_pmfsr_conv_bind_pmfsr)

lemma bind_return_pmfs': "bind_pmfs r return_pmfs = r"
  by transfer (rule bind_return_pmfsr')

lemma bind_return_pmfs: "bind_pmfs (return_pmfs x) r = r x"
  by transfer (rule bind_return_pmfsr)

lemma bind_assoc_pmfs: "(A :: 'a pmfs) \<bind> B \<bind> C = A \<bind> (\<lambda>x. B x \<bind> C)"
  by transfer (rule bind_assoc_pmfsr)

lemma bind_pmfs_cong:
   "r = r' \<Longrightarrow> (\<And>x. x \<in> range_pmfs r \<Longrightarrow> f x = f' x) \<Longrightarrow> bind_pmfs r f = bind_pmfs r' f'"
  by transfer (use bind_pmfsr_cong in blast)

lemma replicate_pmfs_1 [simp]: "replicate_pmfs (Suc 0) r = map_pmfs (\<lambda>x. [x]) r"
  by (simp add: bind_return_pmfs' flip: map_pmfs_conv_bind_pmfs)

lemma weight_pmfs: "weight_spmf (spmf_of_pmfs r) = 1 - loss_pmfs r"
  by transfer (simp add: weight_pmfsr)

lemma loss_pmfs_altdef: "loss_pmfs r = pmf (spmf_of_pmfs r) None"
  by transfer (auto simp: loss_pmfsr_altdef)

lemma loss_pmfs_01: "loss_pmfs r \<in> {0..1}"
  unfolding loss_pmfs_altdef by (simp add: pmf_le_1)


lemma spmf_of_return_pmfs [simp]: "spmf_of_pmfs (return_pmfs x) = return_spmf x"
  by transfer simp

lemma spmf_of_coin_pmfs [simp]: "spmf_of_pmfs coin_pmfs = coin_spmf"
  by transfer simp

lemma spmf_of_bind_pmfs [simp]: "spmf_of_pmfs (r \<bind> f) = spmf_of_pmfs r \<bind> (spmf_of_pmfs \<circ> f)"
  by transfer (simp add: spmf_of_bind_pmfsr)

lemma spmf_of_map_pmfs [simp]: "spmf_of_pmfs (map_pmfs f r) = map_spmf f (spmf_of_pmfs r)"
  by transfer (simp add: spmf_of_map_pmfsr)

definition replicate_spmf where "replicate_spmf n p = map_pmf those (replicate_pmf n p)"

lemma replicate_spmf_0 [simp]: "replicate_spmf 0 p = return_spmf []"
  by (auto simp: replicate_spmf_def)

lemma replicate_spmf_Suc [simp]:
  "replicate_spmf (Suc n) p = do {x \<leftarrow> p; map_spmf (\<lambda>xs. x # xs) (replicate_spmf n p)}"
  by (auto simp: replicate_spmf_def map_bind_pmf bind_spmf_def pmf.map_comp o_def
           intro!: bind_pmf_cong split: option.splits simp flip: map_pmf_def)

lemma spmf_of_replicate_pmfs [simp]:
  "spmf_of_pmfs (replicate_pmfs n r) = replicate_spmf n (spmf_of_pmfs r)"
  by (induction n) (auto simp: o_def)


lemma loss_return_pmfs [simp]: "loss_pmfs (return_pmfs x) = 0"
  by transfer auto

lemma loss_coin_pmfs [simp]: "loss_pmfs (coin_pmfs ) = 0"
  by transfer auto

lemma loss_bind_pmfs:
  "loss_pmfs (r \<bind> f) = loss_pmfs r + (LINT x|measure_spmf (spmf_of_pmfs r). loss_pmfs (f x))"
  by transfer (auto simp: loss_bind_pmfsr)

lemma loss_map_pmfs [simp]: "loss_pmfs (map_pmfs f r) = loss_pmfs r"
  by transfer auto

lemma loss_replicate_pmfs: "loss_pmfs (replicate_pmfs n r) = 1 - (1 - loss_pmfs r) ^ n"
proof (induction n)
  case (Suc n)
  show "loss_pmfs (replicate_pmfs (Suc n) r) = 1 - (1 - loss_pmfs r) ^ Suc n"
    by (simp add: Suc loss_bind_pmfs weight_pmfs algebra_simps)
qed auto


lift_definition ord_pmfs :: "'a pmfs \<Rightarrow> 'a pmfs \<Rightarrow> bool" is ord_pmfsr .

lift_definition lub_pmfs :: "'a pmfs set \<Rightarrow> 'a pmfs" is
  "\<lambda>X. if Complete_Partial_Order.chain ord_pmfsr X then lub_pmfsr X else (\<lambda>_. None)"
  by (auto intro: wf_lub_pmfsr)

lemma lub_pmfs_empty [simp]: "lub_pmfs {} = bot_pmfs"
  by transfer auto

lemma lub_pmfs_const [simp]: "lub_pmfs {r} = r"
  by transfer (auto simp: Complete_Partial_Order.chain_def pmfsr.leq_refl)

lemma bot_pmfs_is_least [simp, intro]: "ord_pmfs bot_pmfs r"
  by transfer (auto simp: ord_pmfsr_def)

lemma partial_function_definitions_pmfs:
  "partial_function_definitions ord_pmfs lub_pmfs"
  (is "partial_function_definitions ?R _")
proof
  fix x show "?R x x"
    by transfer (rule pmfsr.leq_refl)
next
  fix x y z
  assume "?R x y" "?R y z"
  thus "?R x z"
    by transfer (rule pmfsr.leq_trans)
next
  fix x y
  assume "?R x y" "?R y x"
  thus "x = y"
    by transfer (rule pmfsr.leq_antisym)
next
  fix Y r
  assume "Complete_Partial_Order.chain ?R Y" "r \<in> Y"
  thus "?R r (lub_pmfs Y)"
    by transfer (use pmfsr.lub_upper in auto)
next
  fix Y r
  assume "Complete_Partial_Order.chain ?R Y" "\<And>r'. r' \<in> Y \<Longrightarrow> ?R r' r"
  thus "?R (lub_pmfs Y) r"
    by transfer (use pmfsr.lub_least in auto)
qed

lemma ccpo_pmfs: "class.ccpo lub_pmfs ord_pmfs (mk_less ord_pmfs)"
  by (rule ccpo partial_function_definitions_pmfs)+

interpretation pmfs: partial_function_definitions "ord_pmfs" "lub_pmfs"
  rewrites "lub_pmfs {} \<equiv> bot_pmfs"
  by (rule partial_function_definitions_pmfs) simp


declaration \<open>Partial_Function.init "pmfsr" \<^term>\<open>pmfsr.fixp_fun\<close>
  \<^term>\<open>pmfsr.mono_body\<close> @{thm pmfsr.fixp_rule_uc} @{thm pmfsr.fixp_induct_uc}
  NONE\<close>

declare pmfsr.leq_refl[simp]
declare admissible_leI[OF ccpo_pmfsr, cont_intro]

abbreviation "mono_pmfsr \<equiv> monotone (fun_ord ord_pmfsr) ord_pmfsr"

lemma bind_pmfsr_mono':
  assumes fg: "ord_pmfsr f g"
  and hk: "\<And>x :: 'a. ord_pmfsr (h x) (k x)"
  shows "ord_pmfsr (bind_pmfsr f h) (bind_pmfsr g k)"
  unfolding bind_pmfsr_def using assms
  apply (auto simp: ord_pmfsr_def rel_fun_def Option_bind_conv_case split: option.splits)
     apply (metis ord_option_eq_simps(2))
    apply (metis old.prod.inject option.discI option.sel ord_option_eq_simps(2))
   apply (metis Pair_inject option.inject ord_option_eq_simps(2))
  apply (metis fst_conv option.sel ord_option_eq_simps(2) snd_conv)
  done

lemma bind_pmfsr_mono [partial_function_mono]:
  assumes mf: "mono_pmfsr B" and mg: "\<And>y. mono_pmfsr (\<lambda>f. C y f)"
  shows "mono_pmfsr (\<lambda>f. bind_pmfsr (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b pmfsr"
  assume fg: "fun_ord ord_pmfsr f g"
  with mf have "ord_pmfsr (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  moreover from mg have "\<And>y'. ord_pmfsr (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  ultimately show "ord_pmfsr (bind_pmfsr (B f) (\<lambda>y. C y f)) (bind_pmfsr (B g) (\<lambda>y'. C y' g))"
    by (rule bind_pmfsr_mono')
qed

lemma monotone_bind_pmfsr1: "monotone ord_pmfsr ord_pmfsr (\<lambda>y. bind_pmfsr y g)"
  by (rule monotoneI) (simp add: bind_pmfsr_mono')

lemma monotone_bind_pmfsr2:
  assumes g: "\<And>x. monotone ord ord_pmfsr (\<lambda>y. g y x)"
  shows "monotone ord ord_pmfsr (\<lambda>y. bind_pmfsr p (g y))"
  by (rule monotoneI) (auto intro: bind_pmfsr_mono' monotoneD[OF g])

lemma bind_lub_pmfsr:
  assumes chain: "Complete_Partial_Order.chain ord_pmfsr Y"
  shows "bind_pmfsr (lub_pmfsr Y) f = lub_pmfsr ((\<lambda>p. bind_pmfsr p f) ` Y)" (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p x. ennreal (spmf p x * spmf (f x) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD intro: mult_right_mono)
    have chain'': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. p \<bind> f) ` Y)"
      using chain by(rule chain_imageI)(auto intro!: monotoneI bind_spmf_mono' ord_spmf_reflI)
    let ?M = "count_space (set_spmf (lub_spmf Y))"
    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ x. ennreal (spmf (lub_spmf Y) x) * ennreal (spmf (f x) i) \<partial>?M"
      by(auto simp add: ennreal_spmf_lub_spmf ennreal_spmf_bind nn_integral_measure_spmf')
    also have "\<dots> = \<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x * spmf (f x) i)) \<partial>?M"
      by(subst ennreal_spmf_lub_spmf[OF chain Y])(subst SUP_mult_right_ennreal, simp_all add: ennreal_mult Y)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf p x * spmf (f x) i) \<partial>?M)"
      using Y chain' by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf p f) i))"
      by(auto simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_indicator set_lub_spmf[OF chain] in_set_spmf_iff_spmf ennreal_mult intro!: arg_cong [of _ _ Sup] image_cong nn_integral_cong split: split_indicator)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'' by(simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

(*
lemma map_lub_spmf:
  "Complete_Partial_Order.chain (ord_spmf (=)) Y
  \<Longrightarrow> map_spmf f (lub_spmf Y) = lub_spmf (map_spmf f ` Y)"
unfolding map_spmf_conv_bind_spmf[abs_def] by(simp add: bind_lub_spmf o_def)
*)

lemma mcont_bind_pmfsr1: "mcont lub_pmfsr ord_pmfsr lub_pmfsr ord_pmfsr (\<lambda>y. bind_pmfsr y f)"
  using monotone_bind_pmfsr1 by (rule mcontI) (rule contI, simp add: bind_lub_pmfsr)

lemma bind_lub_pmfsr2:
  assumes chain: "Complete_Partial_Order.chain ord Y"
  and g: "\<And>y. monotone ord ord_pmfsr (g y)"
  shows "bind_pmfsr x (\<lambda>y. lub_pmfsr (g y ` Y)) = lub_pmfsr ((\<lambda>p. bind_pmfsr x (\<lambda>y. g y p)) ` Y)"
  (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "\<And>y. Complete_Partial_Order.chain (ord_spmf (=)) (g y ` Y)"
      using chain g[THEN monotoneD] by(rule chain_imageI)
    have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p y. ennreal (spmf x y * spmf (g y p) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD monotoneD[OF g] intro!: mult_left_mono)
    have chain''': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. bind_spmf x (\<lambda>y. g y p)) ` Y)"
      using chain by(rule chain_imageI)(rule monotone_bind_spmf2[OF g, THEN monotoneD])

    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ y. (SUP p\<in>Y. ennreal (spmf x y * spmf (g y p) i)) \<partial>count_space (set_spmf x)"
      by(simp add: ennreal_spmf_bind ennreal_spmf_lub_spmf[OF chain'] Y nn_integral_measure_spmf' SUP_mult_left_ennreal ennreal_mult image_comp)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ y. ennreal (spmf x y * spmf (g y p) i) \<partial>count_space (set_spmf x))"
      unfolding nn_integral_measure_spmf' using Y chain''
      by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf x (\<lambda>y. g y p)) i))"
      by(simp add: ennreal_spmf_bind nn_integral_measure_spmf' ennreal_mult)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'''
      by(auto simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

lemma mcont_bind_pmfsr [cont_intro]:
  assumes f: "mcont luba orda lub_pmfsr ord_pmfsr f"
  and g: "\<And>y. mcont luba orda lub_pmfsr ord_pmfsr (g y)"
  shows "mcont luba orda lub_pmfsr ord_pmfsr (\<lambda>x. bind_pmfsr (f x) (\<lambda>y. g y x))"
proof(rule pmfsr.mcont2mcont'[OF _ _ f])
  fix z
  show "mcont lub_pmfsr ord_pmfsr lub_pmfsr ord_pmfsr (\<lambda>x. bind_pmfsr x (\<lambda>y. g y z))"
    by(rule mcont_bind_pmfsr1)
next
  fix x
  let ?f = "\<lambda>z. bind_pmfsr x (\<lambda>y. g y z)"
  have "monotone orda ord_pmfsr ?f" using mcont_mono[OF g] by(rule monotone_bind_pmfsr2)
  moreover have "cont luba orda lub_pmfsr ord_pmfsr ?f"
  proof(rule contI)
    fix Y
    assume chain: "Complete_Partial_Order.chain orda Y" and Y: "Y \<noteq> {}"
    have "bind_pmfsr x (\<lambda>y. g y (luba Y)) = bind_pmfsr x (\<lambda>y. lub_pmfsr (g y ` Y))"
      by (rule bind_pmfsr_cong) (simp_all add: mcont_contD[OF g chain Y])
    also have "\<dots> = lub_pmfsr ((\<lambda>p. bind_pmfsr x (\<lambda>y. g y p)) ` Y)" using chain
      by (rule bind_lub_pmfsr2)(rule mcont_mono[OF g])
    finally show "bind_pmfsr x (\<lambda>y. g y (luba Y)) = \<dots>" .
  qed
  ultimately show "mcont luba orda lub_pmfsr ord_pmfsr ?f" by(rule mcontI)
qed


lemma map_pmfsr_mono [partial_function_mono]: "mono_pmfsr B \<Longrightarrow> mono_pmfsr (\<lambda>g. map_pmfsr f (B g))"
  unfolding map_pmfsr_conv_bind_pmfsr by(rule bind_pmfsr_mono) simp_all

lemma mcont_map_pmfsr [cont_intro]:
  "mcont luba orda lub_pmfsr ord_pmfsr g
  \<Longrightarrow> mcont luba orda lub_pmfsr ord_pmfsr (\<lambda>x. map_pmfsr f (g x))"
  unfolding map_pmfsr_conv_bind_pmfsr by (rule mcont_bind_pmfsr) simp_all


lemma monotone_set_pmfsr: "monotone ord_pmfsr (\<subseteq>) range_pmfsr"
  apply (rule monotoneI)
  apply (auto simp: ord_pmfsr_def rel_fun_def range_pmfsr_def)
  by (metis in_range_pmfsrI ord_option_eq_simps(2) range_pmfsr_def)

lemma cont_set_pmfsr: "cont lub_pmfsr ord_pmfsr Union (\<subseteq>) range_pmfsr"
  apply (rule contI)
  apply (auto simp: ord_pmfsr_def rel_fun_def range_pmfsr_def)
   apply (metis in_range_pmfsrI lub_pmfsr_eq_SomeE range_pmfsr_def)
  oops


lemma mcont2mcont_set_pmfsr[THEN mcont2mcont, cont_intro]:
  shows mcont_set_pmfsr: "mcont lub_pmfsr ord_pmfsr Union (\<subseteq>) range_pmfsr"
  oops
(*
by(rule mcontI monotone_set_pmfsr cont_set_pmfsr)+
*)



(*
  NB: if a recursively defined sampler (PMFS) is lossless, then due to the monotonicity of
  spmf_of_pmfs, the SPMF defined by the equivalent recurrence is unique, lossless, and equals the
  one generated by the sampler.

  At least I think so.
*)
lemma ord_spmf_eq_and_weight_spmf_1_imp_eq:
  assumes "ord_spmf (=) p q" and "weight_spmf p = 1"
  shows   "p = q"
proof (rule pmf_eqI)
  fix x :: "'a option"
  show "pmf p x = pmf q x"
  proof (cases x)
    case None
    thus ?thesis
      using assms apply (simp add: pmf_None_eq_weight_spmf)
      by (metis ennreal_le_iff measure_nonneg measure_spmf.emeasure_eq_measure
                measure_spmf.subprob_measure_le_1 ord_spmf_eqD_emeasure order_antisym_conv
                space_measure_spmf)
  next
    case [simp]: (Some y)
    show ?thesis
      using assms
      apply auto
      by (smt (verit) ord_option.cases pmf.rel_eq pmf.rel_mono_strong pmf_None_eq_weight_spmf set_pmf_iff)
  qed
qed

lemma
  assumes "weight_spmf p = weight_spmf q" "ord_spmf (=) p q"
  shows   "p = q"
  oops

lemma mono_spmf_of_pmfsr:
  assumes "ord_pmfsr r r'" "wf_pmfsr r" "wf_pmfsr r'"
  shows   "ord_spmf (=) (spmf_of_pmfsr r) (spmf_of_pmfsr r')"
  sorry

lemma mono_spmf_of_pmfs:
  assumes "ord_pmfs r r'"
  shows   "ord_spmf (=) (spmf_of_pmfs r) (spmf_of_pmfs r')"
  using assms by transfer (rule mono_spmf_of_pmfsr)




declaration \<open>Partial_Function.init "pmfs" \<^term>\<open>pmfs.fixp_fun\<close>
  \<^term>\<open>pmfs.mono_body\<close> @{thm pmfs.fixp_rule_uc} @{thm pmfs.fixp_induct_uc}
  NONE\<close>

declare pmfs.leq_refl[simp]
declare admissible_leI[OF ccpo_pmfs, cont_intro]

abbreviation "mono_pmfs \<equiv> monotone (fun_ord ord_pmfs) ord_pmfs"

lemma bind_pmfs_mono':
  assumes fg: "ord_pmfs f g"
  and hk: "\<And>x :: 'a. ord_pmfs (h x) (k x)"
shows "ord_pmfs (bind_pmfs f h) (bind_pmfs g k)"
  using assms by transfer (use bind_pmfsr_mono' in blast)

lemma bind_pmfs_mono [partial_function_mono]:
  assumes mf: "mono_pmfs B" and mg: "\<And>y. mono_pmfs (\<lambda>f. C y f)"
  shows "mono_pmfs (\<lambda>f. bind_pmfs (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b pmfs"
  assume fg: "fun_ord ord_pmfs f g"
  with mf have "ord_pmfs (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  moreover from mg have "\<And>y'. ord_pmfs (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  ultimately show "ord_pmfs (bind_pmfs (B f) (\<lambda>y. C y f)) (bind_pmfs (B g) (\<lambda>y'. C y' g))"
    by (rule bind_pmfs_mono')
qed

lemma monotone_bind_pmfs1: "monotone ord_pmfs ord_pmfs (\<lambda>y. bind_pmfs y g)"
  by (rule monotoneI) (simp add: bind_pmfs_mono')

lemma monotone_bind_pmfs2:
  assumes g: "\<And>x. monotone ord ord_pmfs (\<lambda>y. g y x)"
  shows "monotone ord ord_pmfs (\<lambda>y. bind_pmfs p (g y))"
  by (rule monotoneI) (auto intro: bind_pmfs_mono' monotoneD[OF g])

lemma bind_lub_pmfs:
  assumes chain: "Complete_Partial_Order.chain ord_pmfs Y"
  shows "bind_pmfs (lub_pmfs Y) f = lub_pmfs ((\<lambda>p. bind_pmfs p f) ` Y)" (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p x. ennreal (spmf p x * spmf (f x) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD intro: mult_right_mono)
    have chain'': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. p \<bind> f) ` Y)"
      using chain by(rule chain_imageI)(auto intro!: monotoneI bind_spmf_mono' ord_spmf_reflI)
    let ?M = "count_space (set_spmf (lub_spmf Y))"
    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ x. ennreal (spmf (lub_spmf Y) x) * ennreal (spmf (f x) i) \<partial>?M"
      by(auto simp add: ennreal_spmf_lub_spmf ennreal_spmf_bind nn_integral_measure_spmf')
    also have "\<dots> = \<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x * spmf (f x) i)) \<partial>?M"
      by(subst ennreal_spmf_lub_spmf[OF chain Y])(subst SUP_mult_right_ennreal, simp_all add: ennreal_mult Y)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf p x * spmf (f x) i) \<partial>?M)"
      using Y chain' by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf p f) i))"
      by(auto simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_indicator set_lub_spmf[OF chain] in_set_spmf_iff_spmf ennreal_mult intro!: arg_cong [of _ _ Sup] image_cong nn_integral_cong split: split_indicator)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'' by(simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

(*
lemma map_lub_spmf:
  "Complete_Partial_Order.chain (ord_spmf (=)) Y
  \<Longrightarrow> map_spmf f (lub_spmf Y) = lub_spmf (map_spmf f ` Y)"
unfolding map_spmf_conv_bind_spmf[abs_def] by(simp add: bind_lub_spmf o_def)
*)

lemma mcont_bind_pmfs1: "mcont lub_pmfs ord_pmfs lub_pmfs ord_pmfs (\<lambda>y. bind_pmfs y f)"
  using monotone_bind_pmfs1 by (rule mcontI) (rule contI, simp add: bind_lub_pmfs)

lemma bind_lub_pmfs2:
  assumes chain: "Complete_Partial_Order.chain ord Y"
  and g: "\<And>y. monotone ord ord_pmfs (g y)"
  shows "bind_pmfs x (\<lambda>y. lub_pmfs (g y ` Y)) = lub_pmfs ((\<lambda>p. bind_pmfs x (\<lambda>y. g y p)) ` Y)"
  (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "\<And>y. Complete_Partial_Order.chain (ord_spmf (=)) (g y ` Y)"
      using chain g[THEN monotoneD] by(rule chain_imageI)
    have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p y. ennreal (spmf x y * spmf (g y p) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD monotoneD[OF g] intro!: mult_left_mono)
    have chain''': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. bind_spmf x (\<lambda>y. g y p)) ` Y)"
      using chain by(rule chain_imageI)(rule monotone_bind_spmf2[OF g, THEN monotoneD])

    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ y. (SUP p\<in>Y. ennreal (spmf x y * spmf (g y p) i)) \<partial>count_space (set_spmf x)"
      by(simp add: ennreal_spmf_bind ennreal_spmf_lub_spmf[OF chain'] Y nn_integral_measure_spmf' SUP_mult_left_ennreal ennreal_mult image_comp)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ y. ennreal (spmf x y * spmf (g y p) i) \<partial>count_space (set_spmf x))"
      unfolding nn_integral_measure_spmf' using Y chain''
      by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf x (\<lambda>y. g y p)) i))"
      by(simp add: ennreal_spmf_bind nn_integral_measure_spmf' ennreal_mult)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'''
      by(auto simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

lemma mcont_bind_pmfs [cont_intro]:
  assumes f: "mcont luba orda lub_pmfs ord_pmfs f"
  and g: "\<And>y. mcont luba orda lub_pmfs ord_pmfs (g y)"
  shows "mcont luba orda lub_pmfs ord_pmfs (\<lambda>x. bind_pmfs (f x) (\<lambda>y. g y x))"
proof(rule pmfs.mcont2mcont'[OF _ _ f])
  fix z
  show "mcont lub_pmfs ord_pmfs lub_pmfs ord_pmfs (\<lambda>x. bind_pmfs x (\<lambda>y. g y z))"
    by(rule mcont_bind_pmfs1)
next
  fix x
  let ?f = "\<lambda>z. bind_pmfs x (\<lambda>y. g y z)"
  have "monotone orda ord_pmfs ?f" using mcont_mono[OF g] by(rule monotone_bind_pmfs2)
  moreover have "cont luba orda lub_pmfs ord_pmfs ?f"
  proof(rule contI)
    fix Y
    assume chain: "Complete_Partial_Order.chain orda Y" and Y: "Y \<noteq> {}"
    have "bind_pmfs x (\<lambda>y. g y (luba Y)) = bind_pmfs x (\<lambda>y. lub_pmfs (g y ` Y))"
      by (rule bind_pmfs_cong) (simp_all add: mcont_contD[OF g chain Y])
    also have "\<dots> = lub_pmfs ((\<lambda>p. bind_pmfs x (\<lambda>y. g y p)) ` Y)" using chain
      by (rule bind_lub_pmfs2)(rule mcont_mono[OF g])
    finally show "bind_pmfs x (\<lambda>y. g y (luba Y)) = \<dots>" .
  qed
  ultimately show "mcont luba orda lub_pmfs ord_pmfs ?f" by(rule mcontI)
qed

lemma map_pmfs_mono [partial_function_mono]: "mono_pmfs B \<Longrightarrow> mono_pmfs (\<lambda>g. map_pmfs f (B g))"
  unfolding map_pmfs_conv_bind_pmfs by(rule bind_pmfs_mono) simp_all

lemma mcont_map_pmfs [cont_intro]:
  "mcont luba orda lub_pmfs ord_pmfs g
  \<Longrightarrow> mcont luba orda lub_pmfs ord_pmfs (\<lambda>x. map_pmfs f (g x))"
  unfolding map_pmfs_conv_bind_pmfs by (rule mcont_bind_pmfs) simp_all

lemma replicate_pmfs_mono [partial_function_mono]:
  "mono_pmfs B \<Longrightarrow> mono_pmfs (\<lambda>g. replicate_pmfs n (B g))"
  by (induction n) (auto intro!: partial_function_mono)

lemma mcont_replicate_pmfs [cont_intro]:
  assumes f: "mcont luba orda lub_pmfs ord_pmfs f"
  shows "mcont luba orda lub_pmfs ord_pmfs (\<lambda>x. replicate_pmfs n (f x))"
  by (induction n) (auto intro!: cont_intro assms)



lemma monotone_set_pmfs: "monotone ord_pmfs (\<subseteq>) range_pmfs"
  unfolding monotone_def
  by transfer (use monotone_set_pmfsr in \<open>auto simp: monotone_def\<close>)

lemma cont_set_pmfs: "cont lub_pmfs ord_pmfs Union (\<subseteq>) range_pmfs"
  oops

lemma mcont2mcont_set_pmfs[THEN mcont2mcont, cont_intro]:
  shows mcont_set_pmfs: "mcont lub_pmfs ord_pmfs Union (\<subseteq>) range_pmfs"
  oops
(*
by(rule mcontI monotone_set_pmfs cont_set_pmfs)+
*)



definition random_bit_list
  where "random_bit_list = [False, False, True, True, True, False, True, True, False, False, False, False, True,
 True, True, False, False, True, True, True, True, True, True, True, False, False, True,
 True, False, True, False, True, False, False, False, False, True, True, True, True,
 True, False, True, False, False, True, False, True, True, False, False, False, True,
 False, True, True, False, True, False, False, False, False, True, True, True, False,
 False, False, False, True, True, True, True, False, False, False, True, True, False,
 True, False, True, False, False, True, False, True, False, False, True, False, True,
 True, False, False, False, False, False, False, False, False, True, True, False, True,
 False, True, False, True, False, True, False, True, True, False, True, True, True,
 True, True, True, False, True, True, False, True, True, True, False, True, True, False,
 False, False, True, True, True, True, True, False, True, False, False, False, False,
 False, False, False, False, False, False, False, True, False, False, False, False,
 True, False, False, False, True, True, False, False, False, True, False, False, True,
 True, True, True, False, True, False, False, False, True, True, False, False, False,
 True, False, False, False, True, True, False, True, False, False, False, True, False,
 True, True, False, True, True, True, True, False, False, True, True, False, True,
 False, False, True, False, False, False, False, False, False, True, True, True, False,
 True, False, False, False, False, False, False, False, False, True, True, True, True,
 False, True, True, True, False, False, True, False, True, False, True, False, False,
 True, True, False, True, True, True, True, True, False, False, True, True, True, False,
 False, True, False, False, False, False, False, False, True, False, True, True, False,
 True, True, False, False, False, False, True, False, False, False, True, False, True,
 True, False, True, False, False, True, True, True, False, True, True, False, False,
 True, False, False, True, True, True, True, False, False, True, False, False, False,
 False, False, True, True, False, False, True, True, False, True, True, True, False,
 True, True, True, True, True, True, True, True, True, True, True, False, True, False,
 True, False, True, True, True, True, True, True, False, False, True, False, True,
 False, False, True, False, True, False, False, False, False, False, False, True, False,
 True, False, True, True, False, False, True, True, False, True, True, False, True,
 False, True, False, True, True, False, True, True, True, True, True, False, True,
 False, False, False, False, True, False, True, False, True, True, False, True, False,
 False, False, True, True, False, False, False, True, False, False, False, False, False,
 False, True, False, True, True, False, False, True, False, True, True, False, False,
 False, False, False, False, True, False, True, False, True, True, False, True, False,
 True, True, True, False, True, True, False, True, True, True, False, True, False,
 False, True, True, True, False, True, True, True, True, True, True, False, True, False,
 True, False, False, True, False, True, True, False, False, False, False, True, False,
 False, True, True, False, True, True, True, False, True, False, True, False, False,
 False, True, True, True, True, True, False, True, True, False, False, True, True, True,
 False, False, True, True, False, True, True, False, False, False, False, False, True,
 True, True, False, False, False, True, True, False, True, True, True, False, True,
 False, True, True, True, False, False, True, True, False, True, False, True, False,
 False, False, True, True, True, False, False, True, True, False, True, True, False,
 False, False, True, False, False, False, False, True, False, False, True, True, False,
 True, True, False, True, False, False, True, True, True, False, True, True, True, True,
 False, False, True, True, True, False, False, False, True, False, True, False, False,
 True, True, False, True, False, False, True, False, False, True, True, True, False,
 True, True, True, False, True, False, True, True, False, True, False, False, True,
 False, False, True, False, True, False, False, True, True, True, True, True, True,
 False, False, False, False, True, True, True, False, True, True, True, False, True,
 False, False, True, True, True, True, True, False, False, False, True, True, False,
 True, False, True, True, True, False, False, True, True, False, True, False, True,
 True, True, False, False, True, True, True, True, False, False, True, False, False,
 False, True, True, True, False, True, False, True, False, True, True, False, False,
 False, False, False, False, False, True, False, False, True, True, True, True, True,
 True, False, True, True, True, False, True, False, False, False, False, True, True,
 True, True, True, True, True, True, True, True, True, True, True, True, False, False,
 True, False, True, True, False, True, False, True, False, False, True, False, False,
 True, True, False, False, False, True, False, False, True, False, False, True, True,
 True, True, False, False, True, False, True, True, True, True, True, True, False,
 False, False, False, False, False, False, False, True, True, False, True, False, True,
 True, True, True, True, True, False, True, True, True, False, False, True, True, False,
 False, False, False, True, True, False, True, True, True, True, True, True, True, True,
 False, True, False, True, True, True, True, False, True, False, True, True, True, True,
 True, True, False, True, True, False, True, False, True, False, True, True, False,
 True, True, True, False, False, False, True, False, True, True, False, False, False,
 True, False, True, True, False, True, True, False, False, True, False, True, False,
 False, False, False, True, False, False, False, True, True, False, True, False, False,
 False, True, True, True, True, True, False, False, False, False, True, False, False,
 True, False, False, True, True, True, True, False, True, True, False, True, False,
 True, True, True, True, False, False, False, False, False, True, True, True, True,
 True, False, True, True, False, False, True, True, False, False, True, False, True,
 True, False, False, True, False, True, True, False, True, True, True, True, False,
 False, False, False, True, True, True, True, True, True, True, False, True, True, True,
 True, False, False, True, True, True, False, True, True, True, True, False, True,
 False, False, False, True, False, True, True, True, True, False, False, False, True,
 False]"


definition random_bits
  where "random_bits i = cycle (rotate i random_bit_list)"


code_lazy_type stream

partial_function (pmfs) bernoulli_pmfs :: "real \<Rightarrow> bool pmfs" where
  "bernoulli_pmfs p =
     do {b \<leftarrow> coin_pmfs;
         if b then
           return_pmfs (p \<ge> 1/2)
         else
           bernoulli_pmfs (if p < 1/2 then 2 * p else 2 * p - 1)}"

lemmas [code] = bernoulli_pmfs.simps

value "run_pmfs' (bernoulli_pmfs (1/3)) (random_bits 1)"
value "run_pmfs' (bernoulli_pmfs (1/3)) (random_bits 2)"
value "run_pmfs' (bernoulli_pmfs (1/3)) (random_bits 8)"


partial_function (pmfs) geometric_pmfs :: "real \<Rightarrow> nat pmfs" where
  "geometric_pmfs p =
     do {b \<leftarrow> bernoulli_pmfs p;
         if b then return_pmfs 0 else map_pmfs Suc (geometric_pmfs p)}"

lemmas [code] = geometric_pmfs.simps


value "run_pmfs' (geometric_pmfs (1/3)) (random_bits 1)"
value "map (\<lambda>i. fst (the (run_pmfs' (geometric_pmfs (1/3)) (random_bits i)))) [0..<100]"


lemma loss_pmfs_bernoulli [simp]: "loss_pmfs (bernoulli_pmfs p) = 0"
proof -
  define f where "f = (\<lambda>p. loss_pmfs (bernoulli_pmfs p))"
  have f_rec: "f p = f (if p < 1 / 2 then 2 * p else 2 * p - 1) / 2" for p
    unfolding f_def
    by (subst bernoulli_pmfs.simps)
       (simp_all add: loss_bind_pmfs spmf_of_set_def integral_pmf_of_set UNIV_bool
                 del: spmf_of_pmf_pmf_of_set)
  have f_01: "f p \<in> {0..1}" for p
    using loss_pmfs_01[of "bernoulli_pmfs p"] by (auto simp: f_def)
  have f_le: "f p \<le> 1 / 2 ^ n" for n
  proof (induction n arbitrary: p)
    case (Suc p)
    thus ?case
      using f_01[of p] by (auto simp: f_rec[of p])
  qed (use f_01 in auto)
  show "f p = 0"
  proof (rule ccontr)
    assume "f p \<noteq> 0"
    with f_01[of p] have "f p > 0"
      by auto
    have "\<exists>n. 2 ^ n > 1 / f p"
      by (rule real_arch_pow) auto
    then obtain n where "2 ^ n > 1 / f p"
      by auto
    hence "f p > 1 / 2 ^ n"
      using \<open>f p > 0\<close> by (auto simp: field_simps)
    with f_le[of n] show False
      by simp
  qed
qed

lemma spmf_of_pmfs_bernoulli [simp]: "spmf_of_pmfs (bernoulli_pmfs p) = spmf_of_pmf (bernoulli_pmf p)"
  sorry


lemma loss_pmfs_geometric [simp]:
  assumes "p \<in> {0<..1}"
  shows   "loss_pmfs (geometric_pmfs p) = 0"
proof -
  have "loss_pmfs (geometric_pmfs p) = loss_pmfs (geometric_pmfs p) * (1 - p)"
    using assms by (subst geometric_pmfs.simps) (simp_all add: loss_bind_pmfs)
  thus "loss_pmfs (geometric_pmfs p) = 0"
    using assms by (auto simp: algebra_simps)
qed



partial_function (pmfs) while_pmfs :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a pmfs) \<Rightarrow> 'a \<Rightarrow> 'a pmfs" where
  "while_pmfs guard body s =
     (if guard s then return_pmfs s else body s \<bind> while_pmfs guard body)"

lemmas [code] = while_pmfs.simps

value "run_pmfs (while_pmfs (\<lambda>n::nat. n > 42) (\<lambda>n. map_pmfs (\<lambda>b. of_bool b + 2 * n) coin_pmfs) 0) (random_bits 0)"
value "run_pmfs (while_pmfs (\<lambda>n::nat. n > 42) (\<lambda>n. map_pmfs (\<lambda>b. of_bool b + 2 * n) coin_pmfs) 0) (random_bits 4)"
value "run_pmfs (while_pmfs (\<lambda>n::nat. n > 42) (\<lambda>n. map_pmfs (\<lambda>b. of_bool b + 2 * n) coin_pmfs) 0) (random_bits 5)"



datatype 'a mytree = Node 'a "'a mytree list"

partial_function (pmfs) foo :: "real \<Rightarrow> bool mytree pmfs" where
  "foo p = do {
     b \<leftarrow> coin_pmfs;
     n \<leftarrow> geometric_pmfs p; map_pmfs (\<lambda>xs. Node b xs) (replicate_pmfs n (foo (2 * p)))}"

lemmas [code] = foo.simps

value "run_pmfs' (foo 0.1) (random_bits 1)"
value "run_pmfs' (foo 0.1) (random_bits 2)"
value "run_pmfs' (foo 0.1) (random_bits 3)"


context
  fixes n :: nat
begin

partial_function (pmfs) fast_dice_roll :: "nat \<Rightarrow> nat \<Rightarrow> nat pmfs"
where
  "fast_dice_roll v c =
  (if v \<ge> n then if c < n then return_pmfs c else fast_dice_roll (v - n) (c - n)
   else do {
     b \<leftarrow> coin_pmfs;
     fast_dice_roll (2 * v) (2 * c + (if b then 1 else 0)) } )"

definition fast_uniform :: "nat pmfs"
  where "fast_uniform = fast_dice_roll 1 0"

end

lemmas [code] = fast_dice_roll.simps

value "run_pmfs' (fast_uniform 10) ([True, False, True, True, False] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([False, False, True, True, False] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, False, True, False, False] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, False, True, True, True] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, False, True, True, False, True, True, False, True] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, True, True, True, True, True, False, True, True] @- sconst False)"
value "map (\<lambda>i. fst (the (run_pmfs' (fast_uniform 10) (random_bits i)))) [0..<100]"
value "run_pmfs' (replicate_pmfs 100 (fast_uniform 10)) (random_bits 0)"
value "run_pmfs' (replicate_pmfs 100 (fast_uniform 10)) (random_bits 43)"
value "run_pmfs (consumption_pmfs (replicate_pmfs 100 (fast_uniform 10))) (random_bits 43)"


ML_val \<open>
@{theory}
|> Theory.defs_of
|> (fn defs => Defs.specifications_of defs (Defs.Const, @{const_name bernoulli_pmfs}))
|> map (#def #> the)
\<close>

ML_val \<open>
@{theory}
|> Global_Theory.facts_of
|> (fn f => Facts.extern @{context} f "PMF_Sampler.bernoulli_pmfs_def")
\<close>

ML_val \<open>
@{theory}
|> Theory.axiom_table
|> (fn tbl => Name_Space.lookup tbl "PMF_Sampler.bernoulli_pmfs_def")
|> the
|> Syntax.pretty_term @{context}
|> Pretty.writeln
\<close>

term "ccpo.fixp (fun_lub lub_pmfs) (fun_ord ord_pmfs)"

thm ccpo.fixp_def[OF pmfs.ccpo]
thm ccpo.iterates_def[OF pmfs.ccpo]

find_theorems ccpo.fixp monotone "_ = _" name:Complete "ccpo.fixp"

thm fun_lub_def

ML_val \<open>@{term "pmfs.fixp_fun"}\<close>


end