theory Standard_PMFs
  imports
    "HOL-Probability.Probability" 
begin

text \<open>This is a library of code equations for common pmfs based on the primitve nat_pmf, which
performs sampling a natural number uniformly from a range.\<close>

definition nat_pmf :: "nat \<Rightarrow> nat pmf" where
  "nat_pmf n = pmf_of_set {0..n}"

lemma pmf_of_set_code [code]:
  "pmf_of_set (set xs) =
     (if xs = [] then
        Code.abort (STR ''pmf_of_set {}'') (\<lambda>_. pmf_of_set {})
      else (let xs' = remdups xs in
        map_pmf (\<lambda>k. xs' ! k) (nat_pmf (length xs' - 1))))"
proof -
  have "pmf_of_set (set xs) = map_pmf (\<lambda>k. xs ! k) (nat_pmf (length xs - 1))"
    if "xs \<noteq> []" "distinct xs" for xs :: "'a list"
  proof -
    define n where "n = length xs"
    from \<open>xs \<noteq> []\<close> have n: "n > 0" "length xs \<ge> n"
      by (force simp: n_def)+
    have "map_pmf ((!) xs) (nat_pmf (n - 1)) = pmf_of_set ((!) xs ` {0..n - 1})"
      unfolding nat_pmf_def using that n
      by (intro map_pmf_of_set_inj inj_on_nth) 
         (auto simp: minus_nat.diff_Suc split: nat.splits)
    also have "{0..n - 1} = {..<n}"
      using n by auto
    also have "(!) xs ` {..<n} = set xs"
      by (auto simp: n_def set_conv_nth)
    finally show ?thesis
      by (simp add: n_def)
  qed
  from this[of "remdups xs"] show ?thesis
    by (auto simp: Let_def)
qed

lemma eq_bernoulli_pmfI: "pmf d True = p \<Longrightarrow> d = bernoulli_pmf p"
  by (metis (full_types) pmf_False_conv_True pmf_bernoulli_True pmf_eq_iff pmf_le_1 pmf_nonneg)

lemma bernoulli_pmf_code [code]:
  "bernoulli_pmf (Ratreal p) = (let (a, b) = quotient_of (max 0 (min 1 p)) in
     map_pmf (\<lambda>k. int k < a) (nat_pmf (nat b - 1)))" (is "_ = ?rhs")
proof (cases "p \<in> {0..1}")
  case True
  obtain x y where xy: "quotient_of p = (x, y)"
    by (cases "quotient_of p")
  have p_eq: "p = of_int x / of_int y"
    using xy by (metis quotient_of_div)
  have "y > 0"
    using xy by (simp add: quotient_of_denom_pos)
  have "x \<ge> 0"
    using True xy
    by (metis Fract_of_int_quotient \<open>0 < y\<close> atLeastAtMost_iff quotient_of_div zero_le_Fract_iff)
  have "Ratreal p \<in> {0..1}"
    using True by simp
  hence "x \<ge> 0" "x \<le> y"
    using \<open>y > 0\<close> unfolding p_eq by (auto simp: field_simps)
  define x' y' where "x' = nat x" and "y' = nat y"
  have [simp]: "x = int x'" "y = int y'" and "x' \<ge> 0" "y' > 0" "x' \<le> y'"
    using \<open>x \<ge> 0\<close> \<open>y > 0\<close> \<open>x \<le> y\<close> unfolding x'_def y'_def by auto
  
  show ?thesis
  proof (rule sym, rule eq_bernoulli_pmfI)
    have "pmf ?rhs True = measure_pmf.prob (pmf_of_set {0..y'-1}) ((\<lambda>k. k < x') -` {True})"
      using True \<open>y > 0\<close> by (auto simp: xy nat_pmf_def pmf_map)
    also have "{0..y'-1} = {0..<y'}"
      using \<open>y' > 0\<close> by (metis Suc_diff_1 atLeastLessThanSuc_atLeastAtMost)
    also have "(\<lambda>k. k < x') -` {True} = {0..<x'}"
      by force
    also have "measure_pmf.prob (pmf_of_set {0..<y'}) {0..<x'} = Ratreal p"
      using \<open>x' \<le> y'\<close> \<open>y' > 0\<close> by (subst measure_pmf_of_set) (auto simp: p_eq of_rat_divide)
    finally show "pmf ?rhs True = Ratreal p" .
  qed
qed (auto intro!: pmf_eqI simp: bernoulli_pmf.rep_eq nat_pmf_def pmf_of_set_singleton)

lemma binomial_pmf_code [code]:
  "binomial_pmf n p =
     (if 0 \<le> p \<and> p \<le> 1 then
        map_pmf (length \<circ> filter id) (replicate_pmf n (bernoulli_pmf p))
      else
        Code.abort (STR ''binomial_pmf: probability out of range'') (\<lambda>_. binomial_pmf n p))"
  using binomial_pmf_altdef by simp

lemma geometric_pmf_code [code]: "geometric_pmf p =
    (if 0 < p \<and> p \<le> 1 then
       bernoulli_pmf p \<bind> (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf p))
     else
       Code.abort (STR ''geometric_pmf: probability out of range'') (\<lambda>_. geometric_pmf p)
    )"
  using geometric_bind_pmf_unfold[of p] by simp

end