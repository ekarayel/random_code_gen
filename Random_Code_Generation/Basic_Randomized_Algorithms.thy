theory Basic_Randomized_Algorithms
  imports 
    Randomized_Algorithm 
    Probabilistic_While.Bernoulli 
    Probabilistic_While.Geometric
begin

text \<open>Bernoulli distribution\<close>

declare [[function_internals]]

partial_function (random_alg) bernoulli_ra :: "real \<Rightarrow> bool random_alg" where
  "bernoulli_ra p = do {
     b \<leftarrow> coin_ra;
     if b then return_ra (p \<ge> 1 / 2)
     else if p < 1 / 2 then bernoulli_ra (2 * p)
     else bernoulli_ra (2 * p - 1)
   }"

lemma bernoulli_ra_correct_aux: "ord_spmf (=) (bernoulli x) (spmf_of_ra (bernoulli_ra x))"
proof (induction arbitrary:x rule:bernoulli.fixp_induct)
  case 1
  thus "spmf.admissible (\<lambda>bernoulli. \<forall>x. ord_spmf (=) (bernoulli x) (spmf_of_ra (bernoulli_ra x)))" 
    by simp
next
  case 2
  thus "ord_spmf (=) (return_pmf None) (spmf_of_ra (bernoulli_ra x))" by simp
next
  case (3 p)
  thus ?case by (subst bernoulli_ra.simps)
      (auto intro:ord_spmf_bind_reflI simp:spmf_of_ra_bind spmf_of_ra_coin spmf_of_ra_return)
qed

lemma bernoulli_ra_correct: "bernoulli x = spmf_of_ra (bernoulli_ra x)"
  using lossless_bernoulli weight_spmf_le_1 unfolding lossless_spmf_def
  by (intro eq_iff_ord_spmf[OF _ bernoulli_ra_correct_aux]) auto 

context 
  includes lifting_syntax
begin

lemma bernoulli_ra_transfer [transfer_rule]:
  "((=) ===> rel_spmf_of_ra) bernoulli bernoulli_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def bernoulli_ra_correct by simp

end

text \<open>Geometric distribution\<close>

partial_function (random_alg) geometric_ra :: "real \<Rightarrow> nat random_alg" where
  "geometric_ra p = do {
     b \<leftarrow> bernoulli_ra p;
     if b then return_ra 0 else map_ra ((+) 1) (geometric_ra p)
  }"

lemma geometric_ra_correct: "spmf_of_ra (geometric_ra x) = geometric_spmf x"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) geometric_spmf geometric_ra"
    unfolding geometric_ra_def geometric_spmf_def
    apply (rule fixp_ra_parametric[OF geometric_spmf.mono geometric_ra.mono])
    by transfer_prover
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by auto
qed

text \<open>Replication of a distribution\<close>

fun replicate_ra :: "nat \<Rightarrow> 'a random_alg \<Rightarrow> 'a list random_alg"
  where 
    "replicate_ra 0 f = return_ra []" |
    "replicate_ra (Suc n) f = do { xh \<leftarrow> f; xt \<leftarrow> replicate_ra n f; return_ra (xh#xt) }"

fun replicate_spmf :: "nat \<Rightarrow> 'a spmf \<Rightarrow> 'a list spmf"
  where 
    "replicate_spmf 0 f = return_spmf []" |
    "replicate_spmf (Suc n) f = do { xh \<leftarrow> f; xt \<leftarrow> replicate_spmf n f; return_spmf (xh#xt) }"

lemma replicate_ra_correct: "spmf_of_ra (replicate_ra n f) = replicate_spmf n (spmf_of_ra f)"
  by (induction n) (auto simp :spmf_of_ra_return spmf_of_ra_bind)

lemma replicate_spmf_of_pmf: "replicate_spmf n (spmf_of_pmf f) = spmf_of_pmf (replicate_pmf n f)"
  by (induction n) (simp_all add:spmf_of_pmf_bind)

text \<open>Binomial distribution\<close>

definition binomial_ra :: "nat \<Rightarrow> real \<Rightarrow> nat random_alg"
  where "binomial_ra n p = map_ra (length \<circ> filter id) (replicate_ra n (bernoulli_ra p))"

lemma
  assumes "p \<in> {0..1}"
  shows "spmf_of_ra (binomial_ra n p) = spmf_of_pmf (binomial_pmf n p)"
proof -
  have "spmf_of_ra(replicate_ra n (bernoulli_ra p))=spmf_of_pmf(replicate_pmf n (bernoulli_pmf p))"
    unfolding replicate_ra_correct bernoulli_ra_correct[symmetric] bernoulli_eq_bernoulli_pmf
    by (simp add:replicate_spmf_of_pmf)

  thus ?thesis
    unfolding binomial_pmf_altdef[OF assms] binomial_ra_def
    by (simp flip:map_spmf_of_pmf add:spmf_of_ra_map_ra)
qed

end