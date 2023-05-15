theory Sample_PMF
  imports 
    Standard_PMFs
    "HOL-Probability.Probability" 
    "HOL-Library.Code_Target_Numeral"
    "Fisher_Yates.Fisher_Yates" 
    "Random_BSTs.Random_BSTs" 
    "Quick_Sort_Cost.Randomised_Quick_Sort" 
    "List_Inversions.List_Inversions"
  keywords "estimate_pmf" :: "diag"
begin

subsection \<open>Implementing standard PMFs in terms of the primitives\<close>

text \<open>Uniform distribution of integers between 0 and \<open>n\<close> (inclusive):\<close>
definition integer_pmf :: "integer \<Rightarrow> integer pmf" where
  "integer_pmf n = pmf_of_set {0..n}"

declare [[code abort: integer_pmf]]

lemma nat_pmf_code [code]: "nat_pmf n = map_pmf nat_of_integer (integer_pmf (integer_of_nat n))"
  unfolding nat_pmf_def integer_pmf_def
proof (rule map_pmf_of_set_bij_betw [symmetric])
  show bij: "bij_betw nat_of_integer {0..integer_of_nat n} {0..n}"
    apply (intro bij_betwI[of _ _ _ integer_of_nat])
       apply (auto simp: integer_of_nat_eq_of_nat)
    apply (metis max_absorb2 of_nat_le_iff of_nat_of_integer)
    done

  have "0 \<in> {0..integer_of_nat n}"
    by (simp add: integer_of_nat_eq_of_nat)
  thus "{0..integer_of_nat n} \<noteq> {}"
    by blast

  show "finite {0..integer_of_nat n}"
    using bij_betw_finite[OF bij] by simp
qed

subsection \<open>Code printing and trusted code\<close>

text \<open>
  This is just a marker so that we can visually differentiate between a regular value
  and a value sampled from a distribution.
\<close>
definition SAMPLE :: "'a \<Rightarrow> 'a pmf" where "SAMPLE x = undefined"

notation (output) SAMPLE ("\<^bold>s\<^bold>a\<^bold>m\<^bold>p\<^bold>l\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>l\<^bold>u\<^bold>e\<^bold>: _" [0])


definition termify_pmf :: "('a :: term_of \<Rightarrow> term) \<Rightarrow> 'a pmf \<Rightarrow> term" where
  "termify_pmf f x = Code_Evaluation.term_of x"

lemma term_of_pmf_code [code]:
  "Code_Evaluation.term_of (x :: 'a :: term_of pmf) =
     Code_Evaluation.App
       (Code_Evaluation.Const (STR ''Sample_PMF.SAMPLE'') (Typerep.typerep TYPE('a \<Rightarrow> 'a pmf)))
       (termify_pmf Code_Evaluation.term_of x)"
  by (simp add: term_of_anything)

code_printing
  type_constructor pmf \<rightharpoonup> (SML) "_ Pmf.pmf" and (Eval) "_ Pmf.pmf"
  | constant "return_pmf" \<rightharpoonup> (SML) "Pmf.return" and (Eval) "Pmf.return"
  | constant "bind_pmf" \<rightharpoonup> (SML) "Pmf.bind" and (Eval) "Pmf.bind"
  | constant "map_pmf" \<rightharpoonup> (SML) "Pmf.map" and (Eval) "Pmf.map"
  | constant "integer_pmf" \<rightharpoonup> (SML) "Pmf.integer" and (Eval) "Pmf.integer"
  | constant "termify_pmf" \<rightharpoonup> (SML) "Pmf.termify" and (Eval) "Pmf.termify"

declare [[code abort: termify_pmf]]


code_printing
  code_module "PMF" \<rightharpoonup> (SML) \<open>

signature PMF = sig

type 'a pmf 
val return : 'a -> 'a pmf;
val bind : 'a pmf -> ('a -> 'b pmf) -> 'b pmf;
val map : ('a -> 'b) -> 'a pmf -> 'b pmf;
val integer : int -> int pmf;
val sample : 'a pmf -> 'a;
val termify : ('a -> 'term) -> 'a pmf -> 'term;

end

structure Pmf : PMF = struct

type 'a pmf = unit -> 'a;

fun return x = K x;

fun bind d f () = f (d ()) ();

fun integer n () = Random.random_range 0 n;

fun sample d = d ();

fun map f d () = f (d ());

fun termify term_of d = term_of (sample d)

end;

\<close>


subsection \<open>Estimation of mean and variance\<close>

class to_real =
  fixes to_real :: "'a \<Rightarrow> real"

instantiation real :: to_real
begin
definition "to_real x = (x :: real)"
instance ..
end

instantiation nat :: to_real
begin
definition "to_real x = (of_nat (x :: nat))"
instance ..
end

instantiation int :: to_real
begin
definition "to_real x = (of_int (x :: int))"
instance ..
end

instantiation rat :: to_real
begin
definition "to_real x = (of_rat (x :: rat))"
instance ..
end

instantiation bool :: to_real
begin
definition "to_real b = (if b then 1 else 0)"
instance ..
end

(* estimates mean and variance by sampling n time and computing the empiric mean/variance *)
definition estimate :: "nat \<Rightarrow> 'a :: to_real pmf \<Rightarrow> (real \<times> real) pmf"
  where "estimate n d = (
    map_pmf
      (\<lambda>xs. let m = sum_list (map to_real xs) / real n;
                s = sum_list (map (\<lambda>n. (to_real n - m)^2) xs) / real (n - 1)
            in (m, s))
      (replicate_pmf n d)
    )"


ML \<open>
signature PMF_ESTIMATE = sig
val estimate_cmd : xstring -> int -> string -> Toplevel.state -> unit
end

structure PMF_Estimate : PMF_ESTIMATE = struct

fun rat_of_term @{term "0 :: real"} = (0, 1)
  | rat_of_term @{term "1 :: real"} = (1, 1)
  | rat_of_term (@{term "uminus :: real \<Rightarrow> real"} $ t) = apfst (fn x => ~x) (rat_of_term t)
  | rat_of_term t =
      case t of
        Const (\<^const_name>\<open>numeral\<close>, _) $ _ => (snd (HOLogic.dest_number t), 1)
      | @{term "(/) :: real \<Rightarrow> real \<Rightarrow> real"} $ a $ b =>
          let
            val (a', b') = apply2 (snd o HOLogic.dest_number) (a, b)
          in
            if b' = 0 then raise TERM ("rat_of_term", [t])
            else if b' < 0 then (~a', ~b')
            else (a', b')
          end
      | _ => raise TERM ("rat_of_term", [t])

fun pretty_rat accuracy (a, b) =
  Real.fmt (StringCvt.FIX (SOME accuracy)) (Real.fromInt a / Real.fromInt b)

fun mk_pmfT T = Type (\<^type_name>\<open>pmf\<close>, [T])
fun mk_estimateC T = Const (\<^const_name>\<open>estimate\<close>, \<^typ>\<open>nat\<close> --> mk_pmfT T --> \<^typ>\<open>(real \<times> real) pmf\<close>)

fun dest_sample (Const (\<^const_name>\<open>SAMPLE\<close>, _) $ t) = t
  | dest_sample t = raise TERM ("dest_sample", [t])

fun estimate_cmd name n_samples raw_t state =
  let
    val accuracy = 4
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val T = fastype_of t
    val T =
      case T of
        Type (\<^type_name>\<open>pmf\<close>, [T]) => T
      | _ => raise TYPE ("estimate_cmd", [T], [])
    val _ = writeln ("Using " ^ Int.toString n_samples ^ " samples...")
    val (m, v) =
      mk_estimateC T $ HOLogic.mk_number @{typ nat} n_samples $ t
      |> Value_Command.value_select name ctxt
      |> dest_sample
      |> HOLogic.dest_prod
      |> apply2 rat_of_term
      |> apply2 (pretty_rat accuracy)
  in
    Pretty.string_of (Pretty.block [Pretty.str "Estimated mean: ", Pretty.str m]) ^ "\n" ^
    Pretty.string_of (Pretty.block [Pretty.str "Estimated variance: ", Pretty.str v])
    |> writeln
  end
    handle TYPE (_, [T], _) =>
      Output.error_message (Pretty.string_of (Pretty.block
        [Pretty.str "Expression must be of type ?'a pmf, but has type ",
          Syntax.pretty_typ (Toplevel.context_of state) T, Pretty.str "."]))
end

val opt_evaluator =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "";

val ten =
  Scan.one (fn t => Token.kind_of t = Token.Nat andalso Token.content_of t = "10")

(* parser for natural numbers, either literal or of form 10^k *)
val mynat =
  (ten |-- Args.$$$ "^" |-- Parse.nat) >> (fn k => Integer.pow k 10) || Parse.nat

val opt_samples =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Args.$$$ "samples" |-- Args.colon |-- mynat --| \<^keyword>\<open>)\<close>) 1000;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>estimate_pmf\<close> "estimate mean and variance of a PMF by sampling"
    (opt_evaluator -- opt_samples -- Parse.term
      >> (fn ((name, n_samples), t) => Toplevel.keep (PMF_Estimate.estimate_cmd name n_samples t)));
\<close>


subsection \<open>Tests\<close>

subsubsection \<open>Bernoulli distribution\<close>

value "replicate_pmf 20 (bernoulli_pmf (1 / 7))"
     
(* theoretically: mean 0.14286, variance 0.12245 *)
estimate_pmf (samples: 10^5) "bernoulli_pmf (1 / 7)"



subsubsection \<open>Binomial distribution\<close>

value "binomial_pmf 100 (1 / 3)"

(* theoretically: mean 33.333, variance 22.222 *)
estimate_pmf (samples: 10^4) "binomial_pmf 100 (1/3)"



subsubsection \<open>Geometric distribution\<close>

value "replicate_pmf 100 (geometric_pmf (1/10))"

(* theoretically: mean 6, variance 42 *)
estimate_pmf (samples: 10^5) "geometric_pmf (1 / 7)"



subsubsection \<open>Sum of two dice rolls\<close>

definition bar :: "nat pmf"
  where "bar = do {x \<leftarrow> pmf_of_set {1..6}; y \<leftarrow> pmf_of_set {1..6}; return_pmf (x + y)}"

value "replicate_pmf 20 bar"

(* theoretically: mean 7, variance 5.8333 *)
estimate_pmf (samples: 10^5) "bar"


subsubsection \<open>Random permutations\<close>

lemma fold_random_permutation_code [code]:
  "fold_random_permutation f s (set xs) =
     (if xs = [] then return_pmf s
      else 
        pmf_of_set (set xs) \<bind> (\<lambda>a. fold_random_permutation f (f a s) (set xs - {a})))"
  by (cases "xs = []") (auto)

value "fold_random_permutation (#) [] {1..200::int}"


subsubsection \<open>Additional examples from AFP\<close>

(* Fisher_Yates.Fisher_Yates *)

value "fisher_yates [1..<50]"

lemmas [code] = snd_sort_and_count_inversions[symmetric]

(* number of inversions of a random permutation. Theoretical mean: 612.5 *)
estimate_pmf (samples: 10^4) "map_pmf inversion_number (fisher_yates [1..50])"



(* Quick_Sort_Cost.Randomised_Quick_Sort *)

definition QS :: "nat \<Rightarrow> (nat list \<times> nat) pmf" where
  "QS n = (let R = Set.filter (\<lambda>(x,y). x \<le> y) ({1..n}\<times>{1..n}) in rquicksort R [1..<n+1])"

value "QS 10"

(* estimating mean/variance of quick sort cost *)
(* theoretical mean: 2(n + 1)H_n - 4n, i.e. for n = 10: 24.4373 *)
estimate_pmf (samples: 10^4) "map_pmf snd (QS 10)"
estimate_pmf (samples: 10^4) "rqs_cost 10"



(* Random_BSTs.Random_BSTs *)

lemma random_bst_code [code]:
 "random_bst (set xs) =
     (if xs = [] then
        return_pmf Leaf
      else do {
        x \<leftarrow> pmf_of_set (set xs);
        l \<leftarrow> random_bst (Set.filter (\<lambda>y. y < x) (set xs));
        r \<leftarrow> random_bst (Set.filter (\<lambda>y. y > x) (set xs));
        return_pmf (Node l x r)
     })"
  by (subst random_bst.simps) (auto simp: Set.filter_def)

value "random_bst {1..100::nat}"

(* height of random BST *)
(* theoretical mean: \<le> 16.433 *)
estimate_pmf "map_pmf height (random_bst {1..100::nat})"

(* internal path length of a random BST (is equidistributed to cost of randomised QuickSort *)
(* theoretical mean: 2(n + 1)H_n - 4n, i.e. for n = 100: 647.850 *)
estimate_pmf "map_pmf ipl (random_bst {1..100::nat})"
estimate_pmf "rqs_cost 100"

end