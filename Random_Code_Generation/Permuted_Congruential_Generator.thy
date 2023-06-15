section \<open>A Pseudorandom Number Generator\<close>

text \<open>In this section we introduce a PRG, that can be used to generate random bits. It is an
implementation of O'Neil's Permuted congruential generator~\cite{oneill2014} 
(specifically PCG-XSH-RR). In empirical tests it ranks high~\cite{bhattacharjee2018, singh2020} 
while having a low implementation complexity.

This is for easy testing purposes only, the generated code can be run with any source of random
bits.\<close>

theory Permuted_Congruential_Generator
  imports 
    "HOL-Library.Word" 
    "HOL-Library.Stream" 
    "Coin_Space_2"
    "HOL-Library.Code_Lazy"
begin

text \<open>The following are default constants from the reference implementation~\cite{pcgbasic}.\<close>

definition pcg_mult :: "64 word"
  where "pcg_mult = 6364136223846793005"
definition pcg_increment :: "64 word"
  where "pcg_increment = 1442695040888963407"

fun pcg_rotr :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word"
  where "pcg_rotr x r = Bit_Operations.or (drop_bit r x) (push_bit (32-r) x)"

fun pcg_step :: "64 word \<Rightarrow> 64 word"
  where "pcg_step state = state * pcg_mult + pcg_increment"

text \<open>Based on \cite[Section~6.3.1]{oneill2014}:\<close>

fun pcg_get :: "64 word \<Rightarrow> 32 word"
  where "pcg_get state = 
    (let count = unsigned (drop_bit 59 state);
         x     = xor (drop_bit 18 state) state 
      in pcg_rotr (ucast (drop_bit 27 x)) count)" 

fun pcg_init :: "64 word \<Rightarrow> 64 word"
  where "pcg_init seed = pcg_step (seed + pcg_increment)"

definition to_bits :: "32 word \<Rightarrow> bool list"
  where "to_bits x = map (\<lambda>k. bit x k) [0..<32]"

primcorec cmap_iterate ::" ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> coin_stream"
  where
    "cmap_iterate m f s = Coin (m s) (cmap_iterate m f (f s))"

lemma cmap_iterate: "cmap_iterate m f s = to_coins (smap m (siterate f s))"
proof (rule coin_stream.coinduct
    [where R="(\<lambda>xs ys. (\<exists>x. xs = cmap_iterate m f x \<and> ys= to_coins (smap m (siterate f x))))"])
  show "\<exists>x. cmap_iterate m f s = cmap_iterate m f x \<and> 
        to_coins (smap m (siterate f s)) = to_coins (smap m (siterate f x))"
    by (intro exI[where x="s"] refl conjI) 
next
  fix xs ys
  assume "\<exists>x. xs = cmap_iterate m f x \<and> ys = to_coins (smap m (siterate f x))" 
  then obtain x where 0:"xs = cmap_iterate m f x" "ys = to_coins (smap m (siterate f x))"
    by auto

  have "chd xs = chd ys"
    unfolding 0 by (subst cmap_iterate.ctr, subst siterate.ctr) simp
  moreover have "ctl xs = cmap_iterate m f (f x)" 
    unfolding 0 by (subst cmap_iterate.ctr) simp
  moreover have "ctl ys = to_coins(smap m(siterate f (f x)))"
    unfolding 0 by (subst siterate.ctr) simp
  ultimately show 
    "chd xs = chd ys \<and> (\<exists>x. ctl xs=cmap_iterate m f x \<and> ctl ys = to_coins (smap m (siterate f x)))"
    by auto
qed

definition cflat_map_iterate ::  "('a \<Rightarrow> bool list) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> coin_stream"
  where 
    "cflat_map_iterate m f s = cmap_iterate (hd \<circ> fst) 
      (\<lambda>(r,s'). (if tl r = [] then (m s', f s') else (tl r, s'))) (m s, f s)"

lemma cflat_map_iterate_aux:
  fixes f :: "'a \<Rightarrow> 'b stream"
  assumes "\<And>x. (\<exists>n y. n \<noteq> [] \<and> f x = n@-f y \<and> g x = n@-g y)" 
  shows "f x = g x"
proof (rule stream.coinduct[where R="(\<lambda>xs ys. (\<exists>x n. xs = n @- (f x) \<and> ys = n @- (g x)))"])
  show "\<exists>y n. f x = n @-(f y) \<and> g x = n @- (g y)"
    by (intro exI[where x="x"] exI[where x="[]"]) auto
next
  fix xs ys :: "'b stream"
  assume "\<exists>x n. xs = n @- (f x) \<and> ys = n @- (g x)"
  hence "\<exists>x n. n \<noteq> [] \<and> xs = n @- (f x) \<and> ys = n @- (g x)"
    using assms by (metis shift.simps(1))
  then obtain x n where 0:"xs = n @- (f x)" "ys = n @- (g x)" "n \<noteq> []"
    by auto

  have "shd xs = shd ys"
    using 0 by simp
  moreover have "stl xs = tl n@-(f x)" "stl ys = tl n@-(g x)"
    using 0 by auto
  ultimately show "shd xs = shd ys \<and> (\<exists>x n. stl xs =  n@- (f x) \<and> stl ys =  n@- (g x))"
    by auto
qed

lemma cflat_map_iterate:
  assumes "\<And>x. m x \<noteq> []"
  shows "cflat_map_iterate m f s = to_coins (flat (smap m (siterate f s)))"
proof -
  let ?g = "(\<lambda>(r, s'). if tl r = [] then (m s', f s') else (tl r, s'))"

  have liter: "smap (hd \<circ> fst) (siterate ?g (bs, x)) = 
    bs @- (smap (hd \<circ> fst) (siterate ?g (m x, f x)))" if "bs \<noteq> []" for x bs
    using that
  proof (induction bs rule:list_nonempty_induct)
    case (single y)
    then show ?case by (subst siterate.ctr) simp
  next
    case (cons y ys)
    then show ?case by (subst siterate.ctr) (simp add:comp_def)
  qed
  have "smap(hd\<circ>fst) (siterate ?g (m x,f x)) = m x@- smap(hd\<circ>fst) (siterate ?g (m (f x), f (f x)))" 
    for x by (subst liter[OF assms]) auto
  moreover have "flat (smap m (siterate f x)) = m x @- flat (smap m (siterate f (f x)))" for x
    by (subst siterate.ctr) (simp add:flat_Stream[OF assms]) 

  ultimately have "\<exists>n y. n \<noteq> [] \<and> 
    smap (hd \<circ> fst) (siterate ?g (m x, f x)) = n @- smap (hd \<circ> fst) (siterate ?g (m y, f y)) \<and>
    flat (smap m (siterate f x)) = n @- flat (smap m (siterate f y))" for x
    by (intro exI[where x="m x"] exI[where x="f x"] conjI assms)

  hence "smap (hd \<circ> fst) (siterate ?g (m s', f s')) = flat (smap m (siterate f s'))" for s'
    by (rule cflat_map_iterate_aux[where f="(\<lambda>x. smap (hd \<circ> fst) (siterate ?g (m x, f x)))"])
  thus ?thesis
    unfolding cflat_map_iterate_def cmap_iterate by simp
qed


definition random_bits :: "64 word \<Rightarrow> bool stream"
  where "random_bits seed = flat (smap (to_bits \<circ> pcg_get) (siterate pcg_step (pcg_init seed)))"

definition random_coins 
  where "random_coins seed = cflat_map_iterate (to_bits \<circ> pcg_get) pcg_step (pcg_init seed)"

code_lazy_type coin_stream

value "chd (random_coins 0)"

lemma "random_coins x = to_coins (random_bits x)"
  unfolding random_coins_def random_bits_def 
  by (subst cflat_map_iterate) (simp_all add:to_bits_def)

end