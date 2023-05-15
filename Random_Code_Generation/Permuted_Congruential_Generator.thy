theory Permuted_Congruential_Generator
  imports 
    "HOL-Library.Word" 
    "HOL-Library.Stream" 
    "HOL-Library.Code_Lazy"
begin

definition pcg_mult :: "64 word"
  where "pcg_mult = 6364136223846793005"
definition pcg_increment :: "64 word"
  where "pcg_increment = 1442695040888963407"

fun pcg_rotr :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word"
  where "pcg_rotr x r = or (drop_bit r x) (push_bit (32-r) x)"

fun pcg_step :: "64 word \<Rightarrow> 64 word"
  where "pcg_step state = state * pcg_mult + pcg_increment"

fun pcg_get :: "64 word \<Rightarrow> 32 word"
  where "pcg_get state = 
    (let count = unsigned (drop_bit 59 state);
         x     = xor (drop_bit 18 state) state 
      in pcg_rotr (ucast (drop_bit 27 x)) count)" 

fun pcg_init :: "64 word \<Rightarrow> 64 word"
  where "pcg_init seed = pcg_step (seed + pcg_increment)"

definition to_bits :: "32 word \<Rightarrow> bool list"
  where "to_bits x = map (\<lambda>k. bit x k) [0..<32]"

definition random_bits :: "64 word \<Rightarrow> bool stream"
  where "random_bits seed = flat (smap (to_bits \<circ> pcg_get) (siterate pcg_step (pcg_init seed)))"

(*code_lazy_type stream*)

end