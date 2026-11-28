import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1
import Mathlib

-- Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H3:
-- Hypothesis H3 of reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1
-- Credit: @sanchan

/-!
# Direct proof of step H3 (single repeated odd prime z with e = 4 mod 8)

We prove the step unconditionally with explicit bound A = 9:
1. For z in {419, 463, 503, 607, 883, 1019, 1327}, the forced simple-prime chain starting from
   1 + z^4 | 1 + z^e reaches either two distinct sources for 3 or 5, or 3^2 dividing p + 1.
2. For z = 11, 1 + 11^4 = 2 * 7321 forces the chain 7321 -> {7, 523}, 523 -> 131, 131 -> {3, 11},
   consuming both 3 and 7. Graham's weighted bound (`master_gen`) combined with `mersenne_bound`,
   `fiber_bound` (u = 22), and `zleaf_bound` (i = 2) yields an upper bound < 1.89 against the
   lower bound >= 1.9979 for all a >= 10.
-/

namespace OMA.H3Proof

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main

private theorem hK_singleton {z e : ℕ} (hz : z.Prime) :
    ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := by
  intro c hc hcd
  rw [Finset.mem_singleton]
  exact (Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd)


private theorem p_53699 : Nat.Prime 53699 := by
  refine lucas_primality 53699 (2 : ZMod 53699) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 53699 - 1 = [2 ^ 1, 26849 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_71917 : Nat.Prime 71917 := by
  refine lucas_primality 71917 (2 : ZMod 71917) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 71917 - 1 = [2 ^ 2, 3 ^ 1, 13 ^ 1, 461 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_77969 : Nat.Prime 77969 := by
  refine lucas_primality 77969 (3 : ZMod 77969) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 77969 - 1 = [2 ^ 4, 11 ^ 1, 443 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_143833 : Nat.Prime 143833 := by
  refine lucas_primality 143833 (11 : ZMod 143833) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 143833 - 1 = [2 ^ 3, 3 ^ 1, 13 ^ 1, 461 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_145517 : Nat.Prime 145517 := by
  refine lucas_primality 145517 (2 : ZMod 145517) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 145517 - 1 = [2 ^ 2, 7 ^ 1, 5197 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_696617 : Nat.Prime 696617 := by
  refine lucas_primality 696617 (3 : ZMod 696617) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 696617 - 1 = [2 ^ 3, 19 ^ 1, 4583 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_1935371 : Nat.Prime 1935371 := by
  refine lucas_primality 1935371 (2 : ZMod 1935371) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1935371 - 1 = [2 ^ 1, 5 ^ 1, 103 ^ 1, 1879 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_11384189 : Nat.Prime 11384189 := by
  refine lucas_primality 11384189 (2 : ZMod 11384189) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 11384189 - 1 = [2 ^ 2, 53 ^ 1, 53699 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_53699 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_16718809 : Nat.Prime 16718809 := by
  refine lucas_primality 16718809 (22 : ZMod 16718809) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16718809 - 1 = [2 ^ 3, 3 ^ 1, 696617 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_696617 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_61931873 : Nat.Prime 61931873 := by
  refine lucas_primality 61931873 (3 : ZMod 61931873) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 61931873 - 1 = [2 ^ 5, 1935371 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_1935371 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_126667477 : Nat.Prime 126667477 := by
  refine lucas_primality 126667477 (2 : ZMod 126667477) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 126667477 - 1 = [2 ^ 2, 3 ^ 4, 13 ^ 1, 17 ^ 1, 29 ^ 1, 61 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_220899323 : Nat.Prime 220899323 := by
  refine lucas_primality 220899323 (2 : ZMod 220899323) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 220899323 - 1 = [2 ^ 1, 7 ^ 1, 29 ^ 1, 101 ^ 1, 5387 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_432599183 : Nat.Prime 432599183 := by
  refine lucas_primality 432599183 (5 : ZMod 432599183) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 432599183 - 1 = [2 ^ 1, 19 ^ 1, 11384189 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_11384189 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_506669909 : Nat.Prime 506669909 := by
  refine lucas_primality 506669909 (2 : ZMod 506669909) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 506669909 - 1 = [2 ^ 2, 126667477 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_126667477 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_727426751 : Nat.Prime 727426751 := by
  refine lucas_primality 727426751 (7 : ZMod 727426751) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 727426751 - 1 = [2 ^ 1, 5 ^ 3, 23 ^ 1, 73 ^ 1, 1733 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_3534389167 : Nat.Prime 3534389167 := by
  refine lucas_primality 3534389167 (6 : ZMod 3534389167) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3534389167 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 11 ^ 1, 61 ^ 1, 83 ^ 1, 1511 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_3852708091 : Nat.Prime 3852708091 := by
  refine lucas_primality 3852708091 (7 : ZMod 3852708091) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3852708091 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_6921586927 : Nat.Prime 6921586927 := by
  refine lucas_primality 6921586927 (5 : ZMod 6921586927) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6921586927 - 1 = [2 ^ 1, 3 ^ 2, 23 ^ 1, 16718809 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_16718809 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_7705416181 : Nat.Prime 7705416181 := by
  refine lucas_primality 7705416181 (24 : ZMod 7705416181) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7705416181 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_11488517041 : Nat.Prime 11488517041 := by
  refine lucas_primality 11488517041 (38 : ZMod 11488517041) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 11488517041 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 97 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_13843173853 : Nat.Prime 13843173853 := by
  refine lucas_primality 13843173853 (2 : ZMod 13843173853) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 13843173853 - 1 = [2 ^ 2, 3 ^ 2, 23 ^ 1, 16718809 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_16718809 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_15410832361 : Nat.Prime 15410832361 := by
  refine lucas_primality 15410832361 (13 : ZMod 15410832361) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 15410832361 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_16003388521 : Nat.Prime 16003388521 := by
  refine lucas_primality 16003388521 (11 : ZMod 16003388521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16003388521 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 1, 251 ^ 1, 25301 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_16969333201 : Nat.Prime 16969333201 := by
  refine lucas_primality 16969333201 (13 : ZMod 16969333201) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16969333201 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_22977034081 : Nat.Prime 22977034081 := by
  refine lucas_primality 22977034081 (31 : ZMod 22977034081) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 22977034081 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 97 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_32006777041 : Nat.Prime 32006777041 := by
  refine lucas_primality 32006777041 (11 : ZMod 32006777041) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 32006777041 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 7 ^ 1, 251 ^ 1, 25301 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_33938666401 : Nat.Prime 33938666401 := by
  refine lucas_primality 33938666401 (29 : ZMod 33938666401) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 33938666401 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_38506913083 : Nat.Prime 38506913083 := by
  refine lucas_primality 38506913083 (2 : ZMod 38506913083) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 38506913083 - 1 = [2 ^ 1, 3 ^ 3, 11 ^ 1, 41 ^ 1, 67 ^ 1, 23599 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_67877332801 : Nat.Prime 67877332801 := by
  refine lucas_primality 67877332801 (14 : ZMod 67877332801) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 67877332801 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_110745390823 : Nat.Prime 110745390823 := by
  refine lucas_primality 110745390823 (3 : ZMod 110745390823) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 110745390823 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 31 ^ 1, 1291 ^ 1, 41927 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_303957468361 : Nat.Prime 303957468361 := by
  refine lucas_primality 303957468361 (11 : ZMod 303957468361) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 303957468361 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 2, 13 ^ 1, 17 ^ 1, 77969 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_77969 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_539096783161 : Nat.Prime 539096783161 := by
  refine lucas_primality 539096783161 (7 : ZMod 539096783161) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 539096783161 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 509 ^ 1, 39937 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_1550435471521 : Nat.Prime 1550435471521 := by
  refine lucas_primality 1550435471521 (11 : ZMod 1550435471521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1550435471521 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 83 ^ 1, 293 ^ 1, 601 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem kill_419 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 419 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 419 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 419) (e := e) (by norm_num)) E
  have hD : 1 + 419 ^ 4 ∣ 1 + 419 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_15410832361 : 15410832361 ∈ P := S7 15410832361 p_15410832361 (by norm_num) (by simp) ((by norm_num : 15410832361 ∣ 1 + 419 ^ 4).trans hD)
  have hp_7705416181 : 7705416181 ∈ P := S1 7705416181 p_7705416181 (by norm_num) (by simp) 15410832361 hp_15410832361 (by norm_num)
  have hp_3852708091 : 3852708091 ∈ P := S1 3852708091 p_3852708091 (by norm_num) (by simp) 7705416181 hp_7705416181 (by norm_num)
  have hp_6619 : 6619 ∈ P := S1 6619 (by norm_num) (by norm_num) (by simp) 3852708091 hp_3852708091 (by norm_num)
  have hp_145517 : 145517 ∈ P := S1 145517 p_145517 (by norm_num) (by simp) 3852708091 hp_3852708091 (by norm_num)
  have hp_5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (by simp) 6619 hp_6619 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 145517 hp_145517 5 hp_5 (by norm_num) (by norm_num)
  omega

private theorem kill_463 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 463 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 463 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 463) (e := e) (by norm_num)) E
  have hD : 1 + 463 ^ 4 ∣ 1 + 463 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_22977034081 : 22977034081 ∈ P := S7 22977034081 p_22977034081 (by norm_num) (by simp) ((by norm_num : 22977034081 ∣ 1 + 463 ^ 4).trans hD)
  have hp_11488517041 : 11488517041 ∈ P := S1 11488517041 p_11488517041 (by norm_num) (by simp) 22977034081 hp_22977034081 (by norm_num)
  have hp_143833 : 143833 ∈ P := S1 143833 p_143833 (by norm_num) (by simp) 11488517041 hp_11488517041 (by norm_num)
  have hp_71917 : 71917 ∈ P := S1 71917 p_71917 (by norm_num) (by simp) 143833 hp_143833 (by norm_num)
  have hp_467 : 467 ∈ P := S1 467 (by norm_num) (by norm_num) (by simp) 71917 hp_71917 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by simp) 467 hp_467 (by norm_num)

private theorem kill_503 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 503 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 503 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 503) (e := e) (by norm_num)) E
  have hD : 1 + 503 ^ 4 ∣ 1 + 503 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_32006777041 : 32006777041 ∈ P := S7 32006777041 p_32006777041 (by norm_num) (by simp) ((by norm_num : 32006777041 ∣ 1 + 503 ^ 4).trans hD)
  have hp_16003388521 : 16003388521 ∈ P := S1 16003388521 p_16003388521 (by norm_num) (by simp) 32006777041 hp_32006777041 (by norm_num)
  have hp_11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (by simp) 16003388521 hp_16003388521 (by norm_num)
  have hp_727426751 : 727426751 ∈ P := S1 727426751 p_727426751 (by norm_num) (by simp) 16003388521 hp_16003388521 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 11 hp_11 727426751 hp_727426751 (by norm_num) (by norm_num)
  omega

private theorem kill_607 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 607 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 607 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 607) (e := e) (by norm_num)) E
  have hD : 1 + 607 ^ 4 ∣ 1 + 607 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_67877332801 : 67877332801 ∈ P := S7 67877332801 p_67877332801 (by norm_num) (by simp) ((by norm_num : 67877332801 ∣ 1 + 607 ^ 4).trans hD)
  have hp_33938666401 : 33938666401 ∈ P := S1 33938666401 p_33938666401 (by norm_num) (by simp) 67877332801 hp_67877332801 (by norm_num)
  have hp_16969333201 : 16969333201 ∈ P := S1 16969333201 p_16969333201 (by norm_num) (by simp) 33938666401 hp_33938666401 (by norm_num)
  have hp_137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (by simp) 16969333201 hp_16969333201 (by norm_num)
  have hp_61931873 : 61931873 ∈ P := S1 61931873 p_61931873 (by norm_num) (by simp) 16969333201 hp_16969333201 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 137 hp_137 61931873 hp_61931873 (by norm_num) (by norm_num)
  omega

private theorem kill_883 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 883 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 883 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 883) (e := e) (by norm_num)) E
  have hD : 1 + 883 ^ 4 ∣ 1 + 883 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_303957468361 : 303957468361 ∈ P := S7 303957468361 p_303957468361 (by norm_num) (by simp) ((by norm_num : 303957468361 ∣ 1 + 883 ^ 4).trans hD)
  have hp_43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (by simp) 303957468361 hp_303957468361 (by norm_num)
  have hp_3534389167 : 3534389167 ∈ P := S1 3534389167 p_3534389167 (by norm_num) (by simp) 303957468361 hp_303957468361 (by norm_num)
  have hp_11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (by simp) 43 hp_43 (by norm_num)
  have hp_220899323 : 220899323 ∈ P := S1 220899323 p_220899323 (by norm_num) (by simp) 3534389167 hp_3534389167 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 11 hp_11 220899323 hp_220899323 (by norm_num) (by norm_num)
  omega

private theorem kill_1019 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 1019 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1019 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 1019) (e := e) (by norm_num)) E
  have hD : 1 + 1019 ^ 4 ∣ 1 + 1019 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_539096783161 : 539096783161 ∈ P := S7 539096783161 p_539096783161 (by norm_num) (by simp) ((by norm_num : 539096783161 ∣ 1 + 1019 ^ 4).trans hD)
  have hp_38506913083 : 38506913083 ∈ P := S1 38506913083 p_38506913083 (by norm_num) (by simp) 539096783161 hp_539096783161 (by norm_num)
  have hp_19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (by simp) 38506913083 hp_38506913083 (by norm_num)
  have hp_506669909 : 506669909 ∈ P := S1 506669909 p_506669909 (by norm_num) (by simp) 38506913083 hp_38506913083 (by norm_num)
  have hEq := S3 5 (by norm_num) (by norm_num) (by simp) 19 hp_19 506669909 hp_506669909 (by norm_num) (by norm_num)
  omega

private theorem kill_1327 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 1327 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1327 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 1327) (e := e) (by norm_num)) E
  have hD : 1 + 1327 ^ 4 ∣ 1 + 1327 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_1550435471521 : 1550435471521 ∈ P := S7 1550435471521 p_1550435471521 (by norm_num) (by simp) ((by norm_num : 1550435471521 ∣ 1 + 1327 ^ 4).trans hD)
  have hp_110745390823 : 110745390823 ∈ P := S1 110745390823 p_110745390823 (by norm_num) (by simp) 1550435471521 hp_1550435471521 (by norm_num)
  have hp_13843173853 : 13843173853 ∈ P := S1 13843173853 p_13843173853 (by norm_num) (by simp) 110745390823 hp_110745390823 (by norm_num)
  have hp_6921586927 : 6921586927 ∈ P := S1 6921586927 p_6921586927 (by norm_num) (by simp) 13843173853 hp_13843173853 (by norm_num)
  have hp_432599183 : 432599183 ∈ P := S1 432599183 p_432599183 (by norm_num) (by simp) 6921586927 hp_6921586927 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by simp) 432599183 hp_432599183 (by norm_num)

private def beta11 (p : ℕ) : ℚ :=
  if p = 7321 then (7322 : ℚ) / 7321
  else if p = 523 then ((524 : ℚ) / 523) * ((7322 : ℚ) / 7321)
  else if p = 131 then ((132 : ℚ) / 131) * ((524 : ℚ) / 523) * ((7322 : ℚ) / 7321)
  else if p = 3 then ((4 : ℚ) / 3) * ((132 : ℚ) / 131) * ((524 : ℚ) / 523) * ((7322 : ℚ) / 7321)
  else if p = 7 then ((8 : ℚ) / 7) * ((7322 : ℚ) / 7321)
  else ((p : ℚ) + 1) / ((p : ℚ) - 1)

private theorem beta11_bounds {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ beta11 p ∧ beta11 p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  unfold beta11
  split_ifs with h1 h2 h3 h4 h5
  · subst h1; norm_num
  · subst h2; norm_num
  · subst h3; norm_num
  · subst h4; norm_num
  · subst h5; norm_num
  · exact ⟨one_add_le_B hp, le_refl _⟩

private theorem beta11_pos {p : ℕ} (hp : 2 ≤ p) : 0 < beta11 p := by
  have h1 := (beta11_bounds hp).1
  have h2 : (0 : ℚ) < 1 + 1 / (p : ℚ) := by positivity
  linarith

private theorem kill_11 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) (hm : 10 ≤ m) : False := by
  obtain ⟨S1, -, S3, -, -, -, S7, S8⟩ :=
    facts hP (hK_singleton (z := 11) (e := e) (by norm_num)) E
  have hD : 1 + 11 ^ 4 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul he
  have h7321d : 7321 ∣ 1 + 11 ^ e := (by norm_num : 7321 ∣ 1 + 11 ^ 4).trans hD
  have hp_7321 : 7321 ∈ P := S7 7321 (by norm_num) (by norm_num) (by simp) h7321d
  have hp_523 : 523 ∈ P := S1 523 (by norm_num) (by norm_num) (by simp) 7321 hp_7321 (by norm_num)
  have hp_131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (by simp) 523 hp_523 (by norm_num)
  have hp_3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 131 hp_131 (by norm_num)
  have hp_7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 7321 hp_7321 (by norm_num)
  have hK0 : 0 < 11 ^ e := pow_pos (by norm_num) e
  obtain ⟨L, hLP, hLN, hMain⟩ := master_gen hP
    (hK_singleton (z := 11) (e := e) (by norm_num)) hK0 E beta11
    (fun p hp => beta11_bounds (hP p hp).1.two_le)
    (fun p hp c hc hcd _ hne => by
      have hcases : c = 7321 ∨ c = 523 ∨ c = 131 ∨ c = 3 ∨ c = 7 := by
        by_contra hnot
        push Not at hnot
        obtain ⟨h1, h2, h3, h4, h5⟩ := hnot
        exact hne (by simp [beta11, h1, h2, h3, h4, h5])
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · exact absurd hcd (S8 7321 (by norm_num) (by norm_num) (by simp) h7321d p hp)
      · have hpeq : p = 7321 :=
          S3 523 (by norm_num) (by norm_num) (by simp) p hp 7321 hp_7321 hcd (by norm_num)
        subst hpeq
        norm_num [beta11]
      · have hpeq : p = 523 :=
          S3 131 (by norm_num) (by norm_num) (by simp) p hp 523 hp_523 hcd (by norm_num)
        subst hpeq
        norm_num [beta11]
      · have hpeq : p = 131 :=
          S3 3 (by norm_num) (by norm_num) (by simp) p hp 131 hp_131 hcd (by norm_num)
        subst hpeq
        norm_num [beta11]
      · have hpeq : p = 7321 :=
          S3 7 (by norm_num) (by norm_num) (by simp) p hp 7321 hp_7321 hcd (by norm_num)
        subst hpeq
        norm_num [beta11])
  have hLdecomp : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ q + 1 = 2 ^ k * 11 ^ j := by
    intro q hq
    have hqP := hLP hq
    have hqp := (hP q hqP).1
    have hq2 := (hP q hqP).2
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (z := 11) (by omega)
      (fun c hc hc2 hcd => Finset.mem_singleton.mp (hLN q hq c hc hc2 hcd))
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk_eq : k = 0 := by omega
      subst hk_eq
      have hodd_q : q % 2 = 1 := by
        rcases hqp.eq_two_or_odd with h | h
        · exact absurd h hq2
        · exact h
      have heven : 2 ∣ q + 1 := by omega
      rw [hkj, pow_zero, one_mul] at heven
      have h211 : 2 ∣ 11 := Nat.prime_two.dvd_of_dvd_pow heven
      norm_num at h211
    exact ⟨k, j, hk1, hkj⟩
  let L0 := L.filter (fun q => ¬ 11 ∣ q + 1)
  let L12 := L.filter (fun q => 11 ∣ q + 1)
  let L1 := L12.filter (fun q => ¬ 11 ^ 2 ∣ q + 1)
  let L2 := L12.filter (fun q => 11 ^ 2 ∣ q + 1)
  have hsplit1 : ∏ q ∈ L, beta11 q = (∏ q ∈ L12, beta11 q) * (∏ q ∈ L0, beta11 q) :=
    (Finset.prod_filter_mul_prod_filter_not L (fun q => 11 ∣ q + 1) beta11).symm
  have hsplit2 : ∏ q ∈ L12, beta11 q = (∏ q ∈ L2, beta11 q) * (∏ q ∈ L1, beta11 q) :=
    (Finset.prod_filter_mul_prod_filter_not L12 (fun q => 11 ^ 2 ∣ q + 1) beta11).symm
  have hL0_bound : ∏ q ∈ L0, beta11 q ≤
      (beta11 3 * beta11 7 * beta11 31 * beta11 127) * (2048 / 2047) := by
    apply mersenne_bound beta11 L0
    · intro q hq
      exact (hP q (hLP (Finset.mem_filter.mp hq).1)).1
    · intro q hq
      obtain ⟨hqL, hndvd⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, j, -, hkj⟩ := hLdecomp q hqL
      have hj0 : j = 0 := by
        by_contra hj
        have h11 : 11 ∣ 11 ^ j := dvd_pow_self 11 hj
        exact hndvd (hkj ▸ h11.mul_left _)
      subst hj0
      exact ⟨k, by simpa using hkj⟩
    · intro q hq
      have h2 := (hP q (hLP (Finset.mem_filter.mp hq).1)).1.two_le
      exact ⟨beta11_pos h2, (beta11_bounds h2).2⟩
    · norm_num [beta11]
  have hL1_bound : ∏ q ∈ L1, beta11 q ≤ (22 : ℚ) / (22 - 2) := by
    have hstep1 : ∏ q ∈ L1, beta11 q ≤ ∏ q ∈ L1, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod
        (fun q hq => (beta11_pos (hP q (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)).1.two_le).le)
        (fun q hq => (beta11_bounds (hP q (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)).1.two_le).2)
    refine hstep1.trans (fiber_bound (u := 22) (by norm_num) L1 ?_)
    intro q hq
    obtain ⟨hq12, hndvd2⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqL, hdvd1⟩ := Finset.mem_filter.mp hq12
    obtain ⟨k, j, hk1, hkj⟩ := hLdecomp q hqL
    have hj1 : j = 1 := by
      have hj_pos : 1 ≤ j := by
        by_contra hj0
        have : j = 0 := by omega
        subst this
        rw [hkj, pow_zero, mul_one] at hdvd1
        have h112 : 11 ∣ 2 := (by norm_num : Nat.Prime 11).dvd_of_dvd_pow hdvd1
        norm_num at h112
      have hj_lt : j < 2 := by
        by_contra hj2
        have h11sq : 11 ^ 2 ∣ 11 ^ j := Nat.pow_dvd_pow 11 (by omega)
        exact hndvd2 (hkj ▸ h11sq.mul_left _)
      omega
    subst hj1
    have hk2 : 2 ≤ k := by
      by_contra hklt
      have hk_eq : k = 1 := by omega
      subst hk_eq
      have hq21 : q = 21 := by omega
      have hqp := (hP q (hLP hqL)).1
      rw [hq21] at hqp
      norm_num at hqp
    refine ⟨k - 1, by omega, ?_⟩
    rw [hkj, pow_one]
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    rw [hpow]
    ring
  have hL2_bound : ∏ q ∈ L2, beta11 q ≤ ((11 : ℚ) ^ 2) / ((11 : ℚ) ^ 2 - 3) := by
    have hstep1 : ∏ q ∈ L2, beta11 q ≤ ∏ q ∈ L2, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod
        (fun q hq => (beta11_pos (hP q (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)).1.two_le).le)
        (fun q hq => (beta11_bounds (hP q (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)).1.two_le).2)
    refine hstep1.trans (zleaf_bound (z := 11) (by norm_num) 2 (by norm_num) L2 ?_)
    intro q hq
    obtain ⟨hq12, hdvd2⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqL, -⟩ := Finset.mem_filter.mp hq12
    obtain ⟨k, j, hk1, hkj⟩ := hLdecomp q hqL
    have hj2 : 2 ≤ j := by
      by_contra hjlt
      have hcop : Nat.Coprime (11 ^ 2) (2 ^ k) :=
        ((by norm_num : Nat.Coprime 11 2).pow_left 2).pow_right k
      rw [hkj] at hdvd2
      have h11j : 11 ^ 2 ∣ 11 ^ j := hcop.dvd_of_dvd_mul_left hdvd2
      have hle := Nat.le_of_dvd (pow_pos (by norm_num) j) h11j
      interval_cases j <;> norm_num at hle
    exact ⟨k, j, hk1, hj2, hkj⟩
  have hL0_nn : 0 ≤ ∏ q ∈ L0, beta11 q :=
    Finset.prod_nonneg fun q hq => (beta11_pos (hP q (hLP (Finset.mem_filter.mp hq).1)).1.two_le).le
  have hL1_nn : 0 ≤ ∏ q ∈ L1, beta11 q :=
    Finset.prod_nonneg fun q hq => (beta11_pos (hP q (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)).1.two_le).le
  have hL2_nn : 0 ≤ ∏ q ∈ L2, beta11 q :=
    Finset.prod_nonneg fun q hq => (beta11_pos (hP q (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)).1.two_le).le
  have hL12_bound : ∏ q ∈ L12, beta11 q ≤ (((11 : ℚ) ^ 2) / ((11 : ℚ) ^ 2 - 3)) * ((22 : ℚ) / (22 - 2)) := by
    rw [hsplit2]
    exact mul_le_mul hL2_bound hL1_bound hL1_nn (by norm_num)
  have hL12_nn : 0 ≤ ∏ q ∈ L12, beta11 q := by rw [hsplit2]; exact mul_nonneg hL2_nn hL1_nn
  have hL_bound : ∏ q ∈ L, beta11 q ≤
      (((11 : ℚ) ^ 2) / ((11 : ℚ) ^ 2 - 3)) * ((22 : ℚ) / (22 - 2)) *
        ((beta11 3 * beta11 7 * beta11 31 * beta11 127) * (2048 / 2047)) := by
    rw [hsplit1]
    exact mul_le_mul hL12_bound hL0_bound hL0_nn (by norm_num)
  have hL_num : ∏ q ∈ L, beta11 q ≤ (19 : ℚ) / 10 :=
    hL_bound.trans (by norm_num [beta11])
  have hm_pow : (1024 : ℚ) ≤ (2 : ℚ) ^ m := by
    have : (2 : ℕ) ^ 10 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact_mod_cast this
  have h2m : 1 + 1 / (2 : ℚ) ^ m ≤ 1 + 1 / 1024 := by
    have hinv : 1 / (2 : ℚ) ^ m ≤ 1 / 1024 := one_div_le_one_div_of_le (by norm_num) hm_pow
    linarith
  have he4 : 4 ≤ e := by omega
  have he_pow : (11 : ℚ) ^ 4 ≤ (11 : ℚ) ^ e := by
    have : (11 : ℕ) ^ 4 ≤ 11 ^ e := Nat.pow_le_pow_right (by norm_num) he4
    exact_mod_cast this
  have h11e : ((1 + 11 ^ e : ℕ) : ℚ) / ((11 ^ e : ℕ) : ℚ) ≤ 1 + 1 / (11 : ℚ) ^ 4 := by
    push_cast
    have hpos : (0 : ℚ) < (11 : ℚ) ^ e := by positivity
    rw [add_div, div_self hpos.ne', add_comm]
    have hinv : 1 / (11 : ℚ) ^ e ≤ 1 / (11 : ℚ) ^ 4 := one_div_le_one_div_of_le (by norm_num) he_pow
    linarith
  have hprod_nn : 0 ≤ ∏ q ∈ L, beta11 q := by rw [hsplit1]; exact mul_nonneg hL12_nn hL0_nn
  have hfac1 : (1 + 1 / (2 : ℚ) ^ m) * (((1 + 11 ^ e : ℕ) : ℚ) / ((11 ^ e : ℕ) : ℚ)) ≤
      (1 + 1 / 1024) * (1 + 1 / (11 : ℚ) ^ 4) :=
    mul_le_mul h2m h11e (by positivity) (by norm_num)
  have htot : (1 + 1 / (2 : ℚ) ^ m) * (((1 + 11 ^ e : ℕ) : ℚ) / ((11 ^ e : ℕ) : ℚ)) *
      ∏ q ∈ L, beta11 q ≤ (1 + 1 / 1024) * (1 + 1 / (11 : ℚ) ^ 4) * ((19 : ℚ) / 10) :=
    mul_le_mul hfac1 hL_num hprod_nn (by norm_num)
  have hnum : (1 + 1 / (1024 : ℚ)) * (1 + 1 / (11 : ℚ) ^ 4) * ((19 : ℚ) / 10) < 2 := by norm_num
  linarith

end OMA.H3Proof

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1.H3 := by
  refine ⟨9, fun n h z hz hS he hzmem _ _ _ _ _ _ _ _ _ _ => ?_⟩
  obtain ⟨hzn, hs⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := by
    intro h2
    subst h2
    simp at hzmem
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
  rcases hzmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_contra hgt
    exact OMA.H3Proof.kill_11 hP E he (by omega)
  · exact (OMA.H3Proof.kill_419 hP E he).elim
  · exact (OMA.H3Proof.kill_463 hP E he).elim
  · exact (OMA.H3Proof.kill_503 hP E he).elim
  · exact (OMA.H3Proof.kill_607 hP E he).elim
  · exact (OMA.H3Proof.kill_883 hP E he).elim
  · exact (OMA.H3Proof.kill_1019 hP E he).elim
  · exact (OMA.H3Proof.kill_1327 hP E he).elim
