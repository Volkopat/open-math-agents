import OMAStatements.S_oeis_a322921
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Sqrt

open OMA.S_oeis_a322921

namespace OMA.S_oeis_a322921.Proof

private def trialDivisors : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
   67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
   149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
   229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
private theorem trial_spec : ∀ p : Fin 283, p.val.Prime ↔ p.val ∈ trialDivisors := by
  decide +kernel

private def smallPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && trialDivisors.all (fun p => n == p || n % p != 0)

private theorem smallPrime_spec (n : ℕ) (h : n ≤ 80082) :
    smallPrime n = true ↔ n.Prime := by
  simp only [smallPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  constructor
  · rintro ⟨hn, hd⟩
    by_contra hnp
    have hm : Nat.minFac n < 283 := by
      have hs := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
      have hl : Nat.minFac n ≤ Nat.sqrt 80082 := Nat.le_sqrt'.mpr (hs.trans h)
      exact hl.trans_lt (Nat.sqrt_lt'.mpr (by decide : 80082 < 283 ^ 2))
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have hf := (trial_spec ⟨Nat.minFac n, hm⟩).mp hp
    have hc := hd _ hf
    have he : n ≠ Nat.minFac n := by
      intro e
      exact hnp ((Nat.prime_def_minFac).2 ⟨hn, e.symm⟩)
    exact (hc.resolve_left he) (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro p hpList
    have hPLt : p < 283 := by
      simp only [trialDivisors, List.mem_cons, List.not_mem_nil, or_false] at hpList
      omega
    have hPP := (trial_spec ⟨p, hPLt⟩).mpr hpList
    by_cases hEq : n = p
    · exact Or.inl hEq
    · exact Or.inr fun hMod =>
        hEq ((hp.dvd_iff_eq hPP.ne_one).mp (Nat.dvd_of_mod_eq_zero hMod))

private def indicator (n p : ℕ) : ℕ :=
  (smallPrime p && smallPrime (n - p)).toNat

private def block (n start len : ℕ) : ℕ := ∑ j ∈ Finset.range len, indicator n (start + j)

private theorem count_eq (n : ℕ) (hn : n ≤ 80082) :
    decompositions n = block n 0 (n / 2 + 1) := by
  simp only [decompositions, block, Nat.zero_add]
  have hcard : ((Finset.range (n / 2 + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)).card =
      ∑ p ∈ Finset.range (n / 2 + 1), if p.Prime ∧ (n - p).Prime then 1 else 0 := by
    exact (Finset.sum_boole (R := ℕ) _ _).symm
  rw [hcard]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_range.mp hp
  unfold indicator
  by_cases hPair : p.Prime ∧ (n - p).Prime
  · simp [hPair, (smallPrime_spec p (by omega)).mpr hPair.1,
      (smallPrime_spec (n - p) (by omega)).mpr hPair.2]
  · have hfalse : (smallPrime p && smallPrime (n - p)) = false := by
      rw [← Bool.not_eq_true, Bool.and_eq_true, smallPrime_spec p (by omega),
        smallPrime_spec (n - p) (by omega)]
      exact hPair
    simp [hPair, hfalse]

private theorem block_add (n start a b : ℕ) :
    block n start (a + b) = block n start a + block n (start + a) b := by
  simp only [block, Finset.sum_range_add, Nat.add_assoc]

private def countPow (n start : ℕ) : ℕ → ℕ
  | 0 => indicator n start
  | d + 1 => countPow n start d + countPow n (start + 2 ^ d) d

private theorem countPow_eq (n start d : ℕ) : countPow n start d = block n start (2 ^ d) := by
  induction d generalizing start with
  | zero => simp [countPow, block]
  | succ d ih =>
    rw [countPow, ih, ih, pow_succ, Nat.mul_two, block_add]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_0 : countPow 80080 0 12 = 130 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_4096 : countPow 80080 4096 12 = 102 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_8192 : countPow 80080 8192 12 = 107 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_12288 : countPow 80080 12288 12 = 103 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_16384 : countPow 80080 16384 12 = 95 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_20480 : countPow 80080 20480 12 = 103 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_24576 : countPow 80080 24576 12 = 98 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_28672 : countPow 80080 28672 12 = 93 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_32768 : countPow 80080 32768 12 = 101 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_36864 : countPow 80080 36864 11 = 49 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_38912 : countPow 80080 38912 10 = 24 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_39936 : countPow 80080 39936 6 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_40000 : countPow 80080 40000 5 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_40032 : countPow 80080 40032 3 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80080_40040 : countPow 80080 40040 0 = 0 := by
  decide +kernel

private theorem pairs_80080 : decompositions 80080 = 1006 := by
  rw [count_eq 80080 (by decide)]
  change block 80080 0 40041 = 1006
  rw [show block 80080 0 40041 =
    block 80080 0 4096 + block 80080 4096 35945 by
      simpa only [show 4096 + 35945 = 40041 by decide,
        show 0 + 4096 = 4096 by decide] using block_add 80080 0 4096 35945]
  rw [show block 80080 0 4096 = countPow 80080 0 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 0 12).symm,
    count_80080_0]
  rw [show block 80080 4096 35945 =
    block 80080 4096 4096 + block 80080 8192 31849 by
      simpa only [show 4096 + 31849 = 35945 by decide,
        show 4096 + 4096 = 8192 by decide] using block_add 80080 4096 4096 31849]
  rw [show block 80080 4096 4096 = countPow 80080 4096 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 4096 12).symm,
    count_80080_4096]
  rw [show block 80080 8192 31849 =
    block 80080 8192 4096 + block 80080 12288 27753 by
      simpa only [show 4096 + 27753 = 31849 by decide,
        show 8192 + 4096 = 12288 by decide] using block_add 80080 8192 4096 27753]
  rw [show block 80080 8192 4096 = countPow 80080 8192 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 8192 12).symm,
    count_80080_8192]
  rw [show block 80080 12288 27753 =
    block 80080 12288 4096 + block 80080 16384 23657 by
      simpa only [show 4096 + 23657 = 27753 by decide,
        show 12288 + 4096 = 16384 by decide] using block_add 80080 12288 4096 23657]
  rw [show block 80080 12288 4096 = countPow 80080 12288 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 12288 12).symm,
    count_80080_12288]
  rw [show block 80080 16384 23657 =
    block 80080 16384 4096 + block 80080 20480 19561 by
      simpa only [show 4096 + 19561 = 23657 by decide,
        show 16384 + 4096 = 20480 by decide] using block_add 80080 16384 4096 19561]
  rw [show block 80080 16384 4096 = countPow 80080 16384 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 16384 12).symm,
    count_80080_16384]
  rw [show block 80080 20480 19561 =
    block 80080 20480 4096 + block 80080 24576 15465 by
      simpa only [show 4096 + 15465 = 19561 by decide,
        show 20480 + 4096 = 24576 by decide] using block_add 80080 20480 4096 15465]
  rw [show block 80080 20480 4096 = countPow 80080 20480 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 20480 12).symm,
    count_80080_20480]
  rw [show block 80080 24576 15465 =
    block 80080 24576 4096 + block 80080 28672 11369 by
      simpa only [show 4096 + 11369 = 15465 by decide,
        show 24576 + 4096 = 28672 by decide] using block_add 80080 24576 4096 11369]
  rw [show block 80080 24576 4096 = countPow 80080 24576 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 24576 12).symm,
    count_80080_24576]
  rw [show block 80080 28672 11369 =
    block 80080 28672 4096 + block 80080 32768 7273 by
      simpa only [show 4096 + 7273 = 11369 by decide,
        show 28672 + 4096 = 32768 by decide] using block_add 80080 28672 4096 7273]
  rw [show block 80080 28672 4096 = countPow 80080 28672 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 28672 12).symm,
    count_80080_28672]
  rw [show block 80080 32768 7273 =
    block 80080 32768 4096 + block 80080 36864 3177 by
      simpa only [show 4096 + 3177 = 7273 by decide,
        show 32768 + 4096 = 36864 by decide] using block_add 80080 32768 4096 3177]
  rw [show block 80080 32768 4096 = countPow 80080 32768 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80080 32768 12).symm,
    count_80080_32768]
  rw [show block 80080 36864 3177 =
    block 80080 36864 2048 + block 80080 38912 1129 by
      simpa only [show 2048 + 1129 = 3177 by decide,
        show 36864 + 2048 = 38912 by decide] using block_add 80080 36864 2048 1129]
  rw [show block 80080 36864 2048 = countPow 80080 36864 11 by
    simpa only [show (2 : ℕ) ^ 11 = 2048 by decide] using (countPow_eq 80080 36864 11).symm,
    count_80080_36864]
  rw [show block 80080 38912 1129 =
    block 80080 38912 1024 + block 80080 39936 105 by
      simpa only [show 1024 + 105 = 1129 by decide,
        show 38912 + 1024 = 39936 by decide] using block_add 80080 38912 1024 105]
  rw [show block 80080 38912 1024 = countPow 80080 38912 10 by
    simpa only [show (2 : ℕ) ^ 10 = 1024 by decide] using (countPow_eq 80080 38912 10).symm,
    count_80080_38912]
  rw [show block 80080 39936 105 =
    block 80080 39936 64 + block 80080 40000 41 by
      simpa only [show 64 + 41 = 105 by decide,
        show 39936 + 64 = 40000 by decide] using block_add 80080 39936 64 41]
  rw [show block 80080 39936 64 = countPow 80080 39936 6 by
    simpa only [show (2 : ℕ) ^ 6 = 64 by decide] using (countPow_eq 80080 39936 6).symm,
    count_80080_39936]
  rw [show block 80080 40000 41 =
    block 80080 40000 32 + block 80080 40032 9 by
      simpa only [show 32 + 9 = 41 by decide,
        show 40000 + 32 = 40032 by decide] using block_add 80080 40000 32 9]
  rw [show block 80080 40000 32 = countPow 80080 40000 5 by
    simpa only [show (2 : ℕ) ^ 5 = 32 by decide] using (countPow_eq 80080 40000 5).symm,
    count_80080_40000]
  rw [show block 80080 40032 9 =
    block 80080 40032 8 + block 80080 40040 1 by
      simpa only [show 8 + 1 = 9 by decide,
        show 40032 + 8 = 40040 by decide] using block_add 80080 40032 8 1]
  rw [show block 80080 40032 8 = countPow 80080 40032 3 by
    simpa only [show (2 : ℕ) ^ 3 = 8 by decide] using (countPow_eq 80080 40032 3).symm,
    count_80080_40032]
  rw [show block 80080 40040 1 = countPow 80080 40040 0 by
    simpa only [show (2 : ℕ) ^ 0 = 1 by decide] using (countPow_eq 80080 40040 0).symm,
    count_80080_40040]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_0 : countPow 80082 0 12 = 128 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_4096 : countPow 80082 4096 12 = 101 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_8192 : countPow 80082 8192 12 = 104 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_12288 : countPow 80082 12288 12 = 103 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_16384 : countPow 80082 16384 12 = 101 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_20480 : countPow 80082 20480 12 = 100 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_24576 : countPow 80082 24576 12 = 95 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_28672 : countPow 80082 28672 12 = 98 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_32768 : countPow 80082 32768 12 = 89 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_36864 : countPow 80082 36864 11 = 58 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_38912 : countPow 80082 38912 10 = 24 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_39936 : countPow 80082 39936 6 = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_40000 : countPow 80082 40000 5 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_40032 : countPow 80082 40032 3 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
private theorem count_80082_40040 : countPow 80082 40040 1 = 0 := by
  decide +kernel

private theorem pairs_80082 : decompositions 80082 = 1005 := by
  rw [count_eq 80082 (by decide)]
  change block 80082 0 40042 = 1005
  rw [show block 80082 0 40042 =
    block 80082 0 4096 + block 80082 4096 35946 by
      simpa only [show 4096 + 35946 = 40042 by decide,
        show 0 + 4096 = 4096 by decide] using block_add 80082 0 4096 35946]
  rw [show block 80082 0 4096 = countPow 80082 0 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 0 12).symm,
    count_80082_0]
  rw [show block 80082 4096 35946 =
    block 80082 4096 4096 + block 80082 8192 31850 by
      simpa only [show 4096 + 31850 = 35946 by decide,
        show 4096 + 4096 = 8192 by decide] using block_add 80082 4096 4096 31850]
  rw [show block 80082 4096 4096 = countPow 80082 4096 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 4096 12).symm,
    count_80082_4096]
  rw [show block 80082 8192 31850 =
    block 80082 8192 4096 + block 80082 12288 27754 by
      simpa only [show 4096 + 27754 = 31850 by decide,
        show 8192 + 4096 = 12288 by decide] using block_add 80082 8192 4096 27754]
  rw [show block 80082 8192 4096 = countPow 80082 8192 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 8192 12).symm,
    count_80082_8192]
  rw [show block 80082 12288 27754 =
    block 80082 12288 4096 + block 80082 16384 23658 by
      simpa only [show 4096 + 23658 = 27754 by decide,
        show 12288 + 4096 = 16384 by decide] using block_add 80082 12288 4096 23658]
  rw [show block 80082 12288 4096 = countPow 80082 12288 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 12288 12).symm,
    count_80082_12288]
  rw [show block 80082 16384 23658 =
    block 80082 16384 4096 + block 80082 20480 19562 by
      simpa only [show 4096 + 19562 = 23658 by decide,
        show 16384 + 4096 = 20480 by decide] using block_add 80082 16384 4096 19562]
  rw [show block 80082 16384 4096 = countPow 80082 16384 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 16384 12).symm,
    count_80082_16384]
  rw [show block 80082 20480 19562 =
    block 80082 20480 4096 + block 80082 24576 15466 by
      simpa only [show 4096 + 15466 = 19562 by decide,
        show 20480 + 4096 = 24576 by decide] using block_add 80082 20480 4096 15466]
  rw [show block 80082 20480 4096 = countPow 80082 20480 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 20480 12).symm,
    count_80082_20480]
  rw [show block 80082 24576 15466 =
    block 80082 24576 4096 + block 80082 28672 11370 by
      simpa only [show 4096 + 11370 = 15466 by decide,
        show 24576 + 4096 = 28672 by decide] using block_add 80082 24576 4096 11370]
  rw [show block 80082 24576 4096 = countPow 80082 24576 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 24576 12).symm,
    count_80082_24576]
  rw [show block 80082 28672 11370 =
    block 80082 28672 4096 + block 80082 32768 7274 by
      simpa only [show 4096 + 7274 = 11370 by decide,
        show 28672 + 4096 = 32768 by decide] using block_add 80082 28672 4096 7274]
  rw [show block 80082 28672 4096 = countPow 80082 28672 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 28672 12).symm,
    count_80082_28672]
  rw [show block 80082 32768 7274 =
    block 80082 32768 4096 + block 80082 36864 3178 by
      simpa only [show 4096 + 3178 = 7274 by decide,
        show 32768 + 4096 = 36864 by decide] using block_add 80082 32768 4096 3178]
  rw [show block 80082 32768 4096 = countPow 80082 32768 12 by
    simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using (countPow_eq 80082 32768 12).symm,
    count_80082_32768]
  rw [show block 80082 36864 3178 =
    block 80082 36864 2048 + block 80082 38912 1130 by
      simpa only [show 2048 + 1130 = 3178 by decide,
        show 36864 + 2048 = 38912 by decide] using block_add 80082 36864 2048 1130]
  rw [show block 80082 36864 2048 = countPow 80082 36864 11 by
    simpa only [show (2 : ℕ) ^ 11 = 2048 by decide] using (countPow_eq 80082 36864 11).symm,
    count_80082_36864]
  rw [show block 80082 38912 1130 =
    block 80082 38912 1024 + block 80082 39936 106 by
      simpa only [show 1024 + 106 = 1130 by decide,
        show 38912 + 1024 = 39936 by decide] using block_add 80082 38912 1024 106]
  rw [show block 80082 38912 1024 = countPow 80082 38912 10 by
    simpa only [show (2 : ℕ) ^ 10 = 1024 by decide] using (countPow_eq 80082 38912 10).symm,
    count_80082_38912]
  rw [show block 80082 39936 106 =
    block 80082 39936 64 + block 80082 40000 42 by
      simpa only [show 64 + 42 = 106 by decide,
        show 39936 + 64 = 40000 by decide] using block_add 80082 39936 64 42]
  rw [show block 80082 39936 64 = countPow 80082 39936 6 by
    simpa only [show (2 : ℕ) ^ 6 = 64 by decide] using (countPow_eq 80082 39936 6).symm,
    count_80082_39936]
  rw [show block 80082 40000 42 =
    block 80082 40000 32 + block 80082 40032 10 by
      simpa only [show 32 + 10 = 42 by decide,
        show 40000 + 32 = 40032 by decide] using block_add 80082 40000 32 10]
  rw [show block 80082 40000 32 = countPow 80082 40000 5 by
    simpa only [show (2 : ℕ) ^ 5 = 32 by decide] using (countPow_eq 80082 40000 5).symm,
    count_80082_40000]
  rw [show block 80082 40032 10 =
    block 80082 40032 8 + block 80082 40040 2 by
      simpa only [show 8 + 2 = 10 by decide,
        show 40032 + 8 = 40040 by decide] using block_add 80082 40032 8 2]
  rw [show block 80082 40032 8 = countPow 80082 40032 3 by
    simpa only [show (2 : ℕ) ^ 3 = 8 by decide] using (countPow_eq 80082 40032 3).symm,
    count_80082_40032]
  rw [show block 80082 40040 2 = countPow 80082 40040 1 by
    simpa only [show (2 : ℕ) ^ 1 = 2 by decide] using (countPow_eq 80082 40040 1).symm,
    count_80082_40040]
end OMA.S_oeis_a322921.Proof

open OMA.S_oeis_a322921.Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a322921.main) := by
  intro h
  have hh := h 80078 (by decide) ⟨40039, rfl⟩ (2 : Fin 3) (1 : Fin 3) (by decide)
  change decompositions 80080 ≤ decompositions 80082 at hh
  rw [pairs_80080, pairs_80082] at hh
  omega
