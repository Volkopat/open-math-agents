import OMAReductions.R_mo_315770_R1

/-! The divisors of p^k are p^i for i ≤ k, so the sum is T = Σ_{i ≤ k} 1/(p^i + 1). By induction,
T + 1/((p-1) p^k) ≤ 1/2 + 1/(p-1), so T < 1/2 + 1/(p-1); also T ≥ 1/2. For p ≥ 3 this gives
1/2 ≤ T < 1. For p = 2 and k ≤ 1, T is 1/2 or 5/6. For p = 2 and k ≥ 2,
1 < 1/2 + 1/3 + 1/5 ≤ T < 3/2. In each case T is not an integer. -/

namespace OMA.Mo315770

open Finset

theorem tail (p : ℕ) (hp : 2 ≤ p) : ∀ k : ℕ,
    ∑ i ∈ range (k + 1), (1 : ℚ) / ((p : ℚ) ^ i + 1) + 1 / (((p : ℚ) - 1) * (p : ℚ) ^ k) ≤
      1 / 2 + 1 / ((p : ℚ) - 1) := by
  have hp1 : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℚ) - 1 ≠ 0 := by linarith
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hpk : (0 : ℚ) < (p : ℚ) ^ (k + 1) := by positivity
    have hpk0 : (p : ℚ) ^ k ≠ 0 := by positivity
    have hpk1 : (p : ℚ) ^ (k + 1) ≠ 0 := hpk.ne'
    have e : 1 / (((p : ℚ) - 1) * (p : ℚ) ^ k) =
        1 / (((p : ℚ) - 1) * (p : ℚ) ^ (k + 1)) + 1 / (p : ℚ) ^ (k + 1) := by
      field_simp
      ring
    have b : 1 / ((p : ℚ) ^ (k + 1) + 1) ≤ 1 / (p : ℚ) ^ (k + 1) :=
      one_div_le_one_div_of_le hpk (by linarith)
    linarith

theorem not_int_of_bounds (z : ℤ) (n : ℤ) (h1 : (n : ℚ) < z) (h2 : (z : ℚ) < n + 1) : False := by
  have a : n < z := by exact_mod_cast h1
  have b : z < n + 1 := by exact_mod_cast h2
  omega

end OMA.Mo315770

open Finset in
theorem OMA.solution : OMA.R_mo_315770_R1.H1 := by
  intro p k hp z hz
  have hp2 := hp.two_le
  rw [Nat.divisors_prime_pow hp, Finset.sum_map] at hz
  simp only [Function.Embedding.coeFn_mk, Nat.cast_pow] at hz
  have htail := OMA.Mo315770.tail p hp2 k
  have hp1 : (2 : ℚ) ≤ p := by exact_mod_cast hp2
  have hpos : 0 < 1 / (((p : ℚ) - 1) * (p : ℚ) ^ k) := by
    have : (0 : ℚ) < (p : ℚ) - 1 := by linarith
    positivity
  have hlow : (1 : ℚ) / 2 ≤ ∑ i ∈ range (k + 1), (1 : ℚ) / ((p : ℚ) ^ i + 1) := by
    have h := Finset.single_le_sum (f := fun i => (1 : ℚ) / ((p : ℚ) ^ i + 1))
      (fun i _ => by positivity) (Finset.mem_range.2 (Nat.succ_pos k))
    simp only [pow_zero] at h
    have e0 : (1 : ℚ) / (1 + 1) = 1 / 2 := by norm_num
    linarith
  rw [hz] at htail hlow
  rcases Nat.lt_or_ge 2 p with h3 | h3
  · have hp3 : (3 : ℚ) ≤ p := by exact_mod_cast h3
    have hq : 1 / ((p : ℚ) - 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    exact OMA.Mo315770.not_int_of_bounds z 0 (by push_cast; linarith) (by push_cast; linarith)
  · obtain rfl : p = 2 := by omega
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · norm_num [Finset.sum_range_succ] at hz
        exact OMA.Mo315770.not_int_of_bounds z 0 (by push_cast; linarith) (by push_cast; linarith)
      · norm_num [Finset.sum_range_succ] at hz
        exact OMA.Mo315770.not_int_of_bounds z 0 (by push_cast; linarith) (by push_cast; linarith)
    · have h3s : ∑ i ∈ range 3, (1 : ℚ) / ((2 : ℚ) ^ i + 1) ≤
          ∑ i ∈ range (k + 1), (1 : ℚ) / (((2 : ℕ) : ℚ) ^ i + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        intro i _ _
        positivity
      rw [hz] at h3s
      have e3 : ∑ i ∈ range 3, (1 : ℚ) / ((2 : ℚ) ^ i + 1) = 31 / 30 := by
        norm_num [Finset.sum_range_succ]
      have e4 : (1 : ℚ) / 2 + 1 / (((2 : ℕ) : ℚ) - 1) = 3 / 2 := by norm_num
      exact OMA.Mo315770.not_int_of_bounds z 1 (by push_cast; linarith) (by push_cast; linarith)
