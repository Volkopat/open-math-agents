import OMAStatements.S_oeis_a210627
import Mathlib

open OMA.S_oeis_a210627


theorem alt_zero (n j : ℕ) (h : j < n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * (k : ℤ) ^ j = 0 := by
  have := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) h) 0
  rw [fwdDiff_iter_eq_sum_shift] at this
  simpa [zsmul_eq_mul] using this

theorem A038049_eq (n : ℕ) : (A038049 n : ℤ) =
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (k : ℤ) ^ (n - 1) := by
  unfold A038049
  push_cast
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm (by omega),
    show n - (n - k) = k by omega]

theorem OMA.solution : type_of% @OMA.S_oeis_a210627.main := by
  refine ⟨by decide, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  unfold r
  rw [A038049_eq]
  congr 1
  set g : ℕ → ℤ := fun k => (k : ℤ) ^ (m + 4 - 3) * ((m + 4).choose k : ℤ) *
    ((-1) ^ k * (9 * (k : ℤ) ^ 2 - 32 * k + 24) + (k : ℤ) ^ 2) with hg
  have hIcc : Finset.Icc 4 (m + 4) = Finset.Ico 4 (m + 4 + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  have hsplit := Finset.sum_range_add_sum_Ico g (show 4 ≤ m + 4 + 1 by omega)
  have h4 : ∑ k ∈ Finset.range 4, g k = 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hg]
    simp only [show m + 4 - 3 = m + 1 by omega]
    norm_num
  rw [h4, zero_add] at hsplit
  rw [hsplit]
  -- the alternating part vanishes
  have hsign : ∀ k ∈ Finset.range (m + 4 + 1), (-1 : ℤ) ^ k =
      (-1) ^ (m + 4) * (-1) ^ (m + 4 - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← pow_add]
    have : m + 4 + (m + 4 - k) = k + 2 * (m + 4 - k) := by omega
    rw [this, pow_add, pow_mul]; norm_num
  have hexp : m + 4 - 3 = m + 1 := by omega
  have hsum : ∑ k ∈ Finset.range (m + 4 + 1), g k =
      (-1) ^ (m + 4) * (9 * ∑ k ∈ Finset.range (m + 4 + 1),
          (-1 : ℤ) ^ (m + 4 - k) * ((m + 4).choose k : ℤ) * (k : ℤ) ^ (m + 3)
        - 32 * ∑ k ∈ Finset.range (m + 4 + 1),
          (-1 : ℤ) ^ (m + 4 - k) * ((m + 4).choose k : ℤ) * (k : ℤ) ^ (m + 2)
        + 24 * ∑ k ∈ Finset.range (m + 4 + 1),
          (-1 : ℤ) ^ (m + 4 - k) * ((m + 4).choose k : ℤ) * (k : ℤ) ^ (m + 1)) +
      ∑ k ∈ Finset.range (m + 4 + 1), ((m + 4).choose k : ℤ) * (k : ℤ) ^ (m + 4 - 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hg]
    simp only
    rw [hsign k hk, hexp, show m + 4 - 1 = m + 3 by omega]
    ring
  rw [hsum, alt_zero _ _ (by omega), alt_zero _ _ (by omega), alt_zero _ _ (by omega)]
  ring
