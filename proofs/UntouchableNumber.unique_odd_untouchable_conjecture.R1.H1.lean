import OMAReductions.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1
-- Credit: @kofls (shorter proof)
theorem OMA.solution : OMA.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1.H1 := by
  rintro ⟨n, h⟩
  by_cases hn : n ≤ 16
  · interval_cases n <;> revert h <;> decide
  by_cases hp : n.Prime
  · rw [hp.sum_properDivisors] at h; omega
  have s := Nat.minFac_sq_le_self (by omega) hp
  have e := Nat.div_mul_cancel n.minFac_dvd
  have t := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
  have : n.minFac ≤ n / n.minFac := by nlinarith
  have q : 5 ≤ n / n.minFac := by nlinarith
  have := Finset.sum_le_sum_of_subset (f := id) (show {1, n / n.minFac} ⊆ n.properDivisors by
    simp [Finset.insert_subset_iff, Nat.mem_properDivisors, Nat.div_dvd_of_dvd n.minFac_dvd,
      Nat.div_lt_self (by omega : 0 < n) t]; omega)
  rw [Finset.sum_pair (by omega)] at this
  simp at this; omega
