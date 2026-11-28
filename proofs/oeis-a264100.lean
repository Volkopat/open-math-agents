import OMAStatements.S_oeis_a264100
import Mathlib.Algebra.BigOperators.Intervals

open OMA.S_oeis_a264100 Finset

-- The first difference is endingWeight; its jump keeps exactly the divisors.
theorem OMA.solution : type_of% @OMA.S_oeis_a264100.main := by
  intro n
  simp only [totalLength, sum_range_succ, Nat.add_sub_cancel_left, endingWeight]
  have h : (∑ k ∈ Icc 1 (n + 1), (k + 1) * (n / k)) =
      ∑ k ∈ Icc 1 n, (k + 1) * (n / k) := by
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    simp
  rw [← h, Nat.add_sub_add_left, ← sum_tsub_distrib]
  · simp_rw [Nat.succ_div, mul_add, Nat.add_sub_cancel_left,
      mul_ite, mul_one, mul_zero, ← sum_filter]
    have hf : (Icc 1 (n + 1)).filter (· ∣ n + 1) = (n + 1).divisors := by
      ext k
      simp [Nat.divisors]
    rw [hf, sum_add_distrib]
    simp
  · intro k hk
    exact Nat.mul_le_mul_left _ (Nat.div_le_div_right (by omega))
