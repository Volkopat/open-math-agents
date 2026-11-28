import OMAStatements.S_oeis_a097204
import Mathlib

-- Problem: A097204: Binomial transform of A033312.
-- Upstream: formal-conjectures statements/oeis-a097204.lean:0 (declaration OMA.S_oeis_a097204.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

namespace OMA.P_oeis_a097204

open OMA.S_oeis_a097204
open scoped BigOperators

/-- Sum of the descending factorials of `n`. -/
private def v (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.descFactorial k : ℤ)

private lemma a_eq (n : ℕ) : a n = v n - 2 ^ n := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (Nat.sum_range_choose n)
  push_cast at h
  simp only [a, v, mul_sub, mul_one, Finset.sum_sub_distrib, h,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_comm]

private lemma v_succ (n : ℕ) : v (n + 1) = ((n : ℤ) + 1) * v n + 1 := by
  rw [v, Finset.sum_range_succ']
  simp only [Nat.descFactorial_zero, Nat.succ_descFactorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, ← Finset.mul_sum, v]

end OMA.P_oeis_a097204

open OMA.P_oeis_a097204 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097204.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, Nat.add_sub_cancel, a_eq, v_succ,
    Nat.cast_add, Nat.cast_ofNat]
  ring
