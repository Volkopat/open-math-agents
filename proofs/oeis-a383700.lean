import OMAStatements.S_oeis_a383700
import Mathlib

open OMA.S_oeis_a383700 Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a383700.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have c (p : ℤ[X]) (z : ℤ) (i : ℕ) : (p * (X + C z)).coeff (i+1) = p.coeff i + z * p.coeff (i+1) := by
    simp [mul_add, coeff_mul_C, mul_comm]
  have d (p : ℤ[X]) (z : ℤ) : (p * (X + C z)).coeff 0 = z * p.coeff 0 := by
    simp [mul_add, coeff_mul_C, mul_comm]
  simp only [a, Finset.prod_range_succ, c, d, Nat.reduceSubDiff, Nat.add_sub_cancel]
  push_cast
  ring
