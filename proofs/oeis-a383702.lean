import OMAStatements.S_oeis_a383702
import Mathlib

-- Problem: A383702, the conjectured recurrence for the x^2-coefficients of prod (x + 4j + 3).
-- Upstream: formal-conjectures statements/oeis-a383702.lean (declaration OMA.S_oeis_a383702.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: multiplying by (x + c) gives w(n+1) = v(n) + c w(n), v(n+1) = u(n) + c v(n),
-- u(n+1) = c u(n) for the coefficients of x^2, x, 1; eliminating u and v gives the recurrence
-- (E - c(n+2))(E - c(n+1))(E - c(n)) w = 0, which expands to the stated one.

namespace OMA.P_oeis_a383702

open OMA.S_oeis_a383702 Polynomial

theorem row_succ (n : ℕ) : row (n + 1) = row n * (X + C (4 * (n : ℤ) + 3)) := by
  unfold row
  rw [Finset.prod_range_succ]

theorem coeff_step (p : Polynomial ℤ) (c : ℤ) (k : ℕ) :
    (p * (X + C c)).coeff (k + 1) = p.coeff k + c * p.coeff (k + 1) := by
  rw [mul_add, coeff_add, coeff_mul_X, coeff_mul_C]
  ring

theorem coeff_step0 (p : Polynomial ℤ) (c : ℤ) :
    (p * (X + C c)).coeff 0 = c * p.coeff 0 := by
  rw [mul_add, coeff_add, coeff_mul_C]
  simp
  ring

theorem main' : ∀ n : ℕ, 3 ≤ n →
    a n + 3 * (-4 * (n : ℤ) + 5) * a (n - 1) +
      (48 * (n : ℤ) ^ 2 - 168 * n + 151) * a (n - 2) -
      (4 * (n : ℤ) - 9) ^ 3 * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  unfold a
  -- w = coeff 2, v = coeff 1, u = coeff 0
  have w3 := coeff_step (row (m + 2)) (4 * ((m + 2 : ℕ) : ℤ) + 3) 1
  have w2 := coeff_step (row (m + 1)) (4 * ((m + 1 : ℕ) : ℤ) + 3) 1
  have w1 := coeff_step (row m) (4 * (m : ℤ) + 3) 1
  have v2 := coeff_step (row (m + 1)) (4 * ((m + 1 : ℕ) : ℤ) + 3) 0
  have v1 := coeff_step (row m) (4 * (m : ℤ) + 3) 0
  have u1 := coeff_step0 (row m) (4 * (m : ℤ) + 3)
  rw [← row_succ] at w3 w2 w1 v2 v1 u1
  push_cast at w3 w2 w1 v2 v1 u1 ⊢
  rw [w3, w2, v2, w1, v1, u1]
  ring

end OMA.P_oeis_a383702

theorem OMA.solution : type_of% @OMA.S_oeis_a383702.main := OMA.P_oeis_a383702.main'
