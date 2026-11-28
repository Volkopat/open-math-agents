import OMAStatements.S_oeis_a214615
import Mathlib

-- Problem: A214615, the recurrence a(n) = a(n-1) - (n-1)^2 a(n-2) for the values at 1 of the
-- polynomials M(0) = 1, M(1) = X, M(k+2) = X M(k+1) - (k+1)^2 M(k).
-- Upstream: formal-conjectures statements/oeis-a214615.lean (declaration OMA.S_oeis_a214615.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated recurrence holds).
-- Proof: evaluate the defining polynomial recursion at X = 1.

namespace OMA.P_oeis_a214615

open OMA.S_oeis_a214615 Polynomial

theorem main' : ∀ n : ℕ, 2 ≤ n →
    a n - a (n - 1) + ((n : ℤ) - 1) ^ 2 * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  unfold a
  rw [meixner]
  simp only [eval_sub, eval_mul, eval_X, eval_C, one_mul]
  push_cast
  ring

end OMA.P_oeis_a214615

theorem OMA.solution : type_of% @OMA.S_oeis_a214615.main := OMA.P_oeis_a214615.main'
