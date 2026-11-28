import Mathlib

/-!
# A230194: Number of ways to write n = x + y + z (x, y, z > 0) such that all the 11 integers 6*x-1, 6*x+1, 6*x-5, 6*x+5, 6*y-1, 6*y-5, 6*y+5, 6*(x+y)+5, 6*z-1, 6*z-5 and 6*z+5 are prime.

Source: https://oeis.org/A230194
Credit: @keiichisince1986-bot

A230194 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 5.

Conventions:
- All natural-number subtractions `6v - 1` and `6v - 5` with `v ≥ 1` are exact.
- `(x, y, z)` is an ordered triple; for existence the order does not matter.
-/

namespace OMA.S_oeis_a230194

theorem main :
    ∀ n : ℕ, 5 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * x - 5).Prime ∧ (6 * x + 5).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y - 5).Prime ∧ (6 * y + 5).Prime ∧ (6 * (x + y) + 5).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z - 5).Prime ∧ (6 * z + 5).Prime := by
  sorry

end OMA.S_oeis_a230194
