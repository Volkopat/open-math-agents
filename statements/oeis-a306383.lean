import Mathlib

/-!
# A306383: Number of ways to write n as x*(2x+1) + y*(2y+1) + z*(2z+1), where x,y,z are nonnegative integers with x <= y <= z.

Source: https://oeis.org/A306383
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) > 0 for any integer n > 138158.
2. Any integer n > 146858 can be written as the sum of three hexagonal numbers (A000384).
3. Any integer n > 33066 can be written as the sum of three pentagonal numbers (A000326).

Formalization notes:
* Second hexagonal numbers k(2k+1), hexagonal numbers k(2k-1) and pentagonal numbers k(3k-1)/2, all
  with k ≥ 0. a(n) > 0 is the existence of a representation (the order x ≤ y ≤ z does not matter).
* Controls (computed): below 400000 the largest non-represented numbers are 138158, 146858 and 33066
  respectively, matching the thresholds.
-/

namespace OMA.S_oeis_a306383



/-- The conjectures of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 138158 < n → ∃ x y z : ℕ, x * (2 * x + 1) + y * (2 * y + 1) + z * (2 * z + 1) = n) ∧
      (∀ n : ℕ, 146858 < n → ∃ x y z : ℕ, x * (2 * x - 1) + y * (2 * y - 1) + z * (2 * z - 1) = n) ∧
      ∀ n : ℕ, 33066 < n → ∃ x y z : ℕ,
        x * (3 * x - 1) / 2 + y * (3 * y - 1) / 2 + z * (3 * z - 1) / 2 = n := by
  sorry

end OMA.S_oeis_a306383
