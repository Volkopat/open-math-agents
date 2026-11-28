import Mathlib

/-!
# OEIS A204238

Source: https://oeis.org/A204238 and https://oeis.org/A204237.
The entry uses positive row and column indices and sequence offset 1.
Colin Barker's two conjectures are the recurrence (for n >= 3, so that
both earlier indices are defined) and the ordinary generating function
with zero constant term. Sela Fried proved both in 2026.
-/

namespace OMA.S_oeis_a204238

open Matrix PowerSeries
open scoped Matrix BigOperators

/-- The leading square submatrix of A204237, with one added to each Fin index. -/
def principalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  max (3 * ((i.val : ℚ) + 1) - ((j.val : ℚ) + 1))
      (3 * ((j.val : ℚ) + 1) - ((i.val : ℚ) + 1))

/-- A204238 at each positive index. -/
def a (n : ℕ) : ℚ := (principalMatrix n).det

/-- The ordinary generating function starts with the coefficient of X. -/
noncomputable def generatingFunction : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else a n

/-- Both of Colin Barker's A204238 conjectures. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = -8 * a (n - 1) - 16 * a (n - 2)) ∧
    generatingFunction = -(X * (X - C 2)) * ((C 4 * X + 1) ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a204238
