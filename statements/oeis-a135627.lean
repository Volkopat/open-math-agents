import Mathlib

/-!
# OEIS A135627: Perfect numbers minus 1.

Source: https://oeis.org/A135627
Credit: @unserus

OEIS (J. Lowell): "Conjecture: every odd prime is a factor of at least one number in this sequence."
The terms are `m - 1` for `m` a perfect number (`Nat.Perfect`, which includes `0 < m`, so `m - 1`
is the true predecessor). "Is a factor of" is read as divisibility.
-/

namespace OMA.S_oeis_a135627

/-- Every odd prime divides `m - 1` for some perfect number `m`. -/
theorem main : ∀ q : ℕ, q.Prime → Odd q → ∃ m : ℕ, m.Perfect ∧ q ∣ m - 1 := by
  sorry

end OMA.S_oeis_a135627
