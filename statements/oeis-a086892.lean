import Mathlib.Data.Finite.Defs

/-!
# OEIS A086892

The Ailon–Rudnick conjecture for the bases 2 and 3, with indices starting at 1.

Source: https://oeis.org/A086892
-/

namespace OMA.S_oeis_a086892

theorem main : Set.Infinite {n : ℕ | 1 ≤ n ∧ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1} := by
  sorry

end OMA.S_oeis_a086892
