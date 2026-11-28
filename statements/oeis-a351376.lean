import Mathlib

/-!
# A351376: Least nonnegative integer m such that n = x^3 + y^3 - (z^5 + m^5) for some nonnegative integers x,y,z with z <= m.

Source: https://oeis.org/A351376
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A351376 (Zhi-Wei Sun, Feb 09 2022): a(n) exists for any
nonnegative integer n.

Conventions:
* The sequence has offset 0 (data 0, 0, 0, 2, 76, 3, 1, 1, 0, 0, 6, 5, ...).
* The equation n = x^3 + y^3 - (z^5 + m^5) is written without subtraction as n + z^5 + m^5 = x^3 +
  y^3; x, y, z, m are natural numbers with z <= m.
* `a(n) exists` means that some m with the stated property exists (then the least such m exists);
  it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a351376

/-- The conjecture recorded in A351376. -/
theorem main : ∀ n : ℕ, ∃ m x y z : ℕ, z ≤ m ∧ n + z ^ 5 + m ^ 5 = x ^ 3 + y ^ 3 := by
  sorry

end OMA.S_oeis_a351376
