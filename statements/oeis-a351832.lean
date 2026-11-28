import Mathlib

/-!
# A351832: Least nonnegative integer m such that n = x^6 + y^6 - (z^2 + m^2) for some nonnegative integers x,y,z with z <= m.

Source: https://oeis.org/A351832
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A351832 (Zhi-Wei Sun, Feb 21 2022): a(n) exists for
each nonnegative integer n.

Conventions:
* The sequence has offset 0 (data 0, 0, 0, 6, 6, 20, 7, 7, 19, 24, 24, 7, ...).
* The equation n = x^6 + y^6 - (z^2 + m^2) is written without subtraction as n + z^2 + m^2 = x^6 +
  y^6; x, y, z, m are natural numbers with z <= m.
* `a(n) exists` means that some m with the stated property exists (then the least such m exists);
  it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a351832

/-- The conjecture recorded in A351832. -/
theorem main : ∀ n : ℕ, ∃ m x y z : ℕ, z ≤ m ∧ n + z ^ 2 + m ^ 2 = x ^ 6 + y ^ 6 := by
  sorry

end OMA.S_oeis_a351832
