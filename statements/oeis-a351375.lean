import Mathlib

/-!
# A351375: Least nonnegative integer m such that n = x^5 + y^5 - (z^3 + m^3) for some nonnegative integers x,y,z with z <= m.

Source: https://oeis.org/A351375
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A351375 (Zhi-Wei Sun, Feb 09 2022): a(n) exists for any
nonnegative integer n.

Conventions:
* The sequence has offset 0 (data 0, 0, 0, 174, 3, 3, 3, 53, 53, 25, 3, 20, ...).
* The equation n = x^5 + y^5 - (z^3 + m^3) is written without subtraction as n + z^3 + m^3 = x^5 +
  y^5; x, y, z, m are natural numbers with z <= m.
* `a(n) exists` means that some m with the stated property exists (then the least such m exists);
  it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a351375

/-- The conjecture recorded in A351375. -/
theorem main : ∀ n : ℕ, ∃ m x y z : ℕ, z ≤ m ∧ n + z ^ 3 + m ^ 3 = x ^ 5 + y ^ 5 := by
  sorry

end OMA.S_oeis_a351375
