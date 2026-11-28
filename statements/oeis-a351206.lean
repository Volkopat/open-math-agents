import Mathlib

/-!
# A351206: Least positive integer m such that n = x^4 + (y^4 + z^4 + 7*w^2)/m^4 for some nonnegative integers x,y,z,w with y <= z.

Source: https://oeis.org/A351206
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A351206 (Zhi-Wei Sun, Feb 04 2022): a(n) exists for any
nonnegative integer n.

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, ...).
* The equation n = x^4 + (y^4 + z^4 + 7*w^2)/m^4 is an equation between rational numbers;
  multiplied by m^4 > 0 it is the equivalent equation m^4*n = m^4*x^4 + y^4 + z^4 + 7*w^2 between
  natural numbers, which is how it is stated.
* `a(n) exists` means that some m with the stated property exists (then the least such m exists);
  it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a351206

/-- The conjecture recorded in A351206. -/
theorem main : ∀ n : ℕ, ∃ m x y z w : ℕ, 0 < m ∧ y ≤ z ∧
    m ^ 4 * n = m ^ 4 * x ^ 4 + y ^ 4 + z ^ 4 + 7 * w ^ 2 := by
  sorry

end OMA.S_oeis_a351206
