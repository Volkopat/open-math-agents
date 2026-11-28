import Mathlib

/-!
# A282972: Number of ways to write n as 4*x^4 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that 79*y^2 - 220*y*z + 205*z^2 is a square.

Source: https://oeis.org/A282972
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; parts verified for n up to 10^7 and 10^6):
(i) a(n) > 0 for all n = 0, 1, 2, ....
(ii) Any positive integer n can be written as 4*x^4 + y^2 + z^2 + w^2 with x, y, z nonnegative integers
and w a positive integer such that 169*y^2 - 444*y*z + 396*z^2 (or 289*y^2 - 654*y*z + 401*z^2) is a
square.

Formalization notes:
* a(n) > 0 is stated as the existence of a representation.
* The quadratic forms are computed in ℤ (they are positive definite, so their values are ≥ 0). The
  "or" in (ii) is read as two separate claims, both stated.
* Controls (computed): all claims hold for n < 1500.
-/

namespace OMA.S_oeis_a282972

/-- The conjecture of the entry. -/
theorem main :
    (∀ n : ℕ, ∃ x y z w : ℕ, 4 * x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (79 * (y : ℤ) ^ 2 - 220 * y * z + 205 * (z : ℤ) ^ 2)) ∧
      (∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ 4 * x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (169 * (y : ℤ) ^ 2 - 444 * y * z + 396 * (z : ℤ) ^ 2)) ∧
      ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ 4 * x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (289 * (y : ℤ) ^ 2 - 654 * y * z + 401 * (z : ℤ) ^ 2) := by
  sorry

end OMA.S_oeis_a282972
