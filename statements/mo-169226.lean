import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Group.Abs

/-! Source: https://mathoverflow.net/questions/169226 -/

namespace OMA.S_mo_169226

/-- The greatest common divisor of the four coordinates. -/
def content (x y z w : ℤ) : ℕ :=
  Int.gcd (Int.gcd x y : ℤ) (Int.gcd z w : ℤ)

/-- The difference of the Gaussian norms of x+iy and z+iw, with coefficient b. -/
def quad (b : ℕ) (x y z w : ℤ) : ℤ :=
  x ^ 2 + y ^ 2 - (b : ℤ) * (z ^ 2 + w ^ 2)

/-- With m positive and primitive parameters, keep the positive denominators
quad b m n r s that divide 2*m, and set q to that quotient. -/
theorem main :
    ∀ (b : ℕ) (x y z w : ℤ), quad b x y z w = 1 ↔
      ∃ m n r s q : ℤ, 0 < m ∧ 0 < q ∧ content m n r s = 1 ∧
        quad b m n r s * q = 2 * m ∧
        |x| = q * m - 1 ∧ y = q * n ∧ z = q * r ∧ w = q * s := by
  sorry

end OMA.S_mo_169226
