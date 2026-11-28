import Mathlib

/-!
# A308222: Numbers that are the perimeter of a primitive Heronian isosceles triangle.

Source: https://oeis.org/A308222
Credit: @agchua

Formula line of A308222 (the entry is by Peter Kagey, May 16 2019):
  a(n) = 2*A096033(n+2) (conjectured).
A308222 has offset 1, so the claim is stated for n ≥ 1. The entry's comment: a primitive Heronian
triangle is a triangle with integer sides and area, where the side lengths do not share a common
divisor. An isosceles triangle has sides a, a, b with 0 < b < 2a (a nondegenerate triangle). Its
side lengths share no common divisor iff gcd(a, b) = 1. By Heron's formula its area K satisfies
16 K^2 = (2a + b) b b (2a - b) = b^2 (4a^2 - b^2), so its area is an integer iff
16 K^2 = b^2 (4a^2 - b^2) for some natural number K. Its perimeter is 2a + b. A308222(n) is the
n-th such perimeter in increasing order, Nat.nth IsPerim (n - 1).

The referenced sequence, by its own entry's definition:
* A096033 (offset 1): Difference between leg and hypotenuse in primitive Pythagorean triangles,
  in increasing order. A primitive Pythagorean triangle has legs x, y > 0 and hypotenuse z with
  x^2 + y^2 = z^2 and gcd(x, y) = 1; the differences are the numbers z - x, where x is either leg
  (the roles of x and y are symmetric). A096033(n) is Nat.nth IsDiff (n - 1).
-/

namespace OMA.S_oeis_a308222

/-- p is the perimeter 2a + b of a primitive Heronian isosceles triangle with sides a, a, b. -/
def IsPerim (p : ℕ) : Prop :=
  ∃ a b K : ℕ, 0 < b ∧ b < 2 * a ∧ Nat.gcd a b = 1 ∧
    16 * K ^ 2 = b ^ 2 * (4 * a ^ 2 - b ^ 2) ∧ p = 2 * a + b

/-- A308222(n), n ≥ 1: the n-th perimeter of a primitive Heronian isosceles triangle. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsPerim (n - 1)

/-- d is a difference z - x between the hypotenuse z and a leg x of a primitive Pythagorean
triangle with legs x, y. -/
def IsDiff (d : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ Nat.gcd x y = 1 ∧ d = z - x

/-- A096033(n), n ≥ 1: the n-th difference between leg and hypotenuse in primitive
Pythagorean triangles. -/
noncomputable def a096033 (n : ℕ) : ℕ := Nat.nth IsDiff (n - 1)

/-- The conjecture: a(n) = 2 * A096033(n + 2) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 * a096033 (n + 2) := by
  sorry

end OMA.S_oeis_a308222
