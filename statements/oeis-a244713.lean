import Mathlib

/-!
# A244713: positive numbers primitively represented by x^2 + x*y - 2*y^2

Source: https://oeis.org/A244713
Credit: @jagong-cmu

A244713 lists the positive numbers primitively represented by the binary quadratic
form (1, 1, -2), that is `x^2 + x*y - 2*y^2` (discriminant 9). Offset 1, so
a(1), a(2), a(3), ... = 1, 4, 7, ...

Formalizes Colin Barker's OEIS A244713 conjecture (Oct 31 2016):
`a(n) = a(n-1)+a(n-11)-a(n-12) for n>12.`

Conventions:
* A positive integer `k` is primitively represented when `k = x^2 + x*y - 2*y^2` for some
  integers `x, y` with `gcd(x, y) = 1`.
* `a n` is the `n`-th such number, counting from `a 1`, via `Nat.nth` (which counts from 0).
* The recurrence is stated in `ℤ` (to avoid ℕ subtraction) for every `n >= 13`,
  which is the range `n > 12` of the conjecture.
-/

namespace OMA.S_oeis_a244713

/-- `k` is a positive number primitively represented by `x^2 + x*y - 2*y^2`. -/
def primRep (k : ℕ) : Prop :=
  0 < k ∧ ∃ x y : ℤ, Int.gcd x y = 1 ∧ x ^ 2 + x * y - 2 * y ^ 2 = k

/-- `a n` is the `n`-th positive number primitively represented by the form, from `a 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth primRep (n - 1)

/-- For all `n > 12`: `a(n) = a(n-1) + a(n-11) - a(n-12)`. -/
theorem main : ∀ n : ℕ, 13 ≤ n →
    (a n : ℤ) = a (n - 1) + a (n - 11) - a (n - 12) := by
  sorry

end OMA.S_oeis_a244713
