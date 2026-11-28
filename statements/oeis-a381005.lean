import Mathlib

/-!
# A381005: Ordered short legs of a family of Pythagorean triangles.

Source: https://oeis.org/A381005
Credit: @bnb9001

For `n ≥ 1` the entry defines the Pythagorean triangles with
a = 2^(4n) + 2^(2n+1), b = 2^(4n) - 2^(4n-2) - 2^(2n) - 1 and c = 2^(4n) + 2^(4n-2) + 2^(2n) + 1
(the sequence lists the short legs b: 7, 175, 3007, ...).

Conjecture: these Pythagorean triangles are primitive. Chai Wah Wu notes that the conjecture is
true. A triangle is primitive when its three sides have greatest common divisor 1.
(The entries A381006 and A381007 state the same conjecture for the same triangles.)
-/

namespace OMA.S_oeis_a381005

/-- The leg `a = 2^(4n) + 2^(2n+1)`. -/
def A (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (2 * n + 1)

/-- The leg `b = 2^(4n) - 2^(4n-2) - 2^(2n) - 1`. -/
def B (n : ℕ) : ℕ := 2 ^ (4 * n) - 2 ^ (4 * n - 2) - 2 ^ (2 * n) - 1

/-- The hypotenuse `c = 2^(4n) + 2^(4n-2) + 2^(2n) + 1`. -/
def C (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (4 * n - 2) + 2 ^ (2 * n) + 1

/-- For every `n ≥ 1` the triangle `(A n, B n, C n)` is primitive. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.gcd (Nat.gcd (A n) (B n)) (C n) = 1 := by
  sorry

end OMA.S_oeis_a381005
