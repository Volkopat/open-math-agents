import Mathlib

/-!
# A381007: Ordered hypotenuses of the Pythagorean triangles defined by a = 2^(4n) + 2^(2n+1), b = 2^(4n) - 2^(4n-2) - 2^(2n) - 1, c = 2^(4n) + 2^(4n-2) + 2^(2n) + 1.

Source: https://oeis.org/A381007
Credit: @max-otc

For n ≥ 1 (OEIS offset 1) the triangle has legs a(n), b(n) and hypotenuse c(n) as in the title.
Conjecture in the entry: these Pythagorean triangles are primitive, i.e. gcd(a, b, c) = 1 for every n ≥ 1.
(Chai Wah Wu, Feb 13 2025, notes that it holds: Euclid's formula with x = 2^(2n), y = 2^(2n-1) + 1.)
-/

namespace OMA.S_oeis_a381007

/-- The leg a(n) = 2^(4n) + 2^(2n+1). -/
def legA (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (2 * n + 1)

/-- The leg b(n) = 2^(4n) - 2^(4n-2) - 2^(2n) - 1. -/
def legB (n : ℕ) : ℕ := 2 ^ (4 * n) - 2 ^ (4 * n - 2) - 2 ^ (2 * n) - 1

/-- The hypotenuse c(n) = 2^(4n) + 2^(4n-2) + 2^(2n) + 1 (the n-th term of A381007). -/
def hyp (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (4 * n - 2) + 2 ^ (2 * n) + 1

/-- For every n ≥ 1 the triangle (a(n), b(n), c(n)) is primitive: gcd(a, b, c) = 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.gcd (Nat.gcd (legA n) (legB n)) (hyp n) = 1 := by
  sorry

end OMA.S_oeis_a381007
