import Mathlib

/-!
# A333562: a(n) = Sum_{j = 0..3*n} binomial(n+j-1,j)*2^j

Source: https://oeis.org/A333562

Offset 0. Column 3 of the square array A333560.

Conjecture (Peter Bala, in the entry): a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) for prime
p >= 5 and positive integers n and k.

Formalized: `a n` is an integer, the sum runs over `Finset.range (3 * n + 1)`, and the binomial
is `Nat.choose (n + j - 1) j`. For `n >= 1` the natural subtraction is exact; at `n = 0` only
`j = 0` occurs and `Nat.choose 0 0 = 1` agrees with binomial(-1,0) = 1, so a(0) = 1 as in the
data. The conjecture only uses positive arguments. A congruence `x == y (mod N)` is written as
`N ∣ x - y` in the integers.
-/

namespace OMA.S_oeis_a333562

/-- A333562: `a(n) = Sum_{j = 0..3n} binomial(n+j-1, j) * 2^j`. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (3 * n + 1), ((Nat.choose (n + j - 1) j : ℕ) : ℤ) * 2 ^ j

/-- The conjectured supercongruences of the entry. -/
theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a333562
