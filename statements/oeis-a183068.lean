import Mathlib

/-!
# A183068: Central terms of triangle A183065.

Source: https://oeis.org/A183068

A183065 is the triangle with g.f. `Sum_{m >= 0} (4m)!/m!^4 * x^(2m) y^m / (1 - x - x y)^(4m+1)`,
and `a(n) = A183065(2n, n)`, offset 0. The entry gives (Peter Bala, Jul 15 2024, as a formula)
`a(n) = binomial(2n, n) * Sum_{k = 0..n} binomial(n, k)^2 * binomial(2n+2k, 2k) * binomial(2k, k)
      = Sum_{k = 0..n} (2n+2k)!/(k!^4 (n-k)!^2)`,
and conjectures (Peter Bala, Jul 15 2024):

  the supercongruence `a(n p^r) == a(n p^(r-1)) (mod p^(2r))` holds for all primes `p`
  and positive integers `n` and `r`.

Formalized: `a(n)` is defined by the division-free binomial form of the entry's formula above, in `ℕ`
(it reproduces the data 1, 26, 3246, 606500, 137915470, ...). The congruence is stated in `ℤ` as
`p^(2r) ∣ a(n p^r) - a(n p^(r-1))`, for every prime `p` (including 2), every `n ≥ 1`, every `r ≥ 1`.
-/

namespace OMA.S_oeis_a183068

/-- A183068: `a(n) = C(2n,n) * Sum_{k=0..n} C(n,k)^2 C(2n+2k,2k) C(2k,k)`. -/
def a (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n *
    ∑ k ∈ Finset.range (n + 1),
      Nat.choose n k ^ 2 * Nat.choose (2 * n + 2 * k) (2 * k) * Nat.choose (2 * k) k

/-- Bala's conjectured supercongruence. -/
theorem main :
    ∀ p n r : ℕ, p.Prime → 1 ≤ n → 1 ≤ r →
      ((p : ℤ) ^ (2 * r)) ∣ ((a (n * p ^ r) : ℤ) - (a (n * p ^ (r - 1)) : ℤ)) := by
  sorry

end OMA.S_oeis_a183068
