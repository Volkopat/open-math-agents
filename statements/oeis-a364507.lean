import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# A364507: supercongruence for `(5n)! (4n)! / ((3n)!² (2n)! n!)`

Source: https://oeis.org/A364507

`a(n) = (5n)! * (4n)! / ((3n)!^2 * (2n)! * n!) = C(5n, 2n) * C(4n, n)`.
The OEIS entry conjectures that the supercongruences
`a(n * p^r) ≡ a(n * p^(r-1)) (mod p^(3*r))`
hold for all primes `p ≥ 5` and all positive integers `n` and `r`.
-/

namespace OMA.S_oeis_a364507

/-- `a n = (5n)! * (4n)! / ((3n)!^2 * (2n)! * n!)`. -/
def a (n : ℕ) : ℕ :=
  ((5 * n).factorial * (4 * n).factorial) /
    ((3 * n).factorial ^ 2 * (2 * n).factorial * n.factorial)

/-- Conjectured supercongruences for OEIS A364507. -/
theorem main : ∀ (p n r : ℕ), p.Prime → 5 ≤ p → 0 < n → 0 < r →
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a364507
