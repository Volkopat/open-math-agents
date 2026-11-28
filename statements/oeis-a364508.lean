import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# A364508: supercongruence for `(7n)! (6n)! (2n)! / ((4n)!² (3n)!² n!)`

Source: https://oeis.org/A364508

`a(n) = (7n)! * (6n)! * (2n)! / ((4n)!^2 * (3n)!^2 * n!)`.
The OEIS entry conjectures that the supercongruences
`a(n * p^r) ≡ a(n * p^(r-1)) (mod p^(3*r))`
hold for all primes `p ≥ 5` and all positive integers `n` and `r`.
-/

namespace OMA.S_oeis_a364508

/-- `a n = (7n)! * (6n)! * (2n)! / ((4n)!^2 * (3n)!^2 * n!)`. -/
def a (n : ℕ) : ℕ :=
  ((7 * n).factorial * (6 * n).factorial * (2 * n).factorial) /
    ((4 * n).factorial ^ 2 * (3 * n).factorial ^ 2 * n.factorial)

/-- Conjectured supercongruences for OEIS A364508. -/
theorem main : ∀ (p n r : ℕ), p.Prime → 5 ≤ p → 0 < n → 0 < r →
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a364508
