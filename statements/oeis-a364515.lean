import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# A364515: supercongruence for `(1/2) * (6n)! (2n)!² / ((3n)! (4n)! n!³)`

Source: https://oeis.org/A364515

`a(n) = (1/2) * (6n)! * (2n)!^2 / ((3n)! * (4n)! * n!^3)` for `n ≥ 1`, with `a(0) = 1`.
The OEIS entry conjectures that the supercongruences
`a(n * p^r) ≡ a(n * p^(r-1)) (mod p^(3*r))`
hold for all primes `p ≥ 5` and all positive integers `n` and `r`.
-/

namespace OMA.S_oeis_a364515

/-- `a n = (1/2) * (6n)! * (2n)!^2 / ((3n)! * (4n)! * n!^3)` for `n ≥ 1`, with `a 0 = 1`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else ((6 * n).factorial * (2 * n).factorial ^ 2) /
    (2 * (3 * n).factorial * (4 * n).factorial * n.factorial ^ 3)

/-- Conjectured supercongruences for OEIS A364515. -/
theorem main : ∀ (p n r : ℕ), p.Prime → 5 ≤ p → 0 < n → 0 < r →
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a364515
