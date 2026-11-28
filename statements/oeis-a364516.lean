import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# A364516: supercongruence for `(2/3) * (8n)! (3n)!² / ((6n)! (4n)! (2n)! n!²)`

Source: https://oeis.org/A364516

`a(n) = (2/3) * (8n)! * (3n)!^2 / ((6n)! * (4n)! * (2n)! * n!^2)` for `n ≥ 1`, with `a(0) = 1`.
The OEIS entry conjectures that the supercongruences
`a(n * p^r) ≡ a(n * p^(r-1)) (mod p^(3*r))`
hold for all primes `p ≥ 5` and all positive integers `n` and `r`.
-/

namespace OMA.S_oeis_a364516

/-- `a n = (2/3) * (8n)! * (3n)!^2 / ((6n)! * (4n)! * (2n)! * n!^2)` for `n ≥ 1`, with `a 0 = 1`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else (2 * (8 * n).factorial * (3 * n).factorial ^ 2) /
    (3 * (6 * n).factorial * (4 * n).factorial * (2 * n).factorial * n.factorial ^ 2)

/-- Conjectured supercongruences for OEIS A364516. -/
theorem main : ∀ (p n r : ℕ), p.Prime → 5 ≤ p → 0 < n → 0 < r →
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a364516
