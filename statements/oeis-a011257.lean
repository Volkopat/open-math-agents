import Mathlib

/-!
# A011257: sigma(k) is even when the geometric mean of phi(k) and sigma(k) is an integer

Source: https://oeis.org/A011257
Credit: @jagraj28

A011257 lists the numbers `k` such that the geometric mean of `phi(k)` and `sigma(k)` is an
integer, that is, `phi(k) * sigma(k)` is a perfect square (1, 14, 30, 51, 105, ...). The entry
records (Labos Elemer, 2001) that it is conjectured that `sigma(k)` for these numbers is never odd.

`main` states it for `k > 1`. For `k = 1`, `phi(1) = sigma(1) = 1`, so 1 is a term and
`sigma(1) = 1` is odd; the source plainly means the nontrivial terms. A check for `k ≤ 10^6`
finds `k = 1` as the only term with odd `sigma(k)`.

Conventions: `sigma(k)` is the sum of the divisors of `k`; `phi` is Euler's totient. The
geometric mean `sqrt(phi(k) * sigma(k))` is an integer exactly when the product is a square.
-/

namespace OMA.S_oeis_a011257

/-- `sigma k`: the sum of the divisors of `k`. -/
def sigma (k : ℕ) : ℕ := ∑ d ∈ k.divisors, d

/-- Elemer's conjecture in OEIS A011257. -/
theorem main : ∀ k : ℕ, 1 < k → IsSquare (Nat.totient k * sigma k) → Even (sigma k) := by
  sorry

end OMA.S_oeis_a011257
