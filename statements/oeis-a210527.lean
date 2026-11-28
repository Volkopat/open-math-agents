import Mathlib

/-!
# A210527: a(n) = 9*n^2 + 39*n + 83.

Source: https://oeis.org/A210527
Credit: @altalexlt-dot

OEIS A210527 has offset `0,1`, so the sequence is `a(0), a(1), ..., a(n)` (`n + 1` terms
generated up to index `n`). Harvey P. Dale (Mar 18 2016) conjectured that the total number
of primes among `a(0), ..., a(n)` remains strictly below one-half of the total number of
terms generated (`2 * primeCount n < n + 1`) from and after `n = 886`.
-/

namespace OMA.S_oeis_a210527

/-- OEIS A210527: `a(n) = 9*n^2 + 39*n + 83` (offset 0). -/
def a (n : ℕ) : ℕ :=
  9 * n ^ 2 + 39 * n + 83

/-- The number of prime terms among `a(0), ..., a(n)`. -/
def primeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => Nat.Prime (a k))).card

/-- Conjecture of Harvey P. Dale (OEIS A210527): for every `n ≥ 886`, the number of primes
among `a(0), ..., a(n)` is strictly less than half of the `n + 1` terms generated. -/
theorem main : ∀ n : ℕ, 886 ≤ n → 2 * primeCount n < n + 1 := by
  sorry

end OMA.S_oeis_a210527
