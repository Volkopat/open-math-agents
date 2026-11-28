import Mathlib

/-!
# A237588: sigma(n) - 2n + 1 vanishes exactly at the powers of 2 (almost perfect numbers)

Source: https://oeis.org/A237588
Credit: @sntntHb

`a(n) = sigma(n) - 2n + 1` (offset 1), where `sigma(n)` is the sum of the divisors of `n`
(A000203). The entry records the conjecture
  `a(n) = 0` if and only if `n` is a power of 2,
and recalls (from Guy, Unsolved Problems in Number Theory, B2) that a number with
`sigma(n) = 2n - 1` is called almost perfect: powers of 2 are almost perfect, and it is a well known
open question whether there are any others.

Formalized over the integers with Mathlib's `ArithmeticFunction.sigma 1` for the sum of divisors,
for every `n ≥ 1` (the range of the sequence); a power of 2 is `2^k` with `k ≥ 0`.
-/

namespace OMA.S_oeis_a237588

open ArithmeticFunction

/-- `a n = sigma(n) - 2n + 1` (OEIS A237588). -/
def a (n : ℕ) : ℤ := (sigma 1 n : ℤ) - 2 * n + 1

/-- The conjecture in OEIS A237588: for `n ≥ 1`, `a(n) = 0` iff `n` is a power of 2. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a237588
