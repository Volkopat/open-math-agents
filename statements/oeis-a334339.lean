import Mathlib

/-!
# OEIS A334339: sigma(m n) is a cube for some m

Source: https://oeis.org/A334339
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A334339(n) is the least positive integer `m` such that `σ(m n)` is a cube, where `σ(k)` is the
sum of the divisors of `k`.

Conjecture: `a(n)` exists for any `n > 0`. In other words, for any positive integer `n`, there is
a positive integer `m` with `σ(m n)` equal to a cube.

Formalization notes:
* `σ` is `ArithmeticFunction.sigma 1`; "a cube" means `c^3` for a natural number `c`.
-/

namespace OMA.S_oeis_a334339

open ArithmeticFunction

/-- For every positive integer `n` there is a positive `m` such that `σ(m n)` is a cube. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ ∃ c : ℕ, sigma 1 (m * n) = c ^ 3 := by
  sorry

end OMA.S_oeis_a334339
