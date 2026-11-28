import Mathlib

/-!
# A259915: Least positive integer k such that phi(k) and sigma(k*n) are both squares

Source: https://oeis.org/A259915
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A259915): a(n) exists for any n > 0.

(The comment states it as part of a more general conjecture on positive rationals m/n; only the
existence of a(n) for every n > 0 is formalized here.)

Conventions:
* phi is Euler's totient (`Nat.totient`) and sigma(m) the sum of the divisors of m
  (`ArithmeticFunction.sigma 1 m`).
* a(n) exists when some positive k has phi(k) and sigma(k*n) both perfect squares (`IsSquare`).
-/

namespace OMA.S_oeis_a259915

open ArithmeticFunction

/-- Sun's conjecture on A259915: for every `n > 0` there is `k > 0` such that `phi(k)` and
`sigma(k * n)` are both squares. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ IsSquare (Nat.totient k) ∧
    IsSquare (sigma 1 (k * n)) := by
  sorry

end OMA.S_oeis_a259915
