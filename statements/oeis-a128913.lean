import Mathlib

/-!
# A128913: `a(n) = n * π(n)`.

Source: https://oeis.org/A128913
Credit: @cjchaffin

Conjecture (Thomas Ordowski, Aug 12 2012): for each `n` there is at least one prime `p`
such that `2 a(n) < p < 2 a(n+1)`.

Conventions: offset 1; `π(n)` is `Nat.primeCounting n` (primes `≤ n`). The listed terms
begin `0, 2, 6, 8, 15, …`, matching `a(1) = 1 * π(1) = 0` and the example `a(7) = 28`.
-/

namespace OMA.S_oeis_a128913

def a (n : ℕ) : ℕ := n * Nat.primeCounting n

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ 2 * a n < p ∧ p < 2 * a (n + 1) := by
  sorry

end OMA.S_oeis_a128913
