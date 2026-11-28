import Mathlib

/-!
# A128930: `a(n) = prime(n) * π(n)`.

Source: https://oeis.org/A128930
Credit: @cjchaffin

Conjecture (Thomas Ordowski, Aug 11 2012): for each `n` there is at least one prime `p`
such that `a(n) < p < a(n+1)`.

Conventions: offset 1; `prime(n)` is the `n`-th prime with `prime(1) = 2`
(`Nat.nth Nat.Prime (n - 1)`); `π(n)` is `Nat.primeCounting n` (primes `≤ n`).
The listed terms begin `0, 3, 10, 14, …`, matching `a(1) = 2 * π(1) = 0`.
-/

namespace OMA.S_oeis_a128930

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

noncomputable def a (n : ℕ) : ℕ := prime n * Nat.primeCounting n

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ a n < p ∧ p < a (n + 1) := by
  sorry

end OMA.S_oeis_a128930
