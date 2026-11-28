import Mathlib

/-!
# A176584: Primes of the form p = k^3 + (largest square <= k^3).

Source: https://oeis.org/A176584
Credit: @keiichisince1986-bot

A176584 is the sequence `a(n)` named in the title. The entry states:
Consider k = 4 * x^2 + 1, where the largest square <= k^3 is (8 * x^3 + 3 * x)^2. Bunyakowsky's
conjecture implies there are infinitely many primes of the form (4 * x^2 + 1)^3 + (8 * x^3 + 3 * x)^2,
and so that the sequence is infinite. (The statement below is the claim that the sequence is
infinite, unconditionally.)

Conventions:
- The largest square `≤ k^3` is `(Nat.sqrt (k^3))^2`.
-/

namespace OMA.S_oeis_a176584

theorem main :
    {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = k ^ 3 + Nat.sqrt (k ^ 3) ^ 2}.Infinite := by
  sorry

end OMA.S_oeis_a176584
