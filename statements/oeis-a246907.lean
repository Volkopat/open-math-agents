import Mathlib

/-!
# A246907: Numbers n such that sigma(n + sigma(n)) = 3n.

Source: https://oeis.org/A246907
Credit: @azmiozgen

Conjecture (from the entry): for n >= 2, the terms are the numbers n of the form 2^k such that
3*(2^k) - 1 is prime.

Formalization notes:
* Stated as a characterization of all n ≥ 2: sigma(n + sigma(n)) = 3n if and only if n = 2^k
  for some k with 3 * 2^k - 1 prime (n ≥ 2 forces k ≥ 1). The first term 1 is outside the range.
* Controls (computed): the terms below 70000 are 1, 2, 4, 8, 16, 64, 128, 2048, as in the entry.
-/

namespace OMA.S_oeis_a246907

open ArithmeticFunction

/-- For `n ≥ 2`: `σ(n + σ(n)) = 3n` iff `n = 2^k` with `3·2^k - 1` prime. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (sigma 1 (n + sigma 1 n) = 3 * n ↔ ∃ k : ℕ, n = 2 ^ k ∧ (3 * 2 ^ k - 1).Prime) := by
  sorry

end OMA.S_oeis_a246907
