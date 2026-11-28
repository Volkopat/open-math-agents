import Mathlib

/-!
# When does the totient divide the sum of divisors?

MathOverflow question 418927, asked by math110: https://mathoverflow.net/q/418927
Lean statement by @AlfredMelson.
-/

namespace OMA.S_mo_418927

theorem main :
    {n : ℕ | 0 < n ∧ n.totient ∣ ∑ d ∈ n.divisors, d}.Infinite := by
  sorry

end OMA.S_mo_418927
