import Mathlib.Data.Nat.ModEq

/- Thomas Ordowski’s conjecture of August 3, 2018, for OEIS A126762.
   Source: https://oeis.org/A126762
   Credit: @sobrien032
   The sequence starts at n = 1. Its defining condition is a literal
   remainder equality. When k > n, this agrees with congruence modulo k.
   The claim gives the least index for both conditions explicitly. -/

namespace OMA.S_oeis_a126762

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ a : ℕ, IsLeast {k : ℕ | n < k ∧ n ^ k % k = n} a ∧
      IsLeast {k : ℕ | n < k ∧ n ^ (k - 1) % k = 1} a := by
  sorry

end OMA.S_oeis_a126762
