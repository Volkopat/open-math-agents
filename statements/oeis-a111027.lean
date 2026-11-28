import Mathlib

/-!
# OEIS A111027: Wieferich primes in base 12

Source: https://oeis.org/A111027
Credit: @keiichisince1986-bot
-/

namespace OMA.S_oeis_a111027

/-- There are infinitely many primes satisfying the Wieferich congruence in base 12. -/
theorem main :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.ModEq (p ^ 2) (12 ^ (p - 1)) 1} := by
  sorry

end OMA.S_oeis_a111027
