import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime midpoints in OEIS A398132

Mauro Torelli's OEIS entry records the conjecture that every prime above three
is strictly between two primes at equal distance from it.
Source: https://oeis.org/A398132 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.
-/

namespace OMA.S_oeis_a398132

theorem main : ∀ n : ℕ, n.Prime → 3 < n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < n ∧ n < q ∧ p + q = 2 * n := by
  sorry

end OMA.S_oeis_a398132
