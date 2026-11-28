import Mathlib.Data.Nat.Totient

/-! Cloitre’s characterization of primes of the form 1 + 2^a 3^b.
Source: https://oeis.org/A058383
-/

namespace OMA.S_oeis_a058383

theorem main : ∀ x : ℕ, 7 ≤ x →
    (x.totient + (x - 1).totient = (4 * x - 3) / 3 ↔
      x.Prime ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x = 1 + 2 ^ a * 3 ^ b) := by
  sorry

end OMA.S_oeis_a058383
