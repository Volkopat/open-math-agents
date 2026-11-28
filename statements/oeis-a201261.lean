import Mathlib

/-!
# A201261: Primes of the form n^3 + 7

Source: https://oeis.org/A201261

Conjecture (OEIS A201261, implied by the Bateman-Horn conjecture):
There are infinitely many primes of the form `n^3 + 7`.

Conventions:
- Offset: `1`; first terms: `7` (`n = 0`), `71` (`n = 4`), `223` (`n = 6`),
  `5839` (`n = 18`), `13831` (`n = 24`), ...
-/

namespace OMA.S_oeis_a201261

/-- The set of primes of the form `n^3 + 7` (OEIS A201261). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p = n ^ 3 + 7}

/-- Conjecture: there are infinitely many primes of the form `n^3 + 7`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a201261
