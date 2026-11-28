import Mathlib

/-!
# A216880: Numbers of the form 3*p - 2 where p and 6*p + 1 are prime

Source: https://oeis.org/A216880

Conjecture (OEIS A216880, implied by Dickson's conjecture):
There are infinitely many numbers of the form `3 * p - 2` such that both `p` and `6 * p + 1`
are prime.

Conventions:
- Offset: `1`; first terms: `4` (`p = 2`), `7` (`p = 3`), `13` (`p = 5`),
  `19` (`p = 7`), `31` (`p = 11`), `37` (`p = 13`), ...
-/

namespace OMA.S_oeis_a216880

/-- The set of integers `3 * p - 2` where `p` and `6 * p + 1` are prime (OEIS A216880). -/
def S : Set ℕ :=
  {m : ℕ | ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (6 * p + 1) ∧ m = 3 * p - 2}

/-- Conjecture: OEIS A216880 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a216880
