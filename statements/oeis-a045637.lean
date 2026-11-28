import Mathlib

/-!
# A045637: Primes of the form p^2 + 4, where p is prime

Source: https://oeis.org/A045637

Conjecture (OEIS A045637, under Bunyakovsky's conjecture):
There are infinitely many primes of the form `p^2 + 4` where `p` is prime.

Conventions:
- Offset: `1`; first terms: `13` (`p = 3`), `29` (`p = 5`), `53` (`p = 7`),
  `173` (`p = 13`), `293` (`p = 17`), `1373` (`p = 37`), ...
-/

namespace OMA.S_oeis_a045637

/-- The set of primes of the form `p^2 + 4` with `p` prime (OEIS A045637). -/
def S : Set ℕ :=
  {q : ℕ | Nat.Prime q ∧ ∃ p : ℕ, Nat.Prime p ∧ q = p ^ 2 + 4}

/-- Conjecture: there are infinitely many primes of the form `p^2 + 4` with `p` prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a045637
