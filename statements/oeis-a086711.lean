import Mathlib

/-!
# OEIS A086711

Conjecture: infinitely many primes have equal sums of prime factors, counted with
multiplicity, for their predecessor and successor.

Sources: https://oeis.org/A086711 and https://oeis.org/A001414
Credit: @gblacher2
-/

namespace OMA.S_oeis_a086711

theorem main :
    {p : ℕ | p.Prime ∧ (p - 1).primeFactorsList.sum = (p + 1).primeFactorsList.sum}.Infinite := by
  sorry

end OMA.S_oeis_a086711
