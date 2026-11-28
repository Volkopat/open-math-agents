import Mathlib

/-!
# A256775: Primes of the form n^2 + 81

Source: https://oeis.org/A256775
Credit: @enzo2

A256775 lists the primes of the form n^2 + 81. The OEIS entry states:
Conjecture: sequence is infinite.

The sequence is the set of primes p for which there is a natural number n
with p = n^2 + 81, so the conjecture says that this set is infinite.
-/

namespace OMA.S_oeis_a256775

theorem main :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 81}.Infinite := by
  sorry

end OMA.S_oeis_a256775
