import Mathlib

/-!
# OEIS A131626

Source: https://oeis.org/A131626 (OEIS Foundation, CC BY-SA 4.0).
Conjecture posed by Cino Hilliard, September 2007.

For each positive integer x the entry starts at the first prime and evaluates
2 * p * x + q for consecutive primes p, q, stopping at the first nonprime.
The conjecture says this initial run of primes is finite for every positive x.
Lean indexes primes from zero, so index i corresponds to p = prime(i + 1)
in the one-based indexing used by the source.
-/

namespace OMA.S_oeis_a131626

/-- Every positive x encounters a nonprime at some index in its row. -/
theorem main :
    ∀ x : ℕ, 0 < x → ∃ i : ℕ,
      ¬ Nat.Prime (2 * Nat.nth Nat.Prime i * x + Nat.nth Nat.Prime (i + 1)) := by
  sorry

end OMA.S_oeis_a131626
