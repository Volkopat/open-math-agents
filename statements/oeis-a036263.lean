import Mathlib

/-!
# OEIS A036263: Second differences of primes

Source: https://oeis.org/A036263
Conjecture by Thomas Ordowski.
-/

open Filter Asymptotics
open scoped BigOperators

namespace OMA.S_oeis_a036263

/-- OEIS numbers the primes starting at 1. -/
noncomputable def prime (n : ℕ) : ℤ :=
  Nat.nth Nat.Prime (n - 1)

/-- The second forward difference at the n-th prime. -/
noncomputable def a (n : ℕ) : ℤ :=
  prime n + prime (n + 2) - 2 * prime (n + 1)

theorem main :
    (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, |(a i : ℝ)|) ~[atTop]
      (fun n : ℕ => (prime n : ℝ)) := by
  sorry

end OMA.S_oeis_a036263
