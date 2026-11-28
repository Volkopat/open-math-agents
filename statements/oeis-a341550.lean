import Mathlib

/-!
# OEIS A341550

Bill McEachen conjectures that infinitely many primes arise from three consecutive
primes `p, q, r` as `p * q + 2 * r`. The sequence records the resulting primes.
Mathlib numbers the primes from index zero, starting with 2.

Source: https://oeis.org/A341550
Formalization: @a5teri5k
-/

namespace OMA.S_oeis_a341550

theorem main :
    {x : ℕ | x.Prime ∧ ∃ i : ℕ,
      x = Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) +
        2 * Nat.nth Nat.Prime (i + 2)}.Infinite := by
  sorry

end OMA.S_oeis_a341550
