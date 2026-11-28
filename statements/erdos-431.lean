import Mathlib

/-!
# Erdős Problem 431

Source: https://www.erdosproblems.com/431
Credit: @mattdorman

The source asks (Ostmann's inverse Goldbach problem): are there two infinite sets `A` and `B` such
that `A + B` agrees with the set of prime numbers up to finitely many exceptions?

Reading used here: `A, B ⊆ ℕ` and `A + B = {a + b : a ∈ A, b ∈ B}` (pointwise sum). Agreeing up to
finitely many exceptions means the symmetric difference of `A + B` and the set of primes is
finite. The statement below is the affirmative answer (the source records that the answer is
surely no; a disproof settles it equally).
-/

open Pointwise

namespace OMA.S_erdos_431

theorem main :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (symmDiff (A + B) {p : ℕ | p.Prime}).Finite := by
  sorry

end OMA.S_erdos_431
