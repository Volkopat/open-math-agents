import Mathlib

/-!
# A389680: Numbers k for which no i > 1 exists such that k + i is composite and its least prime factor exceeds i^2.

Source: https://oeis.org/A389680
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A389680 (Giorgos Kalogeropoulos, Oct 10 2025): this
sequence is finite.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, ...).
* The terms are the positive integers k for which there is no i > 1 such that k + i is composite
  and its least prime factor exceeds i^2. Since k + i >= 3, `composite` is `not prime`, and the
  least prime factor is `Nat.minFac`.
* `The sequence is finite` is `Set.Finite` of the set of all such k.
-/

namespace OMA.S_oeis_a389680

/-- The conjecture recorded in A389680. -/
theorem main : Set.Finite {k : ℕ | 0 < k ∧
    ¬ ∃ i : ℕ, 1 < i ∧ ¬ (k + i).Prime ∧ i ^ 2 < (k + i).minFac} := by
  sorry

end OMA.S_oeis_a389680
