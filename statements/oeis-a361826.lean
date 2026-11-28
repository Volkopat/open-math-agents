import Mathlib

/-!
# A361826: a(n) is equal to the number of roots of the equation n*cos(x) = sqrt(x).

Source: https://oeis.org/A361826
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A361826 (Nicolay Avilov, Mar 27 2023): a(n) =
2*floor(n^2/(2*Pi)) + 1.

Conventions:
* The sequence has offset 1 (data 1, 1, 3, 5, 7, 11, 15, 21, 25, 31, 39, 45, ...).
* a(n) is the number of real roots x of n*cos(x) = sqrt(x); the square root requires x >= 0, which
  is stated explicitly because `Real.sqrt` is 0 on negative numbers. The (finite) number of roots
  is `Set.ncard` of the solution set.
* Pi is `Real.pi`, and the floor of the positive real n^2/(2*Pi) is the natural-number floor
  `Nat.floor`. The statement is for n >= 1 (the offset of the sequence).
-/

namespace OMA.S_oeis_a361826

/-- The conjecture recorded in A361826. -/
theorem main : ∀ n : ℕ, 0 < n →
    Set.ncard {x : ℝ | 0 ≤ x ∧ (n : ℝ) * Real.cos x = Real.sqrt x} =
      2 * ⌊(n : ℝ) ^ 2 / (2 * Real.pi)⌋₊ + 1 := by
  sorry

end OMA.S_oeis_a361826
