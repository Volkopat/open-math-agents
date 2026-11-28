import Mathlib

/-!
# Infinitely many interval numerators of convergents to 2π (OEIS A362602)

Source: https://oeis.org/A362602
Credit: @etaubman

The elements are integer numerators, with a positive integer interval
index. Hurwitz's theorem gives infinitely many fractions approximating 2π
well enough to be convergents by Legendre's criterion. Doubling a fraction's
denominator gives the required interval index for its numerator.
-/

namespace OMA.S_oeis_a362602

def numerators : Set ℤ :=
  {p | (∃ j : ℕ, ((2 * Real.pi).convergent j).num = p) ∧
       ∃ k : ℕ, 0 < k ∧ |Real.pi * (k : ℝ) - (p : ℝ)| ≤ 1 / (k : ℝ)}

theorem main : numerators.Infinite := by
  sorry

end OMA.S_oeis_a362602
