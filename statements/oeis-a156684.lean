import Mathlib

/-!
# OEIS A156684

The sequence counts primitive Pythagorean triples with both legs strictly below
`n`. We count each leg pair once, with the smaller leg first. A positive
hypotenuse is uniquely determined by the pair whenever the sum of the two
squares is a square.

The limit follows from the asymptotic formula of Benito and Varona (2002).
Their ordered-leg count is twice the count used in the sequence.

Source: https://oeis.org/A156684
Reference: https://doi.org/10.1016/S0377-0427(01)00496-4
Formalization: @a5teri5k
-/

namespace OMA.S_oeis_a156684

open Filter
open scoped Topology

def a (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter fun (x, y) ↦
    0 < x ∧ x < y ∧ Nat.Coprime x y ∧
      (Nat.sqrt (x ^ 2 + y ^ 2)) ^ 2 = x ^ 2 + y ^ 2).card

theorem main :
    Tendsto (fun n : ℕ ↦ (a n : ℝ) / (n : ℝ)) atTop
      (𝓝 (2 / Real.pi ^ 2 * Real.log (1 + Real.sqrt 2))) := by
  sorry

end OMA.S_oeis_a156684
