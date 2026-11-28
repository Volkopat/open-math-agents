import Mathlib

/-!
# OEIS A399492: growth of the step-echo sequence

Source: https://oeis.org/A399492
Credit: @gblacher2
-/

open Filter
open scoped Asymptotics

namespace OMA.S_oeis_a399492

/-- The terms from index zero through the given index, inclusive. -/
def termsThrough : ℕ → Array ℕ
  | 0 => #[0]
  | 1 => #[0, 1]
  | n + 2 =>
      let previous := termsThrough (n + 1)
      let last := previous[n + 1]!
      let gap := last - previous[n]!
      let indices := Finset.range (n + 2)
      let pairs := (indices ×ˢ indices).filter fun (i, j) =>
        i < j ∧ previous[j]! - previous[i]! = gap
      previous.push (last + 1 + pairs.card)

def a (n : ℕ) : ℕ := (termsThrough n)[n]!

theorem main :
    (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

end OMA.S_oeis_a399492
