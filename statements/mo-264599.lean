import Mathlib

/-!
# A partition of the unit interval into continuum many sets of full outer measure

Source: https://mathoverflow.net/questions/264599
Credit: @artnoage

Lebesgue volume on arbitrary sets is interpreted as outer measure. The interval
itself indexes the parts, so the partition has continuum many members.
-/

namespace OMA.S_mo_264599

open MeasureTheory Set

theorem main :
    ∃ A : Icc (0 : ℝ) 1 → Set ℝ,
      Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = Icc 0 1 ∧
      ∀ i, volume (A i) = 1 := by
  sorry

end OMA.S_mo_264599
