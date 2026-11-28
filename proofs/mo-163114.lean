import OMAStatements.S_mo_163114
import Mathlib

/-!
MathOverflow 163114: a three-element BCL algebra on `{0, 1, 2}` (constant `0`) in which
`0 * 1 = 0` and `1 * 2 = 0` but `0 * 2 = 1`, so the relation is not transitive. All three axioms
are checked by `decide`.
-/

open OMA.S_mo_163114

namespace OMA.P163114

/-- A three-element BCL algebra on `{0, 1, 2}` with constant `0`; rows `x`, columns `y`. -/
def T : Fin 3 → Fin 3 → Fin 3 := ![![0, 0, 1], ![1, 0, 0], ![1, 2, 0]]

lemma bcl : IsBCL T 0 := by
  unfold IsBCL T
  decide

end OMA.P163114

open OMA.P163114 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_163114.main) := by
  intro h
  have := (h (Fin 3) T 0 bcl).2.2 0 1 2 (by decide) (by decide)
  revert this
  decide
