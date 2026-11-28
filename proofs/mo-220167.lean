import OMAStatements.S_mo_220167
import Mathlib

open MeasureTheory in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_220167.main) := fun h => by
  simpa using h Unit 0 ℝ ℝ (· + 1) (contDiff_id.add contDiff_const) ⟨(· - 1), contDiff_id.sub contDiff_const, fun x => by simp, fun x => by simp⟩ 0 (by simp) (by simp)
