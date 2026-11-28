import OMAStatements.S_oeis_a102091
import Mathlib

-- Credit: @ryansolves
-- The third count is 108. Its two-ring centered number is 325 = 5 * 65.
open OMA.S_oeis_a102091

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a102091.main) := by
  intro conjecture
  have member : ∃ k : ℕ, (consecutiveCounts k).1 = 108 := ⟨2, rfl⟩
  have excludes := (conjecture 108 (by decide)).mpr member
  exact excludes 2 5 (by norm_num) (Or.inl rfl) ⟨65, rfl⟩
