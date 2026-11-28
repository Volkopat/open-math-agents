import OMAStatements.S_oeis_a069187
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a069187.main) := by
  intro h
  have ⟨m, hm, _, he⟩ := (h 1 (by decide)).mp
    ⟨1, 1, squarefree_one, by decide, by decide⟩
  have hp : 0 < m ^ 2 := by positivity
  have hs : 1 ≤ m ^ 2 := hp
  have hb := Nat.mul_le_mul hs (show 2 ≤ m ^ 2 + 1 by omega)
  omega