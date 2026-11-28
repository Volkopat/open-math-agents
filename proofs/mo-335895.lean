import OMAStatements.S_mo_335895
import Mathlib

-- Problem: mo-335895, can every symmetric partition of the positions of an n x n matrix be
-- coloured with n colours, constantly on classes, so that distinct classes meeting a common
-- row or column get different colours?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For n = 3 take the classes A = {(0,1),(1,0)}, B = {(0,2),(2,0)}, C = {(0,0),(1,1)} and
-- D = {(1,2),(2,1),(2,2)}. A, B, C all meet row 0, and D meets A and C in row 1 and B in
-- row 2, so four different colours would be needed, but only three are available.

namespace MO335895

def cl : Fin 3 × Fin 3 → Fin 4 := fun x =>
  (![![2, 0, 1], ![0, 2, 3], ![1, 3, 3]] : Fin 3 → Fin 3 → Fin 4) x.1 x.2

theorem key : ∀ a b c d : Fin 3, a = b ∨ a = c ∨ b = c ∨ a = d ∨ b = d ∨ c = d := by
  decide

end MO335895

open OMA.S_mo_335895 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_335895.main) := by
  intro h
  have hsym : SymmetricBlocks 3 (Setoid.ker MO335895.cl) := by
    intro i j
    show MO335895.cl (i, j) = MO335895.cl (j, i)
    revert i j
    decide
  obtain ⟨color, h1, h2, h3⟩ := h 3 (Setoid.ker MO335895.cl) hsym
  have hne : ∀ x y : Fin 3 × Fin 3, (x.1 = y.1 ∨ x.2 = y.2) →
      MO335895.cl x ≠ MO335895.cl y → color x ≠ color y := by
    intro x y hxy hcl hc
    exact hcl (h3 x y hxy hc)
  have hAB := hne (0, 1) (0, 2) (Or.inl rfl) (by decide)
  have hAC := hne (0, 1) (0, 0) (Or.inl rfl) (by decide)
  have hBC := hne (0, 2) (0, 0) (Or.inl rfl) (by decide)
  have hAD := hne (1, 0) (1, 2) (Or.inl rfl) (by decide)
  have hCD := hne (1, 1) (1, 2) (Or.inl rfl) (by decide)
  have hBD := hne (2, 0) (2, 1) (Or.inl rfl) (by decide)
  have e1 : color (1, 0) = color (0, 1) := h1 1 0
  have e2 : color (1, 1) = color (0, 0) := by
    apply h2
    show MO335895.cl (1, 1) = MO335895.cl (0, 0)
    decide
  have e3 : color (2, 0) = color (0, 2) := h1 2 0
  have e4 : color (2, 1) = color (1, 2) := h1 2 1
  rw [e1] at hAD
  rw [e2] at hCD
  rw [e3, e4] at hBD
  rcases MO335895.key (color (0, 1)) (color (0, 2)) (color (0, 0)) (color (1, 2)) with
    h' | h' | h' | h' | h' | h'
  · exact hAB h'
  · exact hAC h'
  · exact hBC h'
  · exact hAD h'
  · exact hBD h'
  · exact hCD h'
