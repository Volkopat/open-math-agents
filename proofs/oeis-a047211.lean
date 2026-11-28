import OMAStatements.S_oeis_a047211
import Mathlib

open OMA.S_oeis_a047211

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a047211.main) := by
  intro h
  have hp : (M 1).charpoly = Polynomial.X - Polynomial.C (1 : ℚ) := by
    rw [Matrix.charpoly, Matrix.det_eq_elem_of_subsingleton _ 0, Matrix.charmatrix_apply_eq]
    simp [M]
  have hi : Irreducible (M 1).charpoly := hp.symm ▸ Polynomial.irreducible_X_sub_C 1
  exact (by decide : ¬ ((1 : ℕ) % 5 = 2 ∨ 1 % 5 = 4)) ((h 1 (by decide)).1 hi)