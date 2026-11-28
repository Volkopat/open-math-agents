import OMAStatements.S_mo_362974
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Upper bound for smallest eigenvalue of infinite family of graphs

Question by Yahav Boneh on MathOverflow, 13 June 2020.
https://mathoverflow.net/questions/362974/upper-bound-for-smallest-eigenvalue-of-infinite-family-of-graphs

Formal statement and earlier edge-bound development credited to @etaubman.
Original half-shift proof credited to @grp06 (#27506).
-/

open OMA.S_mo_362974 (adjacency)

theorem OMA.solution : type_of% @OMA.S_mo_362974.main := by
  classical
  intro n G _ _ edges _
  refine ⟨-(1 / 2 : ℝ), by norm_num, 0, ?_⟩
  intro i _
  obtain ⟨u, v, huv⟩ := edges i
  let A := adjacency (G i)
  let C : Matrix (Fin (n i)) (Fin (n i)) ℝ := A + (1 / 2 : ℝ) • 1
  have hdiag (w : Fin (n i)) : C w w = (1 / 2 : ℝ) := by
    simp [C, A, adjacency]
  have hentry {x y : Fin (n i)} (hxy : (G i).Adj x y) : C x y = 1 := by
    simp [C, A, adjacency, hxy, hxy.ne]
  have hnot : ¬ C.PosSemidef := by
    intro h
    have hdet := (h.submatrix ![u, v]).det_nonneg
    rw [Matrix.det_fin_two] at hdet
    norm_num [Matrix.submatrix_apply, hdiag, hentry huv, hentry huv.symm] at hdet
  have hA : A.IsHermitian := (G i).isHermitian_adjMatrix ℝ
  have hC : C.IsHermitian :=
    hA.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all (1 / 2 : ℝ)))
  obtain ⟨j, hj⟩ : ∃ j, hC.eigenvalues j < 0 := by
    simpa only [hC.posSemidef_iff_eigenvalues_nonneg, Pi.le_def, Pi.zero_apply, not_forall, not_le] using hnot
  have heigen : Module.End.HasEigenvalue C.toLin' (hC.eigenvalues j) := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin']
    exact hC.eigenvalues_mem_spectrum_real j
  have hshift : C.toLin' = A.toLin' + (1 / 2 : ℝ) • LinearMap.id := by
    simp only [C, map_add, map_smul, Matrix.toLin'_one]
  rw [hshift, Module.End.hasEigenvalue_add_iff, Matrix.toLin'_apply'] at heigen
  exact ⟨hC.eigenvalues j - 1 / 2, by linarith, heigen⟩
