import OMAStatements.S_mo_266728

-- Retains @connoranderson's original simplex characterization (statement PR #24207).
-- @Genbox registered the alternative main proof in PR #28389.
-- Standard inverse-sign and determinant APIs replace two algebraic arguments.

namespace OMA.S_mo_266728
open Matrix Finset Set

private lemma column_hull {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    convexHull ℝ (Set.range A.col) = (A.mulVec) '' stdSimplex ℝ (Fin n) := by
  rw [←convexHull_rangle_single_eq_stdSimplex]
  change _ = (A.mulVecLin : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) '' _
  rw [LinearMap.image_convexHull,←Set.range_comp]
  congr 2
  funext j
  exact (Matrix.mulVec_single_one A j).symm

private lemma total {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (h : ∀ j, ∑ i, A i j=1) : ∑ i, (A *ᵥ x) i = ∑ i, x i := by
  simp only [mulVec,dotProduct]
  rw [sum_comm]
  simp_rw [←Finset.sum_mul,h,one_mul]

private lemma adj_sign {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    0 ≤ A⁻¹ i j ↔ 0 ≤ A.det*A.adjugate i j := by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul,
    mul_nonneg_iff, inv_nonneg, inv_nonpos]

private lemma hull_test {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    convexHull ℝ (Set.range A.col) ∩ {v : Fin n → ℝ | ∀ i, 0≤v i} = stdSimplex ℝ (Fin n) ↔
    (∀ j, ∑ i, A i j=1) ∧ A.det≠0 ∧ ∀ i j, 0≤A.det*A.adjugate i j := by
  rw [column_hull]
  constructor
  · intro h
    have vertices (j : Fin n) : ∃ w ∈ stdSimplex ℝ (Fin n), A *ᵥ w=Pi.single j 1 := by
      have hj := single_mem_stdSimplex ℝ j
      rw [←h] at hj
      exact hj.1
    choose w hw hAw using vertices
    let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => w j i)
    have hAB : A*B=1 := by
      ext i j
      simpa only [Matrix.mul_apply,B,Matrix.of_apply,Matrix.mulVec, dotProduct,Pi.single_apply,
        Matrix.one_apply,eq_comm] using congrFun (hAw j) i
    have hdet : A.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hAB
    have hB : A⁻¹=B := Matrix.inv_eq_right_inv hAB
    have hBA : B*A=1 := hB ▸ Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
    refine ⟨?_,hdet,fun i j => (adj_sign A i j).mp (hB ▸ (hw j).1 i)⟩
    intro j
    have he : B *ᵥ A.col j = Pi.single j 1 := by
      funext i
      have hh := congrFun₂ hBA i j
      simpa only [Matrix.mul_apply,Matrix.one_apply,Pi.single_apply,Matrix.mulVec,dotProduct,Matrix.col_apply,eq_comm] using hh
    have ht := total B (A.col j) (fun k => (hw k).2)
    rw [he] at ht
    simpa [Matrix.col_apply] using ht.symm
  · rintro ⟨ha,hd,hco⟩
    have hi := isUnit_iff_ne_zero.mpr hd
    ext v
    constructor
    · rintro ⟨⟨w,hw,rfl⟩,hn⟩
      exact ⟨hn,(total A w ha).trans hw.2⟩
    · intro hv
      refine ⟨⟨A⁻¹ *ᵥ v,⟨?_,?_⟩,?_⟩,hv.1⟩
      · intro i
        change 0 ≤ ∑ j,A⁻¹ i j*v j
        exact Finset.sum_nonneg fun j _ => mul_nonneg ((adj_sign A i j).mpr (hco i j)) (hv.1 j)
      · have he := total A (A⁻¹ *ᵥ v) ha
        rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hi,Matrix.one_mulVec] at he
        exact he.symm.trans hv.2
      · rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hi,Matrix.one_mulVec]

end OMA.S_mo_266728

open OMA.S_mo_266728

theorem OMA.solution : type_of% @OMA.S_mo_266728.main := by
  intro n A
  exact and_congr_right fun _ => hull_test A

