import OMAStatements.S_mo_40478

/-!
Adapted from @Genbox, merged PR #30064
(head 065cd083ab65e5423747659237e571c4e0162031).
Registered statement credit: @AkiRA-COM-FP, PR #13357.
The same axial matrix refutes both cyclic-diagonal assertions. Standard determinant
nonvanishing from a left inverse and uniform finite-index normalization replace
manual scalar and duplicated index calculations.
-/

open Matrix Set OMA.S_mo_40478
open scoped BigOperators

private theorem fin01 : (0 : Fin 3) ≠ 1 := by decide
private theorem fin02 : (0 : Fin 3) ≠ 2 := by decide
private theorem fin10 : (1 : Fin 3) ≠ 0 := by decide
private theorem fin12 : (1 : Fin 3) ≠ 2 := by decide
private theorem fin20 : (2 : Fin 3) ≠ 0 := by decide
private theorem fin21 : (2 : Fin 3) ≠ 1 := by decide

private def axial : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else if i = 2 ∧ j = 2 then 1 else 0

private theorem axial_sums (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) :
    let t := R 2 0 + R 2 1 + R 2 2
    let C := cyclicDiagonalSums (R.transpose * axial * R)
    C ⟨1, by decide⟩ + C ⟨2, by decide⟩ = t^2 - 1 ∧
      C ⟨1, by decide⟩ - C ⟨2, by decide⟩ = 2 * (R.det * t) := by
  let t := R 2 0 + R 2 1 + R 2 2
  have hRR : R * R.transpose = 1 := mul_eq_one_comm.mp hR
  have rowNorm : R 2 0 ^ 2 + R 2 1 ^ 2 + R 2 2 ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) hRR
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h
    simpa [pow_two] using h
  let U : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    if i = 2 then R j 0 + R j 1 + R j 2 else (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
  let V : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = 2 then 1 else R i j
  have hcol (j : Fin 3) : ∑ k, (R.transpose * R) k j = 1 := by
    rw [hR]
    simp [Matrix.one_apply]
  have hUV : U * R = V := by
    ext i j
    by_cases hi : i = 2
    · subst i
      rw [Matrix.mul_apply, Fin.sum_univ_three]
      simp [U, V, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] at hcol ⊢
      linear_combination hcol j
    · calc
        (U * R) i j = ((1 : Matrix (Fin 3) (Fin 3) ℝ) * R) i j := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          simp [U, hi]
        _ = V i j := by simp [V, hi]
  have hU : U.det = t := by
    rw [Matrix.det_fin_three]
    norm_num [fin01, fin02, fin10, fin12, fin20, fin21, U, Matrix.one_apply, t]
  have hdet : V.det = R.det * t := by
    rw [← hUV, Matrix.det_mul, hU, mul_comm]
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have h21 : (2 : Fin 3) + 1 = 0 := by decide
  have h12 : (1 : Fin 3) + 2 = 0 := by decide
  have h22 : (2 : Fin 3) + 2 = 1 := by decide
  dsimp
  constructor
  · norm_num [fin01, fin02, fin10, fin12, fin20, fin21, cyclicDiagonalSums, axial, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply, h11, h21, h12, h22]
    linear_combination -rowNorm
  · rw [Matrix.det_fin_three] at hdet
    norm_num [fin01, fin02, fin10, fin12, fin20, fin21, cyclicDiagonalSums, axial, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply, V, t, h11, h21, h12, h22] at hdet ⊢
    linear_combination 2 * hdet

private theorem axial_ne_zero (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) :
    cyclicDiagonalSums (R.transpose * axial * R) ≠ 0 := by
  intro hzero
  have h := axial_sums R hR
  rw [hzero] at h
  simp only [Pi.zero_apply, zero_add, sub_zero] at h
  have hdet : R.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hR
  obtain ⟨h₁, h₂⟩ := h
  have ht : R 2 0 + R 2 1 + R 2 2 = 0 := by
    have hp : R.det * (R 2 0 + R 2 1 + R 2 2) = 0 := by linarith
    exact (mul_eq_zero.mp hp).resolve_left hdet
  simp [ht] at h₁

private def turn : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  if i = j then if i = 1 then 1 else -1 else 0

theorem OMA.solution : type_of% @OMA.S_mo_40478.main := by
  constructor
  · intro h
    obtain ⟨R, hR, hz⟩ := h 3 axial
    exact axial_ne_zero R hR hz
  · intro h
    let v := cyclicDiagonalSums axial
    have hv : v ∈ orthogonalCyclicImage axial := by
      refine ⟨1, ?_, ?_, ?_⟩ <;> simp [v]
    have hneg : -v ∈ orthogonalCyclicImage axial := by
      refine ⟨turn, ?_, ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [fin01, fin02, fin10, fin12, fin20, fin21, turn, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply]
      · norm_num [fin01, fin02, fin10, fin12, fin20, fin21, turn, Matrix.det_fin_three]
      · funext ⟨i, hi⟩
        fin_cases i
        · exact (hi (by decide)).elim
        all_goals norm_num [fin01, fin02, fin10, fin12, fin20, fin21,
          cyclicDiagonalSums, axial, turn, v, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.transpose_apply, show (1 : Fin 3) + 1 = 2 by decide,
          show (2 : Fin 3) + 1 = 0 by decide, show (1 : Fin 3) + 2 = 0 by decide,
          show (2 : Fin 3) + 2 = 1 by decide]
    have hmid := h 3 axial hv hneg (show 0 ≤ (1/2 : ℝ) by norm_num)
      (show 0 ≤ (1/2 : ℝ) by norm_num) (by norm_num)
    have hz : (1/2 : ℝ) • v + (1/2 : ℝ) • (-v) = 0 := by
      rw [smul_neg, add_neg_cancel]
    rw [hz] at hmid
    obtain ⟨R, hR, _, hz'⟩ := hmid
    exact axial_ne_zero R hR hz'