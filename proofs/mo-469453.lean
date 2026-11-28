import OMAStatements.S_mo_469453
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
A four-dimensional counterexample. Let A=diag(0,1,-1,i), let U be the real
Sylvester Hadamard matrix divided by 2, and let B=UAU. Both matrices are normal
and their common spectrum is {0,1,-1,i}. The two commutator determinants are
-1 and 0, respectively, so their ranks differ.

The question was previously answered negatively by Jordan Payette (2024) in
the linked cross-post, using a different explicit real-matrix counterexample:
https://math.stackexchange.com/a/4902130
This proof verifies the Hadamard-conjugate witness against the full source.
-/

namespace OMA.S_mo_469453

open scoped Matrix

private noncomputable def diagonalValues : Fin 4 → ℂ := ![0, 1, -1, Complex.I]

private noncomputable def matrixA : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal diagonalValues

private noncomputable def matrixU : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1 / 2, 1 / 2, 1 / 2, 1 / 2;
     1 / 2, -1 / 2, 1 / 2, -1 / 2;
     1 / 2, 1 / 2, -1 / 2, -1 / 2;
     1 / 2, -1 / 2, -1 / 2, 1 / 2]

private noncomputable def matrixB : Matrix (Fin 4) (Fin 4) ℂ :=
  matrixU * matrixA * matrixU

private theorem matrixU_square : matrixU * matrixU = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixU, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private theorem matrixU_adjoint : matrixUᴴ = matrixU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixU, Matrix.conjTranspose_apply, map_ofNat]

private theorem matrixA_normal : IsStarNormal matrixA := by
  refine ⟨?_⟩
  change matrixAᴴ * matrixA = matrixA * matrixAᴴ
  simp [matrixA, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, mul_comm]

private theorem sandwich_mul (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    (matrixU * X * matrixU) * (matrixU * Y * matrixU) = matrixU * (X * Y) * matrixU := by
  have hu (Z : Matrix (Fin 4) (Fin 4) ℂ) : matrixU * (matrixU * Z) = Z := by
    rw [← mul_assoc, matrixU_square, one_mul]
  simp only [mul_assoc, hu]

private theorem matrixB_normal : IsStarNormal matrixB := by
  refine ⟨?_⟩
  change matrixBᴴ * matrixB = matrixB * matrixBᴴ
  have hb : matrixBᴴ = matrixU * matrixAᴴ * matrixU := by
    simp only [matrixB, Matrix.conjTranspose_mul, matrixU_adjoint, mul_assoc]
  rw [hb, matrixB, sandwich_mul, sandwich_mul]
  exact congrArg (fun X => matrixU * X * matrixU) matrixA_normal.star_comm_self.eq

private noncomputable def unitU : (Matrix (Fin 4) (Fin 4) ℂ)ˣ :=
  ⟨matrixU, matrixU, matrixU_square, matrixU_square⟩

private theorem spectrum_matrixB : spectrum ℂ matrixB = spectrum ℂ matrixA := by
  exact spectrum.units_conjugate (u := unitU)

private theorem matrixA_spectrum :
    ∀ z ∈ spectrum ℂ matrixA, z.im = 0 ∨ ‖z‖ = 1 := by
  intro z hz
  rw [matrixA, spectrum_diagonal] at hz
  obtain ⟨i, rfl⟩ := hz
  fin_cases i <;> simp [diagonalValues]

private theorem matrixB_spectrum :
    ∀ z ∈ spectrum ℂ matrixB, z.im = 0 ∨ ‖z‖ = 1 := by
  rw [spectrum_matrixB]
  exact matrixA_spectrum


private theorem matrixB_eq : matrixB =
    !![Complex.I/4, -1/2-Complex.I/4, 1/2-Complex.I/4, Complex.I/4;
       -1/2-Complex.I/4, Complex.I/4, Complex.I/4, 1/2-Complex.I/4;
       1/2-Complex.I/4, Complex.I/4, Complex.I/4, -1/2-Complex.I/4;
       Complex.I/4, 1/2-Complex.I/4, -1/2-Complex.I/4, Complex.I/4] := by
  ext i j
  change ((matrixU * Matrix.diagonal diagonalValues) * matrixU) i j = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixU, diagonalValues,
      Fin.sum_univ_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

private theorem commutator_eq : matrixA * matrixB - matrixB * matrixA =
    !![0, 1/2+Complex.I/4, 1/2-Complex.I/4, 1/4;
       -1/2-Complex.I/4, 0, Complex.I/2, 1/4-3*Complex.I/4;
       -1/2+Complex.I/4, -Complex.I/2, 0, 1/4+3*Complex.I/4;
       -1/4, -1/4+3*Complex.I/4, -1/4-3*Complex.I/4, 0] := by
  rw [matrixB_eq]
  ext i j
  simp only [Matrix.sub_apply, matrixA, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalValues, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

private theorem adjoint_commutator_eq : matrixAᴴ * matrixB - matrixB * matrixAᴴ =
    !![0, 1/2+Complex.I/4, 1/2-Complex.I/4, -1/4;
       -1/2-Complex.I/4, 0, Complex.I/2, 3/4+Complex.I/4;
       -1/2+Complex.I/4, -Complex.I/2, 0, 3/4-Complex.I/4;
       1/4, -3/4-Complex.I/4, -3/4+Complex.I/4, 0] := by
  rw [matrixB_eq]
  ext i j
  simp only [Matrix.sub_apply, matrixA, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalValues, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Matrix.conjTranspose_apply]

private theorem succAbove_four (i : Fin 4) (j : Fin 3) :
    i.succAbove j =
      (!![1, 2, 3; 0, 2, 3; 0, 1, 3; 0, 1, 2] : Matrix (Fin 4) (Fin 3) (Fin 4)) i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem det_commutator : (matrixA * matrixB - matrixB * matrixA).det = -1 := by
  rw [commutator_eq, Matrix.det_succ_row_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_four]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.succ, Complex.ext_iff,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

private theorem det_adjoint_commutator : (matrixAᴴ * matrixB - matrixB * matrixAᴴ).det = 0 := by
  rw [adjoint_commutator_eq, Matrix.det_succ_row_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_four]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.succ, Complex.ext_iff,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

private theorem det_ne_zero_of_full_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (h : A.rank = Fintype.card ι) : A.det ≠ 0 := by
  have hlin : LinearIndependent ℂ A.col := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    simpa only [Set.finrank, ← A.rank_eq_finrank_span_cols] using h.symm
  exact ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hlin)).ne_zero

private theorem rank_lt_of_det_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (h : A.det = 0) : A.rank < Fintype.card ι := by
  have hle := A.rank_le_card_width
  have hne : A.rank ≠ Fintype.card ι := by
    intro heq
    exact det_ne_zero_of_full_rank A heq h
  exact lt_of_le_of_ne hle hne

private theorem rank_comparison_of_determinants
    (C D : Matrix (Fin 4) (Fin 4) ℂ) (hC : C.det = -1) (hD : D.det = 0) :
    D.rank < C.rank := by
  have hc : C.rank = 4 := by
    simpa only [Fintype.card_fin] using
      Matrix.rank_of_det_ne_zero (A := C) (by rw [hC]; exact neg_ne_zero.mpr one_ne_zero)
  rw [hc]
  simpa only [Fintype.card_fin] using rank_lt_of_det_zero D hD

private theorem commutator_rank_strict :
    (matrixAᴴ * matrixB - matrixB * matrixAᴴ).rank <
      (matrixA * matrixB - matrixB * matrixA).rank :=
  rank_comparison_of_determinants _ _ det_commutator det_adjoint_commutator


end OMA.S_mo_469453

open OMA.S_mo_469453 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_469453.main) := by
  intro h
  exact (ne_of_gt commutator_rank_strict)
    (h 4 matrixA matrixB matrixA_normal matrixB_normal matrixA_spectrum matrixB_spectrum)
