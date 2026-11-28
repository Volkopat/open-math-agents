import OMAStatements.S_mo_475684
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A five-dimensional real Hermitian subspace with no rank-one matrix

The negative answer was recorded in July 2024 by Narutaka Ozawa and Michał Jan:
https://mathoverflow.net/questions/475684#comment1236569_475684
https://mathoverflow.net/questions/474920

We formalize it using a three-by-three witness, with actual real dimension and
complex matrix rank. This is a formalization of a known negative resolution.
-/

open Matrix
open scoped Matrix

namespace HermitianSubspace

/-- A real five-parameter family of Hermitian matrices. -/
def matrix (c : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(c 0 : ℂ), 0, (c 1 : ℂ) + (c 2 : ℂ) * Complex.I;
    0, (c 0 : ℂ), (c 3 : ℂ) + (c 4 : ℂ) * Complex.I;
    (c 1 : ℂ) - (c 2 : ℂ) * Complex.I,
      (c 3 : ℂ) - (c 4 : ℂ) * Complex.I, (c 0 : ℂ)]


def linearMap : (Fin 5 → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := matrix
  map_add' c d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, add_mul, sub_eq_add_neg] <;> ring
  map_smul' r c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Complex.real_smul, mul_sub, mul_assoc]

lemma linearMap_injective : Function.Injective linearMap := by
  intro c d h
  change matrix c = matrix d at h
  have hget (i j : Fin 3) : matrix c i j = matrix d i j := congrFun (congrFun h i) j
  funext i
  fin_cases i
  · simpa [matrix] using congrArg Complex.re (hget 0 0)
  · simpa [matrix] using congrArg Complex.re (hget 0 2)
  · simpa [matrix] using congrArg Complex.im (hget 0 2)
  · simpa [matrix] using congrArg Complex.re (hget 1 2)
  · simpa [matrix] using congrArg Complex.im (hget 1 2)

def space : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) := LinearMap.range linearMap

lemma space_finrank : Module.finrank ℝ space = 5 := by
  rw [space, LinearMap.finrank_range_of_inj linearMap_injective]
  simp

lemma one_mem_space : (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ space := by
  refine ⟨![1, 0, 0, 0, 0], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [linearMap, matrix, Matrix.one_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

lemma matrix_isHermitian (c : Fin 5 → ℝ) : (matrix c).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, star_add, star_sub, star_mul] <;> ring

lemma isHermitian_of_mem_space {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A ∈ space) :
    A.IsHermitian := by
  obtain ⟨c, rfl⟩ := hA
  exact matrix_isHermitian c


theorem rank_one_principal_minor_zero
    (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M.rank = 1)
    (f : Fin 2 → Fin 3) : (M.submatrix f f).det = 0 := by
  by_contra hdet
  have hr : (M.submatrix f f).rank = 2 := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
  have hle := M.rank_submatrix_le f f
  rw [hM, hr] at hle
  norm_num at hle


theorem matrix_rank_ne_one (c : Fin 5 → ℝ) : (matrix c).rank ≠ 1 := by
  intro hr
  have h01 := congrArg Complex.re
    (rank_one_principal_minor_zero (matrix c) hr ![0, 1])
  rw [Matrix.det_fin_two] at h01
  norm_num [matrix, Matrix.submatrix_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.succ,
    Complex.mul_re] at h01
  have h0 : c 0 = 0 := by nlinarith [sq_nonneg (c 0)]
  have h02 := congrArg Complex.re
    (rank_one_principal_minor_zero (matrix c) hr ![0, 2])
  rw [Matrix.det_fin_two] at h02
  norm_num [matrix, Matrix.submatrix_apply, h0,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.succ,
    Complex.mul_re, Complex.mul_im] at h02
  have h1 : c 1 = 0 := by nlinarith [sq_nonneg (c 1), sq_nonneg (c 2)]
  have h2 : c 2 = 0 := by nlinarith [sq_nonneg (c 1), sq_nonneg (c 2)]
  have h12 := congrArg Complex.re
    (rank_one_principal_minor_zero (matrix c) hr ![1, 2])
  rw [Matrix.det_fin_two] at h12
  norm_num [matrix, Matrix.submatrix_apply, h0,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.succ,
    Complex.mul_re, Complex.mul_im] at h12
  have h3 : c 3 = 0 := by nlinarith [sq_nonneg (c 3), sq_nonneg (c 4)]
  have h4 : c 4 = 0 := by nlinarith [sq_nonneg (c 3), sq_nonneg (c 4)]
  have hzero : matrix c = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix, h0, h1, h2, h3, h4]
  simp [hzero] at hr

end HermitianSubspace

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_475684.main) := by
  intro h
  obtain ⟨A, hA, hr⟩ := h 3 (by decide) HermitianSubspace.space
    (by simpa using HermitianSubspace.space_finrank)
    HermitianSubspace.one_mem_space
    (fun _ hA => HermitianSubspace.isHermitian_of_mem_space hA)
  obtain ⟨c, rfl⟩ := hA
  exact HermitianSubspace.matrix_rank_ne_one c hr
