import OMAStatements.S_arxiv_2412_01494
import Mathlib

namespace OMA.P_arxiv_2412_01494

open OMA.S_arxiv_2412_01494

/-- Standard D1Q3 discrete velocity stencil `c = (0, 1, -1)`. -/
def cD1Q3 : Fin 3 → ℤ := fun i =>
  match i.val with
  | 0 => 0
  | 1 => 1
  | _ => -1

/-- Strictly positive, non-symmetric doubly stochastic `3 × 3` collision matrix with
real eigenvalues `1, 1/2, 1/4`. -/
noncomputable def C1 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i.val, j.val with
    | 0, 0 => 2 / 3
    | 0, 1 => 1 / 6
    | 0, 2 => 1 / 6
    | 1, 0 => 1 / 12
    | 1, 1 => 7 / 12
    | 1, 2 => 1 / 3
    | 2, 0 => 1 / 4
    | 2, 1 => 1 / 4
    | _, _ => 1 / 2

/-- Distinct collision matrix `C2 = C1ᵀ`, which induces the identical D1Q3 finite difference
scheme on the conserved variable. -/
noncomputable def C2 : Matrix (Fin 3) (Fin 3) ℝ := C1.transpose

/-- Invertible moment matrix for `C1` (`det M1 = 9`). -/
def M1 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i.val, j.val with
    | 0, _ => 1
    | 1, 0 => -2
    | 1, _ => 1
    | 2, 2 => 2
    | _, _ => -1

/-- Invertible moment matrix for `C2` (`det M2 = 3`). -/
def M2 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i.val, j.val with
    | 0, _ => 1
    | 1, 0 => -1
    | 1, 1 => 1
    | 1, _ => 0
    | 2, 0 => 0
    | 2, 1 => -1
    | _, _ => 1

/-- Relaxation rates `s = (0, 1/2, 3/4)` (eigenvalues `1 - s_i = 1, 1/2, 1/4`). -/
noncomputable def sRates : Fin 3 → ℝ := fun i =>
  match i.val with
  | 0 => 0
  | 1 => 1 / 2
  | _ => 3 / 4

/-- Equilibrium moments `eq = (1, 0, 0)` (corresponding to uniform stationary density `(1/3,1/3,1/3)`). -/
def eqMom : Fin 3 → ℝ := fun i =>
  match i.val with
  | 0 => 1
  | _ => 0

lemma C1_valid : IsValidLBCollision C1 := by
  refine ⟨?_, ?_, M1, sRates, eqMom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [C1]
  · intro j; fin_cases j <;> simp [Fin.sum_univ_three, C1] <;> norm_num
  · rw [Matrix.det_fin_three]
    norm_num [M1]
  · intro j; fin_cases j <;> rfl
  · rfl
  · intro i hi; fin_cases i
    · exact absurd rfl hi
    · norm_num [sRates]
    · norm_num [sRates]
  · rfl
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, M1, C1, sRates, eqMom, Matrix.diagonal_apply] <;>
      norm_num

lemma C2_valid : IsValidLBCollision C2 := by
  refine ⟨?_, ?_, M2, sRates, eqMom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [C2, C1]
  · intro j; fin_cases j <;> simp [Fin.sum_univ_three, C2, C1] <;> norm_num
  · rw [Matrix.det_fin_three]
    norm_num [M2]
  · intro j; fin_cases j <;> rfl
  · rfl
  · intro i hi; fin_cases i
    · exact absurd rfl hi
    · norm_num [sRates]
    · norm_num [sRates]
  · rfl
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, M2, C2, C1, sRates, eqMom, Matrix.diagonal_apply] <;>
      norm_num

lemma fds_eq (ξ : ℝ) (_ : ξ ≠ 0) : fdsCharPoly cD1Q3 C1 ξ = fdsCharPoly cD1Q3 C2 ξ := by
  unfold fdsCharPoly C2
  set D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (fun i => ξ ^ cD1Q3 i)
  have hDt : D.transpose = D := Matrix.diagonal_transpose _
  calc (D * C1).charpoly
      = (C1 * D).charpoly := Matrix.charpoly_mul_comm D C1
    _ = (C1 * D.transpose).charpoly := by rw [hDt]
    _ = ((D * C1.transpose).transpose).charpoly := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = (D * C1.transpose).charpoly := Matrix.charpoly_transpose _

lemma C1_ne_C2 : C1 ≠ C2 := by
  intro h
  have h01 : C1 0 1 = C2 0 1 := congrFun (congrFun h 0) 1
  norm_num [C1, C2] at h01

end OMA.P_arxiv_2412_01494

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2412_01494.main) := by
  intro h
  have heq := h 3 OMA.P_arxiv_2412_01494.cD1Q3 OMA.P_arxiv_2412_01494.C1 OMA.P_arxiv_2412_01494.C2
    OMA.P_arxiv_2412_01494.C1_valid OMA.P_arxiv_2412_01494.C2_valid OMA.P_arxiv_2412_01494.fds_eq
  exact OMA.P_arxiv_2412_01494.C1_ne_C2 heq
