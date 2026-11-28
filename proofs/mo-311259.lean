import OMAStatements.S_mo_311259
import Mathlib

-- Problem: mo-311259, is the block matrix [E B; -B 0] (E the endpoint-damped diagonal matrix
-- with entries -a, a > 0) always diagonalizable over the complex numbers?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For d = 1, a = 2 and B = [1] the matrix is M = [-2 1; -1 0], and (M + 1)^2 = 0. If
-- M = P D Q with D diagonal and Q the inverse of P, then (D + 1)^2 = 0, so D = -1 and M = -1,
-- contradicting the off-diagonal entry 1.

namespace MO311259

open OMA.S_mo_311259 Matrix

def B : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1

theorem M11 : blockMatrix 1 2 B (Sum.inl 0) (Sum.inl 0) = -2 := by
  simp [blockMatrix, endpointMatrix]

theorem M12 : blockMatrix 1 2 B (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp [blockMatrix, B]

theorem M21 : blockMatrix 1 2 B (Sum.inr 0) (Sum.inl 0) = -1 := by
  simp [blockMatrix, B]

theorem M22 : blockMatrix 1 2 B (Sum.inr 0) (Sum.inr 0) = 0 := by
  simp [blockMatrix]

theorem sq_zero : (blockMatrix 1 2 B + 1) * (blockMatrix 1 2 B + 1) = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    (have hi : i = 0 := Subsingleton.elim _ _
     have hj : j = 0 := Subsingleton.elim _ _
     subst hi hj
     simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply, M11, M12, M21, M22]
     try norm_num)

theorem nil_diag {ι : Type} [Fintype ι] [DecidableEq ι] (M P Q : Matrix ι ι ℂ) (e : ι → ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hM : M = P * diagonal e * Q)
    (hN : (M + 1) * (M + 1) = 0) : M = -1 := by
  subst hM
  have hQP' : ∀ Y : Matrix ι ι ℂ, Q * (P * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have h1 : P * diagonal e * Q + 1 = P * (diagonal e + 1) * Q := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ]
  have key : Q * ((P * diagonal e * Q + 1) * (P * diagonal e * Q + 1)) * P =
      (diagonal e + 1) * (diagonal e + 1) := by
    rw [h1]
    simp only [Matrix.mul_assoc, hQP', hQP, Matrix.mul_one]
  have h2 : (diagonal e + 1 : Matrix ι ι ℂ) * (diagonal e + 1) = 0 := by
    rw [← key, hN, Matrix.mul_zero, Matrix.zero_mul]
  have hD : (diagonal e + 1 : Matrix ι ι ℂ) = diagonal (fun i => e i + 1) := by
    ext i j
    by_cases h : i = j
    · rw [h]
      simp
    · simp [h]
  have h3 : ∀ i, e i = -1 := by
    intro i
    have h5 := congrFun (congrFun h2 i) i
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at h5
    have h6 : (e i + 1) * (e i + 1) = 0 := h5
    have h7 := mul_self_eq_zero.mp h6
    linear_combination h7
  have h4 : (diagonal e : Matrix ι ι ℂ) = -1 := by
    ext i j
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, h3]
      simp
    · rw [Matrix.diagonal_apply_ne _ h]
      simp [h]
  rw [h4, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hPQ]

end MO311259

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_311259.main) := by
  intro h
  obtain ⟨P, Q, e, hPQ, hQP, hM⟩ := h 1 one_pos 2 two_pos MO311259.B
  have hneg := MO311259.nil_diag _ P Q e hPQ hQP hM MO311259.sq_zero
  have h12 := congrFun (congrFun hneg (Sum.inl 0)) (Sum.inr 0)
  rw [MO311259.M12] at h12
  simp at h12
