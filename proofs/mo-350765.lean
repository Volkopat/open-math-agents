import OMAStatements.S_mo_350765
import Mathlib

-- Problem: mo-350765, is there a universal C with
-- |(A_ee)^{-1} - (B_ee)^{-1}| <= C |A^{-1} - B^{-1}| (max norms) for positive definite A, B and
-- every principal submatrix?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For s > 0 let A = [2 -s; -s s^2] and B = [5/4 -s/4; -s/4 s^2/4]. Both are positive
-- definite, A^{-1} = [1 1/s; 1/s 2/s^2] and B^{-1} = [1 1/s; 1/s 5/s^2], so
-- |A^{-1} - B^{-1}| = 3/s^2, while the 1 x 1 principal blocks give |1/2 - 4/5| = 3/10.
-- Hence 3/10 <= 3 C / s^2 for all s > 0, which fails for s^2 > 10 C.

open scoped Matrix.Norms.Elementwise

open Matrix

namespace MO350765

noncomputable def A (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2, -s; -s, s ^ 2]

noncomputable def B (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![5 / 4, -s / 4; -s / 4, s ^ 2 / 4]

noncomputable def P (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / s; 1 / s, 2 / s ^ 2]

noncomputable def Q (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / s; 1 / s, 5 / s ^ 2]

def e : Fin 1 ↪ Fin 2 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

theorem A_inv (s : ℝ) (hs : s ≠ 0) : (A s)⁻¹ = P s := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [A, P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.mulVec,
      dotProduct]
     try field_simp
     try ring)

theorem B_inv (s : ℝ) (hs : s ≠ 0) : (B s)⁻¹ = Q s := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [B, Q, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.mulVec,
      dotProduct]
     try field_simp
     try ring)

theorem ne_zero_cases (x : Fin 2 → ℝ) (hx : x ≠ 0) : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  apply hx
  ext i
  fin_cases i
  · exact hcon.1
  · exact hcon.2

theorem form_pos (s a b : ℝ) (hs : s ≠ 0) (h : a ≠ 0 ∨ b ≠ 0) (c : ℝ) (hc : 0 < c) :
    0 < a ^ 2 + c * (a - s * b) ^ 2 := by
  by_cases h0 : a = 0
  · have hb : b ≠ 0 := by
      rcases h with h | h
      · exact absurd h0 h
      · exact h
    have h2 : 0 < (s * b) ^ 2 := by positivity
    rw [h0]
    nlinarith [mul_pos hc h2]
  · have h1 : 0 < a ^ 2 := by positivity
    have h2 : 0 ≤ c * (a - s * b) ^ 2 := by positivity
    linarith

theorem A_pd (s : ℝ) (hs : s ≠ 0) : (A s).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A]
  · intro x hx
    have hval : star x ⬝ᵥ (A s *ᵥ x) = (x 0) ^ 2 + 1 * (x 0 - s * x 1) ^ 2 := by
      simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hval]
    exact form_pos s (x 0) (x 1) hs (ne_zero_cases x hx) 1 one_pos

theorem B_pd (s : ℝ) (hs : s ≠ 0) : (B s).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [B]
  · intro x hx
    have hval : star x ⬝ᵥ (B s *ᵥ x) = (x 0) ^ 2 + (1 / 4) * (x 0 - s * x 1) ^ 2 := by
      simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hval]
    exact form_pos s (x 0) (x 1) hs (ne_zero_cases x hx) (1 / 4) (by norm_num)

theorem A_sub (s : ℝ) : ((A s).submatrix e e)⁻¹ = !![1 / 2] := by
  have h : (A s).submatrix e e = !![2] := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [h]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply]

theorem B_sub (s : ℝ) : ((B s).submatrix e e)⁻¹ = !![4 / 5] := by
  have h : (B s).submatrix e e = !![5 / 4] := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [h]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply]

theorem PQ_norm (s : ℝ) (hs : s ≠ 0) : ‖P s - Q s‖ ≤ 3 / s ^ 2 := by
  have h3 : (0 : ℝ) ≤ 3 / s ^ 2 := by positivity
  have e00 : (P s - Q s) 0 0 = 0 := by simp [P, Q]
  have e01 : (P s - Q s) 0 1 = 0 := by simp [P, Q]
  have e10 : (P s - Q s) 1 0 = 0 := by simp [P, Q]
  have e11 : (P s - Q s) 1 1 = -(3 / s ^ 2) := by
    simp [P, Q]
    ring
  rw [Matrix.norm_le_iff h3]
  intro i j
  fin_cases i <;> fin_cases j
  · show ‖(P s - Q s) 0 0‖ ≤ 3 / s ^ 2
    rw [e00, norm_zero]
    exact h3
  · show ‖(P s - Q s) 0 1‖ ≤ 3 / s ^ 2
    rw [e01, norm_zero]
    exact h3
  · show ‖(P s - Q s) 1 0‖ ≤ 3 / s ^ 2
    rw [e10, norm_zero]
    exact h3
  · show ‖(P s - Q s) 1 1‖ ≤ 3 / s ^ 2
    rw [e11, norm_neg, Real.norm_eq_abs, abs_of_nonneg h3]

theorem lower : (3 / 10 : ℝ) ≤ ‖(!![1 / 2] - !![4 / 5] : Matrix (Fin 1) (Fin 1) ℝ)‖ := by
  have h4 : ‖((1 / 2 : ℝ) - 4 / 5)‖ ≤
      ‖(!![1 / 2] - !![4 / 5] : Matrix (Fin 1) (Fin 1) ℝ)‖ :=
    Matrix.norm_entry_le_entrywise_sup_norm
      (!![1 / 2] - !![4 / 5] : Matrix (Fin 1) (Fin 1) ℝ) (i := 0) (j := 0)
  rw [Real.norm_eq_abs] at h4
  have h5 := neg_le_abs ((1 / 2 : ℝ) - 4 / 5)
  linarith

end MO350765

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_350765.main) := by
  rintro ⟨C, hC, h⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 10 * C + 10 := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    rw [hs]
    linarith
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs1
    linarith
  have hs2 : 10 * C < s ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < s ^ 2 := by positivity
  have key := h 2 1 MO350765.e (MO350765.A s) (MO350765.B s) (MO350765.A_pd s hs0)
    (MO350765.B_pd s hs0)
  rw [MO350765.A_inv s hs0, MO350765.B_inv s hs0, MO350765.A_sub, MO350765.B_sub] at key
  have h5 : (3 / 10 : ℝ) ≤ C * (3 / s ^ 2) :=
    le_trans MO350765.lower
      (le_trans key (mul_le_mul_of_nonneg_left (MO350765.PQ_norm s hs0) hC.le))
  rw [← mul_div_assoc, le_div_iff₀ hpos] at h5
  nlinarith
