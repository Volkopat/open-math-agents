import OMAStatements.S_oeis_a377278
import Mathlib

-- Problem: A377278: Denominators in a harmonic triangle; q-analog of A126615, here q = 2.
-- Upstream: formal-conjectures statements/oeis-a377278.lean:0 (declaration OMA.S_oeis_a377278.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a377278

lemma OMA.aux_rd_pos (k : ℕ) : (0:ℚ) < OMA.S_oeis_a377278.rowDivisor (k+1) := by
  unfold OMA.S_oeis_a377278.rowDivisor
  have : (2:ℚ) ≤ 2^(k+1) := by
    calc (2:ℚ) = 2^1 := by norm_num
      _ ≤ 2^(k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

lemma OMA.aux_tele (r : ℕ) :
    row r = 1 - ∑ i ∈ Finset.range r, 1 / rowDivisor (i+2) := by
  induction r with
  | zero => simp [row, rowDivisor]; norm_num
  | succ n ih =>
    have h1 := OMA.aux_rd_pos n
    have h2 := OMA.aux_rd_pos (n+1)
    have hb : rowDivisor (n+1+1) = 2 * rowDivisor (n+1) + 1 := by
      unfold rowDivisor; ring
    rw [Finset.sum_range_succ, ← sub_sub, ← ih]
    unfold row
    rw [Finset.sum_range_succ]
    have e : n + 2 = n + 1 + 1 := rfl
    rw [e, hb] at *
    have h3 : (0:ℚ) < 2 * rowDivisor (n+1) + 1 := by linarith
    field_simp
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a377278.main := by
  intro r
  rw [OMA.aux_tele]
  have hne : ∀ i : Fin r, rowDivisor (i.val+2) ≠ 0 := fun i => (OMA.aux_rd_pos (i.val+1)).ne'
  have hdet : (Matrix.diagonal (fun i : Fin r => rowDivisor (i.val+2))).det = twoFactorial r := by
    rw [Matrix.det_diagonal]; rfl
  have hunit : IsUnit (Matrix.diagonal (fun i : Fin r => rowDivisor (i.val+2))).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hne i))
  letI : Invertible (Matrix.diagonal (fun i : Fin r => rowDivisor (i.val+2))) :=
    Matrix.invertibleOfIsUnitDet _ hunit
  have hinv : ⅟(Matrix.diagonal (fun i : Fin r => rowDivisor (i.val+2))) =
      Matrix.diagonal (fun i : Fin r => (rowDivisor (i.val+2))⁻¹) := by
    apply invOf_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hne i)
  have hp : principal r = Matrix.fromBlocks (Matrix.of fun _ _ => (1:ℚ)) (Matrix.of fun _ _ => 1)
      (Matrix.of fun _ _ => 1) (Matrix.diagonal (fun i : Fin r => rowDivisor (i.val+2))) := rfl
  have htf : twoFactorial r ≠ 0 := by rw [← hdet]; exact hunit.ne_zero
  rw [hp, Matrix.det_fromBlocks₂₂, hdet, mul_div_cancel_left₀ _ htf, Matrix.det_unique, hinv]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_range]
