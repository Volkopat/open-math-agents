import OMAStatements.S_oeis_a086205
import Mathlib

namespace OMA.S_oeis_a086205

open Finset

lemma gchoose_eq (x : ℂ) (j : ℕ) : gchoose x j = Ring.choose x j := by
  rw [Ring.choose_eq_smul, gchoose]
  have h : (descPochhammer ℂ j).eval x = (descPochhammer ℤ j).smeval x := by
    rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      descPochhammer_map]
  rw [h, div_eq_inv_mul, Algebra.smul_def]
  simp

lemma gchoose_add (x y : ℂ) (j : ℕ) :
    gchoose (x + y) j = ∑ ij ∈ antidiagonal j, gchoose x ij.1 * gchoose y ij.2 := by
  simp only [gchoose_eq]
  exact Ring.add_choose_eq j (Commute.all _ _)

lemma gchoose_nat (m j : ℕ) : gchoose (m : ℂ) j = ((m.choose j : ℕ) : ℂ) := by
  rw [gchoose_eq, Ring.choose_natCast]


lemma main_aux (n : ℕ) (z : ℂ) :
    Matrix.det (Matrix.of fun i j : Fin (n + 1) => gchoose ((i.val : ℂ) ^ 2 + z) j.val)
      = (a n : ℂ) := by
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i k => (((i.val ^ 2).choose k.val : ℕ) : ℂ) with hP
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun k j => if k.val ≤ j.val then gchoose z (j.val - k.val) else 0 with hU
  have hM : (Matrix.of fun i j : Fin (n + 1) => gchoose ((i.val : ℂ) ^ 2 + z) j.val) = P * U := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, hP, hU]
    have h1 : ((i.val : ℂ) ^ 2) = (((i.val ^ 2 : ℕ)) : ℂ) := by push_cast; ring
    rw [h1, gchoose_add]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [gchoose_nat]
    have hj := j.isLt
    have : ∑ k ∈ range (j.val + 1), ((i.val ^ 2).choose k : ℂ) * gchoose z (j.val - k)
        = ∑ k ∈ range (n + 1), ((i.val ^ 2).choose k : ℂ) * (if k ≤ j.val then gchoose z (j.val - k) else 0) := by
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    rw [this, ← Fin.sum_univ_eq_sum_range (fun k => ((i.val ^ 2).choose k : ℂ) * (if k ≤ j.val then gchoose z (j.val - k) else 0)) (n + 1)]
  have hU1 : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · simp [hU, gchoose_eq]
    · intro i j hij
      simp only [hU, Matrix.of_apply]
      rw [if_neg]
      exact not_le.mpr hij
  rw [hM, Matrix.det_mul, hU1, mul_one, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin n, P 0 j.succ = 0 := by
    intro j
    simp [hP]
  simp only [hz, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [hP, Matrix.of_apply, Fin.val_zero]
  simp only [Fin.val_zero, zero_pow two_ne_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
    Fin.succAbove_zero, pow_zero]
  unfold a
  have h := RingHom.map_det (Int.castRingHom ℂ)
    (Matrix.of fun i j : Fin n => (((i.val + 1) ^ 2).choose (j.val + 1) : ℤ))
  rw [eq_intCast] at h
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [h]
  congr 1

end OMA.S_oeis_a086205

theorem OMA.solution : type_of% @OMA.S_oeis_a086205.main := by
  intro n z
  exact OMA.S_oeis_a086205.main_aux n z
