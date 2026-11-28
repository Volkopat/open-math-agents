import OMAStatements.S_oeis_a114278

open Matrix

namespace BC4I

open OMA.S_oeis_a114278

def ev (n : ℕ) : Fin (n + 1) → ℚ := fun j => if j.val = 0 then 1 else 0

theorem entry_zero (i : ℕ) : entry i 0 = 1 := by
  unfold entry
  rw [Finset.sum_range_one]
  simp

theorem entry_lt (i k : ℕ) (h : i < k) : entry i k = 0 := by
  unfold entry
  apply Finset.sum_eq_zero
  intro j _
  rw [Nat.choose_eq_zero_of_lt (by omega : i - j < k), mul_zero]

theorem entry_self (i : ℕ) : entry i i = 1 := by
  unfold entry
  rw [Finset.sum_eq_single 0]
  · rw [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self]
    all_goals norm_num
  · intro b hb hb0
    rw [Finset.mem_range] at hb
    rw [Nat.choose_eq_zero_of_lt (by omega : i - b < i), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : 0 < i + 1)) h

theorem corner_apply {n : ℕ} (i j : Fin (n + 1)) : corner n i j = (entry i.val j.val : ℚ) := rfl

theorem ev_zero (n : ℕ) (h : 0 < n + 1) : ev n ⟨0, h⟩ = 1 := by
  show (if (0 : ℕ) = 0 then (1 : ℚ) else 0) = 1
  exact if_pos rfl

theorem ev_ne (n : ℕ) (j : Fin (n + 1)) (hj : j.val ≠ 0) : ev n j = 0 := by
  show (if j.val = 0 then (1 : ℚ) else 0) = 0
  exact if_neg hj

theorem mulVec_ev (n : ℕ) : corner n *ᵥ ev n = fun _ => 1 := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · rw [corner_apply, ev_zero, mul_one]
    show ((entry i.val 0 : ℕ) : ℚ) = 1
    rw [entry_zero, Nat.cast_one]
  · intro j _ hj
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
    rw [ev_ne n j hj', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem corner_det (n : ℕ) : (corner n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (corner n)]
  · apply Finset.prod_eq_one
    intro i _
    rw [corner_apply, entry_self, Nat.cast_one]
  · intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hlt' : i.val < j.val := hlt
    rw [corner_apply, entry_lt i.val j.val hlt', Nat.cast_zero]

end BC4I

theorem OMA.solution : type_of% @OMA.S_oeis_a114278.main := by
  intro n
  have hdet : IsUnit (OMA.S_oeis_a114278.corner n).det := by
    rw [BC4I.corner_det]
    exact isUnit_one
  have hinv : (OMA.S_oeis_a114278.corner n)⁻¹ * OMA.S_oeis_a114278.corner n = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have key : (OMA.S_oeis_a114278.corner n)⁻¹ *ᵥ (fun _ => (1 : ℚ)) = BC4I.ev n := by
    rw [← BC4I.mulVec_ev n, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h := congrFun key (Fin.last n)
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  rw [h]
  rcases n with _ | m
  · show (if (0 : ℕ) = 0 then (1 : ℚ) else 0) = 0 ^ 0
    rw [if_pos rfl, pow_zero]
  · rw [BC4I.ev_ne (m + 1) (Fin.last (m + 1)) (by rw [Fin.val_last]; omega), pow_succ, mul_zero]
