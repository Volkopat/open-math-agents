import OMAStatements.S_oeis_a111967

open Matrix

namespace BC4F

open OMA.S_oeis_a111967

theorem window (i : ℕ) :
    2 ^ Nat.log 2 (i + 1) - 1 ≤ i ∧ i ≤ 2 * (2 ^ Nat.log 2 (i + 1) - 1) := by
  have h1 : 2 ^ Nat.log 2 (i + 1) ≤ i + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2' := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (i + 1)
  have h2 : i + 1 < 2 ^ Nat.log 2 (i + 1) * 2 := by
    rw [← pow_succ]
    exact h2'
  constructor <;> omega

theorem window_unique (i j r : ℕ) (hj : j + 1 = 2 ^ r) (h1 : j ≤ i) (h2 : i ≤ 2 * j) :
    j = 2 ^ Nat.log 2 (i + 1) - 1 := by
  have hl : Nat.log 2 (i + 1) = r := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ]
      omega
  rw [hl]
  omega

theorem mulVec_fred (n : ℕ) :
    corner n *ᵥ (fun j : Fin (n + 1) => fredholm j.val) = fun _ => 1 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, corner, Matrix.of_apply]
  have hw := window i.val
  have hj0 : 2 ^ Nat.log 2 (i.val + 1) - 1 < n + 1 := by
    have := i.isLt
    omega
  rw [Finset.sum_eq_single ⟨2 ^ Nat.log 2 (i.val + 1) - 1, hj0⟩]
  · have hf : fredholm (2 ^ Nat.log 2 (i.val + 1) - 1) = 1 := by
      unfold fredholm
      rw [if_pos (show ∃ r : ℕ, 2 ^ Nat.log 2 (i.val + 1) - 1 + 1 = 2 ^ r from
        ⟨Nat.log 2 (i.val + 1), by
          have := Nat.one_le_two_pow (n := Nat.log 2 (i.val + 1))
          omega⟩)]
    try simp only [Fin.val_mk]
    rw [if_pos hw, hf, one_mul]
  · intro j _ hne
    by_cases hc : j.val ≤ i.val ∧ i.val ≤ 2 * j.val
    · have hf : fredholm j.val = 0 := by
        unfold fredholm
        rw [if_neg]
        rintro ⟨r, hr⟩
        apply hne
        ext
        exact window_unique i.val j.val r hr hc.1 hc.2
      rw [hf, mul_zero]
    · rw [if_neg hc, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem corner_det (n : ℕ) : (corner n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (corner n)]
  · apply Finset.prod_eq_one
    intro i _
    have h : i.val ≤ i.val ∧ i.val ≤ 2 * i.val := ⟨le_rfl, by omega⟩
    simp only [corner, Matrix.of_apply, if_pos h]
  · intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hlt' : i.val < j.val := hlt
    simp only [corner, Matrix.of_apply]
    rw [if_neg (show ¬ (j.val ≤ i.val ∧ i.val ≤ 2 * j.val) by omega)]

end BC4F

theorem OMA.solution : type_of% @OMA.S_oeis_a111967.main := by
  intro n
  have hdet : IsUnit (OMA.S_oeis_a111967.corner n).det := by
    rw [BC4F.corner_det]
    exact isUnit_one
  have hinv : (OMA.S_oeis_a111967.corner n)⁻¹ * OMA.S_oeis_a111967.corner n = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have key : (OMA.S_oeis_a111967.corner n)⁻¹ *ᵥ (fun _ => (1 : ℚ)) =
      fun j : Fin (n + 1) => OMA.S_oeis_a111967.fredholm j.val := by
    rw [← BC4F.mulVec_fred n, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h := congrFun key (Fin.last n)
  simp only [Matrix.mulVec, dotProduct, mul_one, Fin.val_last] at h
  exact h
