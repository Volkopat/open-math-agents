import OMAStatements.S_oeis_a115526

/-!
# Proof of OEIS A115526

We prove that for every `n : ℕ`, the row sum of the last row of `(corner n)⁻¹`
equals `zeros (n + 2)` (the number of `0`-bits in the binary expansion of `n + 2`).

Proof outline:
1. `zeros (2 * m) = zeros m + 1` for `m ≥ 1`, and `zeros (2 * m + 1) = zeros m` for `m ≥ 1`,
   hence `zeros (2 * m + 1) + 1 = zeros (2 * m)`.
2. Define the vector `v : Fin (n + 1) → ℚ := fun i => (zeros (i.val + 2) : ℚ)`.
   We check directly that `corner n *ᵥ v = fun _ => 1`:
   - For `i = 0`: `1 * zeros 2 = 1`.
   - For odd `i`: `-1 * (zeros (i + 2) - zeros (i + 1)) = -1 * (-1) = 1`.
   - For even `i > 0`: `1 * (zeros (i + 2) - zeros (i / 2 + 1)) = 1 * 1 = 1`.
3. Since `corner n` is lower-triangular with diagonal entries `±1`, its determinant is
   `∏ i, sign i.val ≠ 0`, so `corner n` is invertible. Multiplying `corner n *ᵥ v = 1`
   on the left by `(corner n)⁻¹` yields `(corner n)⁻¹ *ᵥ (fun _ => 1) = v`, and evaluating
   at `Fin.last n` gives `∑ j, (corner n)⁻¹ (Fin.last n) j = zeros (n + 2)`.
-/

namespace OMA.A115526Proof

open OMA.S_oeis_a115526 Matrix Finset

private lemma zeros_two : zeros 2 = 1 := by decide

private lemma zeros_two_mul (m : ℕ) (hm : 0 < m) : zeros (2 * m) = zeros m + 1 := by
  unfold zeros
  have hpos : 0 < 2 * m := by omega
  rw [Nat.digits_def' (by decide : 2 ≤ 2) hpos]
  have hmod : (2 * m) % 2 = 0 := by omega
  have hdiv : (2 * m) / 2 = m := by omega
  rw [hmod, hdiv, List.count_cons]
  simp

private lemma zeros_two_mul_add_one (m : ℕ) : zeros (2 * m + 1) = zeros m := by
  unfold zeros
  have hpos : 0 < 2 * m + 1 := by omega
  rw [Nat.digits_def' (by decide : 2 ≤ 2) hpos]
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hmod, hdiv, List.count_cons]
  simp

private lemma corner_lower_tri (n : ℕ) :
    (corner n).IsLowerTriangular := by
  intro i j hij
  unfold corner
  simp only [Matrix.of_apply]
  have hne : j ≠ i := ne_of_gt hij
  rw [if_neg hne, zero_sub]
  by_cases hi : 0 < i.val
  · rw [if_pos hi]
    have hne2 : j ≠ earlierCol i := by
      intro h
      have hv := congrArg Fin.val h
      simp only [earlierCol, earlier] at hv
      have : i.val < j.val := hij
      split_ifs at hv <;> omega
    rw [if_neg hne2, neg_zero]
  · rw [if_neg hi, neg_zero]

private lemma corner_det_ne_zero (n : ℕ) : (corner n).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular (corner n) (corner_lower_tri n)]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  unfold corner
  simp only [Matrix.of_apply, ↓reduceIte]
  by_cases hi : 0 < i.val
  · rw [if_pos hi]
    have hne : i ≠ earlierCol i := by
      intro h
      have hv := congrArg Fin.val h
      simp only [earlierCol, earlier] at hv
      split_ifs at hv <;> omega
    rw [if_neg hne, sub_zero]
    unfold sign; split_ifs <;> norm_num
  · rw [if_neg hi, sub_zero]
    unfold sign; split_ifs <;> norm_num

private lemma corner_mulVec_zeros (n : ℕ) :
    corner n *ᵥ (fun i : Fin (n + 1) => (zeros (i.val + 2) : ℚ)) = fun _ => 1 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, corner, Matrix.of_apply]
  by_cases hi0 : i.val = 0
  · rw [Finset.sum_eq_single i]
    · simp only [hi0, lt_self_iff_false, ↓reduceIte, sub_zero, sign, Nat.zero_mod, one_mul,
        zero_add, zeros_two, Nat.cast_one]
    · intro j _ hji
      simp only [hji, hi0, lt_self_iff_false, ↓reduceIte, sub_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
    have hne : earlierCol i ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp only [earlierCol, earlier] at hv
      split_ifs at hv <;> omega
    have hsum : ∑ j : Fin (n + 1),
        ((if j = i then sign i.val else 0) -
          if 0 < i.val then if j = earlierCol i then sign i.val else 0 else 0) *
          (zeros (j.val + 2) : ℚ) =
        sign i.val * (zeros (i.val + 2) : ℚ) -
        sign i.val * (zeros ((earlierCol i).val + 2) : ℚ) := by
      have h1 : ∀ j : Fin (n + 1),
          ((if j = i then sign i.val else 0) -
            if 0 < i.val then if j = earlierCol i then sign i.val else 0 else 0) *
            (zeros (j.val + 2) : ℚ) =
          (if j = i then sign i.val * (zeros (j.val + 2) : ℚ) else 0) -
          (if j = earlierCol i then sign i.val * (zeros (j.val + 2) : ℚ) else 0) := by
        intro j
        rw [if_pos hipos]
        split_ifs <;> ring
      simp_rw [h1]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hsum]
    rcases Nat.mod_two_eq_zero_or_one i.val with hev | hodd
    · have hs : sign i.val = 1 := by simp [sign, hev]
      have hear : (earlierCol i).val + 2 = i.val / 2 + 1 := by
        simp only [earlierCol, earlier, hev, ↓reduceIte]; omega
      have h2m : i.val + 2 = 2 * (i.val / 2 + 1) := by omega
      rw [hs, hear, h2m, zeros_two_mul (i.val / 2 + 1) (by omega)]
      push_cast; ring
    · have hs : sign i.val = -1 := by simp [sign, hodd]
      have hear : (earlierCol i).val + 2 = i.val + 1 := by
        simp only [earlierCol, earlier, hodd, one_ne_zero, ↓reduceIte]; omega
      set t := (i.val + 1) / 2
      have hodd1 : i.val + 2 = 2 * t + 1 := by omega
      have hev1 : i.val + 1 = 2 * t := by omega
      rw [hs, hear, hodd1, hev1, zeros_two_mul_add_one, zeros_two_mul t (by omega)]
      push_cast; ring

theorem result : type_of% @OMA.S_oeis_a115526.main := by
  intro n
  have hunit : IsUnit (corner n).det := isUnit_iff_ne_zero.mpr (corner_det_ne_zero n)
  have hvec : (corner n)⁻¹ *ᵥ (fun _ : Fin (n + 1) => (1 : ℚ)) =
      fun i : Fin (n + 1) => (zeros (i.val + 2) : ℚ) := by
    rw [← corner_mulVec_zeros n, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
      Matrix.one_mulVec]
  have hlast := congrFun hvec (Fin.last n)
  simpa [Matrix.mulVec, dotProduct] using hlast

end OMA.A115526Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a115526.main := OMA.A115526Proof.result
