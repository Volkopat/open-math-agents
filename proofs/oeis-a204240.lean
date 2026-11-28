import OMAStatements.S_oeis_a204240

-- Problem: A204240, determinants of the matrices max(3i-2j, 3j-2i).
-- Credit: @GarnetCullet
-- Subtract twice the second-to-last row and add the third-to-last to the last row, then do the
-- same with columns: the last row and column become 5 at the second-to-last place and -10 in the
-- corner, so Laplace expansion gives a(n) = -10 a(n-1) - 25 a(n-2). The generating function
-- follows by comparing coefficients with (1 + 5X)^2.

namespace OMA.P_oeis_a204240
open OMA.S_oeis_a204240 Matrix

/-- Entry formula with natural indices. -/
def e (i j : ℕ) : ℚ := if i ≤ j then 3 * (j : ℚ) - 2 * i + 1 else 3 * (i : ℚ) - 2 * j + 1

theorem pm_apply (n : ℕ) (i j : Fin n) : principalMatrix n i j = e i.val j.val := by
  simp only [principalMatrix, e]
  split_ifs with h
  · have : (i.val : ℚ) ≤ j.val := by exact_mod_cast h
    rw [max_eq_right (by linarith)]; ring
  · have : (j.val : ℚ) < i.val := by exact_mod_cast (not_le.mp h)
    rw [max_eq_left (by linarith)]; ring

/-- Second difference in the row index vanishes away from the diagonal. -/
theorem e_diff (k j : ℕ) :
    e (k + 2) j - 2 * e (k + 1) j + e k j = if j = k + 1 then 5 else 0 := by
  rcases Nat.lt_or_ge j (k + 1) with h | h
  · have h1 : ¬ k + 2 ≤ j := by omega
    have h2 : ¬ k + 1 ≤ j := by omega
    have h4 : j ≠ k + 1 := by omega
    by_cases h3 : k ≤ j
    · have hjk : j = k := by omega
      subst hjk; simp only [e, h1, h2, h4, if_false, le_refl, if_true]; push_cast; ring
    · simp only [e, h1, h2, h3, h4, if_false]; push_cast; ring
  · rcases Nat.lt_or_ge j (k + 2) with h' | h'
    · have hj : j = k + 1 := by omega
      subst hj; simp [e]; ring
    · have h1 : k + 2 ≤ j := h'
      have h2 : k + 1 ≤ j := by omega
      have h3 : k ≤ j := by omega
      have h4 : j ≠ k + 1 := by omega
      simp only [e, h1, h2, h3, h4, if_true, if_false]; push_cast; ring

theorem e_symm (i j : ℕ) : e i j = e j i := by
  simp only [e]; split_ifs <;> first | (exfalso; omega) | (have : i = j := by omega); subst this; ring | ring


theorem diff_row (m : ℕ) (j : ℕ) :
    e (m + 2) j + (-2) * e (m + 1) j + 1 * e m j = if j = m + 1 then 5 else 0 := by
  rw [← e_diff]; ring

theorem diff_col (m : ℕ) (i : ℕ) :
    e i (m + 2) + (-2) * e i (m + 1) + 1 * e i m = if i = m + 1 then 5 else 0 := by
  rw [e_symm i, e_symm i, e_symm i, diff_row]

section
variable (m : ℕ)
abbrev L : Fin (m + 3) := Fin.last (m + 2)
abbrev P : Fin (m + 3) := ⟨m + 1, by omega⟩
abbrev Q : Fin (m + 3) := ⟨m, by omega⟩

noncomputable def M1 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℚ :=
  updateRow (principalMatrix (m + 3)) (L m)
    (principalMatrix (m + 3) (L m) + (-2 : ℚ) • principalMatrix (m + 3) (P m))
noncomputable def M2 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℚ :=
  updateRow (M1 m) (L m) (M1 m (L m) + (1 : ℚ) • M1 m (Q m))
noncomputable def M3 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℚ :=
  updateCol (M2 m) (L m) (fun k => M2 m k (L m) + (-2 : ℚ) • M2 m k (P m))
noncomputable def M4 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℚ :=
  updateCol (M3 m) (L m) (fun k => M3 m k (L m) + (1 : ℚ) • M3 m k (Q m))

theorem det_M4 : (M4 m).det = (principalMatrix (m + 3)).det := by
  have hLP : L m ≠ P m := by simp [Fin.ext_iff]
  have hLQ : L m ≠ Q m := by simp [Fin.ext_iff]
  rw [M4, det_updateCol_add_smul_self _ hLQ, M3, det_updateCol_add_smul_self _ hLP,
    M2, det_updateRow_add_smul_self _ hLQ, M1, det_updateRow_add_smul_self _ hLP]

theorem M2_row (j : Fin (m + 3)) :
    M2 m (L m) j = if j.val = m + 1 then 5 else 0 := by
  have hLP : P m ≠ L m := by simp [Fin.ext_iff]
  have hLQ : Q m ≠ L m := by simp [Fin.ext_iff]
  simp only [M2, M1, updateRow_self, updateRow_ne hLQ, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pm_apply]
  exact diff_row m j.val

theorem M2_ne (i j : Fin (m + 3)) (hi : i ≠ L m) : M2 m i j = e i.val j.val := by
  simp only [M2, M1, updateRow_ne hi, pm_apply]

theorem M4_apply (i j : Fin (m + 3)) :
    M4 m i j = if i = L m then (if j = L m then -10 else (if j.val = m + 1 then 5 else 0))
      else (if j = L m then (if i.val = m + 1 then 5 else 0) else e i.val j.val) := by
  have hPL : P m ≠ L m := by simp [Fin.ext_iff]
  have hQL : Q m ≠ L m := by simp [Fin.ext_iff]
  by_cases hj : j = L m
  · subst hj
    simp only [M4, M3, updateCol_self, updateCol_ne hQL,
      smul_eq_mul, if_true]
    by_cases hi : i = L m
    · subst hi
      simp only [M2_row, if_true]
      norm_num
    · simp only [hi, if_false, M2_ne m i _ hi]
      exact diff_col m i.val
  · simp only [M4, M3, updateCol_ne hj, hj, if_false]
    by_cases hi : i = L m
    · subst hi; simp only [M2_row, if_true]
    · simp only [hi, if_false, M2_ne m i _ hi]
end

theorem minor1 (m : ℕ) :
    ((M4 m).submatrix (Fin.last (m + 2)).succAbove (Fin.last (m + 2)).succAbove).det =
      (principalMatrix (m + 2)).det := by
  congr 1
  ext i j
  simp only [Fin.succAbove_last, submatrix_apply, M4_apply, pm_apply]
  have hi : Fin.castSucc i ≠ L m := by simp [Fin.ext_iff]; omega
  have hj : Fin.castSucc j ≠ L m := by simp [Fin.ext_iff]; omega
  simp [hi, hj]

theorem minor2 (m : ℕ) :
    ((M4 m).submatrix (Fin.last (m + 2)).succAbove (Fin.castSucc (Fin.last (m + 1))).succAbove).det =
      5 * (principalMatrix (m + 1)).det := by
  rw [det_succ_column _ (Fin.last (m + 1)), Fin.sum_univ_castSucc]
  have h0 : ∀ i : Fin (m + 1), (M4 m).submatrix (Fin.last (m + 2)).succAbove
      (Fin.castSucc (Fin.last (m + 1))).succAbove i.castSucc (Fin.last (m + 1)) = 0 := by
    intro i
    simp only [Fin.succAbove_last, submatrix_apply, M4_apply]
    have hi : Fin.castSucc (Fin.castSucc i) ≠ L m := by simp [Fin.ext_iff]; omega
    have hl : (Fin.castSucc (Fin.last (m + 1))).succAbove (Fin.last (m + 1)) = L m := by
      simp [Fin.succAbove]
    simp [hi, hl]; omega
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hl : (Fin.castSucc (Fin.last (m + 1))).succAbove (Fin.last (m + 1)) = L m := by
    simp [Fin.succAbove]
  have hv : (M4 m).submatrix (Fin.last (m + 2)).succAbove
      (Fin.castSucc (Fin.last (m + 1))).succAbove (Fin.last (m + 1)) (Fin.last (m + 1)) = 5 := by
    simp only [Fin.succAbove_last, submatrix_apply, M4_apply, hl]
    simp [Fin.ext_iff]
  rw [hv]
  have hsub : (((M4 m).submatrix (Fin.last (m + 2)).succAbove
      (Fin.castSucc (Fin.last (m + 1))).succAbove).submatrix (Fin.last (m + 1)).succAbove
      (Fin.last (m + 1)).succAbove).det = (principalMatrix (m + 1)).det := by
    congr 1
    ext i j
    simp only [Fin.succAbove_last, submatrix_apply, M4_apply, pm_apply]
    have hj : (Fin.castSucc (Fin.last (m + 1))).succAbove (Fin.castSucc j) = Fin.castSucc (Fin.castSucc j) := by
      apply Fin.succAbove_of_castSucc_lt
      simp [Fin.lt_def]; omega
    have hi : Fin.castSucc (Fin.castSucc i) ≠ L m := by simp [Fin.ext_iff]; omega
    have hj' : Fin.castSucc (Fin.castSucc j) ≠ L m := by simp [Fin.ext_iff]; omega
    simp [hj, hi, hj']
  rw [hsub]
  have : ((-1 : ℚ) ^ ((Fin.last (m + 1) : ℕ) + (Fin.last (m + 1) : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  rw [this]; ring

theorem rec (m : ℕ) : (principalMatrix (m + 3)).det =
    -10 * (principalMatrix (m + 2)).det - 25 * (principalMatrix (m + 1)).det := by
  rw [← det_M4, det_succ_row _ (Fin.last (m + 2)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin (m + 1), M4 m (Fin.last (m + 2)) j.castSucc.castSucc = 0 := by
    intro j; rw [M4_apply]
    have hj : Fin.castSucc (Fin.castSucc j) ≠ L m := by simp [Fin.ext_iff]; omega
    simp [hj]; omega
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hp : M4 m (Fin.last (m + 2)) (Fin.castSucc (Fin.last (m + 1))) = 5 := by
    rw [M4_apply]; simp [Fin.ext_iff]
  have hl : M4 m (Fin.last (m + 2)) (Fin.last (m + 2)) = -10 := by
    rw [M4_apply]; simp
  rw [hp, hl, minor1, minor2]
  have s1 : ((-1 : ℚ) ^ ((Fin.last (m + 2) : ℕ) + (Fin.castSucc (Fin.last (m + 1)) : ℕ))) = -1 := by
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [show m + 2 + (m + 1) = 2 * (m + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
  have s2 : ((-1 : ℚ) ^ ((Fin.last (m + 2) : ℕ) + (Fin.last (m + 2) : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  rw [s1, s2]; ring

theorem a_one : a 1 = 1 := by
  simp only [a, det_unique, pm_apply]; simp [e]

theorem a_two : a 2 = -14 := by
  simp only [a, det_fin_two, pm_apply]; simp [e]; norm_num

theorem a_rec (n : ℕ) (hn : 3 ≤ n) : a n = -10 * a (n - 1) - 25 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact rec m

end OMA.P_oeis_a204240

open OMA.P_oeis_a204240 OMA.S_oeis_a204240 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a204240.main := by
  refine ⟨a_rec, ?_⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  ext n
  have hsq : ((C (5 : ℚ)) * X + 1) ^ 2 = 1 + C 10 * X + C 25 * X ^ 2 := by
    simp only [sq, map_ofNat]; ring
  have hexp : generatingFunction * (1 + C 10 * X + C 25 * X ^ 2) =
      generatingFunction + C 10 * (generatingFunction * X ^ 1) +
        C 25 * (generatingFunction * X ^ 2) := by ring
  rw [hsq, hexp, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow',
    coeff_mul_X_pow']
  simp only [generatingFunction, coeff_mk]
  have rhs : -(X * (C (4 : ℚ) * X - 1)) = X - C 4 * X ^ 2 := by ring
  rw [rhs, map_sub, coeff_C_mul, coeff_X, coeff_X_pow]
  rcases n with _ | _ | _ | n
  · simp
  · simp [a_one]
  · simp [a_one, a_two]; norm_num
  · have := a_rec (n + 3) (by omega)
    simp only [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] at this
    simp [show n + 1 + 1 + 1 - 1 = n + 2 by omega, show n + 1 + 1 + 1 - 2 = n + 1 by omega]
    rw [this]; ring
