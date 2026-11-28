import OMAStatements.S_oeis_a273790

open OMA.S_oeis_a273790 PowerSeries

lemma outside_one (x y : ℤ)
    (h : x < -1 ∨ 1 < x ∨ y < -1 ∨ 1 < y) : state 1 x y = true := by
  have off (i j : ℤ) (hij : ¬ (i = 0 ∧ j = 0)) : state 0 i j = false := by
    exact decide_eq_false_iff_not.mpr hij
  rw [state]
  simp (disch := omega) only [off]
  decide

lemma full_two (x y : ℤ) : state 2 x y = true := by
  by_cases hx : -2 ≤ x ∧ x ≤ 2
  · by_cases hy : -2 ≤ y ∧ y ≤ 2
    · obtain ⟨h₁,h₂⟩ := hx
      obtain ⟨h₃,h₄⟩ := hy
      interval_cases x <;> interval_cases y <;> decide
    · rw [state]
      simp (disch := omega) only [outside_one, Bool.toNat_true]
      decide
  · rw [state]
    simp (disch := omega) only [outside_one, Bool.toNat_true]
    decide

lemma full (k : ℕ) (x y : ℤ) : state (k+2) x y = true := by
  induction k generalizing x y with
  | zero => exact full_two x y
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega, state]
    simp only [ih, Bool.toNat_true]
    decide

lemma count_full (k : ℕ) : onCount (k+2) = (2 * ((k:ℤ)+2) + 1)^2 := by
  simp [onCount, full, Finset.card_product, pow_two]

lemma closed_int (k : ℕ) :
    3*a (k+1) = 4*((k:ℤ)+1)^3 + 12*((k:ℤ)+1)^2 + 11*((k:ℤ)+1) - 9 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : a (k+2) = a (k+1) + onCount (k+2) := Finset.sum_range_succ _ _
    rw [h, count_full]
    push_cast
    linarith only [ih]

lemma closed_form (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (4*(n:ℚ)^3+12*(n:ℚ)^2+11*(n:ℚ)-9)/3 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := closed_int k
  have hq : (3:ℚ)*a (k+1) = 4*((k:ℚ)+1)^3 + 12*((k:ℚ)+1)^2 + 11*((k:ℚ)+1)-9 := by
    exact_mod_cast h
  push_cast
  linarith only [hq]

lemma recurrence (n : ℕ) (hn : 4 < n) :
    a n = 4*a (n-1)-6*a (n-2)+4*a (n-3)-a (n-4) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+5 := ⟨n-5, by omega⟩
  simp only [Nat.reduceSubDiff]
  have h₀ := closed_int (k+4)
  have h₁ := closed_int (k+3)
  have h₂ := closed_int (k+2)
  have h₃ := closed_int (k+1)
  have h₄ := closed_int k
  push_cast at h₀ h₁ h₂ h₃
  linarith only [h₀,h₁,h₂,h₃,h₄]

lemma exponential :
    PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) =
      4 + PowerSeries.exp ℚ * (PowerSeries.C (4 / 3 : ℚ) * X ^ 3 + 8 * X ^ 2 + 9 * X - 3) := by
  let e := PowerSeries.exp ℚ
  have eqn : (4 : PowerSeries ℚ) + e * (PowerSeries.C (4/3 : ℚ)*X^3+8*X^2+9*X-3) =
      PowerSeries.C (4 : ℚ) + (e * X^3) * PowerSeries.C (4/3 : ℚ) +
        (e * X^2) * PowerSeries.C 8 + (e * X^1) * PowerSeries.C 9 - e * PowerSeries.C 3 := by
    have cNat (k : ℕ) : PowerSeries.C (k : ℚ) = (k : PowerSeries ℚ) := map_natCast _ k
    rw [show PowerSeries.C (4:ℚ) = 4 from cNat 4,
      show PowerSeries.C (8:ℚ) = 8 from cNat 8, show PowerSeries.C (9:ℚ) = 9 from cNat 9,
      show PowerSeries.C (3:ℚ) = 3 from cNat 3]
    ring
  change _ = 4 + e * _
  rw [eqn]
  ext n
  simp only [map_add, map_sub, coeff_mul_C, coeff_mul_X_pow', coeff_C,
    coeff_mk, e, coeff_exp, Algebra.algebraMap_self_apply]
  rcases n with _ | (_ | (_ | n))
  · change (1 : ℚ) / _ = _
    norm_num
  · have h := closed_form 1 (by decide)
    norm_num at h
    norm_num [h]
  · have h := closed_form 2 (by decide)
    norm_num at h
    norm_num [h]
  · rw [closed_form (n+3) (by omega)]
    simp (disch := omega) [Nat.factorial_succ]
    field_simp
    ring


lemma series_of_recurrence (a : ℕ → ℤ)
    (hr : ∀ n : ℕ, 4 < n → a n = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4))
    (v0 : a 0 = 1) (v1 : a 1 = 6) (v2 : a 2 = 31) (v3 : a 3 = 80) (v4 : a 4 = 161) :
    PowerSeries.mk a * ((1 - X) ^ 4) =
      (1 + 2 * X + 13 * X ^ 2 - 12 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℤ) := by
  suffices hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-4 : ℤ) • (PowerSeries.mk a * (X ^ 1 : PowerSeries ℤ)) +
        (6 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-4 : ℤ) • (PowerSeries.mk a * (X ^ 3 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (2 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (13 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (-12 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 4 : PowerSeries ℤ) by
    simp only [zsmul_eq_mul] at hs
    linear_combination hs
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  by_cases hn : 4 < n
  · have h := hr n (by omega)
    simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega]
    linarith only [h]
  · interval_cases n <;> norm_num [zsmul_eq_mul, v0, v1, v2, v3, v4]

theorem OMA.solution : type_of% @OMA.S_oeis_a273790.main := by
  refine ⟨closed_form, recurrence, series_of_recurrence a recurrence (by decide) ?_ ?_ ?_ ?_, exponential⟩
  · have h := closed_int 0
    norm_num at h
    omega
  · have h := closed_int 1
    norm_num at h
    omega
  · have h := closed_int 2
    norm_num at h
    omega
  · have h := closed_int 3
    norm_num at h
    omega
