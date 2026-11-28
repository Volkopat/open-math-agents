import OMAStatements.S_oeis_a138830
import Mathlib

namespace OMA.S_oeis_a138830

open PowerSeries

instance : DecidablePred isImperfect := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ ∑ d ∈ n.properDivisors, d ≠ n))

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem perfect_below :
    (Finset.range 498).filter (fun n => ∑ d ∈ n.properDivisors, d = n) = {0, 6, 28, 496} := by
  decide

theorem imp_iff (n : ℕ) (hn : n < 498) :
    isImperfect n ↔ (n ≠ 0 ∧ n ≠ 6 ∧ n ≠ 28 ∧ n ≠ 496) := by
  have h := Finset.ext_iff.mp perfect_below n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton] at h
  unfold isImperfect
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨by omega, ?_, ?_, ?_⟩ <;> intro he <;> exact h1 ((h.mpr (by omega)).2)
  · rintro ⟨h0, h6, h28, h496⟩
    refine ⟨by omega, fun he => ?_⟩
    rcases h.mp ⟨hn, he⟩ with h' | h' | h' | h' <;> omega

/-- The number of exceptions (0 and the perfect numbers 6, 28, 496) below n. -/
def e (n : ℕ) : ℕ :=
  (if 0 < n then 1 else 0) + (if 6 < n then 1 else 0) + (if 28 < n then 1 else 0) +
    (if 496 < n then 1 else 0)

theorem count_eq (n : ℕ) (hn : n ≤ 498) : Nat.count isImperfect n + e n = n := by
  induction n with
  | zero => simp [e]
  | succ n ih =>
    have ih := ih (by omega)
    rw [Nat.count_succ]
    by_cases hp : isImperfect n
    · rw [if_pos hp]
      have := (imp_iff n (by omega)).mp hp
      unfold e at ih ⊢
      split_ifs at ih ⊢ <;> omega
    · rw [if_neg hp]
      have h' : ¬ (n ≠ 0 ∧ n ≠ 6 ∧ n ≠ 28 ∧ n ≠ 496) := fun h => hp ((imp_iff n (by omega)).mpr h)
      unfold e at ih ⊢
      split_ifs at ih ⊢ <;> omega

theorem nth_eq (m t : ℕ) (ht : t < 498) (hp : t ≠ 0 ∧ t ≠ 6 ∧ t ≠ 28 ∧ t ≠ 496)
    (hc : t - e t = m) : Nat.nth isImperfect m = t := by
  have h1 := count_eq t (by omega)
  have h2 : Nat.count isImperfect t = m := by omega
  rw [← h2]
  exact Nat.nth_count ((imp_iff t ht).mpr hp)

theorem a_def (j : ℕ) : a j = Nat.nth isImperfect (2 * j - 1) := rfl

theorem a1 : a 1 = 2 := by
  rw [a_def]; exact nth_eq _ _ (by norm_num) (by omega) (by simp [e])

theorem a2 : a 2 = 4 := by
  rw [a_def]; exact nth_eq _ _ (by norm_num) (by omega) (by simp [e])

theorem a_mid (j : ℕ) (h1 : 3 ≤ j) (h2 : j ≤ 13) : a j = 2 * j + 1 := by
  rw [a_def]
  apply nth_eq _ _ (by omega) (by omega)
  unfold e
  split_ifs <;> omega

theorem a_high (j : ℕ) (h1 : 14 ≤ j) (h2 : j ≤ 246) : a j = 2 * j + 2 := by
  rw [a_def]
  apply nth_eq _ _ (by omega) (by omega)
  unfold e
  split_ifs <;> omega

theorem a247 : a 247 = 497 := by
  rw [a_def]; exact nth_eq _ _ (by norm_num) (by omega) (by simp [e])

/-- The denominator. -/
noncomputable def D : ℚ⟦X⟧ := X ^ 2 - 2 * X + 1

/-- The numerator. -/
noncomputable def N : ℚ⟦X⟧ := -X ^ 14 + X ^ 13 - X ^ 3 + X ^ 2 + 2

theorem AD_eq : A * D = C 1 * (A * X ^ 2) - C 2 * (A * X ^ 1) + A := by
  simp only [D, map_one, map_ofNat]
  ring

theorem coeff_AD0 : coeff 0 (A * D) = (a 1 : ℚ) := by
  rw [AD_eq]
  simp [A]

theorem coeff_AD1 : coeff 1 (A * D) = (a 2 : ℚ) - 2 * a 1 := by
  rw [AD_eq]
  simp [coeff_mul_X_pow', A]
  ring

theorem coeff_AD (k : ℕ) : coeff (k + 2) (A * D) =
    (a (k + 1) : ℚ) - 2 * (a (k + 2) : ℚ) + (a (k + 3) : ℚ) := by
  rw [AD_eq]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, one_mul,
    if_pos (show 2 ≤ k + 2 by omega), if_pos (show 1 ≤ k + 2 by omega),
    show k + 2 - 2 + 1 = k + 1 by omega, show k + 2 - 1 + 1 = k + 2 by omega]

theorem coeff_N (k : ℕ) : coeff k N =
    (if k = 0 then 2 else 0) + (if k = 2 then 1 else 0) - (if k = 3 then 1 else 0) +
      (if k = 13 then 1 else 0) - (if k = 14 then 1 else 0) := by
  have hN : N = C 2 * X ^ 0 + C 1 * X ^ 2 - C 1 * X ^ 3 + C 1 * X ^ 13 - C 1 * X ^ 14 := by
    simp only [N, map_one, map_ofNat]
    ring
  rw [hN]
  simp only [map_add, map_sub, coeff_C_mul_X_pow]

theorem agree (k : ℕ) (hk : k < 246) : coeff k (A * D) = coeff k N := by
  rw [coeff_N]
  rcases Nat.lt_or_ge k 16 with hs | hs
  · interval_cases k <;>
      simp only [coeff_AD0, coeff_AD1, coeff_AD] <;>
      norm_num [a1, a2, a_mid, a_high]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [coeff_AD, a_high (j + 1) (by omega) (by omega), a_high (j + 2) (by omega) (by omega),
      a_high (j + 3) (by omega) (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    push_cast
    ring

theorem disagree : coeff 246 (A * D) ≠ coeff 246 N := by
  rw [show (246 : ℕ) = 244 + 2 by norm_num, coeff_AD, coeff_N]
  rw [a_high 245 (by norm_num) (by norm_num), a_high 246 (by norm_num) (by norm_num), a247]
  norm_num

theorem D_ne : constantCoeff D ≠ 0 := by simp [D]

theorem G_eq : G = N * D⁻¹ := rfl

end OMA.S_oeis_a138830

open OMA.S_oeis_a138830 in
theorem OMA.solution : type_of% @OMA.S_oeis_a138830.main := by
  have hGD : G * D = N := by
    rw [G_eq, mul_assoc, PowerSeries.inv_mul_cancel _ D_ne, mul_one]
  have hsub : A - G = (A * D - N) * D⁻¹ := by
    rw [← hGD, ← sub_mul, mul_assoc, PowerSeries.mul_inv_cancel _ D_ne, mul_one]
  refine ⟨fun k hk => ?_, fun h => disagree ?_⟩
  · have hdvd : (PowerSeries.X : PowerSeries ℚ) ^ 246 ∣ A * D - N := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, agree m hm, sub_self]
    have hdvd2 : (PowerSeries.X : PowerSeries ℚ) ^ 246 ∣ A - G := by
      rw [hsub]; exact Dvd.dvd.mul_right hdvd _
    rw [PowerSeries.X_pow_dvd_iff] at hdvd2
    have := hdvd2 k (by omega)
    rw [map_sub, sub_eq_zero] at this
    exact this
  · rw [h, hGD]
