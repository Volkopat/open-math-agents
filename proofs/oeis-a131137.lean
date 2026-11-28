import OMAStatements.S_oeis_a131137
import Mathlib

namespace OMA.A131137Proof

open OMA.S_oeis_a131137

/-! ## The integer numerators `numer n`, with `polylog(-n,1/4)/4 = numer n / 3^(n+1)` -/

/-- `numer 0 = 1`, `numer (n+1) = Sum_{i ≤ n} C(n+1, i) 3^(n-i) numer i` (values 1, 1, 5, 33, 285, ...). -/
def numer : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), (n + 1).choose i * 3 ^ (n - i) * numer i
decreasing_by exact i.isLt

theorem numer_zero : numer 0 = 1 := by
  rw [numer]

theorem numer_succ (n : ℕ) :
    numer (n + 1) = ∑ i ∈ Finset.range (n + 1), (n + 1).choose i * 3 ^ (n - i) * numer i := by
  have hF := Fin.sum_univ_eq_sum_range (fun i => (n + 1).choose i * 3 ^ (n - i) * numer i) (n + 1)
  rw [numer]
  exact hF

/-! ## The series `polyS n = Sum_k k^n (1/4)^k` -/

noncomputable def polyS (n : ℕ) : ℝ := ∑' k : ℕ, (k : ℝ) ^ n * (1 / 4 : ℝ) ^ k

theorem norm_quarter : ‖(1 / 4 : ℝ)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  norm_num

theorem summ (n : ℕ) : Summable (fun k : ℕ => (k : ℝ) ^ n * (1 / 4 : ℝ) ^ k) :=
  summable_pow_mul_geometric_of_norm_lt_one n norm_quarter

/-- The index shift `k -> k + 1` and the binomial expansion of `(k + 1)^n`. -/
theorem polyS_rec (n : ℕ) :
    polyS n = (0 : ℝ) ^ n + 1 / 4 * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * polyS i := by
  have h1 : polyS n = ((0 : ℕ) : ℝ) ^ n * (1 / 4 : ℝ) ^ 0 +
      ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ n * (1 / 4 : ℝ) ^ (k + 1) :=
    (summ n).tsum_eq_zero_add
  have h2 : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) ^ n * (1 / 4 : ℝ) ^ (k + 1) =
      ∑ i ∈ Finset.range (n + 1), 1 / 4 * (n.choose i : ℝ) * ((k : ℝ) ^ i * (1 / 4 : ℝ) ^ k) := by
    intro k
    rw [Nat.cast_add, Nat.cast_one, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h1, tsum_congr h2, Summable.tsum_finsetSum, Finset.mul_sum]
  · congr 1
    · simp
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [tsum_mul_left, polyS]
      ring
  · intro i _
    exact (summ i).mul_left _

theorem polyS_zero : polyS 0 = 4 / 3 := by
  have h := polyS_rec 0
  simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul, pow_zero] at h
  linarith

theorem polyS_eq (n : ℕ) : polyS n = 4 * (numer n : ℝ) / 3 ^ (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [polyS_zero, numer_zero]
      norm_num
    · have h := polyS_rec (m + 1)
      rw [Finset.sum_range_succ, Nat.choose_self, zero_pow (show m + 1 ≠ 0 by omega)] at h
      have hS : polyS (m + 1) =
          1 / 3 * ∑ i ∈ Finset.range (m + 1), ((m + 1).choose i : ℝ) * polyS i := by
        simp only [Nat.cast_one, one_mul, zero_add] at h
        linarith
      rw [hS, numer_succ]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i < m + 1 := Finset.mem_range.mp hi
      rw [ih i hi']
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp hi')
      rw [Nat.add_sub_cancel_left]
      field_simp
      ring

/-! ## The 3-adic unit `unitM n = numer n / n!` -/

def unitM (n : ℕ) : ℚ := (numer n : ℚ) / (n.factorial : ℚ)

theorem unitM_zero : unitM 0 = 1 := by
  rw [show unitM 0 = (numer 0 : ℚ) / ((0 : ℕ).factorial : ℚ) from rfl, numer_zero]
  simp

theorem unitM_succ (n : ℕ) :
    unitM (n + 1) = unitM n +
      ∑ i ∈ Finset.range n, (3 : ℚ) ^ (n - i) / ((n + 1 - i).factorial : ℚ) * unitM i := by
  have key : ∀ i ∈ Finset.range (n + 1),
      (((n + 1).choose i * 3 ^ (n - i) * numer i : ℕ) : ℚ) / ((n + 1).factorial : ℚ)
        = (3 : ℚ) ^ (n - i) / ((n + 1 - i).factorial : ℚ) * unitM i := by
    intro i hi
    have hi' : i ≤ n + 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hC : ((n + 1).choose i : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
    have hf : ((n + 1).factorial : ℚ) =
        ((n + 1).choose i : ℚ) * (i.factorial : ℚ) * ((n + 1 - i).factorial : ℚ) := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hi').symm
    rw [hf, show unitM i = (numer i : ℚ) / (i.factorial : ℚ) from rfl]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
  have hlast : (3 : ℚ) ^ (n - n) / ((n + 1 - n).factorial : ℚ) * unitM n = unitM n := by
    rw [Nat.sub_self, show n + 1 - n = 1 by omega]
    simp
  rw [show unitM (n + 1) = (numer (n + 1) : ℚ) / ((n + 1).factorial : ℚ) from rfl, numer_succ,
    Nat.cast_sum, Finset.sum_div, Finset.sum_congr rfl key, Finset.sum_range_succ, hlast]
  exact add_comm _ _

/-- Legendre: `v_3(m!) ≤ m - 2` for `m ≥ 2`, so `3^(m-1)/m!` has 3-adic norm at most `1/3`. -/
theorem c_bound (m : ℕ) (hm : 2 ≤ m) :
    padicNorm 3 ((3 : ℚ) ^ (m - 1) / (m.factorial : ℚ)) ≤ 1 / 3 := by
  have hv : (3 - 1) * padicValNat 3 m.factorial < m :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3 (by omega)
  have hne1 : (3 : ℚ) ^ (m - 1) ≠ 0 := by positivity
  have hne2 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h3 : padicValRat 3 (3 : ℚ) = 1 := by
    have h := padicValRat.self (p := 3) (by norm_num)
    exact_mod_cast h
  rw [padicNorm.eq_zpow_of_nonzero (div_ne_zero hne1 hne2), padicValRat.div (p := 3) hne1 hne2,
    padicValRat.pow (p := 3), padicValRat.of_nat (p := 3), h3]
  have hexp : -(((m - 1 : ℕ) : ℤ) * 1 - (padicValNat 3 m.factorial : ℤ)) ≤ -1 := by omega
  have h4 := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ ((3 : ℕ) : ℚ) by norm_num) hexp
  refine h4.trans ?_
  norm_num

theorem d_bound (n i : ℕ) (hi : i < n) :
    padicNorm 3 ((3 : ℚ) ^ (n - i) / ((n + 1 - i).factorial : ℚ)) ≤ 1 / 3 := by
  have h := c_bound (n + 1 - i) (by omega)
  rw [show n + 1 - i - 1 = n - i by omega] at h
  exact h

theorem le_one_of_close {x : ℚ} (h : padicNorm 3 (x - 1) ≤ 1 / 3) : padicNorm 3 x ≤ 1 := by
  have h2 : padicNorm 3 (x - 1 + 1) ≤ max (padicNorm 3 (x - 1)) (padicNorm 3 1) :=
    padicNorm.nonarchimedean
  rw [sub_add_cancel, padicNorm.one] at h2
  exact h2.trans (max_le (by linarith) le_rfl)

/-- `unitM n ≡ 1` modulo `3` in `ℤ_(3)`: its distance to `1` has 3-adic norm at most `1/3`. -/
theorem unitM_close (n : ℕ) : padicNorm 3 (unitM n - 1) ≤ 1 / 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [unitM_zero, sub_self, padicNorm.zero]
      norm_num
    · rw [unitM_succ]
      have e : unitM n + ∑ i ∈ Finset.range n,
            (3 : ℚ) ^ (n - i) / ((n + 1 - i).factorial : ℚ) * unitM i - 1
          = (unitM n - 1) + ∑ i ∈ Finset.range n,
            (3 : ℚ) ^ (n - i) / ((n + 1 - i).factorial : ℚ) * unitM i := by ring
      rw [e]
      refine le_trans padicNorm.nonarchimedean (max_le (ih n (Nat.lt_succ_self n)) ?_)
      refine padicNorm.sum_le' (fun i hi => ?_) (by norm_num)
      have hi' : i < n := Finset.mem_range.mp hi
      rw [padicNorm.mul]
      have h1 := d_bound n i hi'
      have h2 := le_one_of_close (ih i (by omega))
      calc _ ≤ 1 / 3 * padicNorm 3 (unitM i) :=
            mul_le_mul_of_nonneg_right h1 (padicNorm.nonneg _)
        _ ≤ 1 / 3 * 1 := mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 1 / 3 := mul_one _

theorem unitM_norm (n : ℕ) : padicNorm 3 (unitM n) = 1 := by
  have h := unitM_close n
  have hne : padicNorm 3 (unitM n - 1) ≠ padicNorm 3 1 := by
    rw [padicNorm.one]
    intro h'
    rw [h'] at h
    norm_num at h
  have h2 := padicNorm.add_eq_max_of_ne hne
  rw [sub_add_cancel, padicNorm.one] at h2
  rw [h2]
  exact max_eq_right (by linarith)

theorem numer_ne_zero (n : ℕ) : numer n ≠ 0 := by
  intro h
  have h1 := unitM_norm n
  rw [show unitM n = (numer n : ℚ) / (n.factorial : ℚ) from rfl, h] at h1
  simp at h1

/-- `v_3(numer n) = v_3(n!)`. -/
theorem val_numer (n : ℕ) : padicValNat 3 (numer n) = padicValNat 3 n.factorial := by
  have h1 := unitM_norm n
  have hN : (numer n : ℚ) ≠ 0 := by exact_mod_cast numer_ne_zero n
  have hF : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [show unitM n = (numer n : ℚ) / (n.factorial : ℚ) from rfl,
    padicNorm.eq_zpow_of_nonzero (div_ne_zero hN hF), padicValRat.div (p := 3) hN hF,
    padicValRat.of_nat (p := 3), padicValRat.of_nat (p := 3)] at h1
  have h3 : ((3 : ℕ) : ℚ) ^ (-((padicValNat 3 (numer n) : ℤ) - (padicValNat 3 n.factorial : ℤ))) =
      ((3 : ℕ) : ℚ) ^ (0 : ℤ) := by
    rw [zpow_zero]
    exact h1
  have h4 := zpow_right_injective₀ (show (0 : ℚ) < ((3 : ℕ) : ℚ) by norm_num)
    (show ((3 : ℕ) : ℚ) ≠ 1 by norm_num) h3
  omega

/-! ## Reduced denominators -/

/-- If `v_3(X) ≤ k` then `X / 3^k` has reduced denominator `3^(k - v_3(X))`. -/
theorem den_eq (X k : ℕ) (hX : X ≠ 0) (hk : padicValNat 3 X ≤ k) :
    ((X : ℚ) / (3 : ℚ) ^ k).den = 3 ^ (k - padicValNat 3 X) := by
  have hdvd : 3 ^ padicValNat 3 X ∣ X := pow_padicValNat_dvd
  have hndvd : ¬ 3 ^ (padicValNat 3 X + 1) ∣ X := pow_succ_padicValNat_not_dvd hX
  generalize padicValNat 3 X = v at hk hdvd hndvd ⊢
  obtain ⟨Y, rfl⟩ := hdvd
  have hY3 : ¬ 3 ∣ Y := by
    rintro ⟨Z, rfl⟩
    exact hndvd ⟨Z, by ring⟩
  have hcop : Nat.Coprime Y (3 ^ (k - v)) :=
    Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3))
  have hq : ((3 ^ v * Y : ℕ) : ℚ) / (3 : ℚ) ^ k = ((Y : ℤ) : ℚ) / (((3 ^ (k - v) : ℕ) : ℤ) : ℚ) := by
    have h3 : (3 : ℚ) ^ k = 3 ^ v * 3 ^ (k - v) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h3]
    push_cast
    exact mul_div_mul_left _ _ (by positivity)
  rw [hq]
  have h := Rat.den_div_eq_of_coprime (a := (Y : ℤ)) (b := ((3 ^ (k - v) : ℕ) : ℤ)) (by positivity)
    (by simpa using hcop)
  exact_mod_cast h

theorem xnum_ne_zero (n : ℕ) : n.factorial * (3 ^ (n + 1) - 2 ^ (n + 1)) ≠ 0 := by
  have hlt : 2 ^ (n + 1) < 3 ^ (n + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
  exact Nat.mul_ne_zero (Nat.factorial_ne_zero n) (Nat.sub_pos_of_lt hlt).ne'

theorem val_xnum (n : ℕ) :
    padicValNat 3 (n.factorial * (3 ^ (n + 1) - 2 ^ (n + 1))) = padicValNat 3 n.factorial := by
  have hlt : 2 ^ (n + 1) < 3 ^ (n + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hnd : ¬ 3 ∣ 3 ^ (n + 1) - 2 ^ (n + 1) := by
    intro h
    have h1 : 3 ∣ 3 ^ (n + 1) := dvd_pow_self 3 (by omega)
    have h2 : 3 ∣ 2 ^ (n + 1) := by
      have h5 := Nat.dvd_sub h1 h
      rwa [Nat.sub_sub_self hlt.le] at h5
    have h6 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  rw [padicValNat.mul (p := 3) (Nat.factorial_ne_zero n) (Nat.sub_pos_of_lt hlt).ne',
    padicValNat.eq_zero_of_not_dvd hnd, add_zero]

/-- `a(n+1) = den(n! (3^(n+1) - 2^(n+1)) / 3^(n+1))`. -/
theorem A_eq (n : ℕ) :
    A131137 (n + 1) =
      (((n.factorial * (3 ^ (n + 1) - 2 ^ (n + 1)) : ℕ) : ℚ) / (3 : ℚ) ^ (n + 1)).den := by
  have hle : 2 ^ (n + 1) ≤ 3 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _
  have hne : n + 1 ≠ 0 := by omega
  have hc : PowerSeries.coeff (n + 1) logSeries
      = (1 : ℚ) ^ (n + 1) / ((n + 1 : ℕ) : ℚ) - (2 / 3 : ℚ) ^ (n + 1) / ((n + 1 : ℕ) : ℚ) := by
    rw [logSeries, map_sub, negLogOneSub, negLogOneSub, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      if_neg hne, if_neg hne]
  rw [A131137, hc]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub hle, Nat.factorial_succ]
  have h3 : (3 : ℚ) ^ (n + 1) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  rw [div_pow]
  first
    | (field_simp; ring)
    | field_simp

end OMA.A131137Proof

open OMA.A131137Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a131137.main := by
  intro n hn
  refine ⟨(numer n : ℚ) / (3 : ℚ) ^ (n + 1), ?_, ?_⟩
  · show (((numer n : ℚ) / (3 : ℚ) ^ (n + 1) : ℚ) : ℝ) = polyS n / 4
    rw [polyS_eq]
    push_cast
    ring
  · have hv : padicValNat 3 n.factorial < n := padicValNat_factorial_lt_of_ne_zero 3 (by omega)
    rw [A_eq, den_eq (numer n) (n + 1) (numer_ne_zero n) (by rw [val_numer]; omega),
      den_eq _ (n + 1) (xnum_ne_zero n) (by rw [val_xnum]; omega), val_numer, val_xnum]
