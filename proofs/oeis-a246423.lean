import OMAStatements.S_oeis_a246423
import Mathlib

namespace OMA.S_oeis_a246423

private lemma inv1m3X_mul :
    (1 - PowerSeries.C (3 : ℤ) * PowerSeries.X) * inv1m3X = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  cases m with
  | zero =>
    simp [inv1m3X]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one]
    simp only [Nat.succ_ne_zero, ↓reduceIte, inv1m3X, PowerSeries.coeff_mk]
    ring

private def inv1pX : PowerSeries ℤ :=
  PowerSeries.mk fun k => (-1 : ℤ) ^ k

private lemma inv1pX_mul :
    (1 + PowerSeries.X) * inv1pX = 1 := by
  ext m
  rw [add_mul, one_mul, map_add]
  cases m with
  | zero =>
    simp [inv1pX]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one]
    simp only [Nat.succ_ne_zero, ↓reduceIte, inv1pX, PowerSeries.coeff_mk]
    ring

private def F_ser : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    if Even m then (-1 : ℤ) ^ (m / 2) * (Nat.choose m (m / 2) : ℤ) else 0

private lemma choose_two_mul_succ (k : ℕ) :
    (k + 1) * Nat.choose (2 * k + 2) (k + 1) = (4 * k + 2) * Nat.choose (2 * k) k := by
  have hsym : Nat.choose (2 * k + 1) (k + 1) = Nat.choose (2 * k + 1) k := by
    have := Nat.choose_symm (show k ≤ 2 * k + 1 by omega)
    simpa [show 2 * k + 1 - k = k + 1 by omega] using this
  have h2 : Nat.choose (2 * k + 2) (k + 1) = 2 * Nat.choose (2 * k + 1) (k + 1) := by
    rw [Nat.choose_succ_succ (2 * k + 1) k, hsym]; ring
  have h1 : Nat.choose (2 * k + 1) (k + 1) =
      Nat.choose (2 * k) k + Nat.choose (2 * k) (k + 1) :=
    Nat.choose_succ_succ (2 * k) k
  have hr : Nat.choose (2 * k) (k + 1) * (k + 1) = Nat.choose (2 * k) k * k := by
    simpa [show 2 * k - k = k by omega] using Nat.choose_succ_right_eq (2 * k) k
  have h3 : (k + 1) * Nat.choose (2 * k + 1) (k + 1) = (2 * k + 1) * Nat.choose (2 * k) k := by
    rw [h1, mul_add]
    linarith
  rw [h2]
  linarith

private lemma F_ser_deriv_eq :
    PowerSeries.derivative ℤ F_ser * (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) +
      PowerSeries.C (4 : ℤ) * PowerSeries.X * F_ser = 0 := by
  ext m
  rw [map_add, mul_add, mul_one, map_add, map_zero]
  have hterm1 : PowerSeries.coeff m (PowerSeries.derivative ℤ F_ser) =
      ((m + 1 : ℕ) : ℤ) * PowerSeries.coeff (m + 1) F_ser := by
    rw [PowerSeries.coeff_derivative]; push_cast; ring
  have hterm2 : PowerSeries.coeff m
      (PowerSeries.derivative ℤ F_ser * (PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2)) =
      if 2 ≤ m then 4 * ((m - 1 : ℕ) : ℤ) * PowerSeries.coeff (m - 1) F_ser else 0 := by
    rw [show PowerSeries.derivative ℤ F_ser * (PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) =
        PowerSeries.C (4 : ℤ) * (PowerSeries.X ^ 2 * PowerSeries.derivative ℤ F_ser) by ring]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    split_ifs with hm
    · rw [PowerSeries.coeff_derivative]
      have hsub : m - 2 + 1 = m - 1 := by omega
      rw [hsub]
      have hcast : ((m - 2 : ℕ) : ℤ) + 1 = ((m - 1 : ℕ) : ℤ) := by omega
      rw [← hcast]; ring
    · ring
  have hterm3 : PowerSeries.coeff m (PowerSeries.C (4 : ℤ) * PowerSeries.X * F_ser) =
      if 1 ≤ m then 4 * PowerSeries.coeff (m - 1) F_ser else 0 := by
    rw [mul_assoc, PowerSeries.coeff_C_mul]
    cases m with
    | zero => simp
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      simp
  rw [hterm1, hterm2, hterm3]
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have h1 : ¬ Even (k + k + 1) := by
      rw [Nat.not_even_iff_odd]; exact ⟨k, by omega⟩
    simp only [F_ser, PowerSeries.coeff_mk, h1, ↓reduceIte, mul_zero, zero_add]
    cases k with
    | zero => simp
    | succ j =>
      have hsub : j + 1 + (j + 1) - 1 = 2 * j + 1 := by omega
      have h2 : ¬ Even (2 * j + 1) := by
        rw [Nat.not_even_iff_odd]; exact ⟨j, rfl⟩
      have hle2 : 2 ≤ j + 1 + (j + 1) := by omega
      have hle1 : 1 ≤ j + 1 + (j + 1) := by omega
      rw [if_pos hle2, if_pos hle1, hsub, if_neg h2]
      ring
  · subst hk
    have h1 : Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩
    have hdiv1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have hsub1 : 2 * k + 1 - 1 = 2 * k := by omega
    have h2e : Even (2 * k) := ⟨k, by omega⟩
    have hdiv2 : 2 * k / 2 = k := by omega
    have hle1 : 1 ≤ 2 * k + 1 := by omega
    have hch := choose_two_mul_succ k
    have hchZ : ((k + 1 : ℕ) : ℤ) * (Nat.choose (2 * k + 2) (k + 1) : ℤ) =
        ((4 * k + 2 : ℕ) : ℤ) * (Nat.choose (2 * k) k : ℤ) := by exact_mod_cast hch
    cases k with
    | zero =>
      simp [F_ser]
    | succ j =>
      have hle2 : 2 ≤ 2 * (j + 1) + 1 := by omega
      simp only [hle2, hle1, ↓reduceIte, F_ser, PowerSeries.coeff_mk, h1, hdiv1, hsub1, h2e, hdiv2]
      have h2j : 2 * (j + 1) + 1 + 1 = 2 * (j + 1) + 2 := by omega
      rw [h2j]
      push_cast at hchZ ⊢
      have hpow : (-1 : ℤ) ^ (j + 1 + 1) = -((-1 : ℤ) ^ (j + 1)) := by rw [pow_succ]; ring
      rw [hpow]
      linear_combination -2 * (-1 : ℤ) ^ (j + 1) * hchZ

private lemma F_ser_sq_mul :
    F_ser ^ 2 * (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) = 1 := by
  set G := F_ser ^ 2 * (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2)
  have hderiv : PowerSeries.derivative ℤ G = 0 := by
    have h1 : PowerSeries.derivative ℤ (F_ser ^ 2) =
        (2 : ℕ) • (F_ser ^ (2 - 1) * PowerSeries.derivative ℤ F_ser) :=
      Derivation.leibniz_pow (PowerSeries.derivative ℤ) F_ser 2
    have h2 : PowerSeries.derivative ℤ (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) =
        PowerSeries.C (8 : ℤ) * PowerSeries.X := by
      rw [map_add, Derivation.map_one_eq_zero, zero_add]
      rw [show PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2 =
          (4 : ℤ) • PowerSeries.X ^ 2 by ext k; simp]
      rw [map_zsmul, Derivation.leibniz_pow]
      simp only [PowerSeries.derivative_X, Nat.reduceSub, pow_one, nsmul_eq_mul,
        zsmul_eq_mul]
      ext k; simp; ring
    rw [show G = F_ser ^ 2 * (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) from rfl]
    rw [Derivation.leibniz, h1, h2]
    simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
    have hfact : F_ser ^ 2 * (PowerSeries.C (8 : ℤ) * PowerSeries.X) +
        (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) *
          (2 * (F_ser * PowerSeries.derivative ℤ F_ser)) =
        2 * F_ser * (PowerSeries.derivative ℤ F_ser *
          (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) +
          PowerSeries.C (4 : ℤ) * PowerSeries.X * F_ser) := by
      have h8 : PowerSeries.C (8 : ℤ) = 2 * PowerSeries.C (4 : ℤ) := by
        ext k; simp; ring
      rw [h8]
      ring
    rw [hfact, F_ser_deriv_eq, mul_zero]
  ext m
  cases m with
  | zero =>
    simp [G, F_ser, pow_two]
  | succ k =>
    have h := congr_arg (PowerSeries.coeff k) hderiv
    rw [PowerSeries.coeff_derivative, map_zero] at h
    have hne : ((k : ℤ) + 1) ≠ 0 := by positivity
    rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact (mul_eq_zero.mp h).resolve_right hne

private noncomputable def R_ser : PowerSeries ℤ :=
  (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) * F_ser

private lemma R_ser_sq :
    R_ser ^ 2 = 1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2 := by
  have h : R_ser ^ 2 = (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) *
      (F_ser ^ 2 * (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2)) := by
    simp only [R_ser]; ring
  rw [h, F_ser_sq_mul, mul_one]

private lemma choose_two_mul_eq_two_mul (k : ℕ) (hk : 1 ≤ k) :
    Nat.choose (2 * k) k = 2 * Nat.choose (2 * k - 1) (k - 1) := by
  have h1 : 2 * k = (2 * k - 1) + 1 := by omega
  have h2 : k = (k - 1) + 1 := by omega
  have hsym : Nat.choose (2 * k - 1) k = Nat.choose (2 * k - 1) (k - 1) := by
    have := Nat.choose_symm (show k - 1 ≤ 2 * k - 1 by omega)
    simpa [show 2 * k - 1 - (k - 1) = k by omega] using this
  conv_lhs => rw [h1, h2]
  rw [Nat.choose_succ_succ, Nat.succ_eq_add_one, ← h2, hsym]
  ring

private lemma even_choose_two_mul (k : ℕ) (hk : 1 ≤ k) :
    2 ∣ Nat.choose (2 * k) k :=
  ⟨Nat.choose (2 * k - 1) (k - 1), choose_two_mul_eq_two_mul k hk⟩

private lemma R_ser_coeff_even (m : ℕ) (hm : 1 ≤ m) :
    2 ∣ PowerSeries.coeff m R_ser := by
  have hR : PowerSeries.coeff m R_ser =
      PowerSeries.coeff m F_ser +
        if 2 ≤ m then 4 * PowerSeries.coeff (m - 2) F_ser else 0 := by
    rw [R_ser, add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul']
    split_ifs <;> ring
  rw [hR]
  have hF : 2 ∣ PowerSeries.coeff m F_ser := by
    simp only [F_ser, PowerSeries.coeff_mk]
    split_ifs with hev
    · rcases hev with ⟨k, hk⟩
      have hk1 : 1 ≤ k := by omega
      have hdiv : m / 2 = k := by omega
      have hm2k : m = 2 * k := by omega
      rw [hdiv, hm2k]
      obtain ⟨c, hc⟩ := even_choose_two_mul k hk1
      refine ⟨(-1 : ℤ) ^ k * (c : ℤ), ?_⟩
      have hcZ : (Nat.choose (2 * k) k : ℤ) = 2 * (c : ℤ) := by exact_mod_cast hc
      rw [hcZ]; ring
    · exact dvd_zero 2
  have h4 : 2 ∣ (if 2 ≤ m then 4 * PowerSeries.coeff (m - 2) F_ser else 0) := by
    split_ifs
    · exact ⟨2 * PowerSeries.coeff (m - 2) F_ser, by ring⟩
    · exact dvd_zero 2
  exact dvd_add hF h4

private lemma R_ser_coeff_zero : PowerSeries.coeff 0 R_ser = 1 := by
  simp [R_ser, F_ser]

private lemma R_ser_constantCoeff : PowerSeries.constantCoeff R_ser = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact R_ser_coeff_zero

private lemma R_ser_coeff_one : PowerSeries.coeff 1 R_ser = 0 := by
  rw [R_ser, add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  simp [F_ser]

private lemma R_ser_coeff_two : PowerSeries.coeff 2 R_ser = 2 := by
  rw [R_ser, add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  simp [F_ser]

private noncomputable def gamma_ser : PowerSeries ℤ :=
  PowerSeries.mk fun k =>
    PowerSeries.coeff k (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 +
      (1 + PowerSeries.X) * R_ser) / 2

private lemma two_mul_gamma :
    PowerSeries.C (2 : ℤ) * gamma_ser =
      1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 +
      (1 + PowerSeries.X) * R_ser := by
  ext m
  rw [PowerSeries.coeff_C_mul, gamma_ser, PowerSeries.coeff_mk]
  have hdvd : 2 ∣ PowerSeries.coeff m
      (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 +
        (1 + PowerSeries.X) * R_ser) := by
    match m with
    | 0 =>
      simp [R_ser_constantCoeff]
    | 1 =>
      rw [map_add, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
        PowerSeries.coeff_succ_X_mul, R_ser_coeff_one, R_ser_coeff_zero]
      norm_num
    | 2 =>
      rw [map_add, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
        PowerSeries.coeff_succ_X_mul, R_ser_coeff_two, R_ser_coeff_one]
      norm_num
    | k + 3 =>
      rw [map_add, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
        PowerSeries.coeff_succ_X_mul]
      simp only [show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega,
        ↓reduceIte, add_zero, zero_add, mul_zero]
      exact dvd_add (R_ser_coeff_even (k + 3) (by omega)) (R_ser_coeff_even (k + 2) (by omega))
  exact Int.mul_ediv_cancel' hdvd

private noncomputable def alpha_ser : PowerSeries ℤ :=
  PowerSeries.mk fun k =>
    PowerSeries.coeff (k + 1)
      (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 -
        (1 + PowerSeries.X) * R_ser) / 2

private lemma two_mul_X_mul_alpha :
    PowerSeries.C (2 : ℤ) * PowerSeries.X * alpha_ser =
      1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 -
      (1 + PowerSeries.X) * R_ser := by
  ext m
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  match m with
  | 0 =>
    simp [R_ser_constantCoeff]
  | 1 =>
    rw [PowerSeries.coeff_succ_X_mul, alpha_ser, PowerSeries.coeff_mk]
    rw [map_sub, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
      PowerSeries.coeff_succ_X_mul, R_ser_coeff_one, R_ser_coeff_zero]
    norm_num
  | 2 =>
    rw [PowerSeries.coeff_succ_X_mul, alpha_ser, PowerSeries.coeff_mk]
    rw [map_sub, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
      PowerSeries.coeff_succ_X_mul, R_ser_coeff_two, R_ser_coeff_one]
    norm_num
  | k + 3 =>
    rw [PowerSeries.coeff_succ_X_mul, alpha_ser, PowerSeries.coeff_mk]
    have hdvd : 2 ∣ PowerSeries.coeff (k + 3)
        (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 -
          (1 + PowerSeries.X) * R_ser) := by
      rw [map_sub, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
        PowerSeries.coeff_succ_X_mul]
      simp only [show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega,
        ↓reduceIte, add_zero, mul_zero, zero_sub]
      exact dvd_neg.mpr (dvd_add (R_ser_coeff_even (k + 3) (by omega))
        (R_ser_coeff_even (k + 2) (by omega)))
    exact Int.mul_ediv_cancel' hdvd

private lemma gamma_coeff_zero : PowerSeries.coeff 0 gamma_ser = 1 := by
  have h := congr_arg (PowerSeries.coeff 0) two_mul_gamma
  rw [PowerSeries.coeff_C_mul] at h
  simp [R_ser_constantCoeff] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  omega

private lemma alpha_coeff_zero : PowerSeries.coeff 0 alpha_ser = 0 := by
  have h := congr_arg (PowerSeries.coeff 1) two_mul_X_mul_alpha
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at h
  rw [map_sub, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
    PowerSeries.coeff_succ_X_mul, R_ser_coeff_one, R_ser_coeff_zero] at h
  simp at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  omega

private lemma alpha_coeff_one : PowerSeries.coeff 1 alpha_ser = 0 := by
  have h := congr_arg (PowerSeries.coeff 2) two_mul_X_mul_alpha
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at h
  rw [map_sub, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, add_mul, one_mul, map_add,
    PowerSeries.coeff_succ_X_mul, R_ser_coeff_two, R_ser_coeff_one] at h
  simp at h
  omega

private lemma gamma_add_X_alpha :
    gamma_ser + PowerSeries.X * alpha_ser =
      1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 := by
  have h2 : PowerSeries.C (2 : ℤ) * (gamma_ser + PowerSeries.X * alpha_ser) =
      PowerSeries.C (2 : ℤ) * (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2) := by
    rw [mul_add, ← mul_assoc, two_mul_gamma, two_mul_X_mul_alpha]
    have hC2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := map_ofNat _ _
    rw [hC2]; ring
  ext m
  have hm := congr_arg (PowerSeries.coeff m) h2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hm
  omega

private lemma gamma_sub_X_alpha :
    gamma_ser - PowerSeries.X * alpha_ser = (1 + PowerSeries.X) * R_ser := by
  have h2 : PowerSeries.C (2 : ℤ) * (gamma_ser - PowerSeries.X * alpha_ser) =
      PowerSeries.C (2 : ℤ) * ((1 + PowerSeries.X) * R_ser) := by
    rw [mul_sub, ← mul_assoc, two_mul_gamma, two_mul_X_mul_alpha]
    have hC2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := map_ofNat _ _
    rw [hC2]; ring
  ext m
  have hm := congr_arg (PowerSeries.coeff m) h2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hm
  omega

private lemma gamma_mul_alpha :
    gamma_ser * alpha_ser = -(PowerSeries.X ^ 2) := by
  have h4 : PowerSeries.C (4 : ℤ) * PowerSeries.X * (gamma_ser * alpha_ser) =
      PowerSeries.C (4 : ℤ) * PowerSeries.X * (-(PowerSeries.X ^ 2)) := by
    have h1 : PowerSeries.C (4 : ℤ) * PowerSeries.X * (gamma_ser * alpha_ser) =
        (PowerSeries.C (2 : ℤ) * gamma_ser) *
          (PowerSeries.C (2 : ℤ) * PowerSeries.X * alpha_ser) := by
      have h42 : PowerSeries.C (4 : ℤ) = PowerSeries.C (2 : ℤ) * PowerSeries.C (2 : ℤ) := by
        rw [← map_mul]; norm_num
      rw [h42]; ring
    rw [h1, two_mul_gamma, two_mul_X_mul_alpha]
    have hsq : (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 +
        (1 + PowerSeries.X) * R_ser) *
        (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 -
        (1 + PowerSeries.X) * R_ser) =
        (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2) ^ 2 -
        (1 + PowerSeries.X) ^ 2 * R_ser ^ 2 := by ring
    rw [hsq, R_ser_sq]
    have hC2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := map_ofNat _ _
    have hC4 : PowerSeries.C (4 : ℤ) = (4 : PowerSeries ℤ) := map_ofNat _ _
    rw [hC2, hC4]; ring
  ext m
  have hm := congr_arg (PowerSeries.coeff (m + 1)) h4
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at hm
  omega

private lemma gamma_inv_exists : ∃ g : PowerSeries ℤ, gamma_ser * g = 1 := by
  have hu : IsUnit (PowerSeries.constantCoeff gamma_ser) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, gamma_coeff_zero]
    exact isUnit_one
  obtain ⟨u, hu'⟩ := (PowerSeries.isUnit_iff_constantCoeff.mpr hu)
  exact ⟨(u⁻¹ : (PowerSeries ℤ)ˣ), by rw [← hu']; exact u.mul_inv⟩

private lemma alpha_dvd_X_sq : ∃ a' : PowerSeries ℤ, alpha_ser = PowerSeries.X ^ 2 * a' := by
  refine ⟨PowerSeries.mk fun k => PowerSeries.coeff (k + 2) alpha_ser, ?_⟩
  ext m
  rw [PowerSeries.coeff_X_pow_mul']
  match m with
  | 0 => simp [alpha_coeff_zero]
  | 1 => simp [alpha_coeff_one]
  | k + 2 => simp

-- Congruence mod X^(M+1) on Polynomial (PowerSeries ℤ)
private def modX (M : ℕ) (p q : Polynomial (PowerSeries ℤ)) : Prop :=
  ∀ j k, k ≤ M → PowerSeries.coeff k (p.coeff j) = PowerSeries.coeff k (q.coeff j)

private lemma modX_refl (M : ℕ) (p : Polynomial (PowerSeries ℤ)) : modX M p p :=
  fun _ _ _ => rfl

private lemma modX_symm {M : ℕ} {p q : Polynomial (PowerSeries ℤ)} (h : modX M p q) :
    modX M q p := fun j k hk => (h j k hk).symm

private lemma modX_trans {M : ℕ} {p q r : Polynomial (PowerSeries ℤ)}
    (h1 : modX M p q) (h2 : modX M q r) : modX M p r :=
  fun j k hk => (h1 j k hk).trans (h2 j k hk)

private lemma modX_add {M : ℕ} {p1 q1 p2 q2 : Polynomial (PowerSeries ℤ)}
    (h1 : modX M p1 q1) (h2 : modX M p2 q2) : modX M (p1 + p2) (q1 + q2) := by
  intro j k hk
  simp only [Polynomial.coeff_add, map_add, h1 j k hk, h2 j k hk]

private lemma modX_sub {M : ℕ} {p1 q1 p2 q2 : Polynomial (PowerSeries ℤ)}
    (h1 : modX M p1 q1) (h2 : modX M p2 q2) : modX M (p1 - p2) (q1 - q2) := by
  intro j k hk
  simp only [Polynomial.coeff_sub, map_sub, h1 j k hk, h2 j k hk]

private lemma modX_mul {M : ℕ} {p1 q1 p2 q2 : Polynomial (PowerSeries ℤ)}
    (h1 : modX M p1 q1) (h2 : modX M p2 q2) : modX M (p1 * p2) (q1 * q2) := by
  intro j k hk
  simp only [Polynomial.coeff_mul, map_sum, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ab _ => ?_
  refine Finset.sum_congr rfl fun cd hcd => ?_
  have hsum : cd.1 + cd.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
  have hc : cd.1 ≤ M := by omega
  have hd : cd.2 ≤ M := by omega
  rw [h1 ab.1 cd.1 hc, h2 ab.2 cd.2 hd]

private lemma modX_C_X_pow_mul_zero (M : ℕ) (r : Polynomial (PowerSeries ℤ)) :
    modX M (Polynomial.C (PowerSeries.X ^ (M + 1)) * r) 0 := by
  intro j k hk
  rw [Polynomial.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega),
    Polynomial.coeff_zero, map_zero]

private lemma modX_cancel_P (M : ℕ) (P_rest D : Polynomial (PowerSeries ℤ))
    (h : modX M ((Polynomial.X + Polynomial.C PowerSeries.X * P_rest) * D) 0) :
    modX M D 0 := by
  have hmain : ∀ k, k ≤ M → ∀ j, PowerSeries.coeff k (D.coeff j) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk j
      have h0 := h (j + 1) k hk
      rw [Polynomial.coeff_zero, map_zero, add_mul, Polynomial.coeff_add, map_add,
        Polynomial.coeff_X_mul] at h0
      have hrest : PowerSeries.coeff k ((Polynomial.C PowerSeries.X * P_rest * D).coeff (j + 1)) = 0 := by
        rw [mul_assoc, Polynomial.coeff_C_mul]
        cases k with
        | zero => simp
        | succ k' =>
          rw [PowerSeries.coeff_succ_X_mul, Polynomial.coeff_mul, map_sum]
          refine Finset.sum_eq_zero fun ab _ => ?_
          rw [PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun cd hcd => ?_
          have hsum : cd.1 + cd.2 = k' := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
          have hd : cd.2 ≤ k' := by omega
          rw [ih cd.2 (by omega) (by omega) ab.2, mul_zero]
      rw [hrest, add_zero] at h0
      exact h0
  intro j k hk
  rw [Polynomial.coeff_zero, map_zero]
  exact hmain k hk j

private lemma poly_binom_coeff (n : ℕ) :
    (((1 + Polynomial.X) * (Polynomial.X - Polynomial.C PowerSeries.X)) ^ n :
      Polynomial (PowerSeries ℤ)).coeff n =
    ∑ k ∈ Finset.range (n + 1),
      PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) * PowerSeries.X ^ k := by
  rw [mul_pow, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (f := fun i j => ((1 + Polynomial.X : Polynomial (PowerSeries ℤ)) ^ n).coeff i *
      ((Polynomial.X - Polynomial.C PowerSeries.X : Polynomial (PowerSeries ℤ)) ^ n).coeff j) n]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : ((1 + Polynomial.X : Polynomial (PowerSeries ℤ)) ^ n).coeff k =
      PowerSeries.C (Nat.choose n k : ℤ) := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']
    rw [Finset.sum_eq_single k]
    · simp only [le_refl, tsub_self, Polynomial.coeff_natCast_ite, ↓reduceIte]
      ext m; simp
    · intro b _ hb
      by_cases hle : b ≤ k
      · rw [if_pos hle, Polynomial.coeff_natCast_ite, if_neg (by omega)]; simp
      · rw [if_neg hle]
    · intro hnk; exact absurd hk hnk
  have h2 : ((Polynomial.X - Polynomial.C PowerSeries.X : Polynomial (PowerSeries ℤ)) ^ n).coeff
      (n - k) = PowerSeries.C ((Nat.choose n k : ℤ) * (-1 : ℤ) ^ k) * PowerSeries.X ^ k := by
    rw [sub_eq_add_neg, add_pow]
    simp only [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (n - k)]
    · rw [show (-Polynomial.C PowerSeries.X : Polynomial (PowerSeries ℤ)) ^ (n - (n - k)) =
          Polynomial.C ((-PowerSeries.X) ^ k) by
        rw [show n - (n - k) = k by omega, ← map_neg, ← map_pow]]
      rw [mul_comm (Polynomial.X ^ (n - k)), mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul', if_pos le_rfl, tsub_self, Polynomial.coeff_natCast_ite,
        if_pos rfl]
      rw [Nat.choose_symm hkn, neg_pow]
      have hC : (Nat.choose n k : PowerSeries ℤ) = PowerSeries.C (Nat.choose n k : ℤ) := by
        ext m; simp
      have hneg1 : (-1 : PowerSeries ℤ) ^ k = PowerSeries.C ((-1 : ℤ) ^ k) := by
        rw [map_pow, map_neg, map_one]
      rw [hC, hneg1, map_mul]
      ring
    · intro b hb hbnk
      rw [show (-Polynomial.C PowerSeries.X : Polynomial (PowerSeries ℤ)) ^ (n - b) =
          Polynomial.C ((-PowerSeries.X) ^ (n - b)) by rw [← map_neg, ← map_pow]]
      rw [mul_comm (Polynomial.X ^ b), mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      split_ifs with hle
      · rw [Polynomial.coeff_natCast_ite, if_neg (by omega)]; simp
      · rw [mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  rw [h1, h2]
  rw [← mul_assoc, ← map_mul]
  congr 1
  congr 1
  ring

private noncomputable def termS1 (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ n * inv1pX ^ (2 * n + 1) *
    (∑ k ∈ Finset.range (n + 1),
      PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) * PowerSeries.X ^ k)

private noncomputable def S1_ser : PowerSeries ℤ :=
  PowerSeries.mk fun m => ∑ n ∈ Finset.range (m + 1), PowerSeries.coeff m (termS1 n)

private lemma R_mul_S1_eq_one : R_ser * S1_ser = 1 := by
  obtain ⟨γ_inv, hγ_inv⟩ := gamma_inv_exists
  obtain ⟨α', hα'⟩ := alpha_dvd_X_sq
  ext M
  rcases Nat.eq_zero_or_pos M with rfl | hMpos
  · simp [R_ser_constantCoeff, S1_ser, termS1, inv1pX]
  · set t : Polynomial (PowerSeries ℤ) := Polynomial.X
    set A : Polynomial (PowerSeries ℤ) := Polynomial.C ((1 + PowerSeries.X) ^ 2) * t
    set B : Polynomial (PowerSeries ℤ) :=
      Polynomial.C PowerSeries.X * (1 + t) * (t - Polynomial.C PowerSeries.X)
    set P : Polynomial (PowerSeries ℤ) := A - B
    set P_rest : Polynomial (PowerSeries ℤ) :=
      Polynomial.C ((2 : PowerSeries ℤ) + PowerSeries.X) * t -
        (1 + t) * (t - Polynomial.C PowerSeries.X)
    have hP_split : P = t + Polynomial.C PowerSeries.X * P_rest := by
      simp only [P, A, B, P_rest, t]
      have h1 : Polynomial.C ((1 + PowerSeries.X) ^ 2) =
          1 + Polynomial.C PowerSeries.X * Polynomial.C ((2 : PowerSeries ℤ) + PowerSeries.X) := by
        rw [← map_mul, ← map_one Polynomial.C, ← map_add]
        congr 1; ring
      rw [h1]; ring
    have hP_fact : P = (Polynomial.C gamma_ser - Polynomial.C PowerSeries.X * t) *
        (t - Polynomial.C alpha_ser) := by
      simp only [P, A, B, t]
      have hsum : Polynomial.C (gamma_ser + PowerSeries.X * alpha_ser) =
          Polynomial.C (1 + PowerSeries.X + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2) :=
        congr_arg Polynomial.C gamma_add_X_alpha
      have hprod : Polynomial.C (gamma_ser * alpha_ser) =
          Polynomial.C (-(PowerSeries.X ^ 2)) :=
        congr_arg Polynomial.C gamma_mul_alpha
      have hC2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := map_ofNat _ _
      rw [hC2] at hsum
      simp only [map_add, map_mul, map_neg, map_pow, map_one, map_ofNat] at hsum hprod ⊢
      linear_combination -hsum * Polynomial.X + hprod
    set S_poly : Polynomial (PowerSeries ℤ) :=
      ∑ n ∈ Finset.range (M + 1), B ^ n * A ^ (M - n)
    have hPS : modX M (P * S_poly) (A ^ (M + 1)) := by
      have hgeom : (A - B) * S_poly = A ^ (M + 1) - B ^ (M + 1) := by
        have := geom_sum₂_mul A B (M + 1)
        have hswap : S_poly = ∑ i ∈ Finset.range (M + 1), A ^ i * B ^ (M - i) := by
          rw [← Finset.sum_range_reflect (fun i => A ^ i * B ^ (M - i)) (M + 1)]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [show M + 1 - 1 - i = M - i by omega, show M - (M - i) = i by omega, mul_comm]
        rw [hswap, mul_comm]
        simpa [Nat.add_sub_cancel] using this
      rw [show P * S_poly = A ^ (M + 1) - B ^ (M + 1) from hgeom]
      have hBpow : modX M (B ^ (M + 1)) 0 := by
        have : B ^ (M + 1) = Polynomial.C (PowerSeries.X ^ (M + 1)) *
            (((1 + t) * (t - Polynomial.C PowerSeries.X)) ^ (M + 1)) := by
          rw [show B = Polynomial.C PowerSeries.X * ((1 + t) * (t - Polynomial.C PowerSeries.X)) by
            simp only [B]; ring]
          rw [mul_pow, ← map_pow]
        rw [this]
        exact modX_C_X_pow_mul_zero M _
      have := modX_sub (modX_refl M (A ^ (M + 1))) hBpow
      simpa using this
    set Q1 : Polynomial (PowerSeries ℤ) :=
      ∑ j ∈ Finset.range (M + 1), Polynomial.C ((PowerSeries.X * γ_inv) ^ j) * t ^ j
    have hQ1 : modX M ((Polynomial.C gamma_ser - Polynomial.C PowerSeries.X * t) * Q1)
        (Polynomial.C gamma_ser) := by
      set u : Polynomial (PowerSeries ℤ) := Polynomial.C (PowerSeries.X * γ_inv) * t
      have hQ1_eq : Q1 = ∑ j ∈ Finset.range (M + 1), u ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [u, mul_pow, ← map_pow]
      have hfac : Polynomial.C gamma_ser - Polynomial.C PowerSeries.X * t =
          Polynomial.C gamma_ser * (1 - u) := by
        simp only [u, mul_sub, mul_one, ← mul_assoc, ← map_mul]
        have : gamma_ser * PowerSeries.X * γ_inv = PowerSeries.X := by
          calc gamma_ser * PowerSeries.X * γ_inv
              = PowerSeries.X * (gamma_ser * γ_inv) := by ring
            _ = PowerSeries.X * 1 := by rw [hγ_inv]
            _ = PowerSeries.X := mul_one _
        rw [this]
      rw [hfac, hQ1_eq, mul_assoc]
      have hgeom : (1 - u) * ∑ j ∈ Finset.range (M + 1), u ^ j = 1 - u ^ (M + 1) := by
        have := mul_neg_geom_sum u (M + 1)
        have h1 : (1 - u) * ∑ i ∈ Finset.range (M + 1), u ^ i =
            -((u - 1) * ∑ i ∈ Finset.range (M + 1), u ^ i) := by ring
        rw [h1, mul_comm (u - 1), geom_sum_mul]
        ring
      rw [hgeom, mul_sub, mul_one]
      have hupow : modX M (Polynomial.C gamma_ser * u ^ (M + 1)) 0 := by
        have : Polynomial.C gamma_ser * u ^ (M + 1) =
            Polynomial.C (PowerSeries.X ^ (M + 1)) *
              (Polynomial.C (gamma_ser * γ_inv ^ (M + 1)) * t ^ (M + 1)) := by
          simp only [u, mul_pow, map_mul, map_pow]; ring
        rw [this]
        exact modX_C_X_pow_mul_zero M _
      have := modX_sub (modX_refl M (Polynomial.C gamma_ser)) hupow
      simpa using this
    set Q2 : Polynomial (PowerSeries ℤ) :=
      ∑ j ∈ Finset.range M, Polynomial.C (alpha_ser ^ j) * t ^ (M - 1 - j)
    have hQ2 : modX M (Polynomial.C alpha_ser * ((t - Polynomial.C alpha_ser) * Q2))
        (Polynomial.C alpha_ser * t ^ M) := by
      have hgeom : (t - Polynomial.C alpha_ser) * Q2 =
          t ^ M - Polynomial.C (alpha_ser ^ M) := by
        have hswap : Q2 = ∑ i ∈ Finset.range M, t ^ i * (Polynomial.C alpha_ser) ^ (M - 1 - i) := by
          rw [← Finset.sum_range_reflect (fun i => t ^ i * (Polynomial.C alpha_ser) ^ (M - 1 - i)) M]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hiM : i < M := Finset.mem_range.mp hi
          rw [show M - 1 - (M - 1 - i) = i by omega, map_pow, mul_comm]
        rw [hswap, mul_comm, geom_sum₂_mul, map_pow]
      rw [hgeom, mul_sub, ← map_mul, ← pow_succ']
      have hαpow : modX M (Polynomial.C (alpha_ser ^ (M + 1))) 0 := by
        have : Polynomial.C (alpha_ser ^ (M + 1)) =
            Polynomial.C (PowerSeries.X ^ (M + 1)) *
              Polynomial.C (PowerSeries.X ^ (M + 1) * α' ^ (M + 1)) := by
          rw [hα', mul_pow, ← pow_mul, show 2 * (M + 1) = (M + 1) + (M + 1) by omega,
            pow_add, mul_assoc, map_mul]
        rw [this]
        exact modX_C_X_pow_mul_zero M _
      have := modX_sub (modX_refl M (Polynomial.C alpha_ser * t ^ M)) hαpow
      simpa using this
    set H : Polynomial (PowerSeries ℤ) := t ^ M * Q1 + Polynomial.C alpha_ser * Q2
    have hPH : modX M (P * H)
        (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * t ^ (M + 1)) := by
      have h1 : P * H =
          (t - Polynomial.C alpha_ser) * t ^ M *
            ((Polynomial.C gamma_ser - Polynomial.C PowerSeries.X * t) * Q1) +
          (Polynomial.C gamma_ser - Polynomial.C PowerSeries.X * t) *
            (Polynomial.C alpha_ser * ((t - Polynomial.C alpha_ser) * Q2)) := by
        rw [hP_fact]; simp only [H]; ring
      rw [h1]
      have hterm1 := modX_mul (modX_refl M ((t - Polynomial.C alpha_ser) * t ^ M)) hQ1
      have hterm2 := modX_mul
        (modX_refl M (Polynomial.C gamma_ser - Polynomial.C PowerSeries.X * t)) hQ2
      have hsum := modX_add hterm1 hterm2
      have halg : (t - Polynomial.C alpha_ser) * t ^ M * Polynomial.C gamma_ser +
          (Polynomial.C gamma_ser - Polynomial.C PowerSeries.X * t) *
            (Polynomial.C alpha_ser * t ^ M) =
          Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * t ^ (M + 1) := by
        simp only [map_sub, map_mul, pow_succ]; ring
      rw [halg] at hsum
      exact hsum
    have hA_pow : A ^ (M + 1) = Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * t ^ (M + 1) := by
      simp only [A, mul_pow, ← map_pow, ← pow_mul, show 2 * (M + 1) = 2 * M + 2 by omega]
    have hdiff_zero : modX M
        (P * (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * S_poly -
          Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * H)) 0 := by
      rw [mul_sub]
      have hL : modX M (P * (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * S_poly))
          (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) *
            Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * t ^ (M + 1)) := by
        rw [show P * (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * S_poly) =
            Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * (P * S_poly) by ring]
        have h1 := modX_mul (modX_refl M (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser))) hPS
        rw [hA_pow] at h1
        rw [mul_assoc]
        exact h1
      have hR : modX M (P * (Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * H))
          (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) *
            Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * t ^ (M + 1)) := by
        rw [show P * (Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * H) =
            Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * (P * H) by ring]
        have := modX_mul (modX_refl M (Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)))) hPH
        rw [show Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) *
            (Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * t ^ (M + 1)) =
            Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) *
              Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * t ^ (M + 1) by ring] at this
        exact this
      have := modX_sub hL hR
      simpa using this
    rw [hP_split] at hdiff_zero
    have hcancel := modX_cancel_P M P_rest _ hdiff_zero
    have heq_tM : ∀ k, k ≤ M →
        PowerSeries.coeff k
          ((Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * S_poly).coeff M) =
        PowerSeries.coeff k
          ((Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * H).coeff M) := by
      intro k hk
      have := hcancel M k hk
      rw [Polynomial.coeff_sub, map_sub, Polynomial.coeff_zero, map_zero, sub_eq_zero] at this
      exact this
    have hH_coeff : H.coeff M = 1 := by
      simp only [H, Polynomial.coeff_add, Polynomial.coeff_C_mul]
      have h1 : (t ^ M * Q1).coeff M = 1 := by
        rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, tsub_self]
        simp only [Q1, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
        rw [Finset.sum_eq_single 0]
        · simp [t]
        · intro j _ hj0
          rw [Polynomial.coeff_X_pow, if_neg (Ne.symm hj0), mul_zero]
        · intro h0; exact absurd (Finset.mem_range.mpr (by omega)) h0
      have h2 : Q2.coeff M = 0 := by
        simp only [Q2, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjM : j < M := Finset.mem_range.mp hj
        rw [Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
      rw [h1, h2, mul_zero, add_zero]
    have hS_coeff : S_poly.coeff M =
        ∑ n ∈ Finset.range (M + 1),
          (1 + PowerSeries.X) ^ (2 * (M - n)) * PowerSeries.X ^ n *
            (∑ k ∈ Finset.range (n + 1),
              PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) * PowerSeries.X ^ k) := by
      simp only [S_poly, Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hterm : B ^ n * A ^ (M - n) =
          Polynomial.C ((1 + PowerSeries.X) ^ (2 * (M - n)) * PowerSeries.X ^ n) *
            (t ^ (M - n) * ((1 + t) * (t - Polynomial.C PowerSeries.X)) ^ n) := by
        simp only [A, B, t, mul_pow, map_mul, map_pow, ← pow_mul]
        ring
      rw [hterm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', if_pos (by omega),
        show M - (M - n) = n by omega, poly_binom_coeff]
    -- Now multiply the coefficient equality (for all k ≤ M) by inv1pX^(2M+2)
    have hmul_inv : PowerSeries.coeff M
        (inv1pX ^ (2 * M + 2) *
          ((Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * S_poly).coeff M)) =
        PowerSeries.coeff M
          (inv1pX ^ (2 * M + 2) *
            ((Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * H).coeff M)) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun ab hab => ?_
      have hsum : ab.1 + ab.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have hb : ab.2 ≤ M := by omega
      rw [heq_tM ab.2 hb]
    have hRHS : inv1pX ^ (2 * M + 2) *
        ((Polynomial.C ((1 + PowerSeries.X) ^ (2 * M + 2)) * H).coeff M) = 1 := by
      rw [Polynomial.coeff_C_mul, hH_coeff, mul_one, ← mul_pow, mul_comm inv1pX, inv1pX_mul, one_pow]
    have hLHS : PowerSeries.coeff M
        (inv1pX ^ (2 * M + 2) *
          ((Polynomial.C (gamma_ser - PowerSeries.X * alpha_ser) * S_poly).coeff M)) =
        PowerSeries.coeff M (R_ser * S1_ser) := by
      rw [Polynomial.coeff_C_mul, gamma_sub_X_alpha, hS_coeff]
      have hsum_eq : inv1pX ^ (2 * M + 2) *
          ((1 + PowerSeries.X) * R_ser *
            ∑ n ∈ Finset.range (M + 1),
              (1 + PowerSeries.X) ^ (2 * (M - n)) * PowerSeries.X ^ n *
                (∑ k ∈ Finset.range (n + 1),
                  PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) *
                    PowerSeries.X ^ k)) =
          R_ser * ∑ n ∈ Finset.range (M + 1), termS1 n := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        simp only [termS1]
        have hpow_split : 2 * M + 2 = (2 * (M - n) + 1) + (2 * n + 1) := by omega
        have hcancel_inv : inv1pX ^ (2 * M + 2) *
            ((1 + PowerSeries.X) * (1 + PowerSeries.X) ^ (2 * (M - n))) =
            inv1pX ^ (2 * n + 1) := by
          rw [hpow_split, pow_add, ← pow_succ', mul_assoc,
            show inv1pX ^ (2 * (M - n) + 1) * (inv1pX ^ (2 * n + 1) *
              (1 + PowerSeries.X) ^ (2 * (M - n) + 1)) =
              ((1 + PowerSeries.X) * inv1pX) ^ (2 * (M - n) + 1) * inv1pX ^ (2 * n + 1) by
              rw [mul_pow]; ring]
          rw [inv1pX_mul, one_pow, one_mul]
        calc inv1pX ^ (2 * M + 2) *
              ((1 + PowerSeries.X) * R_ser *
                ((1 + PowerSeries.X) ^ (2 * (M - n)) * PowerSeries.X ^ n *
                  ∑ k ∈ Finset.range (n + 1),
                    PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) *
                      PowerSeries.X ^ k))
            = R_ser * (PowerSeries.X ^ n *
                (inv1pX ^ (2 * M + 2) *
                  ((1 + PowerSeries.X) * (1 + PowerSeries.X) ^ (2 * (M - n)))) *
                ∑ k ∈ Finset.range (n + 1),
                  PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) *
                    PowerSeries.X ^ k) := by ring
          _ = R_ser * (PowerSeries.X ^ n * inv1pX ^ (2 * n + 1) *
                ∑ k ∈ Finset.range (n + 1),
                  PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) *
                    PowerSeries.X ^ k) := by rw [hcancel_inv]
      rw [hsum_eq, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun ab hab => ?_
      have hsum : ab.1 + ab.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have hb : ab.2 ≤ M := by omega
      congr 1
      rw [map_sum, S1_ser, PowerSeries.coeff_mk]
      rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hb))]
      intro n hn hnot
      have hlt : ab.2 < n := by
        simp only [Finset.mem_range] at hn hnot; omega
      simp only [termS1, mul_assoc, PowerSeries.coeff_X_pow_mul']
      rw [if_neg (by omega)]
    rw [hLHS, hRHS] at hmul_inv
    exact hmul_inv

private lemma S1_eq_F : S1_ser = F_ser := by
  have hFR : F_ser * R_ser = 1 := by
    simp only [R_ser]
    rw [show F_ser * ((1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) * F_ser) =
        F_ser ^ 2 * (1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2) by ring]
    exact F_ser_sq_mul
  calc S1_ser = 1 * S1_ser := (one_mul _).symm
    _ = (F_ser * R_ser) * S1_ser := by rw [hFR]
    _ = F_ser * (R_ser * S1_ser) := mul_assoc _ _ _
    _ = F_ser * 1 := by rw [R_mul_S1_eq_one]
    _ = F_ser := mul_one _

-- Part A: S2 mod 2 equals X^2
private noncomputable def termS2 (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ (n + 1) * inv1pX ^ (2 * n + 1) * PowerSeries.C ((n : ℤ) ^ 2) *
    (∑ k ∈ Finset.range (n + 1),
      PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) * PowerSeries.X ^ k)

private noncomputable def S2_ser : PowerSeries ℤ :=
  PowerSeries.mk fun m => ∑ n ∈ Finset.range (m + 1), PowerSeries.coeff m (termS2 n)

private lemma S2_mod2_eq :
    PowerSeries.map (Int.castRingHom (ZMod 2)) S2_ser = PowerSeries.X ^ 2 := by
  set φ2 : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  set Φ2 : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map φ2
  set u : PowerSeries (ZMod 2) := Φ2 inv1pX
  have hu : (1 + PowerSeries.X) * u = 1 := by
    have h := congr_arg Φ2 inv1pX_mul
    simpa [Φ2, u] using h
  have hz2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h1pX_sq : (1 + PowerSeries.X : PowerSeries (ZMod 2)) ^ 2 = 1 + PowerSeries.X ^ 2 := by
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      have : (2 : ZMod 2) = 0 := by decide
      rw [← map_ofNat PowerSeries.C 2, this, map_zero]
    calc (1 + PowerSeries.X : PowerSeries (ZMod 2)) ^ 2
        = 1 + 2 * PowerSeries.X + PowerSeries.X ^ 2 := by ring
      _ = 1 + 0 * PowerSeries.X + PowerSeries.X ^ 2 := by rw [h2]
      _ = 1 + PowerSeries.X ^ 2 := by ring
  have hS2_mul : (1 + PowerSeries.X) ^ 2 * Φ2 S2_ser =
      (1 + PowerSeries.X) ^ 2 * PowerSeries.X ^ 2 := by
    -- Actually prove (1 + (X*u)^2) * Φ2 S2_ser = (X*u)^2, then use 1 + (X*u)^2 = u^2!
    have hkey : (1 + (PowerSeries.X * u) ^ 2) * Φ2 S2_ser = (PowerSeries.X * u) ^ 2 := by
      ext m
      have hS2_coeff : ∀ k, PowerSeries.coeff k (Φ2 S2_ser) =
          ∑ n ∈ Finset.range (k + 1),
            PowerSeries.coeff k (if Odd n then (PowerSeries.X * u) ^ (n + 1) else 0) := by
        intro k
        rw [PowerSeries.coeff_map, S2_ser, PowerSeries.coeff_mk, map_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← PowerSeries.coeff_map]
        congr 1
        simp only [Φ2, termS2, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C,
          map_sum, u]
        have hP2 : (∑ x ∈ Finset.range (n + 1),
            PowerSeries.C (φ2 (Nat.choose n x : ℤ)) ^ 2 * PowerSeries.C (φ2 (-1 : ℤ)) ^ x *
              PowerSeries.X ^ x) =
            (1 + PowerSeries.X) ^ n := by
          conv_rhs => rw [add_comm, add_pow]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [one_pow, mul_one, mul_comm]
          congr 1
          have hsq : PowerSeries.C (φ2 (Nat.choose n j : ℤ)) ^ 2 * PowerSeries.C (φ2 (-1 : ℤ)) ^ j =
              PowerSeries.C ((Nat.choose n j : ℕ) : ZMod 2) := by
            rw [← map_pow PowerSeries.C, ← map_pow PowerSeries.C, ← map_mul PowerSeries.C]
            congr 1
            simp only [φ2, map_neg, map_one, map_natCast]
            have hneg : (-1 : ZMod 2) = 1 := by decide
            rw [hneg, one_pow, mul_one]
            rcases hz2 (Nat.choose n j : ZMod 2) with h | h <;> simp [h]
          rw [hsq]
          ext r; simp
        rw [hP2]
        have hn_sq : PowerSeries.C (φ2 (n : ℤ)) ^ 2 = if Odd n then 1 else 0 := by
          rw [← map_pow]
          have hval : (φ2 (n : ℤ)) ^ 2 = if Odd n then 1 else 0 := by
            simp only [φ2, map_natCast]
            rcases Nat.even_or_odd n with ⟨q, rfl⟩ | ⟨q, rfl⟩
            · have hnot : ¬ Odd (q + q) := by rw [Nat.not_odd_iff_even]; exact ⟨q, rfl⟩
              rw [if_neg hnot]
              have h2 : ((q + q : ℕ) : ZMod 2) = 0 := by
                push_cast; have : (2 : ZMod 2) = 0 := by decide
                calc (q : ZMod 2) + (q : ZMod 2) = 2 * (q : ZMod 2) := by ring
                  _ = 0 := by rw [this, zero_mul]
              rw [h2]; simp
            · rw [if_pos ⟨q, rfl⟩]
              have h1 : ((2 * q + 1 : ℕ) : ZMod 2) = 1 := by
                push_cast; have : (2 : ZMod 2) = 0 := by decide
                rw [this, zero_mul, zero_add]
              rw [h1]; simp
          rw [hval]
          split_ifs <;> simp
        rw [hn_sq]
        split_ifs with hodd
        · rw [mul_one]
          have hred : u ^ (2 * n + 1) * (1 + PowerSeries.X) ^ n = u ^ (n + 1) := by
            rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
            calc u ^ n * u ^ (n + 1) * (1 + PowerSeries.X) ^ n
                = ((1 + PowerSeries.X) * u) ^ n * u ^ (n + 1) := by rw [mul_pow]; ring
              _ = 1 ^ n * u ^ (n + 1) := by rw [hu]
              _ = u ^ (n + 1) := by simp
          rw [mul_assoc, hred, mul_pow]
        · simp
      -- Rewrite LHS using truncation at M = m
      have hLHS : PowerSeries.coeff m ((1 + (PowerSeries.X * u) ^ 2) * Φ2 S2_ser) =
          PowerSeries.coeff m ((1 + (PowerSeries.X * u) ^ 2) *
            ∑ j ∈ Finset.range (m + 1), (PowerSeries.X * u) ^ (2 * j + 2)) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun ab hab => ?_
        have hsum : ab.1 + ab.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
        have hb : ab.2 ≤ m := by omega
        congr 1
        rw [hS2_coeff ab.2, map_sum]
        have hfilt : ∑ j ∈ Finset.range (m + 1),
            PowerSeries.coeff ab.2 ((PowerSeries.X * u) ^ (2 * j + 2)) =
            ∑ j ∈ (Finset.range (m + 1)).filter (fun j => 2 * j + 1 ≤ ab.2),
              PowerSeries.coeff ab.2 ((PowerSeries.X * u) ^ (2 * j + 2)) := by
          rw [← Finset.sum_subset
            (Finset.filter_subset (fun j => 2 * j + 1 ≤ ab.2) (Finset.range (m + 1)))]
          intro j hj hnot
          simp only [Finset.mem_filter, hj, true_and, not_le] at hnot
          rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hfilt]
        have hsplit : ∑ n ∈ Finset.range (ab.2 + 1),
            PowerSeries.coeff ab.2 (if Odd n then (PowerSeries.X * u) ^ (n + 1) else 0) =
            ∑ j ∈ (Finset.range (m + 1)).filter (fun j => 2 * j + 1 ≤ ab.2),
              PowerSeries.coeff ab.2 ((PowerSeries.X * u) ^ (2 * j + 2)) := by
          have hite : ∑ n ∈ Finset.range (ab.2 + 1),
              PowerSeries.coeff ab.2 (if Odd n then (PowerSeries.X * u) ^ (n + 1) else 0) =
              ∑ n ∈ (Finset.range (ab.2 + 1)).filter Odd,
                PowerSeries.coeff ab.2 ((PowerSeries.X * u) ^ (n + 1)) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun n _ => ?_
            split_ifs <;> simp
          rw [hite]
          refine Finset.sum_bij (fun n _ => n / 2) ?_ ?_ ?_ ?_
          · intro n hn
            simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
            rcases hn.2 with ⟨q, rfl⟩
            exact ⟨by omega, by omega⟩
          · intro n1 hn1 n2 hn2 hdiv
            simp only [Finset.mem_filter] at hn1 hn2
            rcases hn1.2 with ⟨q1, rfl⟩; rcases hn2.2 with ⟨q2, rfl⟩; omega
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj
            exact ⟨2 * j + 1,
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨j, rfl⟩⟩,
              by omega⟩
          · intro n hn
            simp only [Finset.mem_filter] at hn
            rcases hn.2 with ⟨q, rfl⟩
            have hq : (2 * q + 1) / 2 = q := by omega
            rw [hq, show 2 * q + 1 + 1 = 2 * q + 2 by omega]
        exact hsplit
      rw [hLHS]
      have hgeom : (1 + (PowerSeries.X * u) ^ 2) *
          ∑ j ∈ Finset.range (m + 1), (PowerSeries.X * u) ^ (2 * j + 2) =
          (PowerSeries.X * u) ^ 2 + (PowerSeries.X * u) ^ (2 * m + 4) := by
        have hsub : ∀ a b : PowerSeries (ZMod 2), a - b = a + b := by
          intro a b; ext k
          have : -(PowerSeries.coeff k b) = PowerSeries.coeff k b := by
            rcases hz2 (PowerSeries.coeff k b) with h | h <;> simp [h]
          simp [sub_eq_add_neg, this]
        have h1 : ∑ j ∈ Finset.range (m + 1), (PowerSeries.X * u) ^ (2 * j + 2) =
            (PowerSeries.X * u) ^ 2 *
              ∑ j ∈ Finset.range (m + 1), ((PowerSeries.X * u) ^ 2) ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← pow_mul, ← pow_add]; congr 1; omega
        rw [h1, ← mul_assoc, mul_comm (1 + (PowerSeries.X * u) ^ 2), mul_assoc,
          ← hsub 1 ((PowerSeries.X * u) ^ 2)]
        have hg : (1 - (PowerSeries.X * u) ^ 2) *
            ∑ j ∈ Finset.range (m + 1), ((PowerSeries.X * u) ^ 2) ^ j =
            1 - ((PowerSeries.X * u) ^ 2) ^ (m + 1) := by
          have := geom_sum_mul ((PowerSeries.X * u) ^ 2) (m + 1)
          have h2 : (1 - (PowerSeries.X * u) ^ 2) *
              ∑ j ∈ Finset.range (m + 1), ((PowerSeries.X * u) ^ 2) ^ j =
              -((∑ j ∈ Finset.range (m + 1), ((PowerSeries.X * u) ^ 2) ^ j) *
                ((PowerSeries.X * u) ^ 2 - 1)) := by ring
          rw [h2, this]; ring
        rw [hg, hsub, mul_add, mul_one, ← pow_mul, ← pow_add]
        congr 2; omega
      rw [hgeom, map_add]
      have hzero : PowerSeries.coeff m ((PowerSeries.X * u) ^ (2 * m + 4)) = 0 := by
        rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
      rw [hzero, add_zero]
    have h1u : (1 + PowerSeries.X) ^ 2 * (1 + (PowerSeries.X * u) ^ 2) = 1 := by
      calc (1 + PowerSeries.X) ^ 2 * (1 + (PowerSeries.X * u) ^ 2)
          = (1 + PowerSeries.X) ^ 2 + PowerSeries.X ^ 2 * ((1 + PowerSeries.X) * u) ^ 2 := by
            rw [mul_pow, mul_pow]; ring
        _ = (1 + PowerSeries.X ^ 2) + PowerSeries.X ^ 2 * 1 ^ 2 := by rw [h1pX_sq, hu]
        _ = 1 + (PowerSeries.X ^ 2 + PowerSeries.X ^ 2) := by ring
        _ = 1 := by
          have : (PowerSeries.X ^ 2 + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) = 0 := by
            ext k
            rw [map_add, map_zero]
            rcases hz2 (PowerSeries.coeff k (PowerSeries.X ^ 2)) with h | h <;>
              (rw [h]; decide)
          rw [this, add_zero]
    have hXu : (1 + PowerSeries.X) ^ 2 * (PowerSeries.X * u) ^ 2 = PowerSeries.X ^ 2 := by
      calc (1 + PowerSeries.X) ^ 2 * (PowerSeries.X * u) ^ 2
          = PowerSeries.X ^ 2 * ((1 + PowerSeries.X) * u) ^ 2 := by rw [mul_pow, mul_pow]; ring
        _ = PowerSeries.X ^ 2 := by rw [hu, one_pow, mul_one]
    have hres := congr_arg ((1 + PowerSeries.X) ^ 2 * ·) hkey
    rw [← mul_assoc, h1u, one_mul, hXu] at hres
    rw [hres]
  -- Cancel (1 + X)^2 using u^2
  calc Φ2 S2_ser = ((1 + PowerSeries.X) * u) ^ 2 * Φ2 S2_ser := by rw [hu, one_pow, one_mul]
    _ = u ^ 2 * ((1 + PowerSeries.X) ^ 2 * Φ2 S2_ser) := by rw [mul_pow]; ring
    _ = u ^ 2 * ((1 + PowerSeries.X) ^ 2 * PowerSeries.X ^ 2) := by rw [hS2_mul]
    _ = ((1 + PowerSeries.X) * u) ^ 2 * PowerSeries.X ^ 2 := by rw [mul_pow]; ring
    _ = PowerSeries.X ^ 2 := by rw [hu, one_pow, one_mul]

-- Part C: Central binomial coefficient mod 4 via Lucas mod 2
private lemma odd_choose_two_mul_sub_one_iff (m : ℕ) (hm : 1 ≤ m) :
    Odd (Nat.choose (2 * m - 1) (m - 1)) ↔ ∃ j : ℕ, m = 2 ^ j := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hq1 : 1 ≤ q := by omega
      have h2m1 : 2 * m - 1 = 2 * (2 * q - 1) + 1 := by omega
      have hm1 : m - 1 = 2 * (q - 1) + 1 := by omega
      rw [h2m1, hm1]
      have hluc : Nat.choose (2 * (2 * q - 1) + 1) (2 * (q - 1) + 1) ≡
          Nat.choose (2 * q - 1) (q - 1) * Nat.choose 1 1 [MOD 2] := by
        simpa [Nat.mul_add_div (by omega : 0 < 2), Nat.mul_add_mod] using
          Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := 2 * (2 * q - 1) + 1)
            (k := 2 * (q - 1) + 1)
      simp only [Nat.choose_self, mul_one, Nat.ModEq] at hluc
      have hodd_iff : Odd (Nat.choose (2 * (2 * q - 1) + 1) (2 * (q - 1) + 1)) ↔
          Odd (Nat.choose (2 * q - 1) (q - 1)) := by
        rw [Nat.odd_iff, Nat.odd_iff, hluc]
      have ihq : Odd (Nat.choose (2 * q - 1) (q - 1)) ↔ ∃ j : ℕ, q = 2 ^ j :=
        ih q (by omega) hq1
      refine hodd_iff.trans (ihq.trans ?_)
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨j + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨j, hj⟩
        cases j with
        | zero => omega
        | succ j' => exact ⟨j', by rw [pow_succ] at hj; omega⟩
    · cases q with
      | zero =>
        have hm1 : m = 1 := by omega
        subst hm1
        simp only [Nat.reduceMul, Nat.sub_self, Nat.choose_zero_right]
        exact ⟨fun _ => ⟨0, rfl⟩, fun _ => odd_one⟩
      | succ r =>
        have h2m1 : 2 * m - 1 = 2 * (2 * (r + 1)) + 1 := by omega
        have hm1 : m - 1 = 2 * (r + 1) := by omega
        rw [h2m1, hm1]
        have hluc : Nat.choose (2 * (2 * (r + 1)) + 1) (2 * (r + 1)) ≡
            Nat.choose (2 * (r + 1)) (r + 1) * Nat.choose 1 0 [MOD 2] := by
          simpa [Nat.mul_add_div (by omega : 0 < 2), Nat.mul_add_mod] using
            Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
              (n := 2 * (2 * (r + 1)) + 1) (k := 2 * (r + 1))
        simp only [Nat.choose_zero_right, mul_one, Nat.ModEq] at hluc
        have hev : Even (Nat.choose (2 * (r + 1)) (r + 1)) :=
          even_iff_two_dvd.mpr (even_choose_two_mul (r + 1) (by omega))
        have hnotodd : ¬ Odd (Nat.choose (2 * (2 * (r + 1)) + 1) (2 * (r + 1))) := by
          rw [Nat.odd_iff, hluc]
          have h0 : Nat.choose (2 * (r + 1)) (r + 1) % 2 = 0 := Nat.even_iff.mp hev
          omega
        have hnotpow : ¬ ∃ j : ℕ, m = 2 ^ j := by
          rintro ⟨j, hj⟩
          cases j with
          | zero => omega
          | succ j' =>
            have h2dvd : 2 ∣ m := ⟨2 ^ j', by rw [hj, pow_succ]; ring⟩
            omega
        exact ⟨fun h => absurd h hnotodd, fun h => absurd h hnotpow⟩

open Classical in
private lemma choose_two_mul_mod4 (m : ℕ) (hm : 1 ≤ m) :
    (Nat.choose (2 * m) m : ZMod 4) = if ∃ j : ℕ, m = 2 ^ j then 2 else 0 := by
  have heq : Nat.choose (2 * m) m = 2 * Nat.choose (2 * m - 1) (m - 1) :=
    choose_two_mul_eq_two_mul m hm
  rw [heq, Nat.cast_mul, Nat.cast_ofNat]
  split_ifs with hpow
  · have hodd := (odd_choose_two_mul_sub_one_iff m hm).mpr hpow
    rcases hodd with ⟨t, ht⟩
    rw [ht, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have h4 : (4 : ZMod 4) = 0 := by decide
    calc (2 : ZMod 4) * (2 * (t : ZMod 4) + 1)
        = 4 * (t : ZMod 4) + 2 := by ring
      _ = 2 := by rw [h4, zero_mul, zero_add]
  · have hev : Even (Nat.choose (2 * m - 1) (m - 1)) :=
      Nat.not_odd_iff_even.mp (fun h => hpow ((odd_choose_two_mul_sub_one_iff m hm).mp h))
    rcases hev with ⟨t, ht⟩
    rw [ht, Nat.cast_add]
    have h4 : (4 : ZMod 4) = 0 := by decide
    calc (2 : ZMod 4) * ((t : ZMod 4) + (t : ZMod 4))
        = 4 * (t : ZMod 4) := by ring
      _ = 0 := by rw [h4, zero_mul]

private lemma a246423_mod4_decomp (m : ℕ) :
    (a246423 m : ZMod 4) =
      ((PowerSeries.coeff m S1_ser : ℤ) : ZMod 4) +
      2 * ((PowerSeries.coeff m S2_ser : ℤ) : ZMod 4) := by
  set φ4 : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  set Φ4 : PowerSeries ℤ →+* PowerSeries (ZMod 4) := PowerSeries.map φ4
  have hinv : Φ4 inv1m3X = Φ4 inv1pX := by
    ext k
    simp only [Φ4, PowerSeries.coeff_map, inv1m3X, inv1pX, PowerSeries.coeff_mk, φ4, map_pow]
    have h3 : (3 : ZMod 4) = (-1 : ZMod 4) := by decide
    simp [h3]
  have hP1 : ∀ n : ℕ,
      Φ4 (∑ k ∈ Finset.range (n + 1),
        PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * 2 ^ k) * PowerSeries.X ^ k) =
      1 + PowerSeries.C (2 : ZMod 4) * PowerSeries.C ((n : ZMod 4) ^ 2) * PowerSeries.X := by
    intro n
    ext k
    have hsum : PowerSeries.coeff k
        (Φ4 (∑ j ∈ Finset.range (n + 1),
          PowerSeries.C ((Nat.choose n j : ℤ) ^ 2 * 2 ^ j) * PowerSeries.X ^ j)) =
        ∑ j ∈ Finset.range (n + 1),
          PowerSeries.coeff k (PowerSeries.C (φ4 ((Nat.choose n j : ℤ) ^ 2 * 2 ^ j)) *
            PowerSeries.X ^ j) := by
      simp only [Φ4, map_sum, map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X]
    rw [hsum]
    cases k with
    | zero =>
      rw [Finset.sum_eq_single 0]
      · simp [φ4]
      · intro b _ hb0
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hb0), mul_zero]
      · intro h0; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) h0
    | succ k' =>
      cases k' with
      | zero =>
        cases n with
        | zero =>
          simp [φ4]
        | succ n' =>
          rw [Finset.sum_eq_single 1]
          · simp [φ4, mul_comm]
          · intro b _ hb1
            rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hb1), mul_zero]
          · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
      | succ k'' =>
        rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
          mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
          if_neg (by omega), mul_zero, mul_zero]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
        split_ifs with hbk
        · subst hbk
          simp only [φ4, map_mul, map_pow, map_ofNat]
          have h2pow : (2 : ZMod 4) ^ (k'' + 2) = 0 := by
            rw [pow_add]; have : (2 : ZMod 4) ^ 2 = 0 := by decide
            rw [this, mul_zero]
          rw [h2pow, mul_zero, zero_mul]
        · rw [mul_zero]
  have hP2 : ∀ n : ℕ,
      Φ4 (∑ k ∈ Finset.range (n + 1),
        PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * 3 ^ k) * PowerSeries.X ^ k) =
      Φ4 (∑ k ∈ Finset.range (n + 1),
        PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * (-1 : ℤ) ^ k) * PowerSeries.X ^ k) := by
    intro n
    simp only [Φ4, map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, φ4]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h3 : (3 : ZMod 4) = (-1 : ZMod 4) := by decide
    simp [h3]
  change φ4 (a246423 m) = φ4 (PowerSeries.coeff m S1_ser) + 2 * φ4 (PowerSeries.coeff m S2_ser)
  simp only [a246423, S1_ser, S2_ser, PowerSeries.coeff_mk, map_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map]
  have h2C : (2 : ZMod 4) * PowerSeries.coeff m (Φ4 (termS2 n)) =
      PowerSeries.coeff m (PowerSeries.C (2 : ZMod 4) * Φ4 (termS2 n)) := by
    rw [PowerSeries.coeff_C_mul]
  rw [h2C, ← map_add]
  congr 1
  simp only [termA246423, termS1, termS2]
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
    map_pow, map_pow, map_pow, map_pow, map_pow, map_pow,
    PowerSeries.map_X, PowerSeries.map_C, hinv, hP1 n, hP2 n]
  have hCn : PowerSeries.C (φ4 (n : ℤ)) ^ 2 = PowerSeries.C ((n : ZMod 4) ^ 2) := by
    rw [← map_pow PowerSeries.C]; simp [φ4]
  rw [hCn, pow_succ]
  dsimp only [Φ4]
  ring

private lemma two_mul_S2_mod4 (m : ℕ) :
    (2 : ZMod 4) * ((PowerSeries.coeff m S2_ser : ℤ) : ZMod 4) = if m = 2 then 2 else 0 := by
  have hmod2 := congr_arg (PowerSeries.coeff m) S2_mod2_eq
  rw [PowerSeries.coeff_map, PowerSeries.coeff_X_pow] at hmod2
  have hpar : (PowerSeries.coeff m S2_ser) % 2 = if m = 2 then 1 else 0 := by
    have hcast : ((PowerSeries.coeff m S2_ser : ℤ) : ZMod 2) = if m = 2 then 1 else 0 := hmod2
    split_ifs at hcast ⊢ with hm
    · have h1 := (ZMod.intCast_eq_intCast_iff (PowerSeries.coeff m S2_ser) 1 2).mp (by simpa using hcast)
      rw [Int.ModEq] at h1; norm_num at h1; omega
    · have h0 := (ZMod.intCast_eq_intCast_iff (PowerSeries.coeff m S2_ser) 0 2).mp (by simpa using hcast)
      rw [Int.ModEq] at h0; norm_num at h0; omega
  have hdiv := Int.emod_add_mul_ediv (PowerSeries.coeff m S2_ser) 2
  set q := PowerSeries.coeff m S2_ser / 2
  have hcast4 : ((PowerSeries.coeff m S2_ser : ℤ) : ZMod 4) =
      ((if m = 2 then (1 : ℤ) else 0) : ZMod 4) + 2 * (q : ZMod 4) := by
    have : PowerSeries.coeff m S2_ser = (if m = 2 then 1 else 0) + 2 * q := by
      rw [← hpar]; exact hdiv.symm
    rw [this]; push_cast; ring
  rw [hcast4, mul_add]
  have h4 : (2 : ZMod 4) * (2 * (q : ZMod 4)) = 0 := by
    have : (4 : ZMod 4) = 0 := by decide
    calc (2 : ZMod 4) * (2 * (q : ZMod 4)) = 4 * (q : ZMod 4) := by ring
      _ = 0 := by rw [this, zero_mul]
  rw [h4, add_zero]
  split_ifs <;> simp

private lemma int_emod_four_eq_of_zmod4 {x : ℤ} {r : ℤ} (hr : 0 ≤ r ∧ r < 4)
    (h : (x : ZMod 4) = (r : ZMod 4)) : x % 4 = r := by
  have hmod := (ZMod.intCast_eq_intCast_iff x r 4).mp h
  rw [Int.ModEq] at hmod
  norm_num at hmod
  rw [hmod, Int.emod_eq_of_lt hr.1 hr.2]

open Classical in
private theorem main_proved :
    a246423 0 = 1 ∧
    ∀ n : ℕ, 0 < n →
      ((∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k) → a246423 n % 4 = 2) ∧
      ((¬ ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k) → a246423 n % 4 = 0) := by
  refine ⟨?_, ?_⟩
  · simp [a246423, termA246423, inv1m3X]
  · intro n hn
    have hdecomp := a246423_mod4_decomp n
    rw [S1_eq_F, two_mul_S2_mod4] at hdecomp
    have hF : ((PowerSeries.coeff n F_ser : ℤ) : ZMod 4) =
        if Even n then
          ((-1 : ZMod 4) ^ (n / 2)) * (if ∃ j : ℕ, n / 2 = 2 ^ j then 2 else 0)
        else 0 := by
      simp only [F_ser, PowerSeries.coeff_mk]
      by_cases hev : Even n
      · rw [if_pos hev, if_pos hev]
        have hq1 : 1 ≤ n / 2 := by
          rcases hev with ⟨q, rfl⟩; omega
        have hn2 : n = 2 * (n / 2) := by
          rcases hev with ⟨q, rfl⟩; omega
        rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
        congr 1
        conv_lhs => rw [hn2]
        rw [show 2 * (n / 2) / 2 = n / 2 by omega]
        exact choose_two_mul_mod4 (n / 2) hq1
      · rw [if_neg hev, if_neg hev, Int.cast_zero]
    rw [hF] at hdecomp
    have hneg2 : ∀ k : ℕ, ((-1 : ZMod 4) ^ k) * 2 = 2 := by
      intro k
      induction k with
      | zero => simp
      | succ k' ih =>
        rw [pow_succ, mul_assoc, show (-1 : ZMod 4) * 2 = 2 by decide]
        exact ih
    constructor
    · rintro ⟨k, hk2, rfl⟩
      have hev : Even (2 ^ k) := ⟨2 ^ (k - 1), by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
        ring⟩
      have hne2 : 2 ^ k ≠ 2 := by
        have : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk2
        omega
      have hpow : ∃ j : ℕ, 2 ^ k / 2 = 2 ^ j := ⟨k - 1, by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
        omega⟩
      rw [if_pos hev, if_pos hpow, if_neg hne2, add_zero, hneg2] at hdecomp
      exact int_emod_four_eq_of_zmod4 ⟨by omega, by omega⟩ (by simpa using hdecomp)
    · intro hnot
      have hzero : (a246423 n : ZMod 4) = 0 := by
        by_cases hn2 : n = 2
        · subst hn2
          have hev : Even 2 := ⟨1, rfl⟩
          have hpow : ∃ j : ℕ, 2 / 2 = 2 ^ j := ⟨0, rfl⟩
          rw [if_pos hev, if_pos hpow, if_pos rfl, hneg2] at hdecomp
          rw [hdecomp]; decide
        · rw [if_neg hn2, add_zero] at hdecomp
          by_cases hev : Even n
          · rw [if_pos hev] at hdecomp
            have hnotj : ¬ ∃ j : ℕ, n / 2 = 2 ^ j := by
              rintro ⟨j, hj⟩
              cases j with
              | zero =>
                rcases hev with ⟨q, rfl⟩; omega
              | succ j' =>
                refine hnot ⟨j' + 2, by omega, ?_⟩
                rcases hev with ⟨q, rfl⟩
                rw [pow_succ] at hj ⊢
                omega
            rw [if_neg hnotj, mul_zero] at hdecomp
            exact hdecomp
          · rw [if_neg hev] at hdecomp
            exact hdecomp
      exact int_emod_four_eq_of_zmod4 ⟨by omega, by omega⟩ (by simpa using hzero)

end OMA.S_oeis_a246423

theorem OMA.solution : type_of% @OMA.S_oeis_a246423.main :=
  OMA.S_oeis_a246423.main_proved
