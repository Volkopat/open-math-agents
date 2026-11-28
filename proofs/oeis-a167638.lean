import OMAStatements.S_oeis_a167638
import Mathlib

namespace OMA.S_oeis_a167638

open PowerSeries BigOperators

/-! ### Part 1: Legendre-Delannoy Polynomials and 3-Term Recurrence in `ℚ[T]` -/

private noncomputable def legPoly (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C ((Nat.choose n k : ℚ) ^ 2) * Polynomial.X ^ k

private lemma coeff_legPoly (n k : ℕ) :
    (legPoly n).coeff k = (Nat.choose n k : ℚ) ^ 2 := by
  simp only [legPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hkn : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_pow (by norm_num)]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbn : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    simp [show k ≠ b by omega]

private lemma legPoly_recurrence (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.C ((n + 1 : ℕ) : ℚ) * legPoly (n + 1) =
      Polynomial.C ((2 * n + 1 : ℕ) : ℚ) * (1 + Polynomial.X) * legPoly n -
      Polynomial.C (n : ℚ) * (1 - Polynomial.X) ^ 2 * legPoly (n - 1) := by
  ext k
  have h1X : (1 + Polynomial.X : Polynomial ℚ) * legPoly n =
      legPoly n + Polynomial.X * legPoly n := by ring
  have hsq : (1 - Polynomial.X : Polynomial ℚ) ^ 2 * legPoly (n - 1) =
      legPoly (n - 1) - Polynomial.C 2 * (Polynomial.X * legPoly (n - 1)) +
        Polynomial.X ^ 2 * legPoly (n - 1) := by
    simp only [map_ofNat]; ring
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul,
      mul_assoc, Polynomial.coeff_C_mul, h1X, hsq,
      Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  cases k with
  | zero =>
      simp only [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_pow_mul', show ¬ 2 ≤ 0 by omega,
        ↓reduceIte, coeff_legPoly, Nat.choose_zero_right, Nat.cast_one, one_pow]
      push_cast; ring
  | succ k =>
      cases k with
      | zero =>
          simp only [Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul', show ¬ 2 ≤ 1 by omega,
            ↓reduceIte, coeff_legPoly, zero_add, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one, one_pow]
          have hnm : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
            rw [Nat.cast_sub hn, Nat.cast_one]
          rw [hnm]; push_cast; ring
      | succ j =>
          simp only [Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul', show 2 ≤ j + 2 by omega,
            ↓reduceIte, show j + 2 - 2 = j by omega, coeff_legPoly]
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
          by_cases hgt : m + 2 < j + 2
          · rw [Nat.choose_eq_zero_of_lt (by omega : m + 2 < j + 2),
                Nat.choose_eq_zero_of_lt (by omega : m + 1 < j + 2),
                Nat.choose_eq_zero_of_lt (by omega : m + 1 < j + 1),
                Nat.choose_eq_zero_of_lt (by omega : m < j + 2),
                Nat.choose_eq_zero_of_lt (by omega : m < j + 1),
                Nat.choose_eq_zero_of_lt (by omega : m < j)]
            push_cast; ring
          · by_cases heq1 : j + 2 = m + 2
            · have hjm : m = j := by omega
              rw [hjm]
              rw [Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega : j + 1 < j + 2),
                  Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega : j < j + 2),
                  Nat.choose_eq_zero_of_lt (by omega : j < j + 1), Nat.choose_self]
              push_cast; ring
            · by_cases heq2 : j + 2 = m + 1
              · have hjm : m = j + 1 := by omega
                subst hjm
                have h1 : Nat.choose (j + 3) (j + 2) = j + 3 := Nat.choose_succ_self_right (j + 2)
                have h2 : Nat.choose (j + 2) (j + 1) = j + 2 := Nat.choose_succ_self_right (j + 1)
                have h3 : Nat.choose (j + 1) j = j + 1 := Nat.choose_succ_self_right j
                rw [show j + 1 + 1 + 1 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega,
                    h1, Nat.choose_self, h2, Nat.choose_eq_zero_of_lt (by omega : j + 1 < j + 2),
                    Nat.choose_self, h3]
                push_cast; ring
              · -- General case: `j + 2 ≤ m`!
                have hjm : j + 2 ≤ m := by omega
                set D : ℚ := ((Nat.factorial (j + 2) : ℕ) : ℚ) * ((Nat.factorial (m - j) : ℕ) : ℚ)
                have hD0 : D ≠ 0 := mul_ne_zero
                  (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
                  (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
                have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD0
                apply mul_left_cancel₀ hD2
                -- Express `D * C(...)` in terms of `m!` for all 6 binomial coefficients!
                have hc1 : D * (Nat.choose (m + 2) (j + 2) : ℚ) =
                    ((m + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                  have h := Nat.choose_mul_factorial_mul_factorial (show j + 2 ≤ m + 2 by omega)
                  have hsub : m + 2 - (j + 2) = m - j := by omega
                  rw [hsub] at h
                  have hq : (Nat.choose (m + 2) (j + 2) : ℚ) * D = ((Nat.factorial (m + 2) : ℕ) : ℚ) := by
                    simpa [D, mul_assoc] using (show ((Nat.choose (m + 2) (j + 2) * Nat.factorial (j + 2) * Nat.factorial (m - j) : ℕ) : ℚ) =
                      ((Nat.factorial (m + 2) : ℕ) : ℚ) by exact_mod_cast h)
                  rw [mul_comm, hq, Nat.factorial_succ, Nat.factorial_succ]
                  push_cast; ring
                have hc2 : D * (Nat.choose (m + 1) (j + 2) : ℚ) =
                    ((m + 1 : ℕ) : ℚ) * ((m - j : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                  have h := Nat.choose_mul_factorial_mul_factorial (show j + 2 ≤ m + 1 by omega)
                  have hsub : m + 1 - (j + 2) = m - j - 1 := by omega
                  have hf : Nat.factorial (m - j) = (m - j) * Nat.factorial (m - j - 1) := by
                    rw [show m - j = (m - j - 1) + 1 by omega, Nat.factorial_succ, show m - j - 1 + 1 = m - j by omega]
                  rw [hsub] at h
                  have hq : (Nat.choose (m + 1) (j + 2) : ℚ) * ((Nat.factorial (j + 2) : ℕ) : ℚ) *
                      ((Nat.factorial (m - j - 1) : ℕ) : ℚ) = ((Nat.factorial (m + 1) : ℕ) : ℚ) := by
                    exact_mod_cast h
                  calc D * (Nat.choose (m + 1) (j + 2) : ℚ)
                    _ = ((m - j : ℕ) : ℚ) * ((Nat.choose (m + 1) (j + 2) : ℚ) *
                          ((Nat.factorial (j + 2) : ℕ) : ℚ) * ((Nat.factorial (m - j - 1) : ℕ) : ℚ)) := by
                          simp only [D, hf, Nat.cast_mul]; ring
                    _ = ((m - j : ℕ) : ℚ) * ((Nat.factorial (m + 1) : ℕ) : ℚ) := by rw [hq]
                    _ = ((m + 1 : ℕ) : ℚ) * ((m - j : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                          rw [Nat.factorial_succ]; push_cast; ring
                have hc3 : D * (Nat.choose (m + 1) (j + 1) : ℚ) =
                    ((j + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                  have h := Nat.choose_mul_factorial_mul_factorial (show j + 1 ≤ m + 1 by omega)
                  have hsub : m + 1 - (j + 1) = m - j := by omega
                  rw [hsub] at h
                  have hq : (Nat.choose (m + 1) (j + 1) : ℚ) * ((Nat.factorial (j + 1) : ℕ) : ℚ) *
                      ((Nat.factorial (m - j) : ℕ) : ℚ) = ((Nat.factorial (m + 1) : ℕ) : ℚ) := by
                    exact_mod_cast h
                  calc D * (Nat.choose (m + 1) (j + 1) : ℚ)
                    _ = ((j + 2 : ℕ) : ℚ) * ((Nat.choose (m + 1) (j + 1) : ℚ) *
                          ((Nat.factorial (j + 1) : ℕ) : ℚ) * ((Nat.factorial (m - j) : ℕ) : ℚ)) := by
                          simp only [D, Nat.factorial_succ (j + 1), Nat.cast_mul]; ring
                    _ = ((j + 2 : ℕ) : ℚ) * ((Nat.factorial (m + 1) : ℕ) : ℚ) := by rw [hq]
                    _ = ((j + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                          rw [Nat.factorial_succ]; push_cast; ring
                have hc4 : D * (Nat.choose m (j + 2) : ℚ) =
                    ((m - j : ℕ) : ℚ) * ((m - j - 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                  have h := Nat.choose_mul_factorial_mul_factorial hjm
                  have hsub : m - (j + 2) = m - j - 2 := by omega
                  have hf : Nat.factorial (m - j) = (m - j) * ((m - j - 1) * Nat.factorial (m - j - 2)) := by
                    have h1 : m - j = (m - j - 1) + 1 := by omega
                    have h2 : m - j - 1 = (m - j - 2) + 1 := by omega
                    conv_lhs => rw [h1, Nat.factorial_succ, ← h1]
                    conv_lhs => rw [h2, Nat.factorial_succ, ← h2]
                  rw [hsub] at h
                  have hq : (Nat.choose m (j + 2) : ℚ) * ((Nat.factorial (j + 2) : ℕ) : ℚ) *
                      ((Nat.factorial (m - j - 2) : ℕ) : ℚ) = ((Nat.factorial m : ℕ) : ℚ) := by
                    exact_mod_cast h
                  calc D * (Nat.choose m (j + 2) : ℚ)
                    _ = ((m - j : ℕ) : ℚ) * ((m - j - 1 : ℕ) : ℚ) * ((Nat.choose m (j + 2) : ℚ) *
                          ((Nat.factorial (j + 2) : ℕ) : ℚ) * ((Nat.factorial (m - j - 2) : ℕ) : ℚ)) := by
                          simp only [D, hf, Nat.cast_mul]; ring
                    _ = ((m - j : ℕ) : ℚ) * ((m - j - 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by rw [hq]
                have hc5 : D * (Nat.choose m (j + 1) : ℚ) =
                    ((j + 2 : ℕ) : ℚ) * ((m - j : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                  have h := Nat.choose_mul_factorial_mul_factorial (show j + 1 ≤ m by omega)
                  have hsub : m - (j + 1) = m - j - 1 := by omega
                  have hf : Nat.factorial (m - j) = (m - j) * Nat.factorial (m - j - 1) := by
                    rw [show m - j = (m - j - 1) + 1 by omega, Nat.factorial_succ, show m - j - 1 + 1 = m - j by omega]
                  rw [hsub] at h
                  have hq : (Nat.choose m (j + 1) : ℚ) * ((Nat.factorial (j + 1) : ℕ) : ℚ) *
                      ((Nat.factorial (m - j - 1) : ℕ) : ℚ) = ((Nat.factorial m : ℕ) : ℚ) := by
                    exact_mod_cast h
                  calc D * (Nat.choose m (j + 1) : ℚ)
                    _ = ((j + 2 : ℕ) : ℚ) * ((m - j : ℕ) : ℚ) * ((Nat.choose m (j + 1) : ℚ) *
                          ((Nat.factorial (j + 1) : ℕ) : ℚ) * ((Nat.factorial (m - j - 1) : ℕ) : ℚ)) := by
                          simp only [D, Nat.factorial_succ (j + 1), hf, Nat.cast_mul]; ring
                    _ = ((j + 2 : ℕ) : ℚ) * ((m - j : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by rw [hq]
                have hc6 : D * (Nat.choose m j : ℚ) =
                    ((j + 2 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
                  have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ m by omega)
                  have hq : (Nat.choose m j : ℚ) * ((Nat.factorial j : ℕ) : ℚ) *
                      ((Nat.factorial (m - j) : ℕ) : ℚ) = ((Nat.factorial m : ℕ) : ℚ) := by
                    exact_mod_cast h
                  calc D * (Nat.choose m j : ℚ)
                    _ = ((j + 2 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ) * ((Nat.choose m j : ℚ) *
                          ((Nat.factorial j : ℕ) : ℚ) * ((Nat.factorial (m - j) : ℕ) : ℚ)) := by
                          simp only [D, Nat.factorial_succ (j + 1), Nat.factorial_succ j, Nat.cast_mul]; ring
                    _ = ((j + 2 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by rw [hq]
                have hmj : ((m - j : ℕ) : ℚ) = (m : ℚ) - (j : ℚ) := by rw [Nat.cast_sub (by omega)]
                have hmj1 : ((m - j - 1 : ℕ) : ℚ) = (m : ℚ) - (j : ℚ) - 1 := by
                  rw [Nat.cast_sub (by omega), hmj, Nat.cast_one]
                rw [show m + 1 + 1 = m + 2 by omega]
                have hL : D ^ 2 * (((m + 2 : ℕ) : ℚ) * (Nat.choose (m + 2) (j + 2) : ℚ) ^ 2) =
                    ((m + 2 : ℕ) : ℚ) * (D * (Nat.choose (m + 2) (j + 2) : ℚ)) ^ 2 := by ring
                have hR : D ^ 2 * (((2 * (m + 1) + 1 : ℕ) : ℚ) *
                      ((Nat.choose (m + 1) (j + 2) : ℚ) ^ 2 + (Nat.choose (m + 1) (j + 1) : ℚ) ^ 2) -
                      ((m + 1 : ℕ) : ℚ) * ((Nat.choose m (j + 2) : ℚ) ^ 2 -
                        2 * (Nat.choose m (j + 1) : ℚ) ^ 2 + (Nat.choose m j : ℚ) ^ 2)) =
                    ((2 * (m + 1) + 1 : ℕ) : ℚ) *
                      ((D * (Nat.choose (m + 1) (j + 2) : ℚ)) ^ 2 + (D * (Nat.choose (m + 1) (j + 1) : ℚ)) ^ 2) -
                    ((m + 1 : ℕ) : ℚ) * ((D * (Nat.choose m (j + 2) : ℚ)) ^ 2 -
                      2 * (D * (Nat.choose m (j + 1) : ℚ)) ^ 2 + (D * (Nat.choose m j : ℚ)) ^ 2) := by ring
                rw [hL, hR, hc1, hc2, hc3, hc4, hc5, hc6, hmj1, hmj]
                push_cast; ring

/-! ### Part 2: Algebraic Identity in `PowerSeries (Polynomial ℚ)` -/

private lemma eq_of_derivative_eq_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (f : PowerSeries R) (hf0 : PowerSeries.coeff 0 f = 0) (hd : PowerSeries.derivative R f = 0) :
    f = 0 := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero => simpa using hf0
  | succ n =>
      have h := congrArg (PowerSeries.coeff n) hd
      rw [PowerSeries.coeff_derivative, map_zero] at h
      have hne : ((n : R) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact (mul_eq_zero.mp h).resolve_right hne

private noncomputable def Pseries : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk legPoly

private noncomputable def Dpoly : PowerSeries (Polynomial ℚ) :=
  1 - PowerSeries.C (Polynomial.C 2 * (1 + Polynomial.X)) * PowerSeries.X +
    PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X ^ 2

private lemma ps_deriv_mul (f g : PowerSeries (Polynomial ℚ)) :
    PowerSeries.derivative (Polynomial ℚ) (f * g) =
      f * PowerSeries.derivative (Polynomial ℚ) g + g * PowerSeries.derivative (Polynomial ℚ) f := by
  simp [Derivation.leibniz]

private lemma ps_deriv_pow (f : PowerSeries (Polynomial ℚ)) (k : ℕ) :
    PowerSeries.derivative (Polynomial ℚ) (f ^ k) =
      (k : PowerSeries (Polynomial ℚ)) * f ^ (k - 1) * PowerSeries.derivative (Polynomial ℚ) f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ps_deriv_mul, ih]
      cases k with
      | zero => simp
      | succ k =>
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
          ring

private lemma Dpoly_mul_Pseries_sq : Dpoly * Pseries ^ 2 = 1 := by
  -- First prove `Dpoly * Pseries' = (C (1 + T) - C ((1 - T)^2) * Y) * Pseries`!
  have hode : Dpoly * PowerSeries.derivative (Polynomial ℚ) Pseries =
      (PowerSeries.C (1 + Polynomial.X) - PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X) * Pseries := by
    apply PowerSeries.ext; intro n
    rw [Dpoly, add_mul, sub_mul, one_mul, mul_assoc, mul_assoc, sub_mul, mul_assoc,
        map_add, map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative]
    cases n with
    | zero =>
        rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_X_pow_mul']
        simp only [show ¬ 2 ≤ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero,
          Pseries, PowerSeries.coeff_mk, legPoly, Finset.sum_range_succ, Finset.range_zero,
          Finset.sum_empty, zero_add, Nat.choose_self, Nat.choose_zero_right,
          Nat.cast_one, one_pow, pow_zero, pow_one, mul_one, map_one]
        ring
    | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul']
        cases n with
        | zero =>
            simp only [show ¬ 2 ≤ 1 by omega, ↓reduceIte, mul_zero, add_zero,
              PowerSeries.coeff_derivative, Pseries, PowerSeries.coeff_mk]
            have hrec := legPoly_recurrence 1 (by omega)
            simp only [Nat.sub_self] at hrec
            have hleg0 : legPoly 0 = 1 := by simp [legPoly]
            have hleg1 : legPoly 1 = 1 + Polynomial.X := by
              simp [legPoly, Finset.sum_range_succ]
            rw [hleg1, hleg0] at hrec
            have h2 : Polynomial.C ((1 + 1 : ℕ) : ℚ) = 2 := by rw [map_natCast]; norm_num
            have h3 : Polynomial.C ((2 * 1 + 1 : ℕ) : ℚ) = 3 := by rw [map_natCast]; norm_num
            have h1 : Polynomial.C ((1 : ℕ) : ℚ) = 1 := by simp
            have hc2 : Polynomial.C (2 : ℚ) = 2 := by rw [map_ofNat]
            rw [h2, h3, h1] at hrec
            rw [hleg1, hleg0, hc2]
            push_cast
            linear_combination hrec
        | succ m =>
            simp only [show 2 ≤ m + 2 by omega, ↓reduceIte, show m + 2 - 2 = m by omega,
              PowerSeries.coeff_derivative, Pseries, PowerSeries.coeff_mk]
            have hrec := legPoly_recurrence (m + 2) (by omega)
            simp only [show m + 2 - 1 = m + 1 by omega] at hrec
            have hc1 : Polynomial.C (((m + 2) + 1 : ℕ) : ℚ) = ((m + 3 : ℕ) : Polynomial ℚ) := by
              rw [map_natCast]
            have hc2 : Polynomial.C ((2 * (m + 2) + 1 : ℕ) : ℚ) = ((2 * m + 5 : ℕ) : Polynomial ℚ) := by
              rw [map_natCast]; congr 1
            have hc3 : Polynomial.C ((m + 2 : ℕ) : ℚ) = ((m + 2 : ℕ) : Polynomial ℚ) := by
              rw [map_natCast]
            rw [hc1, hc2, hc3] at hrec
            have hc2' : Polynomial.C (2 : ℚ) = 2 := by rw [map_ofNat]
            rw [hc2']
            push_cast at hrec ⊢
            linear_combination hrec
  have hd1 : PowerSeries.derivative (Polynomial ℚ) (1 : PowerSeries (Polynomial ℚ)) = 0 := by
    simp
  have hdD : PowerSeries.derivative (Polynomial ℚ) Dpoly =
      -PowerSeries.C (Polynomial.C 2) *
        (PowerSeries.C (1 + Polynomial.X) - PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X) := by
    simp only [Dpoly, map_add, map_sub, hd1, ps_deriv_mul,
      PowerSeries.derivative_C, PowerSeries.derivative_X, ps_deriv_pow,
      mul_one, mul_zero, add_zero, zero_sub, Nat.reduceSub, pow_one]
    have h2 : ((2 : ℕ) : PowerSeries (Polynomial ℚ)) = PowerSeries.C (Polynomial.C 2) := by
      rw [← map_natCast PowerSeries.C, ← map_natCast Polynomial.C]
      norm_num
    rw [h2, map_mul PowerSeries.C, map_add PowerSeries.C, map_one]
    ring
  have hd0 : PowerSeries.derivative (Polynomial ℚ) (Dpoly * Pseries ^ 2 - 1) = 0 := by
    have hdp : PowerSeries.derivative (Polynomial ℚ) (Pseries ^ 2) =
        PowerSeries.C (Polynomial.C 2) * Pseries * PowerSeries.derivative (Polynomial ℚ) Pseries := by
      rw [sq, ps_deriv_mul]
      have h2 : (2 : PowerSeries (Polynomial ℚ)) = PowerSeries.C (Polynomial.C 2) := by
        rw [show (2 : PowerSeries (Polynomial ℚ)) = ((2 : ℕ) : PowerSeries (Polynomial ℚ)) by norm_num,
            ← map_natCast PowerSeries.C, ← map_natCast Polynomial.C]; norm_num
      rw [← h2]; ring
    rw [map_sub, hd1, sub_zero, ps_deriv_mul, hdp, hdD]
    linear_combination PowerSeries.C (Polynomial.C 2) * Pseries * hode
  have h0 : PowerSeries.coeff 0 (Dpoly * Pseries ^ 2 - 1) = 0 := by
    rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow, map_one]
    have hD0 : PowerSeries.constantCoeff Dpoly = 1 := by
      simp [Dpoly, map_add, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X]
    have hP0 : PowerSeries.constantCoeff Pseries = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      simp [Pseries, legPoly]
    rw [hD0, hP0]; ring
  exact sub_eq_zero.mp (eq_of_derivative_eq_zero _ h0 hd0)

/-! ### Part 3: Substitution Homomorphism `T ↦ 1 + X`, `Y ↦ X^2` and Exponential Matching -/

private noncomputable abbrev evalPoly (p : Polynomial ℚ) : PowerSeries ℚ :=
  Polynomial.aeval (1 + PowerSeries.X) p

private noncomputable def evalSub (F : PowerSeries (Polynomial ℚ)) : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m / 2 + 1), PowerSeries.coeff (m - 2 * n) (evalPoly (PowerSeries.coeff n F))

private lemma coeff_evalSub (F : PowerSeries (Polynomial ℚ)) (m : ℕ) :
    PowerSeries.coeff m (evalSub F) =
      ∑ n ∈ Finset.range (m / 2 + 1), PowerSeries.coeff (m - 2 * n) (evalPoly (PowerSeries.coeff n F)) := by
  simp [evalSub]

private lemma evalSub_add (F G : PowerSeries (Polynomial ℚ)) :
    evalSub (F + G) = evalSub F + evalSub G := by
  apply PowerSeries.ext; intro m
  simp only [map_add, coeff_evalSub, evalPoly, Finset.sum_add_distrib]

private lemma evalSub_sub (F G : PowerSeries (Polynomial ℚ)) :
    evalSub (F - G) = evalSub F - evalSub G := by
  apply PowerSeries.ext; intro m
  simp only [map_sub, coeff_evalSub, evalPoly, Finset.sum_sub_distrib]

private lemma evalSub_one : evalSub 1 = 1 := by
  apply PowerSeries.ext; intro m
  rw [coeff_evalSub, PowerSeries.coeff_one, Finset.sum_range_succ']
  have hrest : ∑ n ∈ Finset.range (m / 2),
      PowerSeries.coeff (m - 2 * (n + 1)) (evalPoly (PowerSeries.coeff (n + 1) 1)) = 0 := by
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [PowerSeries.coeff_one, if_neg (by omega)]; simp [evalPoly]
  rw [hrest, zero_add, PowerSeries.coeff_one, if_pos rfl, mul_zero, Nat.sub_zero]
  simp [evalPoly, PowerSeries.coeff_one]

private lemma evalSub_C (p : Polynomial ℚ) : evalSub (PowerSeries.C p) = evalPoly p := by
  apply PowerSeries.ext; intro m
  rw [coeff_evalSub, Finset.sum_range_succ']
  have hrest : ∑ n ∈ Finset.range (m / 2),
      PowerSeries.coeff (m - 2 * (n + 1)) (evalPoly (PowerSeries.coeff (n + 1) (PowerSeries.C p))) = 0 := by
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [PowerSeries.coeff_C, if_neg (by omega)]; simp [evalPoly]
  rw [hrest, zero_add, PowerSeries.coeff_zero_C, mul_zero, Nat.sub_zero]

private lemma evalSub_X : evalSub PowerSeries.X = PowerSeries.X ^ 2 := by
  apply PowerSeries.ext; intro m
  rw [coeff_evalSub, PowerSeries.coeff_X_pow]
  by_cases hm : 2 ≤ m
  · rw [Finset.sum_eq_single 1]
    · simp only [PowerSeries.coeff_one_X, evalPoly, map_one, mul_one, PowerSeries.coeff_one]
      by_cases hm2 : m = 2
      · subst hm2; simp
      · rw [if_neg (by omega), if_neg (by omega)]
    · intro n _ hne
      rw [PowerSeries.coeff_X, if_neg hne]; simp [evalPoly]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn0 : n = 0 := by have := Finset.mem_range.mp hn; omega
    subst hn0; simp [evalPoly]

private lemma evalSub_mul (F G : PowerSeries (Polynomial ℚ)) :
    evalSub (F * G) = evalSub F * evalSub G := by
  apply PowerSeries.ext; intro m
  rw [coeff_evalSub, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (evalSub F) * PowerSeries.coeff b (evalSub G))]
  -- Expand both sides as double sums over `(n1, n2)` and `(i, j)` with `2*(n1+n2) + i + j = m`!
  have hL : ∑ n ∈ Finset.range (m / 2 + 1),
      PowerSeries.coeff (m - 2 * n) (evalPoly (PowerSeries.coeff n (F * G))) =
      ∑ p ∈ (Finset.range (m / 2 + 1)).sigma (fun n => Finset.range (n + 1)),
        ∑ i ∈ Finset.range (m - 2 * p.1 + 1),
          PowerSeries.coeff i (evalPoly (PowerSeries.coeff p.2 F)) *
            PowerSeries.coeff (m - 2 * p.1 - i) (evalPoly (PowerSeries.coeff (p.1 - p.2) G)) := by
    rw [← Finset.sum_sigma' (Finset.range (m / 2 + 1)) (fun n => Finset.range (n + 1))
      (fun n n1 => ∑ i ∈ Finset.range (m - 2 * n + 1),
        PowerSeries.coeff i (evalPoly (PowerSeries.coeff n1 F)) *
          PowerSeries.coeff (m - 2 * n - i) (evalPoly (PowerSeries.coeff (n - n1) G)))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a F * PowerSeries.coeff b G)]
    dsimp only [evalPoly]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun n1 _ => ?_
    rw [map_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (evalPoly (PowerSeries.coeff n1 F)) *
            PowerSeries.coeff j (evalPoly (PowerSeries.coeff (n - n1) G)))]
  -- Flatten LHS to a triple sum over `n1, n2, i` with `2*n1 + 2*n2 + i ≤ m`:
  let S : Finset (ℕ × ℕ × ℕ) :=
    ((Finset.range (m / 2 + 1)) ×ˢ ((Finset.range (m / 2 + 1)) ×ˢ (Finset.range (m + 1)))).filter
      (fun t => 2 * t.1 + 2 * t.2.1 + t.2.2 ≤ m)
  let term (t : ℕ × ℕ × ℕ) : ℚ :=
    PowerSeries.coeff t.2.2 (evalPoly (PowerSeries.coeff t.1 F)) *
      PowerSeries.coeff (m - 2 * t.1 - 2 * t.2.1 - t.2.2) (evalPoly (PowerSeries.coeff t.2.1 G))
  have hLHS_eq : ∑ n ∈ Finset.range (m / 2 + 1),
      PowerSeries.coeff (m - 2 * n) (evalPoly (PowerSeries.coeff n (F * G))) = ∑ t ∈ S, term t := by
    have hL2 : ∑ p ∈ (Finset.range (m / 2 + 1)).sigma (fun n => Finset.range (n + 1)),
        ∑ i ∈ Finset.range (m - 2 * p.1 + 1),
          PowerSeries.coeff i (evalPoly (PowerSeries.coeff p.2 F)) *
            PowerSeries.coeff (m - 2 * p.1 - i) (evalPoly (PowerSeries.coeff (p.1 - p.2) G)) =
        ∑ x ∈ ((Finset.range (m / 2 + 1)).sigma (fun n => Finset.range (n + 1))).sigma
            (fun p => Finset.range (m - 2 * p.1 + 1)),
          PowerSeries.coeff x.2 (evalPoly (PowerSeries.coeff x.1.2 F)) *
            PowerSeries.coeff (m - 2 * x.1.1 - x.2) (evalPoly (PowerSeries.coeff (x.1.1 - x.1.2) G)) :=
      Finset.sum_sigma' _ _ _
    rw [hL, hL2]
    refine Finset.sum_nbij (fun x => (x.1.2, x.1.1 - x.1.2, x.2)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨by omega, by omega, by omega⟩, by omega⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hx hy
      have h1 : x.1.2 = y.1.2 := congrArg Prod.fst hxy
      have h2 : x.1.1 - x.1.2 = y.1.1 - y.1.2 := congrArg (fun p => p.2.1) hxy
      have h3 : x.2 = y.2 := congrArg (fun p => p.2.2) hxy
      have h11 : x.1.1 = y.1.1 := by omega
      exact Sigma.ext (Sigma.ext h11 (heq_of_eq h1)) (heq_of_eq h3)
    · intro t ht
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
      refine ⟨⟨⟨t.1 + t.2.1, t.1⟩, t.2.2⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · refine Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [term]
      congr 2; congr 1; omega
  have hRHS_eq : ∑ a ∈ Finset.range (m + 1),
      PowerSeries.coeff a (evalSub F) * PowerSeries.coeff (m - a) (evalSub G) = ∑ t ∈ S, term t := by
    have hR : ∑ a ∈ Finset.range (m + 1),
        PowerSeries.coeff a (evalSub F) * PowerSeries.coeff (m - a) (evalSub G) =
        ∑ x ∈ ((Finset.range (m + 1)).sigma (fun a => Finset.range (a / 2 + 1))).sigma
            (fun y => Finset.range ((m - y.1) / 2 + 1)),
          PowerSeries.coeff (x.1.1 - 2 * x.1.2) (evalPoly (PowerSeries.coeff x.1.2 F)) *
            PowerSeries.coeff (m - x.1.1 - 2 * x.2) (evalPoly (PowerSeries.coeff x.2 G)) := by
      have hR1 : ∑ a ∈ Finset.range (m + 1),
          PowerSeries.coeff a (evalSub F) * PowerSeries.coeff (m - a) (evalSub G) =
          ∑ a ∈ Finset.range (m + 1), ∑ n1 ∈ Finset.range (a / 2 + 1), ∑ n2 ∈ Finset.range ((m - a) / 2 + 1),
            PowerSeries.coeff (a - 2 * n1) (evalPoly (PowerSeries.coeff n1 F)) *
              PowerSeries.coeff (m - a - 2 * n2) (evalPoly (PowerSeries.coeff n2 G)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [coeff_evalSub, coeff_evalSub, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n1 _ => ?_
        rw [Finset.mul_sum]
      rw [hR1]
      rw [Finset.sum_sigma' (Finset.range (m + 1)) (fun a => Finset.range (a / 2 + 1))
        (fun a n1 => ∑ n2 ∈ Finset.range ((m - a) / 2 + 1),
          PowerSeries.coeff (a - 2 * n1) (evalPoly (PowerSeries.coeff n1 F)) *
            PowerSeries.coeff (m - a - 2 * n2) (evalPoly (PowerSeries.coeff n2 G)))]
      exact Finset.sum_sigma' _ _ _
    rw [hR]
    refine Finset.sum_nbij (fun x => (x.1.2, x.2, x.1.1 - 2 * x.1.2)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨by omega, by omega, by omega⟩, by omega⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hx hy
      have h1 : x.1.2 = y.1.2 := congrArg Prod.fst hxy
      have h2 : x.2 = y.2 := congrArg (fun p => p.2.1) hxy
      have h3 : x.1.1 - 2 * x.1.2 = y.1.1 - 2 * y.1.2 := congrArg (fun p => p.2.2) hxy
      have h11 : x.1.1 = y.1.1 := by omega
      exact Sigma.ext (Sigma.ext h11 (heq_of_eq h1)) (heq_of_eq h2)
    · intro t ht
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
      refine ⟨⟨⟨2 * t.1 + t.2.2, t.1⟩, t.2.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · refine Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [term]
      congr 2; congr 1; omega
  rw [hLHS_eq, hRHS_eq]

private lemma evalSub_pow (F : PowerSeries (Polynomial ℚ)) (k : ℕ) :
    evalSub (F ^ k) = (evalSub F) ^ k := by
  induction k with
  | zero => simp [evalSub_one]
  | succ k ih => rw [pow_succ, pow_succ, evalSub_mul, ih]

private lemma evalSub_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries (Polynomial ℚ)) :
    evalSub (∑ i ∈ s, f i) = ∑ i ∈ s, evalSub (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply PowerSeries.ext; intro m; simp [coeff_evalSub]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, evalSub_add, ih]

private lemma evalPoly_legPoly (n : ℕ) : evalPoly (legPoly n) = gPoly n := by
  simp only [evalPoly, legPoly, gPoly, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/-! ### Part 4: Constructing `E_poly = Q⁻¹ = exp(L_poly)` and Finishing A167638 -/

private noncomputable def Lpoly : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun n => if n = 0 then 0 else Polynomial.C ((1 : ℚ) / (n : ℚ)) * legPoly n

private lemma evalSub_Lpoly : evalSub Lpoly = balaLog := by
  apply PowerSeries.ext; intro m
  rw [coeff_evalSub, balaLog, PowerSeries.coeff_mk, balaLogTrunc, map_sum]
  -- Trim `Icc 1 m` to `Icc 1 (m / 2)` since for `n > m / 2`, `2 * n > m`!
  have htrim : ∑ n ∈ Finset.Icc 1 m,
      PowerSeries.coeff m (PowerSeries.C ((1 : ℚ) / (n : ℚ)) * (gPoly n * PowerSeries.X ^ (2 * n))) =
      ∑ n ∈ Finset.Icc 1 (m / 2),
        PowerSeries.coeff m (PowerSeries.C ((1 : ℚ) / (n : ℚ)) * (gPoly n * PowerSeries.X ^ (2 * n))) := by
    symm
    refine Finset.sum_subset (by intro n hn; simp only [Finset.mem_Icc] at hn ⊢; exact ⟨hn.1, by omega⟩) ?_
    intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    rw [PowerSeries.coeff_C_mul, mul_comm (gPoly n), PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
  rw [htrim, Finset.sum_range_succ']
  simp only [Lpoly, PowerSeries.coeff_mk, ↓reduceIte, map_zero, add_zero]
  refine Finset.sum_nbij (fun n => n + 1) ?_ ?_ ?_ ?_
  · intro n hn; simp only [Finset.mem_range, Finset.mem_Icc] at hn ⊢; omega
  · intro a _ b _ hab; dsimp only at hab; omega
  · intro n hn; simp only [Finset.mem_coe, Finset.mem_Icc] at hn
    exact ⟨n - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
  · intro n hn
    simp only [Finset.mem_range] at hn
    rw [if_neg (by omega), PowerSeries.coeff_C_mul, mul_comm (gPoly (n + 1)),
        PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
    simp only [evalPoly, map_mul, Polynomial.aeval_C]
    rw [show Polynomial.aeval (1 + PowerSeries.X) (legPoly (n + 1)) = gPoly (n + 1) from evalPoly_legPoly (n + 1)]
    change PowerSeries.coeff (m - 2 * (n + 1)) (PowerSeries.C ((1 : ℚ) / ((n + 1 : ℕ) : ℚ)) * gPoly (n + 1)) = _
    rw [PowerSeries.coeff_C_mul]

private noncomputable def Etrunc (N : ℕ) : PowerSeries (Polynomial ℚ) :=
  ∑ k ∈ Finset.range (N + 1),
    PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial k : ℚ))) * Lpoly ^ k

private lemma Lpoly_pow_lt (k n : ℕ) (h : n < k) : PowerSeries.coeff n (Lpoly ^ k) = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (Lpoly ^ k) * PowerSeries.coeff b Lpoly)]
      refine Finset.sum_eq_zero fun a ha => ?_
      have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases hlt : a < k
      · rw [ih a hlt, zero_mul]
      · rw [show n - a = 0 by omega]; simp [Lpoly]

private lemma Etrunc_agree (N₁ N₂ n : ℕ) (h1 : n ≤ N₁) (h2 : n ≤ N₂) :
    PowerSeries.coeff n (Etrunc N₁) = PowerSeries.coeff n (Etrunc N₂) := by
  have htrim : ∀ N, n ≤ N → PowerSeries.coeff n (Etrunc N) = PowerSeries.coeff n (Etrunc n) := by
    intro N hN
    simp only [Etrunc, map_sum, PowerSeries.coeff_C_mul]
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ N + 1)) ?_
    intro k hk hnot
    simp only [Finset.mem_range] at hk hnot
    rw [Lpoly_pow_lt k n (by omega), mul_zero]
  rw [htrim N₁ h1, htrim N₂ h2]

private noncomputable def Epoly : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun n => PowerSeries.coeff n (Etrunc n)

private lemma coeff_Epoly_eq_Etrunc (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n Epoly = PowerSeries.coeff n (Etrunc N) := by
  rw [Epoly, PowerSeries.coeff_mk]
  exact Etrunc_agree n N n (le_refl n) hn

private lemma Epoly_ode :
    PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Epoly = Epoly * (Pseries - 1) := by
  have hdL : PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Lpoly = Pseries - 1 := by
    apply PowerSeries.ext; intro n
    cases n with
    | zero =>
        rw [PowerSeries.coeff_zero_X_mul, map_sub, PowerSeries.coeff_one, if_pos rfl]
        simp [Pseries, legPoly]
    | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, map_sub,
            PowerSeries.coeff_one, if_neg (by omega), sub_zero]
        simp only [Lpoly, Pseries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
        have hpos : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [show ((n : Polynomial ℚ) + 1) = Polynomial.C ((n + 1 : ℕ) : ℚ) by rw [map_natCast]; push_cast; ring,
            mul_comm (Polynomial.C ((1 : ℚ) / ((n + 1 : ℕ) : ℚ)) * legPoly (n + 1)), ← mul_assoc,
            ← map_mul, mul_one_div_cancel hpos, map_one, one_mul]
  apply PowerSeries.ext; intro n
  -- Compare with `Etrunc n`!
  have hdE : PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) (Etrunc n) =
      (Etrunc n - PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial n : ℚ))) * Lpoly ^ n) * (Pseries - 1) := by
    have hderiv : PowerSeries.derivative (Polynomial ℚ) (Etrunc n) =
        (∑ k ∈ Finset.range n, PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial k : ℚ))) * Lpoly ^ k) *
          PowerSeries.derivative (Polynomial ℚ) Lpoly := by
      simp only [Etrunc, map_sum]
      rw [Finset.sum_range_succ']
      have hd1 : PowerSeries.derivative (Polynomial ℚ) (1 : PowerSeries (Polynomial ℚ)) = 0 := by
        simp
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul,
        hd1, add_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ps_deriv_mul, PowerSeries.derivative_C, mul_zero, add_zero,
          ps_deriv_pow, Nat.add_sub_cancel]
      have hc : PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial (k + 1) : ℚ))) *
          ((k + 1 : ℕ) : PowerSeries (Polynomial ℚ)) =
          PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial k : ℚ))) := by
        rw [show ((k + 1 : ℕ) : PowerSeries (Polynomial ℚ)) = PowerSeries.C (Polynomial.C ((k + 1 : ℕ) : ℚ)) by
          rw [map_natCast, map_natCast], ← map_mul, ← map_mul]
        congr 2
        rw [Nat.factorial_succ, Nat.cast_mul]
        have hpos : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp [hpos]
      calc PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial (k + 1) : ℚ))) *
            (((k + 1 : ℕ) : PowerSeries (Polynomial ℚ)) * Lpoly ^ k * PowerSeries.derivative (Polynomial ℚ) Lpoly)
        _ = (PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial (k + 1) : ℚ))) *
              ((k + 1 : ℕ) : PowerSeries (Polynomial ℚ))) * (Lpoly ^ k * PowerSeries.derivative (Polynomial ℚ) Lpoly) := by ring
        _ = PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial k : ℚ))) * Lpoly ^ k *
              PowerSeries.derivative (Polynomial ℚ) Lpoly := by rw [hc]; ring
    have hsplit : ∑ k ∈ Finset.range n, PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial k : ℚ))) * Lpoly ^ k =
        Etrunc n - PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial n : ℚ))) * Lpoly ^ n := by
      rw [Etrunc, Finset.sum_range_succ]; ring
    rw [hderiv, hsplit]
    calc PowerSeries.X * ((Etrunc n - PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial n : ℚ))) * Lpoly ^ n) *
            PowerSeries.derivative (Polynomial ℚ) Lpoly)
      _ = (Etrunc n - PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial n : ℚ))) * Lpoly ^ n) *
            (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Lpoly) := by ring
      _ = (Etrunc n - PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial n : ℚ))) * Lpoly ^ n) * (Pseries - 1) := by
            rw [hdL]
  have hLHS : PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Epoly) =
      PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) (Etrunc n)) := by
    cases n with
    | zero => simp [PowerSeries.coeff_zero_X_mul]
    | succ m =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
            coeff_Epoly_eq_Etrunc (m + 1) (m + 1) (le_refl _)]
  have hRHS : PowerSeries.coeff n (Epoly * (Pseries - 1)) =
      PowerSeries.coeff n (Etrunc n * (Pseries - 1)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a Epoly * PowerSeries.coeff b (Pseries - 1)),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (Etrunc n) * PowerSeries.coeff b (Pseries - 1))]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [coeff_Epoly_eq_Etrunc n a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))]
  have htail0 : PowerSeries.coeff n
      ((PowerSeries.C (Polynomial.C ((1 : ℚ) / (Nat.factorial n : ℚ))) * Lpoly ^ n) * (Pseries - 1)) = 0 := by
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (Lpoly ^ n) * PowerSeries.coeff b (Pseries - 1))]
    have hsum : ∑ a ∈ Finset.range (n + 1), PowerSeries.coeff a (Lpoly ^ n) * PowerSeries.coeff (n - a) (Pseries - 1) = 0 := by
      refine Finset.sum_eq_zero fun a ha => ?_
      have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases heq : a = n
      · subst heq; rw [Nat.sub_self, map_sub, PowerSeries.coeff_one, if_pos rfl]
        simp [Pseries, legPoly]
      · rw [Lpoly_pow_lt n a (by omega), zero_mul]
    rw [hsum, mul_zero]
  rw [hLHS, hdE, sub_mul, map_sub, htail0, sub_zero, hRHS]

private lemma Epoly_quad :
    PowerSeries.C Polynomial.X * PowerSeries.X ^ 2 * Epoly ^ 2 -
      (1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X) * Epoly + 1 = 0 := by
  set R : PowerSeries (Polynomial ℚ) := Dpoly * Pseries
  have hRP : R * Pseries = 1 := by
    calc R * Pseries = Dpoly * Pseries ^ 2 := by simp only [R]; ring
      _ = 1 := Dpoly_mul_Pseries_sq
  have hR2 : R ^ 2 = Dpoly := by
    calc R ^ 2 = Dpoly * (Dpoly * Pseries ^ 2) := by simp only [R]; ring
      _ = Dpoly := by rw [Dpoly_mul_Pseries_sq, mul_one]
  set Q : PowerSeries (Polynomial ℚ) :=
    PowerSeries.C (Polynomial.C (1 / 2 : ℚ)) * (1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X + R)
  have h2half : PowerSeries.C (Polynomial.C (2 : ℚ)) * PowerSeries.C (Polynomial.C (1 / 2 : ℚ)) = 1 := by
    rw [← map_mul, ← map_mul]; norm_num
  have h2Q : PowerSeries.C (Polynomial.C (2 : ℚ)) * Q =
      1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X + R := by
    simp only [Q, ← mul_assoc, h2half, one_mul]
  -- Prove `X * Q' = -Q * (Pseries - 1)` by multiplying by `2 * R` (whose inverse is `(1/2) * Pseries`)!
  have hd1 : PowerSeries.derivative (Polynomial ℚ) (1 : PowerSeries (Polynomial ℚ)) = 0 := by
    simp
  have hR_deriv : PowerSeries.C (Polynomial.C (2 : ℚ)) * (R * PowerSeries.derivative (Polynomial ℚ) R) =
      -PowerSeries.C (Polynomial.C (2 : ℚ)) *
        (PowerSeries.C (1 + Polynomial.X) - PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X) := by
    have hd := congrArg (PowerSeries.derivative (Polynomial ℚ)) hR2
    rw [ps_deriv_pow, show 2 - 1 = 1 by rfl, pow_one] at hd
    have h2 : ((2 : ℕ) : PowerSeries (Polynomial ℚ)) = PowerSeries.C (Polynomial.C 2) := by
      rw [← map_natCast PowerSeries.C, ← map_natCast Polynomial.C]; norm_num
    rw [h2] at hd
    have hRmul : PowerSeries.C (Polynomial.C 2) * (R * PowerSeries.derivative (Polynomial ℚ) R) =
        PowerSeries.C (Polynomial.C 2) * R * PowerSeries.derivative (Polynomial ℚ) R := by ring
    rw [hRmul, hd]
    simp only [Dpoly, map_add, map_sub, hd1, ps_deriv_mul,
      PowerSeries.derivative_C, PowerSeries.derivative_X, ps_deriv_pow,
      mul_one, mul_zero, add_zero, zero_sub, Nat.reduceSub, pow_one, h2,
      map_mul PowerSeries.C, map_add PowerSeries.C, map_one]
    ring
  have hRR' : R * PowerSeries.derivative (Polynomial ℚ) R =
      -(PowerSeries.C (1 + Polynomial.X) - PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X) := by
    have h := congrArg (fun z => PowerSeries.C (Polynomial.C (1 / 2 : ℚ)) * z) hR_deriv
    linear_combination h - (R * PowerSeries.derivative (Polynomial ℚ) R) * h2half -
      (PowerSeries.C (1 + Polynomial.X) - PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X) * h2half
  have h2Q' : PowerSeries.C (Polynomial.C (2 : ℚ)) * PowerSeries.derivative (Polynomial ℚ) Q =
      -PowerSeries.C (1 + Polynomial.X) + PowerSeries.derivative (Polynomial ℚ) R := by
    have h := congrArg (PowerSeries.derivative (Polynomial ℚ)) h2Q
    rw [ps_deriv_mul (PowerSeries.C (Polynomial.C (2 : ℚ))) Q, PowerSeries.derivative_C, mul_zero, add_zero,
        map_add, map_sub, hd1, zero_sub,
        ps_deriv_mul (PowerSeries.C (1 + Polynomial.X)) PowerSeries.X, PowerSeries.derivative_C,
        PowerSeries.derivative_X, mul_one, mul_zero, add_zero] at h
    exact h
  have hQ_ode_mul : PowerSeries.C (Polynomial.C (2 : ℚ)) * R * (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Q) =
      PowerSeries.C (Polynomial.C (2 : ℚ)) * R * (-Q * (Pseries - 1)) := by
    have hLHS : PowerSeries.C (Polynomial.C (2 : ℚ)) * R * (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Q) =
        PowerSeries.X * (R * (-PowerSeries.C (1 + Polynomial.X) + PowerSeries.derivative (Polynomial ℚ) R)) := by
      rw [← h2Q']; ring
    have hRHS : PowerSeries.C (Polynomial.C (2 : ℚ)) * R * (-Q * (Pseries - 1)) =
        -(1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X + R) * (1 - R) := by
      calc PowerSeries.C (Polynomial.C (2 : ℚ)) * R * (-Q * (Pseries - 1))
        _ = -(PowerSeries.C (Polynomial.C (2 : ℚ)) * Q) * (R * Pseries - R) := by ring
        _ = -(1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X + R) * (1 - R) := by rw [h2Q, hRP]
    rw [hLHS, hRHS, mul_add, hRR']
    have hD_exp : Dpoly = 1 - PowerSeries.C (Polynomial.C 2) * PowerSeries.C (1 + Polynomial.X) * PowerSeries.X +
        PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X ^ 2 := by
      simp only [Dpoly, map_mul]
    have h2eq : PowerSeries.C (Polynomial.C (2 : ℚ)) = 2 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, map_natCast, map_natCast]; norm_num
    rw [h2eq] at hD_exp
    have hR2' : R ^ 2 = 1 - 2 * PowerSeries.C (1 + Polynomial.X) * PowerSeries.X +
        PowerSeries.C ((1 - Polynomial.X) ^ 2) * PowerSeries.X ^ 2 := hR2.trans hD_exp
    linear_combination -hR2'
  have hQ_ode : PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Q = -Q * (Pseries - 1) := by
    have h := congrArg (fun z => PowerSeries.C (Polynomial.C (1 / 2 : ℚ)) * Pseries * z) hQ_ode_mul
    have hinv : PowerSeries.C (Polynomial.C (1 / 2 : ℚ)) * Pseries * (PowerSeries.C (Polynomial.C (2 : ℚ)) * R) = 1 := by
      calc PowerSeries.C (Polynomial.C (1 / 2 : ℚ)) * Pseries * (PowerSeries.C (Polynomial.C (2 : ℚ)) * R)
        _ = (PowerSeries.C (Polynomial.C (2 : ℚ)) * PowerSeries.C (Polynomial.C (1 / 2 : ℚ))) * (R * Pseries) := by ring
        _ = 1 := by rw [h2half, hRP, mul_one]
    linear_combination h - (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Q) * hinv +
      (-Q * (Pseries - 1)) * hinv
  have hQE : Q * Epoly = 1 := by
    have hd : PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) (Q * Epoly - 1) = 0 := by
      rw [map_sub, hd1, sub_zero, ps_deriv_mul, mul_add]
      calc PowerSeries.X * (Q * PowerSeries.derivative (Polynomial ℚ) Epoly) +
            PowerSeries.X * (Epoly * PowerSeries.derivative (Polynomial ℚ) Q)
        _ = Q * (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Epoly) +
            Epoly * (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) Q) := by ring
        _ = Q * (Epoly * (Pseries - 1)) + Epoly * (-Q * (Pseries - 1)) := by rw [hQ_ode, Epoly_ode]
        _ = 0 := by ring
    have hd0 : PowerSeries.derivative (Polynomial ℚ) (Q * Epoly - 1) = 0 := by
      apply PowerSeries.ext; intro n
      have h := congrArg (PowerSeries.coeff (n + 1)) hd
      rw [PowerSeries.coeff_succ_X_mul, map_zero] at h
      exact h
    have h0 : PowerSeries.coeff 0 (Q * Epoly - 1) = 0 := by
      rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_one]
      have hD0 : PowerSeries.constantCoeff Dpoly = 1 := by
        simp [Dpoly, map_add, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X]
      have hP0 : PowerSeries.constantCoeff Pseries = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [Pseries, legPoly]
      have hQ0 : PowerSeries.constantCoeff Q = 1 := by
        simp only [Q, R, map_mul, map_add, map_sub, map_one, PowerSeries.constantCoeff_C,
          PowerSeries.constantCoeff_X, hD0, hP0, mul_zero, sub_zero, mul_one]
        have : (1 : Polynomial ℚ) + 1 = Polynomial.C 2 := by rw [map_ofNat]; ring
        rw [this, ← map_mul]; norm_num
      have hE0 : PowerSeries.constantCoeff Epoly = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Epoly_eq_Etrunc 0 0 (le_refl 0)]
        simp [Etrunc]
      rw [hQ0, hE0]; ring
    exact sub_eq_zero.mp (eq_of_derivative_eq_zero _ h0 hd0)
  -- Finally deduce the quadratic `C T * Y^2 * Epoly^2 - (1 - C (1 + T) * Y) * Epoly + 1 = 0`!
  have hdiff_sq : (1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X) ^ 2 - R ^ 2 =
      PowerSeries.C (Polynomial.C (4 : ℚ)) * PowerSeries.C Polynomial.X * PowerSeries.X ^ 2 := by
    rw [hR2, Dpoly]
    have h2 : PowerSeries.C (Polynomial.C (2 : ℚ) * (1 + Polynomial.X)) =
        PowerSeries.C (Polynomial.C (2 : ℚ)) * PowerSeries.C (1 + Polynomial.X) := map_mul _ _ _
    have h4 : PowerSeries.C (Polynomial.C (4 : ℚ)) * PowerSeries.C Polynomial.X =
        PowerSeries.C ((1 + Polynomial.X) ^ 2 - (1 - Polynomial.X) ^ 2) := by
      rw [← map_mul]; congr 1
      have : Polynomial.C (4 : ℚ) = 4 := by rw [map_ofNat]
      rw [this]; ring
    have h2eq : PowerSeries.C (Polynomial.C (2 : ℚ)) = 2 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, map_natCast, map_natCast]; norm_num
    rw [h2, h2eq, h4, map_sub, map_pow, map_pow]
    ring
  have h2eq : PowerSeries.C (Polynomial.C (2 : ℚ)) = 2 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, map_natCast, map_natCast]; norm_num
  have h4eq : PowerSeries.C (Polynomial.C (4 : ℚ)) = 4 := by
    rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num, map_natCast, map_natCast]; norm_num
  rw [h2eq] at h2Q
  rw [h4eq] at hdiff_sq
  have hQE2 : (1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X + R) * Epoly = 2 := by
    linear_combination -Epoly * h2Q + 2 * hQE
  have h4quad : 4 * (PowerSeries.C Polynomial.X * PowerSeries.X ^ 2 * Epoly ^ 2 -
      (1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X) * Epoly + 1) = 0 := by
    linear_combination -Epoly ^ 2 * hdiff_sq +
      ((1 - PowerSeries.C (1 + Polynomial.X) * PowerSeries.X - R) * Epoly - 2) * hQE2
  have h4ne : (4 : PowerSeries (Polynomial ℚ)) ≠ 0 := by
    intro h
    have h0 := congrArg (PowerSeries.coeff 0) h
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_ofNat, map_zero] at h0
    exact absurd h0 (by norm_num)
  exact (mul_eq_zero.mp h4quad).resolve_left h4ne

private lemma evalSub_Epoly_eq_balaExp : evalSub Epoly = balaExp := by
  have hL0 : PowerSeries.coeff 0 balaLog = 0 := by
    rw [← evalSub_Lpoly, coeff_evalSub]
    simp [Lpoly]
  have hL_pow_lt : ∀ k m, m < k → PowerSeries.coeff m (balaLog ^ k) = 0 := by
    intro k; induction k with
    | zero => intro m hm; omega
    | succ k ih =>
        intro m hm
        rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (balaLog ^ k) * PowerSeries.coeff b balaLog)]
        refine Finset.sum_eq_zero fun a ha => ?_
        have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        by_cases hlt : a < k
        · rw [ih a hlt, zero_mul]
        · rw [show m - a = 0 by omega, hL0, mul_zero]
  have hE_ode : PowerSeries.X * PowerSeries.derivative ℚ balaExp =
      balaExp * (PowerSeries.X * PowerSeries.derivative ℚ balaLog) := by
    apply PowerSeries.ext; intro n
    cases n with
    | zero =>
        rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
            ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_zero_X_mul, mul_zero]
    | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a balaExp * PowerSeries.coeff b (PowerSeries.X * PowerSeries.derivative ℚ balaLog))]
        rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero]
        simp only [balaExp, PowerSeries.coeff_mk, expCoeffs]
        have hpos : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring, div_mul_cancel₀ _ hpos,
            Fin.sum_univ_eq_sum_range (fun k =>
          ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) balaLog * expCoeffs balaLog (n - k))]
        refine Finset.sum_nbij (fun k => n - k) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_range] at ha hb
          dsimp only at hab; omega
        · intro j hj
          simp only [Finset.mem_coe, Finset.mem_range] at hj
          exact ⟨n - j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
        · intro k hk
          simp only [Finset.mem_range] at hk
          rw [show n + 1 - (n - k) = k + 1 by omega, PowerSeries.coeff_succ_X_mul,
              PowerSeries.coeff_derivative]
          push_cast; ring
  -- Show `evalSub (Etrunc m)` agrees with `balaExp` through degree `m`, AND with `evalSub Epoly` at degree `m`!
  apply PowerSeries.ext; intro m
  have h1 : PowerSeries.coeff m (evalSub Epoly) = PowerSeries.coeff m (evalSub (Etrunc m)) := by
    rw [coeff_evalSub, coeff_evalSub]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnm : n ≤ m := by have := Finset.mem_range.mp hn; omega
    rw [coeff_Epoly_eq_Etrunc m n hnm]
  rw [h1]
  have heval_trunc : evalSub (Etrunc m) =
      ∑ k ∈ Finset.range (m + 1), PowerSeries.C ((1 : ℚ) / (Nat.factorial k : ℚ)) * balaLog ^ k := by
    simp only [Etrunc, evalSub_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evalSub_mul, evalSub_C, evalSub_pow, evalSub_Lpoly]
    simp only [evalPoly, Polynomial.aeval_C]
    rfl
  set T := ∑ k ∈ Finset.range (m + 1), PowerSeries.C ((1 : ℚ) / (Nat.factorial k : ℚ)) * balaLog ^ k
  have hT_ode : ∀ r ≤ m,
      PowerSeries.coeff r (PowerSeries.X * PowerSeries.derivative ℚ T) =
      PowerSeries.coeff r (T * (PowerSeries.X * PowerSeries.derivative ℚ balaLog)) := by
    have hdT : PowerSeries.X * PowerSeries.derivative ℚ T =
        (T - PowerSeries.C ((1 : ℚ) / (Nat.factorial m : ℚ)) * balaLog ^ m) *
          (PowerSeries.X * PowerSeries.derivative ℚ balaLog) := by
      have hderiv : PowerSeries.derivative ℚ T =
          (∑ k ∈ Finset.range m, PowerSeries.C ((1 : ℚ) / (Nat.factorial k : ℚ)) * balaLog ^ k) *
            PowerSeries.derivative ℚ balaLog := by
        simp only [T, map_sum]
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul,
          Derivation.map_one_eq_zero, add_zero, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul,
            mul_zero, add_zero, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
        have hc : PowerSeries.C ((1 : ℚ) / (Nat.factorial (k + 1) : ℚ)) * ((k + 1 : ℕ) : PowerSeries ℚ) =
            PowerSeries.C ((1 : ℚ) / (Nat.factorial k : ℚ)) := by
          rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by rw [map_natCast],
              ← map_mul]
          congr 1; rw [Nat.factorial_succ, Nat.cast_mul]
          have hpos : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          field_simp [hpos]
        calc PowerSeries.C ((1 : ℚ) / (Nat.factorial (k + 1) : ℚ)) *
              (((k + 1 : ℕ) : PowerSeries ℚ) * (balaLog ^ k * PowerSeries.derivative ℚ balaLog))
          _ = (PowerSeries.C ((1 : ℚ) / (Nat.factorial (k + 1) : ℚ)) * ((k + 1 : ℕ) : PowerSeries ℚ)) *
                (balaLog ^ k * PowerSeries.derivative ℚ balaLog) := by ring
          _ = PowerSeries.C ((1 : ℚ) / (Nat.factorial k : ℚ)) * balaLog ^ k *
                PowerSeries.derivative ℚ balaLog := by rw [hc]; ring
      have hsplit : ∑ k ∈ Finset.range m, PowerSeries.C ((1 : ℚ) / (Nat.factorial k : ℚ)) * balaLog ^ k =
          T - PowerSeries.C ((1 : ℚ) / (Nat.factorial m : ℚ)) * balaLog ^ m := by
        dsimp only [T]; rw [Finset.sum_range_succ]; ring
      rw [hderiv, hsplit]; ring
    intro r hr
    rw [hdT, sub_mul, map_sub]
    have htail : PowerSeries.coeff r
        ((PowerSeries.C ((1 : ℚ) / (Nat.factorial m : ℚ)) * balaLog ^ m) *
          (PowerSeries.X * PowerSeries.derivative ℚ balaLog)) = 0 := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (balaLog ^ m) * PowerSeries.coeff b (PowerSeries.X * PowerSeries.derivative ℚ balaLog))]
      have hsum : ∑ a ∈ Finset.range (r + 1),
          PowerSeries.coeff a (balaLog ^ m) * PowerSeries.coeff (r - a) (PowerSeries.X * PowerSeries.derivative ℚ balaLog) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        by_cases hlt : a < m
        · rw [hL_pow_lt m a hlt, zero_mul]
        · rw [show r - a = 0 by omega, PowerSeries.coeff_zero_X_mul, mul_zero]
      rw [hsum, mul_zero]
    rw [htail, sub_zero]
  have hT_eq : ∀ r ≤ m, PowerSeries.coeff r T = PowerSeries.coeff r balaExp := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr
      cases r with
      | zero =>
          simp only [T, map_sum, PowerSeries.coeff_C_mul]
          rw [Finset.sum_range_succ']
          have hrest : ∑ k ∈ Finset.range m, ((1 : ℚ) / (Nat.factorial (k + 1) : ℚ)) *
              PowerSeries.coeff 0 (balaLog ^ (k + 1)) = 0 := by
            refine Finset.sum_eq_zero fun k _ => by rw [hL_pow_lt (k + 1) 0 (by omega), mul_zero]
          rw [hrest, zero_add]
          simp [balaExp, expCoeffs]
      | succ r =>
          have h1 := hT_ode (r + 1) hr
          have h2 := congrArg (PowerSeries.coeff (r + 1)) hE_ode
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative] at h1 h2
          have hmul_eq : PowerSeries.coeff (r + 1) (T * (PowerSeries.X * PowerSeries.derivative ℚ balaLog)) =
              PowerSeries.coeff (r + 1) (balaExp * (PowerSeries.X * PowerSeries.derivative ℚ balaLog)) := by
            rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a T * PowerSeries.coeff b (PowerSeries.X * PowerSeries.derivative ℚ balaLog)),
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a balaExp * PowerSeries.coeff b (PowerSeries.X * PowerSeries.derivative ℚ balaLog))]
            refine Finset.sum_congr rfl fun a ha => ?_
            have har : a ≤ r + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            by_cases heq : a = r + 1
            · subst heq; rw [Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero, mul_zero]
            · rw [ih a (by omega) (by omega)]
          have hpos : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          have hr1 : ((r : ℚ) + 1) = ((r + 1 : ℕ) : ℚ) := by push_cast; ring
          rw [hr1] at h1 h2
          have heq : PowerSeries.coeff (r + 1) T * ((r + 1 : ℕ) : ℚ) =
              PowerSeries.coeff (r + 1) balaExp * ((r + 1 : ℕ) : ℚ) := by
            rw [h1, h2, hmul_eq]
          exact mul_right_cancel₀ hpos heq
  rw [heval_trunc]
  exact hT_eq m (le_refl m)

theorem main_proof :
    ∀ A : PowerSeries ℚ,
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.X * (1 + PowerSeries.X) * A ^ 2 -
        (1 + PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 3) * A +
        (1 + PowerSeries.X - PowerSeries.X ^ 2) = 0 →
      A = 1 + PowerSeries.X ^ 3 * balaExp := by
  intro A hA0 hAeq
  -- First show `A₀ := 1 + X^3 * balaExp` satisfies the EXACT SAME quadratic equation!
  have hEquad : (1 + PowerSeries.X) * PowerSeries.X ^ 4 * balaExp ^ 2 -
      (1 - (PowerSeries.C 2 + PowerSeries.X) * PowerSeries.X ^ 2) * balaExp + 1 = 0 := by
    have h := congrArg evalSub Epoly_quad
    rw [evalSub_add, evalSub_sub, evalSub_one, evalSub_mul, evalSub_mul, evalSub_mul,
        evalSub_sub, evalSub_one, evalSub_mul, evalSub_C, evalSub_C, evalSub_pow, evalSub_pow,
        evalSub_X, evalSub_Epoly_eq_balaExp] at h
    have h0 : evalSub 0 = 0 := by
      apply PowerSeries.ext; intro m; simp [coeff_evalSub]
    rw [h0] at h
    have hT : evalPoly Polynomial.X = 1 + PowerSeries.X := by simp [evalPoly]
    have h1T : evalPoly (1 + Polynomial.X) = PowerSeries.C 2 + PowerSeries.X := by
      simp only [evalPoly, map_add, map_one, Polynomial.aeval_X]
      have h2 : PowerSeries.C (2 : ℚ) = 2 := by rw [map_ofNat]
      rw [h2]; ring
    rw [hT, h1T, ← pow_mul] at h
    exact h
  set A₀ : PowerSeries ℚ := 1 + PowerSeries.X ^ 3 * balaExp
  have hA₀0 : PowerSeries.coeff 0 A₀ = 1 := by
    simp only [A₀, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul',
      show ¬ 3 ≤ 0 by omega, ↓reduceIte, add_zero]
  have hA₀eq : PowerSeries.X * (1 + PowerSeries.X) * A₀ ^ 2 -
      (1 + PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 3) * A₀ +
      (1 + PowerSeries.X - PowerSeries.X ^ 2) = 0 := by
    have h2 : PowerSeries.C (2 : ℚ) = 2 := by rw [map_ofNat]
    simp only [A₀, h2] at hEquad ⊢
    linear_combination PowerSeries.X ^ 3 * hEquad
  -- Uniqueness of formal power series solution with `coeff 0 = 1`:
  -- `(A - A₀) * (1 + 2X - X^3 - X(1+X)(A + A₀)) = 0`!
  have hfactor : (A - A₀) * (1 + PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 3 -
      PowerSeries.X * (1 + PowerSeries.X) * (A + A₀)) = 0 := by
    linear_combination hA₀eq - hAeq
  set U : PowerSeries ℚ := 1 + PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 3 -
      PowerSeries.X * (1 + PowerSeries.X) * (A + A₀)
  have hU0 : PowerSeries.coeff 0 U = 1 := by
    simp only [U, map_sub, map_add, PowerSeries.coeff_one,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X, mul_zero, add_zero,
      PowerSeries.coeff_X_pow, show (0 : ℕ) ≠ 3 by omega, ↓reduceIte, sub_zero,
      mul_assoc, PowerSeries.coeff_zero_X_mul]
  have hdiff0 : ∀ n : ℕ, PowerSeries.coeff n (A - A₀) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have h := congrArg (PowerSeries.coeff n) hfactor
      rw [map_zero, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (A - A₀) * PowerSeries.coeff b U),
          Finset.sum_range_succ, Nat.sub_self, hU0, mul_one] at h
      have hrest : ∑ a ∈ Finset.range n, PowerSeries.coeff a (A - A₀) * PowerSeries.coeff (n - a) U = 0 :=
        Finset.sum_eq_zero fun a ha => by rw [ih a (Finset.mem_range.mp ha), zero_mul]
      rw [hrest, zero_add] at h
      exact h
  apply PowerSeries.ext; intro n
  exact sub_eq_zero.mp (by simpa using hdiff0 n)

end OMA.S_oeis_a167638

theorem OMA.solution : type_of% @OMA.S_oeis_a167638.main :=
  OMA.S_oeis_a167638.main_proof
