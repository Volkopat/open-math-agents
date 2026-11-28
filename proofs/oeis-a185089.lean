import OMAStatements.S_oeis_a185089

/-!
# Proof of OEIS A185089 (Mathar's recurrence)

We prove R. J. Mathar's 5-term linear recurrence with linear coefficients for the sequence
`a n = ∑ k ∈ Finset.range (n / 2 + 1), (n - k).choose k * s k`, where `s` is the little
Schroeder sequence (OEIS A001003) defined via Narayana numbers.

Outline:
1. Show exact divisibility `m ∣ m.choose k * m.choose (k - 1)` for `1 ≤ k ≤ m`, expressing
   `(s m : ℚ)` as a rational sum `∑ k ∈ Finset.Icc 1 m, F m k`.
2. Prove the 3-term little Schroeder recurrence `(m + 1) * s m = (6 * m - 3) * s (m - 1) -
   (m - 2) * s (m - 2)` for `m ≥ 2` by Wilf-Zeilberger telescoping.
3. Match `S = PowerSeries.mk (fun m => (s m : ℚ))` with the formal power series
   `TS = (largeSchroderSeries + 1) / 2` via the differential equation derived from
   `2 * X * TS ^ 2 - (1 + X) * TS + 1 = 0`, establishing `2 * X * S ^ 2 - (1 + X) * S + 1 = 0`.
4. Use `PowerSeries.subst` at `u = X ^ 2 * (1 - X)⁻¹` to show `(1 - X) * A = S.subst u`,
   deduce the quadratic equation for `A = PowerSeries.mk (fun n => (a n : ℚ))`, differentiate to
   obtain the first-order linear ODE `Q1 * d⁄dX ℚ A + Q0 * A + R = 0`, and extract the `n`-th
   coefficient for `n ≥ 5`.
-/

namespace ProofA185089

open Finset PowerSeries
open OMA.S_oeis_a185089 (s a)

/-! ## Step 1: Exact divisibility and rational formula for `s` -/

private lemma dvd_choose_mul_choose_pred {m k : ℕ} (hk1 : 1 ≤ k) :
    m ∣ m.choose k * m.choose (k - 1) := by
  rcases m with _ | m
  · rw [show k = (k - 1) + 1 by omega, Nat.choose_zero_succ]
    simp
  · rcases eq_or_lt_of_le hk1 with rfl | hk2
    · simp
    · have h1 : k * (m + 1).choose k = (m + 1) * m.choose (k - 1) := by
        have := Nat.add_one_mul_choose_eq m (k - 1)
        rw [show k - 1 + 1 = k by omega] at this
        linarith
      have h2 : (k - 1) * (m + 1).choose (k - 1) = (m + 1) * m.choose (k - 2) := by
        have := Nat.add_one_mul_choose_eq m (k - 2)
        rw [show k - 2 + 1 = k - 1 by omega] at this
        linarith
      have hd1 : m + 1 ∣ k * ((m + 1).choose k * (m + 1).choose (k - 1)) := by
        refine ⟨m.choose (k - 1) * (m + 1).choose (k - 1), ?_⟩
        calc
          k * ((m + 1).choose k * (m + 1).choose (k - 1))
              = (k * (m + 1).choose k) * (m + 1).choose (k - 1) := by ring
          _ = ((m + 1) * m.choose (k - 1)) * (m + 1).choose (k - 1) := by rw [h1]
          _ = (m + 1) * (m.choose (k - 1) * (m + 1).choose (k - 1)) := by ring
      have hd2 : m + 1 ∣ (k - 1) * ((m + 1).choose k * (m + 1).choose (k - 1)) := by
        refine ⟨(m + 1).choose k * m.choose (k - 2), ?_⟩
        calc
          (k - 1) * ((m + 1).choose k * (m + 1).choose (k - 1))
              = (m + 1).choose k * ((k - 1) * (m + 1).choose (k - 1)) := by ring
          _ = (m + 1).choose k * ((m + 1) * m.choose (k - 2)) := by rw [h2]
          _ = (m + 1) * ((m + 1).choose k * m.choose (k - 2)) := by ring
      have hsub := Nat.dvd_sub hd1 hd2
      have hdiff :
          k * ((m + 1).choose k * (m + 1).choose (k - 1)) -
            (k - 1) * ((m + 1).choose k * (m + 1).choose (k - 1)) =
            (m + 1).choose k * (m + 1).choose (k - 1) := by
        rw [← Nat.sub_mul, show k - (k - 1) = 1 by omega, one_mul]
      rwa [hdiff] at hsub

private def F (m k : ℕ) : ℚ :=
  if m = 0 ∨ k = 0 then 0
  else (m.choose k : ℚ) * (m.choose (k - 1) : ℚ) * 2 ^ (k - 1) / (m : ℚ)

private lemma F_eq_zero_of_lt {m k : ℕ} (h : m < k) : F m k = 0 := by
  unfold F
  split_ifs with h0
  · rfl
  · simp [Nat.choose_eq_zero_of_lt h]

private lemma s_cast_eq_sum_F {m : ℕ} (hm : 1 ≤ m) :
    (s m : ℚ) = ∑ k ∈ Finset.Icc 1 m, F m k := by
  have hdiv : m ∣ ∑ k ∈ Finset.Icc 1 m, m.choose k * m.choose (k - 1) * 2 ^ (k - 1) := by
    refine Finset.dvd_sum fun k hk => ?_
    exact dvd_mul_of_dvd_left (dvd_choose_mul_choose_pred (Finset.mem_Icc.mp hk).1) _
  have hm0 : m ≠ 0 := by omega
  have hmul : m * s m = ∑ k ∈ Finset.Icc 1 m, m.choose k * m.choose (k - 1) * 2 ^ (k - 1) := by
    simp only [s, hm0, ↓reduceIte]
    exact Nat.mul_div_cancel' hdiv
  have hq : (m : ℚ) * (s m : ℚ) =
      ∑ k ∈ Finset.Icc 1 m, (m.choose k : ℚ) * (m.choose (k - 1) : ℚ) * 2 ^ (k - 1) := by
    exact_mod_cast hmul
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hdivQ : (s m : ℚ) =
      (∑ k ∈ Finset.Icc 1 m, (m.choose k : ℚ) * (m.choose (k - 1) : ℚ) * 2 ^ (k - 1)) / (m : ℚ) :=
    (eq_div_iff hmQ).mpr (by linarith)
  rw [hdivQ, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  simp [F, hm0, hk0]

/-! ## Step 2: Wilf-Zeilberger proof of the little Schroeder recurrence -/

private lemma nat_choose_sub_mul (n k : ℕ) :
    (n + 1 - k) * (n + 1).choose k = (n + 1) * n.choose k := by
  rcases le_or_gt k (n + 1) with hk | hk
  · have h := Nat.add_one_mul_choose_eq n (n - k)
    rcases eq_or_lt_of_le hk with rfl | hklt
    · simp
    · rw [show n - k + 1 = n + 1 - k by omega] at h
      rw [← Nat.choose_symm (by omega : k ≤ n), ← Nat.choose_symm hk]
      linarith
  · simp [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega : n < k)]

private lemma choose_pred_rat {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m) :
    ((m - 1).choose k : ℚ) = ((m : ℚ) - k) / (m : ℚ) * (m.choose k : ℚ) := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnat := nat_choose_sub_mul (m - 1) k
  rw [show m - 1 + 1 = m by omega] at hnat
  have hq : ((m - k : ℕ) : ℚ) * (m.choose k : ℚ) = (m : ℚ) * ((m - 1).choose k : ℚ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hk] at hq
  field_simp
  linarith

private lemma choose_succ_right_rat {m k : ℕ} (hk : k ≤ m) :
    (m.choose (k + 1) : ℚ) = ((m : ℚ) - k) / ((k : ℚ) + 1) * (m.choose k : ℚ) := by
  have hnat := Nat.choose_succ_right_eq m k
  have hq : (m.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (m.choose k : ℚ) * ((m - k : ℕ) : ℚ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hk] at hq
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

private lemma F_pred_rat {m k : ℕ} (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    F (m - 1) k = ((m : ℚ) - k) * ((m : ℚ) - k + 1) / ((m : ℚ) * ((m : ℚ) - 1)) * F m k := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have h1 := choose_pred_rat (by omega : 1 ≤ m) hkm
  have h2 := choose_pred_rat (by omega : 1 ≤ m) (by omega : k - 1 ≤ m)
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hm1Q : (m : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  simp only [F, hm0, hm1, hk0, or_self, ↓reduceIte]
  rw [h1, h2, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub hk1]
  simp only [Nat.cast_one]
  field_simp
  ring

private lemma F_pred2_rat {m k : ℕ} (hm : 3 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    F (m - 2) k =
      ((m : ℚ) - k) ^ 2 * ((m : ℚ) - k - 1) * ((m : ℚ) - k + 1) /
        ((m : ℚ) * ((m : ℚ) - 1) ^ 2 * ((m : ℚ) - 2)) * F m k := by
  rcases eq_or_lt_of_le hkm with rfl | hkm1
  · rw [F_eq_zero_of_lt (by omega)]
    ring
  · have hstep1 := F_pred_rat (m := m - 1) (k := k) (by omega) hk1 (by omega)
    have hstep2 := F_pred_rat (m := m) (k := k) (by omega) hk1 hkm
    rw [show m - 1 - 1 = m - 2 by omega] at hstep1
    rw [hstep1, hstep2, Nat.cast_sub (by omega : 1 ≤ m)]
    simp only [Nat.cast_one]
    have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm1Q : (m : ℚ) - 1 ≠ 0 := by
      have : (3 : ℚ) ≤ m := by exact_mod_cast hm
      linarith
    have hm2Q : (m : ℚ) - 2 ≠ 0 := by
      have : (3 : ℚ) ≤ m := by exact_mod_cast hm
      linarith
    have hm11Q : (m : ℚ) - 1 - 1 ≠ 0 := by
      have : (3 : ℚ) ≤ m := by exact_mod_cast hm
      linarith
    field_simp
    ring

private lemma F_succ_k_rat {m k : ℕ} (hm : 1 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    F m (k + 1) =
      2 * ((m : ℚ) - k) * ((m : ℚ) - k + 1) / ((k : ℚ) * ((k : ℚ) + 1)) * F m k := by
  have hm0 : m ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have h1 := choose_succ_right_rat hkm
  have h2 := choose_succ_right_rat (m := m) (k := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at h2
  simp only [F, hm0, hk0, Nat.succ_ne_zero, or_self, ↓reduceIte, Nat.add_sub_cancel]
  rw [h1, Nat.cast_sub hk1] at *
  simp only [Nat.cast_one] at h2 ⊢
  rw [sub_add_cancel] at h2
  have hpow : (2 : ℚ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  rw [hpow, h2]
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hk1Q : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private def G (m k : ℕ) : ℚ :=
  (k : ℚ) * ((k : ℚ) - 1) * ((k : ℚ) ^ 2 - 3 * k - 2 * (m : ℚ) ^ 2 + 3 * m + 1) /
    ((m : ℚ) * ((m : ℚ) - 1) ^ 2) * F m k

private lemma wz_identity {m k : ℕ} (hm : 3 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    ((m : ℚ) + 1) * F m k - (6 * (m : ℚ) - 3) * F (m - 1) k + ((m : ℚ) - 2) * F (m - 2) k =
      G m (k + 1) - G m k := by
  unfold G
  rw [F_pred_rat (by omega) hk1 hkm, F_pred2_rat hm hk1 hkm, F_succ_k_rat (by omega) hk1 hkm]
  push_cast
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1Q : (m : ℚ) - 1 ≠ 0 := by
    have : (3 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  have hm2Q : (m : ℚ) - 2 ≠ 0 := by
    have : (3 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1Q : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private lemma s_recurrence {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℚ) + 1) * (s m : ℚ) =
      (6 * (m : ℚ) - 3) * (s (m - 1) : ℚ) - ((m : ℚ) - 2) * (s (m - 2) : ℚ) := by
  rcases eq_or_lt_of_le hm with rfl | hm3
  · have hs0 : s 0 = 1 := by simp [s]
    have hs1 : s 1 = 1 := by simp [s]
    have hs2 : s 2 = 3 := by decide
    simp [hs0, hs1, hs2]
    norm_num
  · have hsum_wz :
        ∑ k ∈ Finset.Icc 1 m,
          (((m : ℚ) + 1) * F m k - (6 * (m : ℚ) - 3) * F (m - 1) k +
            ((m : ℚ) - 2) * F (m - 2) k) =
        ∑ k ∈ Finset.Icc 1 m, (G m (k + 1) - G m k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      exact wz_identity hm3 (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    have htele : ∑ k ∈ Finset.Icc 1 m, (G m (k + 1) - G m k) = G m (m + 1) - G m 1 := by
      have hIcc : Finset.Icc 1 m = (Finset.range m).image (· + 1) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
        · rintro ⟨y, hy, rfl⟩; omega
      rw [hIcc, Finset.sum_image (fun _ _ _ _ h => by omega)]
      have h := Finset.sum_range_sub (fun j => G m (j + 1)) m
      simpa [add_assoc] using h
    have hG1 : G m 1 = 0 := by simp [G]
    have hGm1 : G m (m + 1) = 0 := by simp [G, F_eq_zero_of_lt (Nat.lt_succ_self m)]
    have hsm : ∑ k ∈ Finset.Icc 1 m, F m k = (s m : ℚ) := (s_cast_eq_sum_F (by omega)).symm
    have hsm1 : ∑ k ∈ Finset.Icc 1 m, F (m - 1) k = (s (m - 1) : ℚ) := by
      rw [show Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
          Finset.sum_insert (by simp; omega), F_eq_zero_of_lt (by omega), zero_add]
      exact (s_cast_eq_sum_F (by omega)).symm
    have hsm2 : ∑ k ∈ Finset.Icc 1 m, F (m - 2) k = (s (m - 2) : ℚ) := by
      have h1 : Finset.Icc 1 m = insert m (insert (m - 1) (Finset.Icc 1 (m - 2))) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
        F_eq_zero_of_lt (by omega), F_eq_zero_of_lt (by omega), zero_add, zero_add]
      exact (s_cast_eq_sum_F (by omega)).symm
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hsm, hsm1, hsm2, htele, hG1, hGm1, sub_zero] at hsum_wz
    linarith

/-! ## Step 3: Quadratic functional equation for the generating function of `s` -/

private noncomputable def S : ℚ⟦X⟧ := PowerSeries.mk (fun m => (s m : ℚ))

private lemma coeff_X_pow_mul_eq (f : ℚ⟦X⟧) (k n : ℕ) :
    PowerSeries.coeff n ((X : ℚ⟦X⟧) ^ k * f) = if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [mul_comm, PowerSeries.coeff_mul_X_pow']

private lemma deriv_two : PowerSeries.derivative ℚ (2 : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat C, PowerSeries.derivative_C]

private lemma deriv_four : PowerSeries.derivative ℚ (4 : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat C, PowerSeries.derivative_C]

private lemma deriv_five : PowerSeries.derivative ℚ (5 : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat C, PowerSeries.derivative_C]

private lemma deriv_six : PowerSeries.derivative ℚ (6 : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat C, PowerSeries.derivative_C]

private lemma S_quadratic : 2 * X * S ^ 2 - (1 + X) * S + 1 = 0 := by
  let L : ℚ⟦X⟧ := PowerSeries.largeSchroderSeries.map (Nat.castRingHom ℚ)
  let TS : ℚ⟦X⟧ := C (1 / 2 : ℚ) * (L + 1)
  have hL : L = 1 + X * L + X * L ^ 2 := by
    have hnat := PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    have hmap := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) hnat
    simpa [L, map_add, map_mul, map_pow, map_one, PowerSeries.map_X] using hmap
  have h2TS : 2 * TS = L + 1 := by
    dsimp only [TS]
    have h2 : (2 : ℚ⟦X⟧) = C (2 : ℚ) := (map_ofNat C 2).symm
    rw [h2, ← mul_assoc, ← map_mul]
    norm_num
  have hTS_quad : 2 * X * TS ^ 2 - (1 + X) * TS + 1 = 0 := by
    have hL' : L = 2 * TS - 1 := by
      have := congrArg (fun z => z - 1) h2TS
      simpa using this.symm
    rw [hL'] at hL
    have h4 : 2 * (2 * X * TS ^ 2 - (1 + X) * TS + 1) =
        (1 + X * (2 * TS - 1) + X * (2 * TS - 1) ^ 2) - (2 * TS - 1) := by ring
    have hzero : 2 * (2 * X * TS ^ 2 - (1 + X) * TS + 1) = 0 := by
      rw [h4, ← hL, sub_self]
    have h2ne : (2 : ℚ⟦X⟧) ≠ 0 := by
      intro h
      have := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
      rw [map_ofNat, map_zero] at this
      norm_num at this
    exact (mul_eq_zero.mp hzero).resolve_left h2ne
  -- Differentiate (4 * X * TS - (1 + X))^2 = 1 - 6 * X + X^2
  let W : ℚ⟦X⟧ := 4 * X * TS - (1 + X)
  let D : ℚ⟦X⟧ := 1 - 6 * X + X ^ 2
  have hW2 : W ^ 2 = D := by
    dsimp only [W, D]
    linear_combination 8 * X * hTS_quad
  have hDW2 := congrArg (PowerSeries.derivative ℚ) hW2
  have hLHS_d : PowerSeries.derivative ℚ (W ^ 2) = 2 * W * PowerSeries.derivative ℚ W := by
    rw [PowerSeries.derivative_pow]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [hLHS_d] at hDW2
  have hODE_raw : 2 * D * PowerSeries.derivative ℚ W - PowerSeries.derivative ℚ D * W = 0 := by
    have hmul := congrArg (· * W) hDW2
    linear_combination hmul - 2 * PowerSeries.derivative ℚ W * hW2
  have hdW : PowerSeries.derivative ℚ W = 4 * TS + 4 * X * PowerSeries.derivative ℚ TS - 1 := by
    dsimp only [W]
    simp only [map_sub, map_add, Derivation.leibniz, PowerSeries.derivative_X,
      PowerSeries.derivative_one, deriv_four, smul_eq_mul]
    ring
  have hdD : PowerSeries.derivative ℚ D = -6 + 2 * X := by
    dsimp only [D]
    simp only [map_add, map_sub, Derivation.leibniz, PowerSeries.derivative_pow,
      PowerSeries.derivative_X, PowerSeries.derivative_one, deriv_six, smul_eq_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hODE8 : 8 * ((X ^ 3 - 6 * X ^ 2 + X) * PowerSeries.derivative ℚ TS +
      (1 - 3 * X) * TS + (X - 1)) = 0 := by
    rw [hdW, hdD] at hODE_raw
    dsimp only [W, D] at hODE_raw
    linear_combination hODE_raw
  have h8ne : (8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have hODE : (X ^ 3 - 6 * X ^ 2 + X) * PowerSeries.derivative ℚ TS +
      (1 - 3 * X) * TS + (X - 1) = 0 := (mul_eq_zero.mp hODE8).resolve_left h8ne
  -- Extract the 3-term recurrence for coefficients of TS
  have hTS_rec : ∀ m : ℕ, 2 ≤ m →
      ((m : ℚ) + 1) * PowerSeries.coeff m TS =
        (6 * (m : ℚ) - 3) * PowerSeries.coeff (m - 1) TS -
          ((m : ℚ) - 2) * PowerSeries.coeff (m - 2) TS := by
    intro m hm
    have hsplit : (X ^ 3 - 6 * X ^ 2 + X) * PowerSeries.derivative ℚ TS +
        (1 - 3 * X) * TS + (X - 1) =
        X ^ 3 * PowerSeries.derivative ℚ TS - C (6 : ℚ) * (X ^ 2 * PowerSeries.derivative ℚ TS) +
          X ^ 1 * PowerSeries.derivative ℚ TS + TS - C (3 : ℚ) * (X ^ 1 * TS) + X - 1 := by
      simp only [map_ofNat]
      ring
    have hc := congrArg (PowerSeries.coeff m) (hsplit.symm.trans hODE)
    simp only [map_add, map_sub, map_zero, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
      PowerSeries.coeff_derivative, PowerSeries.coeff_X, PowerSeries.coeff_one] at hc
    have h1m : 1 ≤ m := by omega
    have h2m : 2 ≤ m := hm
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    simp only [h1m, h2m, hm0, hm1, ↓reduceIte] at hc
    rcases eq_or_lt_of_le hm with rfl | hm3
    · simp only [show ¬(3 ≤ 2) by omega, ↓reduceIte] at hc
      norm_num at hc ⊢
      linarith
    · have h3m : 3 ≤ m := hm3
      simp only [h3m, ↓reduceIte] at hc
      rw [show m - 3 + 1 = m - 2 by omega, show m - 2 + 1 = m - 1 by omega,
        show m - 1 + 1 = m by omega,
        Nat.cast_sub (by omega : 3 ≤ m),
        Nat.cast_sub (by omega : 2 ≤ m),
        Nat.cast_sub (by omega : 1 ≤ m)] at hc
      push_cast at hc
      linarith
  -- Base cases: coeff 0 TS = s 0 and coeff 1 TS = s 1
  have hc0 : PowerSeries.coeff 0 TS = (s 0 : ℚ) := by
    dsimp only [TS, L]
    rw [PowerSeries.coeff_C_mul, map_add, PowerSeries.coeff_map,
      PowerSeries.coeff_largeSchroderSeries, PowerSeries.coeff_one]
    simp [s]
    norm_num
  have hc1 : PowerSeries.coeff 1 TS = (s 1 : ℚ) := by
    dsimp only [TS, L]
    simp [s, PowerSeries.coeff_map, PowerSeries.coeff_one]
  -- Strong induction: coeff m TS = (s m : ℚ) for all m
  have hcoeff_eq : ∀ m : ℕ, PowerSeries.coeff m TS = (s m : ℚ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases m with _ | _ | k
      · exact hc0
      · exact hc1
      · have hm : 2 ≤ k + 2 := by omega
        have h1 := hTS_rec (k + 2) hm
        have h2 := s_recurrence hm
        rw [ih (k + 2 - 1) (by omega), ih (k + 2 - 2) (by omega)] at h1
        have hpos : ((k + 2 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
        exact mul_left_cancel₀ hpos (h1.trans h2.symm)
  have hSeq : S = TS := by
    ext m
    simp [S, hcoeff_eq m]
  rwa [hSeq]

/-! ## Step 4: Transfer to `A` via `PowerSeries.subst` and extract Mathar's recurrence -/

private noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

private lemma hockey_stick (m k : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (i + k).choose k = (m + k + 1).choose (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have := Nat.choose_succ_succ (m + k + 1) k
    rw [show m + 1 + k + 1 = m + k + 1 + 1 by omega, show m + 1 + k = m + k + 1 by omega]
    linarith

private lemma coeff_inv_one_sub_X_pow (k m : ℕ) :
    PowerSeries.coeff m (((1 - (X : ℚ⟦X⟧))⁻¹) ^ (k + 1)) = ((m + k).choose k : ℚ) := by
  have hinv_eq : (1 - (X : ℚ⟦X⟧))⁻¹ = PowerSeries.mk (fun _ => (1 : ℚ)) := by
    have hconst : PowerSeries.constantCoeff (1 - (X : ℚ⟦X⟧)) ≠ 0 := by simp
    refine (PowerSeries.inv_eq_iff_mul_eq_one hconst).mpr ?_
    ext n
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mk,
      show PowerSeries.mk (fun _ => (1 : ℚ)) * X = X ^ 1 * PowerSeries.mk (fun _ => (1 : ℚ)) by
        ring,
      coeff_X_pow_mul_eq, PowerSeries.coeff_one]
    cases n <;> simp
  induction k generalizing m with
  | zero =>
    simp [hinv_eq]
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (((1 - (X : ℚ⟦X⟧))⁻¹) ^ (k + 1)) *
          PowerSeries.coeff j ((1 - (X : ℚ⟦X⟧))⁻¹)),
      Nat.succ_eq_add_one]
    simp_rw [ih]
    simp only [hinv_eq, PowerSeries.coeff_mk, mul_one]
    rw [show m + (k + 1) = m + k + 1 by omega]
    exact_mod_cast hockey_stick m k

private lemma one_sub_X_mul_A_eq_subst :
    (1 - (X : ℚ⟦X⟧)) * A = S.subst (X ^ 2 * (1 - X)⁻¹) := by
  let u : ℚ⟦X⟧ := X ^ 2 * (1 - X)⁻¹
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [u])
  have hcoeff_u_pow : ∀ k n : ℕ, 1 ≤ k →
      PowerSeries.coeff n (u ^ k) =
        if 2 * k ≤ n then ((n - k - 1).choose (k - 1) : ℚ) else 0 := by
    intro k n hk
    have hpow : u ^ k = X ^ (2 * k) * ((1 - (X : ℚ⟦X⟧))⁻¹) ^ ((k - 1) + 1) := by
      dsimp only [u]
      rw [mul_pow, ← pow_mul, show k - 1 + 1 = k by omega]
    rw [hpow, coeff_X_pow_mul_eq]
    split_ifs with hle
    · rw [coeff_inv_one_sub_X_pow, show n - 2 * k + (k - 1) = n - k - 1 by omega]
    · rfl
  ext n
  rw [PowerSeries.coeff_subst' hu]
  have hsupp : Function.support (fun d : ℕ => PowerSeries.coeff d S • PowerSeries.coeff n (u ^ d)) ⊆
      (Finset.range (n / 2 + 1) : Set ℕ) := by
    intro d hd
    simp only [Function.mem_support, ne_eq, smul_eq_mul] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    rcases d with _ | d
    · omega
    · have hle : 2 * (d + 1) ≤ n := by
        by_contra hgt
        rw [hcoeff_u_pow (d + 1) n (by omega), if_neg hgt, mul_zero] at hd
        exact hd rfl
      omega
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rcases n with _ | n
  · simp [A, S, a, s]
  · have hLHS : PowerSeries.coeff (n + 1) ((1 - X) * A) = (a (n + 1) : ℚ) - (a n : ℚ) := by
      rw [sub_mul, one_mul, map_sub, show X * A = X ^ 1 * A by rw [pow_one],
        coeff_X_pow_mul_eq]
      simp [A]
    rw [hLHS]
    have han1 : (a (n + 1) : ℚ) =
        ∑ k ∈ Finset.range ((n + 1) / 2 + 1), ((n + 1 - k).choose k : ℚ) * (s k : ℚ) := by
      simp [a]
    have han : (a n : ℚ) =
        ∑ k ∈ Finset.range ((n + 1) / 2 + 1), ((n - k).choose k : ℚ) * (s k : ℚ) := by
      simp only [a, Nat.cast_sum, Nat.cast_mul]
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk1 hk2 => ?_
      simp only [Finset.mem_range] at hk1 hk2
      have hlt : n - k < k := by omega
      simp [Nat.choose_eq_zero_of_lt hlt]
    rw [han1, han, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    simp only [S, PowerSeries.coeff_mk, smul_eq_mul]
    rcases k with _ | k
    · simp [pow_zero, PowerSeries.coeff_one]
    · have h2k : 2 * (k + 1) ≤ n + 1 := by omega
      rw [hcoeff_u_pow (k + 1) (n + 1) (by omega), if_pos h2k]
      simp only [Nat.add_sub_cancel]
      have hpascal : (n + 1 - (k + 1)).choose (k + 1) =
          (n - (k + 1)).choose k + (n - (k + 1)).choose (k + 1) := by
        rw [show n + 1 - (k + 1) = (n - (k + 1)) + 1 by omega]
        exact Nat.choose_succ_succ (n - (k + 1)) k
      have hq : ((n + 1 - (k + 1)).choose (k + 1) : ℚ) =
          ((n - (k + 1)).choose k : ℚ) + ((n - (k + 1)).choose (k + 1) : ℚ) := by
        exact_mod_cast hpascal
      rw [show n + 1 - (k + 1) - 1 = n - (k + 1) by omega]
      rw [hq]
      ring

private lemma A_quadratic :
    (2 * X ^ 4 - 4 * X ^ 3 + 2 * X ^ 2) * A ^ 2 +
      (X ^ 3 - 2 * X ^ 2 + 2 * X - 1) * A + (1 - X) = 0 := by
  let u : ℚ⟦X⟧ := X ^ 2 * (1 - X)⁻¹
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [u])
  have hconst : PowerSeries.constantCoeff (1 - (X : ℚ⟦X⟧)) ≠ 0 := by simp
  have h1X_u : (1 - (X : ℚ⟦X⟧)) * u = X ^ 2 := by
    dsimp only [u]
    rw [mul_left_comm, PowerSeries.mul_inv_cancel _ hconst, mul_one]
  have hsub := congrArg (PowerSeries.substAlgHom hu) S_quadratic
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero,
    PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom] at hsub
  rw [← one_sub_X_mul_A_eq_subst] at hsub
  have hmul := congrArg ((1 - (X : ℚ⟦X⟧)) * ·) hsub
  simp only [mul_zero] at hmul
  linear_combination hmul - (2 * ((1 - X) * A) ^ 2 - (1 - X) * A) * h1X_u

private lemma A_ode :
    (X ^ 6 + 5 * X ^ 5 - 11 * X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X) * PowerSeries.derivative ℚ A +
      (X ^ 5 + 9 * X ^ 4 - 13 * X ^ 3 + 6 * X - 2) * A +
      (X ^ 3 - X ^ 2 - 3 * X + 2) = 0 := by
  let p2 : ℚ⟦X⟧ := 2 * X ^ 4 - 4 * X ^ 3 + 2 * X ^ 2
  let p1 : ℚ⟦X⟧ := X ^ 3 - 2 * X ^ 2 + 2 * X - 1
  let D : ℚ⟦X⟧ := (X - 1) ^ 2 * (X ^ 4 + 6 * X ^ 3 - 5 * X ^ 2 - 2 * X + 1)
  let W : ℚ⟦X⟧ := 2 * p2 * A + p1
  have hW2 : W ^ 2 = D := by
    dsimp only [W, D, p2, p1]
    linear_combination 4 * (2 * X ^ 4 - 4 * X ^ 3 + 2 * X ^ 2) * A_quadratic
  have hDW2 := congrArg (PowerSeries.derivative ℚ) hW2
  have hLHS_d : PowerSeries.derivative ℚ (W ^ 2) = 2 * W * PowerSeries.derivative ℚ W := by
    rw [PowerSeries.derivative_pow]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [hLHS_d] at hDW2
  have hODE_raw : 2 * D * PowerSeries.derivative ℚ W - PowerSeries.derivative ℚ D * W = 0 := by
    have hmul := congrArg (· * W) hDW2
    linear_combination hmul - 2 * PowerSeries.derivative ℚ W * hW2
  have hdW : PowerSeries.derivative ℚ W =
      (16 * X ^ 3 - 24 * X ^ 2 + 8 * X) * A +
        (4 * X ^ 4 - 8 * X ^ 3 + 4 * X ^ 2) * PowerSeries.derivative ℚ A +
        (3 * X ^ 2 - 4 * X + 2) := by
    dsimp only [W, p2, p1]
    simp only [map_add, map_sub, Derivation.leibniz, PowerSeries.derivative_pow,
      PowerSeries.derivative_X, PowerSeries.derivative_one, deriv_two, deriv_four, smul_eq_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hdD : PowerSeries.derivative ℚ D =
      2 * (X - 1) * (X ^ 4 + 6 * X ^ 3 - 5 * X ^ 2 - 2 * X + 1) +
        (X - 1) ^ 2 * (4 * X ^ 3 + 18 * X ^ 2 - 10 * X - 2) := by
    dsimp only [D]
    simp only [map_add, map_sub, Derivation.leibniz, PowerSeries.derivative_pow,
      PowerSeries.derivative_X, PowerSeries.derivative_one, deriv_two, deriv_five, deriv_six,
      smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hfac :
      8 * X * (X - 1) ^ 3 *
        ((X ^ 6 + 5 * X ^ 5 - 11 * X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X) *
            PowerSeries.derivative ℚ A +
          (X ^ 5 + 9 * X ^ 4 - 13 * X ^ 3 + 6 * X - 2) * A +
          (X ^ 3 - X ^ 2 - 3 * X + 2)) = 0 := by
    rw [hdW, hdD] at hODE_raw
    dsimp only [W, D, p2, p1] at hODE_raw
    linear_combination hODE_raw
  have h8ne : (8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have hXne : (X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 1) h
    norm_num at this
  have hX1ne : ((X : ℚ⟦X⟧) - 1) ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 0) h
    norm_num at this
  have hpre_ne : (8 : ℚ⟦X⟧) * X * (X - 1) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h8ne hXne) (pow_ne_zero 3 hX1ne)
  exact (mul_eq_zero.mp hfac).resolve_left hpre_ne

theorem main_recurrence : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 2) * a n - 3 * ((n : ℤ) + 1) * a (n - 1) + 3 * (2 - (n : ℤ)) * a (n - 2)
      + (11 * (n : ℤ) - 20) * a (n - 3) + (11 - 5 * (n : ℤ)) * a (n - 4)
      + (4 - (n : ℤ)) * a (n - 5) = 0 := by
  intro n hn
  have hsplit :
      (X ^ 6 + 5 * X ^ 5 - 11 * X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X) * PowerSeries.derivative ℚ A +
        (X ^ 5 + 9 * X ^ 4 - 13 * X ^ 3 + 6 * X - 2) * A +
        (X ^ 3 - X ^ 2 - 3 * X + 2) =
      X ^ 6 * PowerSeries.derivative ℚ A +
        C (5 : ℚ) * (X ^ 5 * PowerSeries.derivative ℚ A) -
        C (11 : ℚ) * (X ^ 4 * PowerSeries.derivative ℚ A) +
        C (3 : ℚ) * (X ^ 3 * PowerSeries.derivative ℚ A) +
        C (3 : ℚ) * (X ^ 2 * PowerSeries.derivative ℚ A) -
        X ^ 1 * PowerSeries.derivative ℚ A +
        X ^ 5 * A +
        C (9 : ℚ) * (X ^ 4 * A) -
        C (13 : ℚ) * (X ^ 3 * A) +
        C (6 : ℚ) * (X ^ 1 * A) -
        C (2 : ℚ) * A +
        X ^ 3 - X ^ 2 - C (3 : ℚ) * X ^ 1 + C (2 : ℚ) := by
    simp only [map_ofNat]
    ring
  have hc := congrArg (PowerSeries.coeff n) (hsplit.symm.trans A_ode)
  simp only [map_add, map_sub, map_zero, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_derivative, PowerSeries.coeff_X_pow, PowerSeries.coeff_C] at hc
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h5 : 5 ≤ n := hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hn3 : n ≠ 3 := by omega
  simp only [h1, h2, h3, h4, h5, hn0, hn1, hn2, hn3, ↓reduceIte, A, PowerSeries.coeff_mk] at hc
  have hq :
      ((n : ℚ) + 2) * (a n : ℚ) - 3 * ((n : ℚ) + 1) * (a (n - 1) : ℚ) +
        3 * (2 - (n : ℚ)) * (a (n - 2) : ℚ) +
        (11 * (n : ℚ) - 20) * (a (n - 3) : ℚ) +
        (11 - 5 * (n : ℚ)) * (a (n - 4) : ℚ) +
        (4 - (n : ℚ)) * (a (n - 5) : ℚ) = 0 := by
    rcases eq_or_lt_of_le hn with rfl | hn6
    · simp only [show ¬(6 ≤ 5) by omega, ↓reduceIte] at hc
      norm_num at hc ⊢
      linarith
    · have h6 : 6 ≤ n := hn6
      simp only [h6, ↓reduceIte] at hc
      rw [show n - 6 + 1 = n - 5 by omega,
        show n - 5 + 1 = n - 4 by omega,
        show n - 4 + 1 = n - 3 by omega,
        show n - 3 + 1 = n - 2 by omega,
        show n - 2 + 1 = n - 1 by omega,
        show n - 1 + 1 = n by omega,
        Nat.cast_sub (by omega : 6 ≤ n),
        Nat.cast_sub (by omega : 5 ≤ n),
        Nat.cast_sub (by omega : 4 ≤ n),
        Nat.cast_sub (by omega : 3 ≤ n),
        Nat.cast_sub (by omega : 2 ≤ n),
        Nat.cast_sub (by omega : 1 ≤ n)] at hc
      push_cast at hc
      linarith
  exact_mod_cast hq

end ProofA185089

theorem OMA.solution : type_of% @OMA.S_oeis_a185089.main :=
  ProofA185089.main_recurrence
