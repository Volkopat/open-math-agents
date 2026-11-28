import OMAStatements.S_oeis_a300732
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

namespace OMA.P_oeis_a300732

open OMA.S_oeis_a300732

private noncomputable def dPS (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.derivative ℤ f

private lemma coeff_dPS (m : ℕ) (f : PowerSeries ℤ) :
    PowerSeries.coeff m (dPS f) = PowerSeries.coeff (m + 1) f * ((m + 1 : ℕ) : ℤ) := by
  simpa [dPS] using PowerSeries.coeff_derivative f m

private lemma dPS_pow (f : PowerSeries ℤ) (e : ℕ) :
    dPS (f ^ e) = (e : PowerSeries ℤ) * f ^ (e - 1) * dPS f := by
  induction e with
  | zero => simp [dPS]
  | succ e ih =>
    rw [pow_succ, show dPS (f ^ e * f) = dPS (f ^ e) * f + f ^ e * dPS f from by
      simp [dPS, Derivation.leibniz, smul_eq_mul, mul_comm, add_comm]]
    cases e with
    | zero => simp [dPS]
    | succ e' =>
      rw [ih]
      simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ]
      ring

private lemma dvd_mul_coeff_pow (B : PowerSeries ℤ) {e m : ℕ} (_he : 1 ≤ e) (hm : 1 ≤ m) :
    (e : ℤ) ∣ (m : ℤ) * PowerSeries.coeff m (B ^ e) := by
  have hd := congrArg (PowerSeries.coeff (m - 1)) (dPS_pow B e)
  rw [coeff_dPS, show m - 1 + 1 = m by omega] at hd
  have heC : (e : PowerSeries ℤ) = PowerSeries.C (e : ℤ) := by simp
  rw [heC, mul_assoc, PowerSeries.coeff_C_mul] at hd
  refine ⟨PowerSeries.coeff (m - 1) (B ^ (e - 1) * dPS B), ?_⟩
  linarith

private lemma coeff_pow_eq_zero_of_lt {g : PowerSeries ℤ}
    (hg0 : PowerSeries.constantCoeff g = 0) {d n : ℕ} (h : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  have hgX : g = PowerSeries.X * PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) g) := by
    ext k
    rw [← pow_one PowerSeries.X, PowerSeries.coeff_X_pow_mul']
    cases k with
    | zero => rw [if_neg (by omega), PowerSeries.coeff_zero_eq_constantCoeff, hg0]
    | succ p => rw [if_pos (by omega), Nat.add_sub_cancel, PowerSeries.coeff_mk]
  rw [hgX, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private lemma coeff_subst_eq_sum {g : PowerSeries ℤ}
    (hg0 : PowerSeries.constantCoeff g = 0) (F : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst g F) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F * PowerSeries.coeff n (g ^ d) := by
  have hg : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg0
  rw [PowerSeries.coeff_subst' hg]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hge
  exact hd (by rw [coeff_pow_eq_zero_of_lt hg0 (by omega), mul_zero])

private lemma dvd_mul_of_sub {n k : ℕ} {a C : ℤ} (hkn : k < n)
    (ha : (k : ℤ) ∣ a)
    (hC : (n : ℤ) ∣ ((n - k : ℕ) : ℤ) * C) :
    (n : ℤ) ∣ a * C := by
  set m := n - k
  have hm_pos : 0 < m := by omega
  set d := Nat.gcd n m
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right n hm_pos
  have hdn : d ∣ n := Nat.gcd_dvd_left n m
  have hdm : d ∣ m := Nat.gcd_dvd_right n m
  set n' := n / d
  set m' := m / d
  have hn_eq : n = d * n' := (Nat.mul_div_cancel' hdn).symm
  have hm_eq : m = d * m' := (Nat.mul_div_cancel' hdm).symm
  have hcop : Nat.Coprime n' m' := Nat.coprime_div_gcd_div_gcd hd_pos
  have hd_dvd_k : d ∣ k := by
    have hk_eq : k = n - m := by omega
    rw [hk_eq]
    exact Nat.dvd_sub hdn hdm
  have hd_dvd_a : (d : ℤ) ∣ a := dvd_trans (Int.ofNat_dvd.mpr hd_dvd_k) ha
  have hn'_dvd_m'C : (n' : ℤ) ∣ (m' : ℤ) * C := by
    obtain ⟨q, hq⟩ := hC
    rw [hn_eq, hm_eq] at hq
    push_cast at hq
    have hd_ne : (d : ℤ) ≠ 0 := by positivity
    have hmul : (d : ℤ) * ((m' : ℤ) * C) = (d : ℤ) * ((n' : ℤ) * q) := by linarith
    exact ⟨q, mul_left_cancel₀ hd_ne hmul⟩
  have hcop_int : IsCoprime (n' : ℤ) (m' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hn'_dvd_C : (n' : ℤ) ∣ C := hcop_int.dvd_of_dvd_mul_left hn'_dvd_m'C
  rw [hn_eq]
  push_cast
  exact mul_dvd_mul hd_dvd_a hn'_dvd_C

theorem solution : type_of% @OMA.S_oeis_a300732.main := by
  intro A hA0 hA1 hEq
  let B : PowerSeries ℤ := Ring.inverse A
  have hA_unit : IsUnit A := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hA0]; exact isUnit_one)
  have hAB : A * B = 1 := Ring.mul_inverse_cancel A hA_unit
  have hB0 : PowerSeries.constantCoeff B = 1 := by
    have h := congrArg PowerSeries.constantCoeff hAB
    rw [map_mul, hA0, one_mul, map_one] at h; exact h
  intro n hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | r
    · omega
    · simp [hA1]
    · set n := r + 2
      have hn1 : 1 < n := by omega
      have h0 := hEq n hn1
      set g : PowerSeries ℤ := PowerSeries.X * B ^ (2 * n)
      have hg0 : PowerSeries.constantCoeff g = 0 := by
        dsimp only [g]; rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]
      rw [coeff_subst_eq_sum hg0] at h0
      rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h0
      have hterm0 : PowerSeries.coeff 0 A * PowerSeries.coeff n (g ^ 0) = 0 := by
        rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega), mul_zero]
      have hterm_n : PowerSeries.coeff n (g ^ n) = 1 := by
        dsimp only [g]
        rw [mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
            PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hB0, one_pow]
      rw [hterm0, add_zero, hterm_n, mul_one] at h0
      have ha_eq : PowerSeries.coeff n A =
          - ∑ j ∈ Finset.range (n - 1), PowerSeries.coeff (j + 1) A * PowerSeries.coeff n (g ^ (j + 1)) := by
        have hsub : n - 1 = r + 1 := by omega
        rw [hsub]; linarith
      rw [ha_eq, dvd_neg]
      refine Finset.dvd_sum fun j hj => ?_
      rw [Finset.mem_range] at hj
      set k := j + 1
      have hkn : k < n := by omega
      have hgk : PowerSeries.coeff n (g ^ k) = PowerSeries.coeff (n - k) (B ^ (k * (2 * n))) := by
        dsimp only [g]
        rw [mul_pow, ← pow_mul, mul_comm (2 * n) k, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
      rw [hgk]
      have hdvd_e : ((n : ℕ) : ℤ) ∣ ((k * (2 * n) : ℕ) : ℤ) := by
        exact_mod_cast (show n ∣ k * (2 * n) from ⟨k * (2), by ring⟩)
      have hC_dvd : ((n : ℕ) : ℤ) ∣ ((n - k : ℕ) : ℤ) * PowerSeries.coeff (n - k) (B ^ (k * (2 * n))) :=
        dvd_trans hdvd_e (dvd_mul_coeff_pow B (Nat.one_le_iff_ne_zero.mpr (by positivity)) (by omega))
      exact dvd_mul_of_sub hkn (ih k hkn (by omega)) hC_dvd

end OMA.P_oeis_a300732

theorem OMA.solution : type_of% @OMA.S_oeis_a300732.main := OMA.P_oeis_a300732.solution
