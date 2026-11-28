import OMAStatements.S_oeis_a259269
import Mathlib

namespace OMA.ProofA259269

open PowerSeries Finset

private lemma coeff_X_pow_mul_lt {R : Type*} [Semiring R] (p : R⟦X⟧) {n d : ℕ} (h : n < d) :
    coeff n (X ^ d * p) = 0 := by
  rw [coeff_X_pow_mul']
  simp [not_le.mpr h]

private lemma coeff_C_mul_X_pow {R : Type*} [Semiring R] (c : R) (m d : ℕ) :
    coeff d (C c * X ^ m) = if m = d then c else 0 := by
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hmd : m = d
  · subst hmd; simp
  · simp [hmd, Ne.symm hmd]

private lemma X_pow_dvd_sub_trunc {R : Type*} [CommRing R] (f : R⟦X⟧) (n : ℕ) :
    X ^ n ∣ (f - ∑ m ∈ range n, C (coeff m f) * X ^ m) := by
  rw [X_pow_dvd_iff]
  intro d hd
  rw [map_sub, map_sum]
  have hsum : ∑ m ∈ range n, coeff d (C (coeff m f) * X ^ m) = coeff d f := by
    have : ∀ m ∈ range n, coeff d (C (coeff m f) * X ^ m) = if m = d then coeff m f else 0 :=
      fun m _ => coeff_C_mul_X_pow (coeff m f) m d
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp [hd]
  rw [hsum, sub_self]

private lemma coeff_zero_of_unit_deriv {U : ℚ⟦X⟧} (hU : IsUnit U) {r : ℕ} (hr : 1 ≤ r) :
    coeff r ((↑hU.unit⁻¹ : ℚ⟦X⟧) ^ (r + 1) * (U + X * d⁄dX ℚ U)) = 0 := by
  set Uinv : ℚ⟦X⟧ := ↑hU.unit⁻¹
  have hUU : Uinv * U = 1 := by
    change (↑hU.unit⁻¹ : ℚ⟦X⟧) * (↑hU.unit : ℚ⟦X⟧) = 1
    exact_mod_cast Units.inv_mul hU.unit
  set V : ℚ⟦X⟧ := Uinv ^ r
  have hV' : d⁄dX ℚ V = -((r : ℚ) • (Uinv ^ (r + 1) * d⁄dX ℚ U)) := by
    have h1 : d⁄dX ℚ V = (r : ℚ⟦X⟧) * Uinv ^ (r - 1) * d⁄dX ℚ Uinv := derivative_pow Uinv r
    have h2 : d⁄dX ℚ Uinv = -(Uinv ^ 2) * d⁄dX ℚ U := derivative_inv hU.unit
    rw [h1, h2]
    have hpow : Uinv ^ (r - 1) * Uinv ^ 2 = Uinv ^ (r + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hsmul : (r : ℚ) • (Uinv ^ (r + 1) * d⁄dX ℚ U) =
        (r : ℚ⟦X⟧) * (Uinv ^ (r + 1) * d⁄dX ℚ U) := by
      rw [Algebra.smul_def]
      change C (r : ℚ) * _ = _
      simp
    rw [hsmul, ← hpow]
    ring
  have hid : Uinv ^ (r + 1) * (U + X * d⁄dX ℚ U) = V - ((r : ℚ)⁻¹) • (X * d⁄dX ℚ V) := by
    have h1 : Uinv ^ (r + 1) * U = V := by
      rw [pow_succ, mul_assoc, hUU, mul_one]
    have h2 : ((r : ℚ)⁻¹) • (X * d⁄dX ℚ V) = -(Uinv ^ (r + 1) * (X * d⁄dX ℚ U)) := by
      rw [hV', mul_neg, mul_smul_comm, smul_neg, smul_smul]
      have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
      rw [inv_mul_cancel₀ hr0, one_smul]
      congr 1; ring
    rw [mul_add, h1, h2, sub_neg_eq_add]
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  rw [hid, map_sub, map_smul, coeff_succ_X_mul, coeff_derivative, smul_eq_mul]
  have hr0 : ((r' + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  simp only [Nat.succ_eq_add_one]
  field_simp [hr0]
  push_cast
  ring

private lemma lagrange_inv_coeff {G F U : ℚ⟦X⟧} (hU : IsUnit U)
    (hF : F = X * U) (hGF : PowerSeries.subst F G = X) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℚ) * coeff n G = coeff (n - 1) ((↑hU.unit⁻¹ : ℚ⟦X⟧) ^ n) := by
  set Uinv : ℚ⟦X⟧ := ↑hU.unit⁻¹
  have hUU : Uinv * U = 1 := by
    change (↑hU.unit⁻¹ : ℚ⟦X⟧) * (↑hU.unit : ℚ⟦X⟧) = 1
    exact_mod_cast Units.inv_mul hU.unit
  have hF0 : constantCoeff F = 0 := by rw [hF, map_mul, constantCoeff_X, zero_mul]
  have hFs : HasSubst F := HasSubst.of_constantCoeff_zero' hF0
  have hderiv : PowerSeries.subst F (d⁄dX ℚ G) * d⁄dX ℚ F = 1 := by
    have h := congr_arg (d⁄dX ℚ) hGF
    rw [derivative_subst hFs, derivative_X] at h
    exact h
  have hF' : d⁄dX ℚ F = U + X * d⁄dX ℚ U := by
    rw [hF, Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul, mul_one, add_comm]
  set G' : ℚ⟦X⟧ := d⁄dX ℚ G
  obtain ⟨R, hR⟩ := X_pow_dvd_sub_trunc G' n
  have hG' : G' = (∑ m ∈ range n, C (coeff m G') * X ^ m) + X ^ n * R := by
    rw [← hR]; ring
  have hG'F : PowerSeries.subst F G' =
      (∑ m ∈ range n, C (coeff m G') * F ^ m) + F ^ n * PowerSeries.subst F R := by
    conv_lhs => rw [hG']
    rw [← coe_substAlgHom hFs, map_add, map_sum, map_mul, map_pow, substAlgHom_X, coe_substAlgHom]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← coe_substAlgHom hFs, map_mul, map_pow, substAlgHom_X, coe_substAlgHom, subst_C]
    rfl
  have hFUinv : F ^ n * Uinv ^ n = X ^ n := by
    rw [hF, mul_pow, mul_assoc, ← mul_pow, mul_comm U Uinv, hUU, one_pow, mul_one]
  have hmain : Uinv ^ n =
      (∑ m ∈ range n, C (coeff m G') * (X ^ m * Uinv ^ (n - m) * d⁄dX ℚ F)) +
      X ^ n * (PowerSeries.subst F R * d⁄dX ℚ F) := by
    have hmul : Uinv ^ n = PowerSeries.subst F G' * d⁄dX ℚ F * Uinv ^ n := by
      rw [hderiv, one_mul]
    rw [hmul, hG'F, add_mul, add_mul]
    congr 1
    · rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmn : m ≤ n := le_of_lt (Finset.mem_range.mp hm)
      have hFm : F ^ m * Uinv ^ n = X ^ m * Uinv ^ (n - m) := by
        rw [hF, mul_pow, mul_assoc]
        congr 1
        have hsplit : Uinv ^ n = Uinv ^ m * Uinv ^ (n - m) := by
          rw [← pow_add, Nat.add_sub_of_le hmn]
        rw [hsplit, ← mul_assoc, ← mul_pow, mul_comm U Uinv, hUU, one_pow, one_mul]
      calc
        C (coeff m G') * F ^ m * d⁄dX ℚ F * Uinv ^ n
            = C (coeff m G') * ((F ^ m * Uinv ^ n) * d⁄dX ℚ F) := by ring
        _ = C (coeff m G') * (X ^ m * Uinv ^ (n - m) * d⁄dX ℚ F) := by rw [hFm]
    · calc
        F ^ n * PowerSeries.subst F R * d⁄dX ℚ F * Uinv ^ n
            = (F ^ n * Uinv ^ n) * (PowerSeries.subst F R * d⁄dX ℚ F) := by ring
        _ = X ^ n * (PowerSeries.subst F R * d⁄dX ℚ F) := by rw [hFUinv]
  have hcoeff := congr_arg (coeff (n - 1)) hmain
  rw [map_add, coeff_X_pow_mul_lt _ (by omega : n - 1 < n), add_zero, map_sum] at hcoeff
  have hterm : ∀ m ∈ range n,
      coeff (n - 1) (C (coeff m G') * (X ^ m * Uinv ^ (n - m) * d⁄dX ℚ F)) =
      if m = n - 1 then (n : ℚ) * coeff n G else 0 := by
    intro m hm
    have hmlt : m < n := Finset.mem_range.mp hm
    rw [coeff_C_mul]
    by_cases hmeq : m = n - 1
    · subst hmeq
      simp only [↓reduceIte]
      have h1 : n - (n - 1) = 1 := by omega
      rw [h1, pow_one, mul_assoc, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, hF',
        mul_add, hUU, ← mul_assoc, coeff_zero_eq_constantCoeff, map_add, map_one,
        map_mul, map_mul, constantCoeff_X, mul_zero, zero_mul, add_zero, mul_one]
      have hsucc : n - 1 + 1 = n := by omega
      have hcast : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by exact_mod_cast hsucc
      change coeff (n - 1) (d⁄dX ℚ G) = (n : ℚ) * coeff n G
      rw [coeff_derivative, hsucc, hcast, mul_comm]
    · simp only [hmeq, ↓reduceIte]
      have hle : m ≤ n - 1 := by omega
      set r := n - 1 - m
      have hr : 1 ≤ r := by omega
      have hnm : n - m = r + 1 := by omega
      rw [hnm, mul_assoc, coeff_X_pow_mul', if_pos hle, hF',
        coeff_zero_of_unit_deriv hU hr, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))] at hcoeff
  exact hcoeff.symm

private lemma one_sub_mul_binom_sum (Ψ : ℚ⟦X⟧) (n M : ℕ) (hn : 1 ≤ n) :
    (1 - Ψ) * (∑ k ∈ range (M + 1), C (Nat.choose (n + k) k : ℚ) * Ψ ^ k) =
    (∑ k ∈ range (M + 1), C (Nat.choose (n - 1 + k) k : ℚ) * Ψ ^ k) -
      C (Nat.choose (n + M) M : ℚ) * Ψ ^ (M + 1) := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    rw [Finset.sum_range_succ (n := M + 1), mul_add, ih, Finset.sum_range_succ (n := M + 1)]
    have hch : Nat.choose (n + (M + 1)) (M + 1) =
        Nat.choose (n - 1 + (M + 1)) (M + 1) + Nat.choose (n + M) M := by
      have h1 : n + (M + 1) = (n + M) + 1 := by omega
      have h2 : n - 1 + (M + 1) = n + M := by omega
      rw [h1, h2, Nat.choose_succ_succ, add_comm]
    have hchQ : (Nat.choose (n + (M + 1)) (M + 1) : ℚ) =
        (Nat.choose (n - 1 + (M + 1)) (M + 1) : ℚ) + (Nat.choose (n + M) M : ℚ) := by
      exact_mod_cast hch
    have hC : C (Nat.choose (n + (M + 1)) (M + 1) : ℚ) =
        C (Nat.choose (n - 1 + (M + 1)) (M + 1) : ℚ) + C (Nat.choose (n + M) M : ℚ) := by
      rw [hchQ, map_add]
    have hpow : Ψ ^ (M + 1 + 1) = Ψ * Ψ ^ (M + 1) := by rw [pow_succ']
    rw [hpow, sub_mul, one_mul, hC]
    ring

private lemma pow_dvd_one_sub_mul_binom_sum (Ψ : ℚ⟦X⟧) (M : ℕ) :
    ∀ n : ℕ, 1 ≤ n →
      Ψ ^ (M + 1) ∣ (1 - (1 - Ψ) ^ n * ∑ k ∈ range (M + 1), C (Nat.choose (n - 1 + k) k : ℚ) * Ψ ^ k) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Nat.reduceSub, zero_add, Nat.choose_self, Nat.cast_one, map_one, one_mul, pow_one]
      have hgeom : (1 - Ψ) * ∑ k ∈ range (M + 1), Ψ ^ k = 1 - Ψ ^ (M + 1) := by
        have h := geom_sum_mul_neg Ψ (M + 1)
        simpa [mul_comm] using h
      rw [hgeom, sub_sub_cancel]
    · have hn1 : 1 ≤ n := by omega
      obtain ⟨Q, hQ⟩ := ih hn1
      have hstep := one_sub_mul_binom_sum Ψ n M hn1
      have hcalc : 1 - (1 - Ψ) ^ (n + 1) * ∑ k ∈ range (M + 1), C (Nat.choose (n + 1 - 1 + k) k : ℚ) * Ψ ^ k =
          (1 - (1 - Ψ) ^ n * ∑ k ∈ range (M + 1), C (Nat.choose (n - 1 + k) k : ℚ) * Ψ ^ k) +
          (1 - Ψ) ^ n * C (Nat.choose (n + M) M : ℚ) * Ψ ^ (M + 1) := by
        have hsub : n + 1 - 1 = n := by omega
        rw [hsub, pow_succ, mul_assoc, hstep]
        ring
      rw [hcalc, hQ]
      refine ⟨Q + (1 - Ψ) ^ n * C (Nat.choose (n + M) M : ℚ), ?_⟩
      ring

private lemma inv_one_sub_pow_coeff {Ψ : ℚ⟦X⟧} (hΨ : constantCoeff Ψ = 0)
    (hU : IsUnit (1 - Ψ)) {n : ℕ} (hn : 1 ≤ n) :
    coeff (n - 1) ((↑hU.unit⁻¹ : ℚ⟦X⟧) ^ n) =
      ∑ k ∈ range n, (Nat.choose (n - 1 + k) k : ℚ) * coeff (n - 1) (Ψ ^ k) := by
  set Uinv : ℚ⟦X⟧ := ↑hU.unit⁻¹
  have hUU : Uinv * (1 - Ψ) = 1 := by
    change (↑hU.unit⁻¹ : ℚ⟦X⟧) * (↑hU.unit : ℚ⟦X⟧) = 1
    exact_mod_cast Units.inv_mul hU.unit
  have hXΨ : X ∣ Ψ := X_dvd_iff.mpr hΨ
  obtain ⟨P, hP⟩ := hXΨ
  obtain ⟨Q, hQ⟩ := pow_dvd_one_sub_mul_binom_sum Ψ (n - 1) n hn
  have hM : n - 1 + 1 = n := by omega
  rw [hM] at hQ
  set S : ℚ⟦X⟧ := ∑ k ∈ range n, C (Nat.choose (n - 1 + k) k : ℚ) * Ψ ^ k
  have hdiff : Uinv ^ n - S = X ^ n * (P ^ n * Q * Uinv ^ n) := by
    have h1 : (1 - (1 - Ψ) ^ n * S) * Uinv ^ n = Uinv ^ n - S := by
      rw [sub_mul, one_mul, mul_assoc, mul_comm S (Uinv ^ n), ← mul_assoc, ← mul_pow,
        mul_comm (1 - Ψ) Uinv, hUU, one_pow, one_mul]
    rw [← h1, hQ, hP, mul_pow]
    ring
  have hce : coeff (n - 1) (Uinv ^ n - S) = 0 := by
    rw [hdiff, coeff_X_pow_mul_lt _ (by omega : n - 1 < n)]
  have hEq : coeff (n - 1) (Uinv ^ n) = coeff (n - 1) S := sub_eq_zero.mp (by rwa [← map_sub])
  rw [hEq, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul]

private lemma choose_mul_identity {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k) :
    k * (k - 1) * Nat.choose (N + k - 2) k = N * (N - 1) * Nat.choose (N + k - 2) (k - 2) := by
  have hk_fac : k * (k - 1) * Nat.factorial (k - 2) = Nat.factorial k := by
    have hk2 : k = (k - 2) + 2 := by omega
    conv_rhs => rw [hk2]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    have h1 : k - 2 + 1 = k - 1 := by omega
    have h2 : k - 1 + 1 = k := by omega
    rw [h1, h2]
    ring
  have hN_fac : N * (N - 1) * Nat.factorial (N - 2) = Nat.factorial N := by
    have hN2 : N = (N - 2) + 2 := by omega
    conv_rhs => rw [hN2]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    have h1 : N - 2 + 1 = N - 1 := by omega
    have h2 : N - 1 + 1 = N := by omega
    rw [h1, h2]
    ring
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ N + k - 2 by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show k - 2 ≤ N + k - 2 by omega)
  have hs1 : N + k - 2 - k = N - 2 := by omega
  have hs2 : N + k - 2 - (k - 2) = N := by omega
  rw [hs1] at h1
  rw [hs2] at h2
  have hpos : 0 < Nat.factorial (k - 2) * Nat.factorial (N - 2) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    k * (k - 1) * Nat.choose (N + k - 2) k * (Nat.factorial (k - 2) * Nat.factorial (N - 2))
        = Nat.choose (N + k - 2) k * (k * (k - 1) * Nat.factorial (k - 2)) * Nat.factorial (N - 2) := by ring
    _ = Nat.choose (N + k - 2) k * Nat.factorial k * Nat.factorial (N - 2) := by rw [hk_fac]
    _ = Nat.factorial (N + k - 2) := h1
    _ = Nat.choose (N + k - 2) (k - 2) * Nat.factorial (k - 2) * Nat.factorial N := h2.symm
    _ = Nat.choose (N + k - 2) (k - 2) * Nat.factorial (k - 2) * (N * (N - 1) * Nat.factorial (N - 2)) := by rw [hN_fac]
    _ = N * (N - 1) * Nat.choose (N + k - 2) (k - 2) * (Nat.factorial (k - 2) * Nat.factorial (N - 2)) := by ring

private lemma add_two_le_three_pow {e : ℕ} (he : 1 ≤ e) : e + 2 ≤ 3 ^ e := by
  induction e with
  | zero => omega
  | succ e ih =>
    by_cases h0 : e = 0
    · subst h0; norm_num
    · have := ih (by omega)
      calc
        e + 1 + 2 ≤ 3 * (e + 2) := by omega
        _ ≤ 3 * 3 ^ e := by omega
        _ = 3 ^ (e + 1) := by rw [pow_succ']

private lemma split_three_part_spec {k : ℕ} (hk : 2 ≤ k) :
    let e := (k * (k - 1)).factorization 3
    let m := k * (k - 1) / 3 ^ e
    k * (k - 1) = 3 ^ e * m ∧ ¬ 3 ∣ m ∧ e + 2 ≤ k := by
  dsimp only
  set t := k * (k - 1)
  have ht0 : t ≠ 0 := by
    have : 0 < k - 1 := by omega
    positivity
  set e := t.factorization 3
  have hdvd : 3 ^ e ∣ t := Nat.ordProj_dvd t 3
  set m := t / 3 ^ e
  have hmul : 3 ^ e * m = t := Nat.mul_div_cancel' hdvd
  have hndvd : ¬ 3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three ht0
  have hle : e + 2 ≤ k := by
    by_cases he0 : e = 0
    · omega
    · have he1 : 1 ≤ e := by omega
      have hdiv : 3 ^ e ∣ k ∨ 3 ^ e ∣ (k - 1) := by
        have h3p : Nat.Prime 3 := Nat.prime_three
        by_cases h3k : 3 ∣ k
        · left
          have h3nk1 : ¬ 3 ∣ (k - 1) := fun h => by
            have := Nat.dvd_sub h3k h
            have h1 : k - (k - 1) = 1 := by omega
            rw [h1] at this
            omega
          have hcop2 : Nat.Coprime (3 ^ e) (k - 1) :=
            (h3p.coprime_iff_not_dvd.mpr h3nk1).pow_left e
          exact hcop2.dvd_of_dvd_mul_right hdvd
        · right
          have hcop2 : Nat.Coprime (3 ^ e) k :=
            (h3p.coprime_iff_not_dvd.mpr h3k).pow_left e
          exact hcop2.dvd_of_dvd_mul_left hdvd
      have h3lek : 3 ^ e ≤ k := by
        rcases hdiv with h | h
        · exact Nat.le_of_dvd (by omega) h
        · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
      exact le_trans (add_two_le_three_pow he1) h3lek
  exact ⟨hmul.symm, hndvd, hle⟩

private lemma coeff_pow_three_zmod3 (f : (ZMod 3)⟦X⟧) (N : ℕ) :
    coeff N (f ^ 3) = if 3 ∣ N then coeff (N / 3) f else 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP ((ZMod 3)⟦X⟧) 3 := ⟨fun n => by
    constructor
    · intro h
      have hc := congr_arg constantCoeff h
      simp only [map_natCast, map_zero] at hc
      exact (ZMod.natCast_eq_zero_iff n 3).mp hc
    · intro h
      have hz : (n : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff n 3).mpr h
      rw [show (n : (ZMod 3)⟦X⟧) = C (n : ZMod 3) by simp, hz, map_zero]⟩
  set P : (ZMod 3)⟦X⟧ := ∑ m ∈ range (N + 1), C (coeff m f) * X ^ m
  obtain ⟨R, hR⟩ := X_pow_dvd_sub_trunc f (N + 1)
  have hf : f = P + X ^ (N + 1) * R := by rw [← hR]; ring
  have hf3 : f ^ 3 = P ^ 3 + (X ^ (N + 1) * R) ^ 3 := by
    rw [hf, add_pow_char]
  have htail : coeff N ((X ^ (N + 1) * R) ^ 3) = 0 := by
    rw [mul_pow, ← pow_mul]
    exact coeff_X_pow_mul_lt _ (by omega : N < (N + 1) * 3)
  have hP3 : P ^ 3 = ∑ m ∈ range (N + 1), C (coeff m f) * X ^ (3 * m) := by
    have hsum : P ^ 3 = ∑ m ∈ range (N + 1), (C (coeff m f) * X ^ m) ^ 3 := by
      calc
        P ^ 3 = frobenius ((ZMod 3)⟦X⟧) 3 P := rfl
        _ = ∑ m ∈ range (N + 1), frobenius ((ZMod 3)⟦X⟧) 3 (C (coeff m f) * X ^ m) :=
          map_sum (frobenius ((ZMod 3)⟦X⟧) 3) (fun m => C (coeff m f) * X ^ m) (range (N + 1))
        _ = ∑ m ∈ range (N + 1), (C (coeff m f) * X ^ m) ^ 3 := rfl
    rw [hsum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow, ← map_pow, ZMod.pow_card, ← pow_mul, mul_comm m 3]
  rw [hf3, map_add, htail, add_zero, hP3, map_sum]
  have hterm : ∀ m ∈ range (N + 1),
      coeff N (C (coeff m f) * X ^ (3 * m)) = if 3 * m = N then coeff m f else 0 :=
    fun m _ => coeff_C_mul_X_pow (coeff m f) (3 * m) N
  rw [Finset.sum_congr rfl hterm]
  by_cases h3 : 3 ∣ N
  · obtain ⟨q, rfl⟩ := h3
    have hq : q ∈ range (3 * q + 1) := Finset.mem_range.mpr (by omega)
    rw [if_pos ⟨q, rfl⟩, Nat.mul_div_cancel_left q (by norm_num : 0 < 3)]
    rw [Finset.sum_eq_single q]
    · simp
    · intro m _ hmq
      have : 3 * m ≠ 3 * q := by omega
      simp [this]
    · intro h; exact absurd hq h
  · rw [if_neg h3]
    refine Finset.sum_eq_zero fun m _ => ?_
    have : 3 * m ≠ N := fun h => h3 ⟨m, h.symm⟩
    simp [this]

private lemma map_derivative_int_rat (f : ℤ⟦X⟧) :
    (d⁄dX ℤ f).map (Int.castRingHom ℚ) = d⁄dX ℚ (f.map (Int.castRingHom ℚ)) := by
  ext n
  simp [coeff_map, coeff_derivative]

private lemma three_dvd_coeff_sub {A G : ℤ⟦X⟧}
    (hA0 : constantCoeff A = 0)
    (hAG : d⁄dX ℤ A = C (2 : ℤ) * G)
    (hGF : PowerSeries.subst (X - C (3 : ℤ) * A ^ 2 * G) G = X) :
    ∀ N : ℕ, (3 : ℤ) ∣ (coeff N A - coeff N (X ^ 2 + A ^ 3)) := by
  set F : ℤ⟦X⟧ := X - C (3 : ℤ) * A ^ 2 * G
  have hF0 : constantCoeff F = 0 := by simp [F, hA0]
  have hFs : HasSubst F := HasSubst.of_constantCoeff_zero' hF0
  have hconst_subst : ∀ H : ℤ⟦X⟧, constantCoeff (PowerSeries.subst F H) = constantCoeff H := by
    intro H
    rw [← coeff_zero_eq_constantCoeff, coeff_subst' hFs]
    rw [finsum_eq_single _ 0]
    · simp [coeff_zero_eq_constantCoeff]
    · intro d hd
      rw [coeff_zero_eq_constantCoeff, map_pow, hF0, zero_pow hd, smul_zero]
  have hG0 : constantCoeff G = 0 := by
    have h := congr_arg constantCoeff hGF
    rw [hconst_subst G, constantCoeff_X] at h
    exact h
  have hA1 : coeff 1 A = 0 := by
    have h := congr_arg (coeff 0) hAG
    rw [coeff_derivative, coeff_C_mul, coeff_zero_eq_constantCoeff, hG0] at h
    simpa using h
  have hF1 : coeff 1 F = 1 := by
    have hX2A : X ^ 2 ∣ A := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d
      · rw [coeff_zero_eq_constantCoeff]; exact hA0
      · exact hA1
    obtain ⟨A1, hA1_eq⟩ := hX2A
    have hA2G_1 : coeff 1 (C (3 : ℤ) * A ^ 2 * G) = 0 := by
      have heq : C (3 : ℤ) * A ^ 2 * G = X ^ 4 * (C (3 : ℤ) * A1 ^ 2 * G) := by
        rw [hA1_eq]; ring
      rw [heq]
      exact coeff_X_pow_mul_lt _ (by norm_num : 1 < 4)
    rw [show F = X - C (3 : ℤ) * A ^ 2 * G from rfl, map_sub, coeff_X, if_pos rfl, hA2G_1, sub_zero]
  have hG1 : coeff 1 G = 1 := by
    obtain ⟨G1, hG1_eq⟩ := X_dvd_iff.mpr hG0
    obtain ⟨F1, hF1_eq⟩ := X_dvd_iff.mpr hF0
    have hGF_eq : PowerSeries.subst F G = X * (F1 * PowerSeries.subst F G1) := by
      rw [hG1_eq, subst_mul hFs, subst_X hFs, hF1_eq, mul_assoc]
    have h1 := congr_arg (coeff 1) (hGF_eq.symm.trans hGF)
    rw [coeff_X, if_pos rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff, map_mul,
      hconst_subst G1] at h1
    have hF1c : constantCoeff F1 = 1 := by
      rw [← coeff_zero_eq_constantCoeff, ← coeff_succ_X_mul 0 F1, ← hF1_eq]
      exact hF1
    have hG1c : coeff 1 G = constantCoeff G1 := by
      rw [hG1_eq, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]
    rw [hF1c, one_mul] at h1
    rw [hG1c]
    exact h1
  have hA2 : coeff 2 A = 1 := by
    have h := congr_arg (coeff 1) hAG
    rw [coeff_derivative, coeff_C_mul, hG1] at h
    norm_num at h
    omega
  obtain ⟨G1, hG1_eq⟩ := X_dvd_iff.mpr hG0
  set B : ℤ⟦X⟧ := A ^ 2 * G1
  set Ψ : ℤ⟦X⟧ := C (3 : ℤ) * B
  have hF_fac : F = X * (1 - Ψ) := by
    simp only [F, Ψ, B, hG1_eq]
    ring
  have hΨ0 : constantCoeff Ψ = 0 := by simp [Ψ, B, hA0]
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ
  set AQ : ℚ⟦X⟧ := A.map φ
  set GQ : ℚ⟦X⟧ := G.map φ
  set FQ : ℚ⟦X⟧ := F.map φ
  set BQ : ℚ⟦X⟧ := B.map φ
  set ΨQ : ℚ⟦X⟧ := Ψ.map φ
  have hΨQ0 : constantCoeff ΨQ = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    change coeff 0 (Ψ.map φ) = 0
    rw [coeff_map, coeff_zero_eq_constantCoeff, hΨ0, map_zero]
  have hUQ : IsUnit (1 - ΨQ) := by
    rw [isUnit_iff_constantCoeff, map_sub, map_one, hΨQ0, sub_zero]
    exact isUnit_one
  have hFQ : FQ = X * (1 - ΨQ) := by
    simp [FQ, ΨQ, hF_fac]
  have hGFQ : PowerSeries.subst FQ GQ = X := by
    have h : (PowerSeries.map φ) (PowerSeries.subst F G) = (PowerSeries.map φ) X :=
      congr_arg (PowerSeries.map φ) hGF
    have hm : (PowerSeries.map φ) (PowerSeries.subst F G) = PowerSeries.subst FQ GQ :=
      PowerSeries.map_subst hFs G
    rw [hm, map_X] at h
    exact h
  have hAGQ : d⁄dX ℚ AQ = C (2 : ℚ) * GQ := by
    have h := congr_arg (PowerSeries.map φ) hAG
    rw [map_derivative_int_rat, map_mul, map_C] at h
    simpa [AQ, GQ, φ] using h
  have hΨQ_eq : ΨQ = C (3 : ℚ) * BQ := by
    change (C (3 : ℤ) * B).map φ = C (3 : ℚ) * B.map φ
    rw [map_mul, map_C]
    simp [φ]
  intro N
  match N with
  | 0 =>
    simp [coeff_zero_eq_constantCoeff, hA0]
  | 1 =>
    have hX2A : X ^ 2 ∣ A := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d
      · rw [coeff_zero_eq_constantCoeff]; exact hA0
      · exact hA1
    obtain ⟨A1, hA1_eq⟩ := hX2A
    have hA3_1 : coeff 1 (A ^ 3) = 0 := by
      rw [hA1_eq, mul_pow, ← pow_mul]
      exact coeff_X_pow_mul_lt _ (by norm_num : 1 < 2 * 3)
    have hX2_1 : coeff 1 (X ^ 2 : ℤ⟦X⟧) = 0 := by
      rw [show (X ^ 2 : ℤ⟦X⟧) = C 1 * X ^ 2 by simp, coeff_C_mul_X_pow]
      simp
    simp [hA1, hX2_1, hA3_1]
  | 2 =>
    have hX2A : X ^ 2 ∣ A := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d
      · rw [coeff_zero_eq_constantCoeff]; exact hA0
      · exact hA1
    obtain ⟨A1, hA1_eq⟩ := hX2A
    have hA3_2 : coeff 2 (A ^ 3) = 0 := by
      rw [hA1_eq, mul_pow, ← pow_mul]
      exact coeff_X_pow_mul_lt _ (by norm_num : 2 < 2 * 3)
    have hX2_2 : coeff 2 (X ^ 2 : ℤ⟦X⟧) = 1 := by
      rw [show (X ^ 2 : ℤ⟦X⟧) = C 1 * X ^ 2 by simp, coeff_C_mul_X_pow]
      simp
    simp [hA2, hX2_2, hA3_2]
  | N' + 3 =>
    set N := N' + 3
    have hN3 : 3 ≤ N := by omega
    set n := N - 1
    have hn2 : 2 ≤ n := by omega
    have hX2N : coeff N (X ^ 2 : ℤ⟦X⟧) = 0 := by
      rw [show (X ^ 2 : ℤ⟦X⟧) = C 1 * X ^ 2 by simp, coeff_C_mul_X_pow]
      simp [show 2 ≠ N by omega]
    rw [map_add, hX2N, zero_add]
    have hlag := lagrange_inv_coeff hUQ hFQ hGFQ (by omega : 1 ≤ n)
    have hinv := inv_one_sub_pow_coeff hΨQ0 hUQ (by omega : 1 ≤ n)
    rw [hinv] at hlag
    have hrange : ∑ k ∈ range n, (Nat.choose (n - 1 + k) k : ℚ) * coeff (n - 1) (ΨQ ^ k) =
        (n : ℚ) * coeff (n - 1) ΨQ +
        ∑ k ∈ Ico 2 n, (Nat.choose (n - 1 + k) k : ℚ) * coeff (n - 1) (ΨQ ^ k) := by
      have h0 : coeff (n - 1) (ΨQ ^ 0) = 0 := by
        rw [pow_zero, coeff_one]
        simp [show n - 1 ≠ 0 by omega]
      have hsplit1 : range n = insert 0 (insert 1 (Ico 2 n)) := by
        ext k
        simp only [mem_range, mem_insert, mem_Ico]
        omega
      rw [hsplit1, sum_insert (by simp), sum_insert (by simp)]
      rw [h0, mul_zero, zero_add, pow_one]
      have hch1 : Nat.choose (n - 1 + 1) 1 = n := by
        rw [show n - 1 + 1 = n by omega, Nat.choose_one_right]
      rw [hch1]
    rw [hrange] at hlag
    have h2GQ : (2 : ℚ) * coeff n GQ = (N : ℚ) * coeff N AQ := by
      have h := congr_arg (coeff n) hAGQ
      rw [coeff_derivative, coeff_C_mul, show n + 1 = N by omega] at h
      have hcast : ((n : ℚ) + 1) = (N : ℚ) := by exact_mod_cast (show n + 1 = N by omega)
      rw [hcast, mul_comm] at h
      exact h.symm
    have h2ΨQ : (2 : ℚ) * coeff (n - 1) ΨQ = (N : ℚ) * coeff N (AQ ^ 3) := by
      have hA3d : d⁄dX ℤ (A ^ 3) = C (6 : ℤ) * (X * B) := by
        rw [derivative_pow, hAG]
        have hXB : X * B = A ^ 2 * G := by simp only [B, hG1_eq]; ring
        rw [hXB]
        have h3 : ((3 : ℕ) : ℤ⟦X⟧) = C (3 : ℤ) := by simp
        rw [h3]
        have h6 : C (6 : ℤ) = C (3 : ℤ) * C (2 : ℤ) := by rw [← map_mul]; norm_num
        rw [h6]
        ring
      have hZ := congr_arg (coeff n) hA3d
      rw [coeff_derivative, show n + 1 = N by omega, coeff_C_mul] at hZ
      have hZ2 : (N : ℤ) * coeff N (A ^ 3) = 6 * coeff (n - 1) B := by
        have hsucc : n = (n - 1) + 1 := by omega
        have hXB : coeff n (X * B) = coeff (n - 1) B := by
          conv_lhs => rw [hsucc]
          exact coeff_succ_X_mul (n - 1) B
        rw [hXB] at hZ
        have hcast : ((n : ℤ) + 1) = (N : ℤ) := by exact_mod_cast (show n + 1 = N by omega)
        rw [hcast, mul_comm] at hZ
        exact hZ
      have hQ : (((N : ℤ) * coeff N (A ^ 3) : ℤ) : ℚ) = (((6 : ℤ) * coeff (n - 1) B : ℤ) : ℚ) :=
        congr_arg φ hZ2
      have hAQ3 : coeff N (AQ ^ 3) = ((coeff N (A ^ 3) : ℤ) : ℚ) := by
        rw [show AQ ^ 3 = (A ^ 3).map φ by simp [AQ], coeff_map]; rfl
      have hΨBQ : coeff (n - 1) ΨQ = (3 : ℚ) * ((coeff (n - 1) B : ℤ) : ℚ) := by
        rw [hΨQ_eq, coeff_C_mul]
        change (3 : ℚ) * coeff (n - 1) (B.map φ) = _
        rw [coeff_map]; rfl
      rw [hAQ3, hΨBQ]
      push_cast at hQ
      linarith
    have hmul2 : (N : ℚ) * (n : ℚ) * (coeff N AQ - coeff N (AQ ^ 3)) =
        ∑ k ∈ Ico 2 n, (2 : ℚ) * (Nat.choose (N + k - 2) k : ℚ) * (3 : ℚ) ^ k *
          ((coeff (n - 1) (B ^ k) : ℤ) : ℚ) := by
      have hstep : (2 : ℚ) * ((n : ℚ) * coeff n GQ) =
          (2 : ℚ) * ((n : ℚ) * coeff (n - 1) ΨQ +
            ∑ k ∈ Ico 2 n, (Nat.choose (n - 1 + k) k : ℚ) * coeff (n - 1) (ΨQ ^ k)) :=
        congr_arg (fun t => (2 : ℚ) * t) hlag
      have hlhs : (2 : ℚ) * ((n : ℚ) * coeff n GQ) = (N : ℚ) * (n : ℚ) * coeff N AQ := by
        calc
          (2 : ℚ) * ((n : ℚ) * coeff n GQ) = (n : ℚ) * ((2 : ℚ) * coeff n GQ) := by ring
          _ = (n : ℚ) * ((N : ℚ) * coeff N AQ) := by rw [h2GQ]
          _ = (N : ℚ) * (n : ℚ) * coeff N AQ := by ring
      have hrhs1 : (2 : ℚ) * ((n : ℚ) * coeff (n - 1) ΨQ) = (N : ℚ) * (n : ℚ) * coeff N (AQ ^ 3) := by
        calc
          (2 : ℚ) * ((n : ℚ) * coeff (n - 1) ΨQ) = (n : ℚ) * ((2 : ℚ) * coeff (n - 1) ΨQ) := by ring
          _ = (n : ℚ) * ((N : ℚ) * coeff N (AQ ^ 3)) := by rw [h2ΨQ]
          _ = (N : ℚ) * (n : ℚ) * coeff N (AQ ^ 3) := by ring
      rw [hlhs, mul_add, hrhs1, Finset.mul_sum] at hstep
      have hsub : (N : ℚ) * (n : ℚ) * (coeff N AQ - coeff N (AQ ^ 3)) =
          ∑ k ∈ Ico 2 n, (2 : ℚ) * ((Nat.choose (n - 1 + k) k : ℚ) * coeff (n - 1) (ΨQ ^ k)) := by
        linarith
      rw [hsub]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hidx : n - 1 + k = N + k - 2 := by omega
      have hΨk : coeff (n - 1) (ΨQ ^ k) = (3 : ℚ) ^ k * ((coeff (n - 1) (B ^ k) : ℤ) : ℚ) := by
        rw [hΨQ_eq, mul_pow, ← map_pow, coeff_C_mul]
        have hBk : coeff (n - 1) (BQ ^ k) = ((coeff (n - 1) (B ^ k) : ℤ) : ℚ) := by
          rw [show BQ ^ k = (B ^ k).map φ by simp [BQ], coeff_map]; rfl
        rw [hBk]
      rw [hidx, hΨk]
      ring
    have hNn0 : (N : ℚ) * (n : ℚ) ≠ 0 := by
      have : (0 : ℚ) < N := by positivity
      have : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    let eOf : ℕ → ℕ := fun k => (k * (k - 1)).factorization 3
    let mOf : ℕ → ℕ := fun k => k * (k - 1) / 3 ^ eOf k
    have hsplit_all : ∀ k ∈ Ico 2 n,
        k * (k - 1) = 3 ^ eOf k * mOf k ∧ ¬ 3 ∣ mOf k ∧ eOf k + 2 ≤ k :=
      fun k hk => split_three_part_spec (Finset.mem_Ico.mp hk).1
    set D : ℕ := ∏ k ∈ Ico 2 n, mOf k
    have h3nD : ¬ 3 ∣ D := by
      intro h3D
      have hex : ∃ k ∈ Ico 2 n, 3 ∣ mOf k :=
        (Nat.Prime.prime Nat.prime_three).dvd_finsetProd_iff _ |>.mp h3D
      obtain ⟨k, hk, h3m⟩ := hex
      exact (hsplit_all k hk).2.1 h3m
    let termZ : ℕ → ℤ := fun k =>
      ((D / mOf k : ℕ) : ℤ) * 2 * (3 : ℤ) ^ (k - eOf k - 1) *
        (Nat.choose (N + k - 2) (k - 2) : ℤ) * coeff (n - 1) (B ^ k)
    have hQeq : (((D : ℤ) * (coeff N A - coeff N (A ^ 3)) : ℤ) : ℚ) =
        (((3 : ℤ) * ∑ k ∈ Ico 2 n, termZ k : ℤ) : ℚ) := by
      have hAQ_diff : coeff N AQ - coeff N (AQ ^ 3) = ((coeff N A - coeff N (A ^ 3) : ℤ) : ℚ) := by
        have h1 : coeff N AQ = ((coeff N A : ℤ) : ℚ) := by
          change coeff N (A.map φ) = _; rw [coeff_map]; rfl
        have h2 : coeff N (AQ ^ 3) = ((coeff N (A ^ 3) : ℤ) : ℚ) := by
          rw [show AQ ^ 3 = (A ^ 3).map φ by simp [AQ], coeff_map]; rfl
        rw [h1, h2]; push_cast; rfl
      have hdiv : coeff N AQ - coeff N (AQ ^ 3) =
          ∑ k ∈ Ico 2 n, (2 : ℚ) * (Nat.choose (N + k - 2) (k - 2) : ℚ) * (3 : ℚ) ^ k *
            ((coeff (n - 1) (B ^ k) : ℤ) : ℚ) / ((k * (k - 1) : ℕ) : ℚ) := by
        apply mul_left_cancel₀ hNn0
        rw [hmul2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
        have hkk0 : ((k * (k - 1) : ℕ) : ℚ) ≠ 0 := by
          have : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
          exact_mod_cast this.ne'
        have hidQ : ((k * (k - 1) : ℕ) : ℚ) * (Nat.choose (N + k - 2) k : ℚ) =
            (N : ℚ) * (n : ℚ) * (Nat.choose (N + k - 2) (k - 2) : ℚ) := by
          have := choose_mul_identity hN3 hk2
          have hNn : N * (N - 1) = N * n := rfl
          rw [hNn] at this
          exact_mod_cast this
        field_simp [hkk0]
        linear_combination ((coeff (n - 1) (B ^ k) : ℤ) : ℚ) * hidQ
      rw [Int.cast_mul, Int.cast_natCast, ← hAQ_diff, hdiv, Finset.mul_sum,
        Int.cast_mul, Int.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      obtain ⟨hkm, hndvd, hle⟩ := hsplit_all k hk
      have hm_dvd : mOf k ∣ D := Finset.dvd_prod_of_mem mOf hk
      have hm0 : (mOf k : ℚ) ≠ 0 := by
        intro h0
        have : mOf k = 0 := by exact_mod_cast h0
        rw [this] at hndvd
        exact hndvd (dvd_zero 3)
      have hD_eq : (D : ℚ) = ((D / mOf k : ℕ) : ℚ) * (mOf k : ℚ) := by
        exact_mod_cast (Nat.div_mul_cancel hm_dvd).symm
      have hkk_eq : ((k * (k - 1) : ℕ) : ℚ) = (3 : ℚ) ^ eOf k * (mOf k : ℚ) := by
        exact_mod_cast hkm
      have h3pow : (3 : ℚ) ^ k = (3 : ℚ) ^ eOf k * (3 : ℚ) * (3 : ℚ) ^ (k - eOf k - 1) := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      have h3e0 : (3 : ℚ) ^ eOf k ≠ 0 := by positivity
      simp only [termZ, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
      rw [hD_eq, hkk_eq, h3pow]
      field_simp [h3e0, hm0]
    have hZeq : (D : ℤ) * (coeff N A - coeff N (A ^ 3)) = (3 : ℤ) * ∑ k ∈ Ico 2 n, termZ k :=
      Int.cast_injective (α := ℚ) hQeq
    have h3dvd_prod : (3 : ℤ) ∣ (D : ℤ) * (coeff N A - coeff N (A ^ 3)) :=
      ⟨∑ k ∈ Ico 2 n, termZ k, hZeq⟩
    have h3nDZ : ¬ (3 : ℤ) ∣ (D : ℤ) := by
      intro h
      exact h3nD (Int.ofNat_dvd.mp h)
    have h3primeZ : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_three
    rcases h3primeZ.dvd_or_dvd h3dvd_prod with h | h
    · exact absurd h h3nDZ
    · exact h

open Classical in
private lemma coeff_mod3_char {A G : ℤ⟦X⟧}
    (hA0 : constantCoeff A = 0)
    (hAG : d⁄dX ℤ A = C (2 : ℤ) * G)
    (hGF : PowerSeries.subst (X - C (3 : ℤ) * A ^ 2 * G) G = X) :
    ∀ N : ℕ, coeff N A % 3 = if ∃ k : ℕ, N = 2 * 3 ^ k then 1 else 0 := by
  have hdvd := three_dvd_coeff_sub hA0 hAG hGF
  set π : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  set A3 : (ZMod 3)⟦X⟧ := A.map π
  have hstep : ∀ N : ℕ,
      ((coeff N A : ℤ) : ZMod 3) =
        (if N = 2 then (1 : ZMod 3) else 0) + (if 3 ∣ N then ((coeff (N / 3) A : ℤ) : ZMod 3) else 0) := by
    intro N
    have h0 : ((coeff N A - coeff N (X ^ 2 + A ^ 3) : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (hdvd N)
    have h1 : ((coeff N A : ℤ) : ZMod 3) = ((coeff N (X ^ 2 + A ^ 3) : ℤ) : ZMod 3) :=
      sub_eq_zero.mp (by simpa using h0)
    have h2 : ((coeff N (X ^ 2 + A ^ 3) : ℤ) : ZMod 3) = coeff N (X ^ 2 + A3 ^ 3) := by
      have : (X ^ 2 + A ^ 3 : ℤ⟦X⟧).map π = X ^ 2 + A3 ^ 3 := by simp [A3]
      rw [← this, coeff_map]
      rfl
    rw [h1, h2, map_add, coeff_pow_three_zmod3]
    have hX2 : coeff N (X ^ 2 : (ZMod 3)⟦X⟧) = if N = 2 then 1 else 0 := by
      rw [show (X ^ 2 : (ZMod 3)⟦X⟧) = C 1 * X ^ 2 by simp, coeff_C_mul_X_pow]
      by_cases hN2 : N = 2
      · subst hN2; simp
      · simp [hN2, Ne.symm hN2]
    have hA3c : coeff (N / 3) A3 = ((coeff (N / 3) A : ℤ) : ZMod 3) := by
      change coeff (N / 3) (A.map π) = _; rw [coeff_map]; rfl
    rw [hX2, hA3c]
  have hZMod : ∀ N : ℕ, ((coeff N A : ℤ) : ZMod 3) = if ∃ k : ℕ, N = 2 * 3 ^ k then 1 else 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      rw [hstep N]
      by_cases hN0 : N = 0
      · subst hN0
        simp only [OfNat.zero_ne_ofNat, ↓reduceIte, dvd_zero, Nat.zero_div, zero_add]
        have h00 : coeff 0 A = 0 := by rw [coeff_zero_eq_constantCoeff]; exact hA0
        rw [h00, Int.cast_zero]
        have hnex : ¬ ∃ k : ℕ, 0 = 2 * 3 ^ k := by
          rintro ⟨k, hk⟩
          have : 0 < 2 * 3 ^ k := by positivity
          omega
        rw [if_neg hnex]
      · by_cases hN2 : N = 2
        · subst hN2
          have h3n2 : ¬ (3 ∣ 2) := by omega
          have hex : ∃ k : ℕ, 2 = 2 * 3 ^ k := ⟨0, by norm_num⟩
          rw [if_pos rfl, if_neg h3n2, add_zero, if_pos hex]
        · rw [if_neg hN2, zero_add]
          by_cases h3N : 3 ∣ N
          · rw [if_pos h3N]
            have hlt : N / 3 < N := Nat.div_lt_self (by omega) (by norm_num)
            rw [ih (N / 3) hlt]
            have hiff : (∃ k : ℕ, N / 3 = 2 * 3 ^ k) ↔ (∃ k : ℕ, N = 2 * 3 ^ k) := by
              constructor
              · rintro ⟨k, hk⟩
                refine ⟨k + 1, ?_⟩
                obtain ⟨q, rfl⟩ := h3N
                rw [Nat.mul_div_cancel_left q (by norm_num : 0 < 3)] at hk
                rw [hk, pow_succ]
                ring
              · rintro ⟨k, hk⟩
                cases k with
                | zero => simp at hk; exact absurd hk hN2
                | succ k =>
                  refine ⟨k, ?_⟩
                  rw [hk, pow_succ]
                  have : 2 * (3 ^ k * 3) = 3 * (2 * 3 ^ k) := by ring
                  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
            simp [hiff]
          · rw [if_neg h3N]
            have hnex : ¬ ∃ k : ℕ, N = 2 * 3 ^ k := by
              rintro ⟨k, hk⟩
              cases k with
              | zero => simp at hk; exact hN2 hk
              | succ k =>
                apply h3N
                refine ⟨2 * 3 ^ k, ?_⟩
                rw [hk, pow_succ]; ring
            rw [if_neg hnex]
  intro N
  have hz := hZMod N
  by_cases hex : ∃ k : ℕ, N = 2 * 3 ^ k
  · rw [if_pos hex] at hz ⊢
    have hsub : ((coeff N A - 1 : ℤ) : ZMod 3) = 0 := by simp [hz]
    have hd : (3 : ℤ) ∣ (coeff N A - 1) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hsub
    obtain ⟨t, ht⟩ := hd
    omega
  · rw [if_neg hex] at hz ⊢
    have hd : (3 : ℤ) ∣ coeff N A := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hz
    obtain ⟨t, ht⟩ := hd
    omega

end OMA.ProofA259269

theorem OMA.solution : type_of% @OMA.S_oeis_a259269.main := by
  classical
  intro A G hA0 hAG hGF n hn
  have hchar := OMA.ProofA259269.coeff_mod3_char hA0 hAG hGF (4 * n - 2)
  have hiff : (∃ k : ℕ, 4 * n - 2 = 2 * 3 ^ k) ↔ (∃ k : ℕ, 2 * n - 1 = 3 ^ k) := by
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by omega⟩
  rw [hiff] at hchar
  constructor
  · constructor
    · intro h1
      by_contra hne
      rw [if_neg hne] at hchar
      omega
    · intro hex
      rw [if_pos hex] at hchar
      exact hchar
  · intro hne
    rw [if_neg hne] at hchar
    exact hchar
