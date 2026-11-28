import OMAStatements.S_oeis_a186335
import Mathlib

/-!
Paul Barry's central-binomial transform, OEIS A186335.
Recurrence attributed to R. J. Mathar (February 13, 2015).
Source: https://oeis.org/A186335/internal
Pinned formalization by @KoaOkano. Proof by @grp06.
The use of the formal derivative coefficient API follows @caa1982's
neighboring A186338 proof.

The two choices of double step give the factor (1+y). The moment of
(y^j) supplies the central binomial coefficient in the defining sum.
-/

namespace OMA.A186335Proof

open OMA.S_oeis_a186335

private abbrev P := Polynomial ℚ
private abbrev S := PowerSeries P
private noncomputable abbrev L : P →ₗ[ℚ] ℚ :=
  moment fun j => (j.centralBinom : ℚ)

private noncomputable def T (f : P) : P :=
  (Polynomial.X ^ 2 - 4 * Polynomial.X) * Polynomial.derivative f +
    (Polynomial.X - 2) * f

private theorem moment_monomial (n : ℕ) (a : ℚ) :
    L (Polynomial.monomial n a) = (n.centralBinom : ℚ) * a := by
  simp [L, moment, Polynomial.lsum_apply, Polynomial.sum_monomial_index, smul_eq_mul]

private theorem moment_pow (n : ℕ) :
    L ((Polynomial.X : P) ^ n) = (n.centralBinom : ℚ) := by
  rw [← one_mul ((Polynomial.X : P) ^ n), ← Polynomial.C_1,
    Polynomial.C_mul_X_pow_eq_monomial, moment_monomial, mul_one]

private theorem T_pow (n : ℕ) :
    T ((Polynomial.X : P) ^ n) =
      (((n : ℚ) + 1) • (Polynomial.X : P) ^ (n + 1)) -
        (4 * (n : ℚ) + 2) • (Polynomial.X : P) ^ n := by
  cases n with
  | zero => norm_num [T, Polynomial.derivative_one, Polynomial.smul_eq_C_mul, map_ofNat]
  | succ n =>
    unfold T
    rw [Polynomial.derivative_X_pow_succ (R := ℚ) n]
    simp only [Nat.cast_add, Nat.cast_one, Polynomial.smul_eq_C_mul, map_add, map_mul,
      map_one, map_ofNat, pow_succ]
    ring

private theorem moment_T (f : P) : L (T f) = 0 := by
  have hp (n : ℕ) : L (T ((Polynomial.X : P) ^ n)) = 0 := by
    rw [T_pow, map_sub, LinearMap.map_smul, LinearMap.map_smul, moment_pow, moment_pow]
    simp only [smul_eq_mul]
    have h : ((n : ℚ) + 1) * ((n + 1).centralBinom : ℚ) =
        2 * (2 * (n : ℚ) + 1) * (n.centralBinom : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    rw [h]
    ring
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have h : T (f + g) = T f + T g := by
      simp only [T, Polynomial.derivative_add]
      ring
    rw [h, map_add, hf, hg, add_zero]
  | monomial n a =>
    have h : T (Polynomial.monomial n a) = a • T ((Polynomial.X : P) ^ n) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [T, Polynomial.derivative_C_mul, Polynomial.smul_eq_C_mul]
      ring
    rw [h, LinearMap.map_smul, hp, smul_zero]

private noncomputable abbrev z : S := PowerSeries.X
private noncomputable abbrev y : S := PowerSeries.C (Polynomial.X : P)
private noncomputable abbrev dz := PowerSeries.derivative P
private noncomputable abbrev c (a : ℚ) : S := PowerSeries.C (Polynomial.C a)

private theorem numeral_c (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : S) = c (OfNat.ofNat n : ℚ) := by
  simp only [c, map_ofNat]

private noncomputable def A : S := 1 - z - z ^ 2
private noncomputable def B : S := z ^ 2
private noncomputable def D : S := A - y * B
private noncomputable def Q : S := A * (A - 4 * B)
/-- Half the formal derivative of Q. -/
private noncomputable def H : S := -1 - 5 * z + 9 * z ^ 2 + 10 * z ^ 3

private theorem Q_expand : Q = 1 - 2 * z - 5 * z ^ 2 + 6 * z ^ 3 + 5 * z ^ 4 := by
  unfold Q A B
  ring

private theorem derivative_z_mul {K : Type*} [CommRing K] (F G : PowerSeries K) :
    PowerSeries.derivative K (F * G) =
      F * PowerSeries.derivative K G + G * PowerSeries.derivative K F := by
  simpa only [smul_eq_mul] using (PowerSeries.derivative K).leibniz F G

private theorem derivative_z_sq : dz (z ^ 2) = 2 * z := by
  rw [pow_two, derivative_z_mul]
  simp [PowerSeries.derivative_X, two_mul]

private theorem derivative_D : dz D = -1 - 2 * z - y * (2 * z) := by
  simp only [D, A, B, map_sub, derivative_z_mul,
    PowerSeries.derivative_one, PowerSeries.derivative_X, PowerSeries.derivative_C,
    derivative_z_sq, mul_zero, add_zero, zero_sub]

private theorem dQ : dz Q = 2 * H := by
  have hc : dz (4 : S) = 0 := by rw [numeral_c]; exact PowerSeries.derivative_C
  unfold Q A B H
  simp only [map_sub, derivative_z_mul, PowerSeries.derivative_one,
    PowerSeries.derivative_X, derivative_z_sq, hc, mul_zero, add_zero, zero_sub]
  ring

private theorem exists_R : ∃ R : S, D * R = 1 := by
  have h0 : PowerSeries.constantCoeff D = 1 := by
    simp [D, A, B, PowerSeries.constantCoeff_X]
  have hu : IsUnit D := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h0]; exact isUnit_one)
  obtain ⟨u, hu⟩ := hu
  refine ⟨↑(u⁻¹), ?_⟩
  rw [← hu]
  exact u.mul_inv

private theorem coeff_profile (R : S) (hR : D * R = 1) (n : ℕ) :
    PowerSeries.coeff n R = profile n := by
  let s : S := (stepPoly : S)
  let a : S := 1 + PowerSeries.C ((1 : P) + Polynomial.X) * z
  have hs : s = a * z := by
    simp [s, a, stepPoly, z]
  have hD : D = 1 - s := by
    rw [hs]
    simp only [D, A, B, a, map_add, map_one]
    ring
  have hgeom (N : ℕ) :
      R = (∑ k ∈ Finset.range N, s ^ k) + s ^ N * R := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, pow_succ]
      rw [hD] at hR
      linear_combination ih + s ^ N * hR
  have hv : PowerSeries.coeff n (s ^ (n + 1) * R) = 0 := by
    rw [hs, mul_pow, mul_comm (a ^ (n + 1)) (z ^ (n + 1)), mul_assoc,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hsum : (∑ k ∈ Finset.range (n + 1), s ^ k) =
      ((∑ k ∈ Finset.range (n + 1), stepPoly ^ k : Polynomial P) : S) := by
    have h := map_sum (Polynomial.coeToPowerSeries.ringHom : Polynomial P →+* S)
      (fun k : ℕ => stepPoly ^ k) (Finset.range (n + 1))
    simp only [map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow] at h
    exact h.symm
  rw [hgeom (n + 1), map_add, hv, add_zero, hsum, Polynomial.coeff_coe]
  rfl

/-- Differentiate each coefficient as a polynomial in the moment variable. -/
private noncomputable def dy (F : S) : S :=
  PowerSeries.mk fun n => Polynomial.derivative (PowerSeries.coeff n F)

private theorem dy_sub (F G : S) : dy (F - G) = dy F - dy G := by
  apply PowerSeries.ext
  intro n
  simp only [dy, PowerSeries.coeff_mk, map_sub]

private theorem dy_mul (F G : S) : dy (F * G) = dy F * G + F * dy G := by
  apply PowerSeries.ext
  intro n
  simp only [dy, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul,
    map_sum, Polynomial.derivative_mul, Finset.sum_add_distrib]

private theorem dy_one : dy (1 : S) = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [dy, PowerSeries.coeff_mk, PowerSeries.coeff_one, map_zero]
  split_ifs <;> simp [Polynomial.derivative_one]

private theorem dy_z : dy z = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [dy, PowerSeries.coeff_mk, PowerSeries.coeff_X, map_zero]
  split_ifs <;> simp [Polynomial.derivative_one]

private theorem dy_y : dy y = 1 := by
  apply PowerSeries.ext
  intro n
  simp only [dy, PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_one]
  split_ifs <;> simp

private theorem dy_D : dy D = -B := by
  simp [D, A, B, pow_two, dy_sub, dy_mul, dy_one, dy_z, dy_y]

private noncomputable def TS (F : S) : S := (y ^ 2 - 4 * y) * dy F + (y - 2) * F

private theorem moment_TS (F : S) (n : ℕ) :
    L (PowerSeries.coeff n (TS F)) = 0 := by
  have hy : y ^ 2 - 4 * y = PowerSeries.C
      ((Polynomial.X : P) ^ 2 - 4 * Polynomial.X) := by
    simp only [y, map_sub, map_pow, map_mul, map_ofNat]
  have hy' : y - 2 = PowerSeries.C ((Polynomial.X : P) - 2) := by
    simp only [y, map_sub, map_ofNat]
  rw [TS, hy, hy', map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    dy, PowerSeries.coeff_mk]
  change L (T (PowerSeries.coeff n F)) = 0
  exact moment_T _

private theorem differential (R : S) (hR : D * R = 1) :
    Q * dz R + H * R = (2 * z - z ^ 2) * TS R := by
  have hz : dz R = -R ^ 2 * dz D := by
    have h := congrArg (fun F : S => dz F) hR
    change dz (D * R) = dz 1 at h
    rw [derivative_z_mul, PowerSeries.derivative_one] at h
    linear_combination R * h - dz R * hR
  have hy : dy R = B * R ^ 2 := by
    have h := congrArg dy hR
    rw [dy_mul, dy_one, dy_D] at h
    linear_combination R * h - dy R * hR
  have hr : R = D * R ^ 2 := by
    calc
      R = (D * R) * R := by rw [hR, one_mul]
      _ = D * R ^ 2 := by ring
  calc
    Q * dz R + H * R = Q * (-R ^ 2 * dz D) + H * (D * R ^ 2) := by
      rw [hz, ← hr]
    _ = (2 * z - z ^ 2) *
        ((y ^ 2 - 4 * y) * (B * R ^ 2) + (y - 2) * (D * R ^ 2)) := by
      rw [derivative_D]
      unfold Q H D A B
      ring
    _ = (2 * z - z ^ 2) * TS R := by rw [TS, hy, ← hr]

private theorem euler_coeff (F : S) (n : ℕ) :
    PowerSeries.coeff n (z * dz F) = (n : ℚ) • PowerSeries.coeff n F := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      Polynomial.smul_eq_C_mul]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one]
    ring

private theorem moment_shift (F : S) (k n : ℕ) (hk : k ≤ n) (r : ℚ) :
    L (PowerSeries.coeff n (z ^ k * (c r * F))) =
      r * L (PowerSeries.coeff (n - k) F) := by
  rw [PowerSeries.coeff_X_pow_mul', if_pos hk, PowerSeries.coeff_C_mul,
    ← Polynomial.smul_eq_C_mul, LinearMap.map_smul, smul_eq_mul]

private theorem extraction (R : S) (hR : D * R = 1) (m : ℕ) :
    let n := (m : ℚ) + 4
    n * sequence (m+4) + (1-2*n) * sequence (m+3) + 5*(1-n) * sequence (m+2)
      + 3*(2*n-3) * sequence (m+1) + 5*(n-2) * sequence m = 0 := by
  let E := z * dz R
  have he :
      E - z ^ 1 * (c 2 * E) - z ^ 2 * (c 5 * E) +
          z ^ 3 * (c 6 * E) + z ^ 4 * (c 5 * E) -
          z ^ 1 * (c 1 * R) - z ^ 2 * (c 5 * R) +
          z ^ 3 * (c 9 * R) + z ^ 4 * (c 10 * R) =
        z ^ 2 * (c 2 * TS R) - z ^ 3 * (c 1 * TS R) := by
    have h := congrArg (fun F : S => z * F) (differential R hR)
    change z * (Q * dz R + H * R) = z * ((2 * z - z ^ 2) * TS R) at h
    rw [Q_expand, H] at h
    have h1 : c 1 = 1 := by simp only [c, map_one]
    have h2 : c 2 = 2 := (numeral_c 2).symm
    have h5 : c 5 = 5 := (numeral_c 5).symm
    have h6 : c 6 = 6 := (numeral_c 6).symm
    have h9 : c 9 = 9 := (numeral_c 9).symm
    have h10 : c 10 = 10 := (numeral_c 10).symm
    simp only [E, h1, h2, h5, h6, h9, h10]
    linear_combination h
  have hm (n : ℕ) : L (PowerSeries.coeff n R) = sequence n := by
    rw [coeff_profile R hR]
    rfl
  have e := congrArg (fun F => L (PowerSeries.coeff (m + 4) F)) he
  change L (PowerSeries.coeff (m + 4) _) = L (PowerSeries.coeff (m + 4) _) at e
  simp (disch := omega) only [map_add, map_sub, moment_shift,
    show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega,
    moment_TS, mul_zero, sub_zero, E, euler_coeff, LinearMap.map_smul, smul_eq_mul,
    hm] at e
  dsimp
  push_cast at e
  linear_combination e

theorem result : type_of% @OMA.S_oeis_a186335.main := by
  obtain ⟨R, hR⟩ := exists_R
  exact extraction R hR

end OMA.A186335Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a186335.main :=
  OMA.A186335Proof.result
