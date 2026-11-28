import OMAStatements.S_oeis_a186334
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination

/-!
Let P be the generating series over the polynomial ring in y, defined by
(1 - z - (1 + y)z²) P = 1. The Catalan moment annihilates
y(4 - y) ∂P/∂y + (2 - 2y) P. Eliminating the derivative in y gives the
claimed recurrence by taking coefficients in z.
-/

namespace OMA.S_oeis_a186334

open Polynomial Finset
open scoped PowerSeries

private abbrev R := ℚ[X]
private abbrev S := PowerSeries R

private noncomputable def geom (n : ℕ) : Polynomial R :=
  ∑ k ∈ range (n+1), stepPoly ^ k

private theorem geom_step (n : ℕ) :
    (geom (n+1)) = 1 + stepPoly * (geom n) := by
  simp only [geom]
  rw [sum_range_succ', mul_sum]
  simp only [pow_zero, pow_succ', add_comm (1 : Polynomial R)]

private theorem step_coeff_lt (i k : ℕ) (h : i < k) : (stepPoly ^ k).coeff i = 0 := by
  rw [stepPoly, mul_pow, Polynomial.coeff_mul_X_pow']
  simp [not_le_of_gt h]

private theorem geom_drop (i k : ℕ) (h : i < k+1) :
    (geom (k+1)).coeff i = (geom k).coeff i := by
  simp only [geom]
  rw [sum_range_succ, Polynomial.coeff_add, step_coeff_lt _ _ h, add_zero]

private theorem profile_zero : profile 0 = 1 := by
  simp [profile]

private theorem profile_one : profile 1 = 1 := by
  change (geom 1).coeff 1 = 1
  rw [geom_step 0]
  simp [geom, stepPoly, add_mul, mul_assoc, ← pow_two, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]

private theorem profile_step (n : ℕ) :
    profile (n+2) = profile (n+1) + (1 + (Polynomial.X : R)) * profile n := by
  change (geom (n+2)).coeff (n+2) = (geom (n+1)).coeff (n+1) +
    (1 + (Polynomial.X : R)) * (geom n).coeff n
  rw [geom_step (n+1)]
  have hs : stepPoly = Polynomial.X + Polynomial.C (1 + (Polynomial.X : R)) * Polynomial.X^2 := by
    unfold stepPoly
    ring
  rw [hs]
  rw [add_mul, mul_assoc]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
    and_false, if_false, zero_add, Polynomial.coeff_C_mul]
  have hx := Polynomial.coeff_X_pow_mul (geom (n+1)) 1 (n+1)
  rw [pow_one] at hx
  rw [hx, Polynomial.coeff_X_pow_mul, geom_drop n n (by omega)]

private noncomputable def z : S := PowerSeries.X
private noncomputable def y : R := Polynomial.X
private noncomputable def a : R := 1 + y
private noncomputable def C (r : R) : S := PowerSeries.C (R := R) r
private noncomputable def cf (n : ℕ) : S →ₗ[R] R := PowerSeries.coeff (R := R) n
private noncomputable def P : S := PowerSeries.mk profile
private noncomputable def L : S := 1 - z - C a * z^2
private noncomputable def Pz : S := PowerSeries.derivative R P
private noncomputable def Py : S := PowerSeries.mk fun n => Polynomial.derivative (profile n)

private theorem cf_C (n : ℕ) (r : R) (s : S) : cf n (C r * s) = r * cf n s := by
  exact PowerSeries.coeff_C_mul n s r

private theorem cf_z_pow (n k : ℕ) (s : S) :
    cf n (z^k * s) = if k ≤ n then cf (n-k) s else 0 := by
  exact PowerSeries.coeff_X_pow_mul' s k n

private theorem cf_L (s : S) (n : ℕ) :
    cf n (L * s) = cf n s - (if 1 ≤ n then cf (n-1) s else 0) -
      a * (if 2 ≤ n then cf (n-2) s else 0) := by
  rw [L, sub_mul, sub_mul, one_mul, map_sub, map_sub, mul_assoc, cf_C,
    show z * s = z^1 * s by rw [pow_one], cf_z_pow, cf_z_pow]

@[simp] private theorem cf_P (n : ℕ) : cf n P = profile n := by
  exact PowerSeries.coeff_mk _ _

@[simp] private theorem cf_Py (n : ℕ) :
    cf n Py = Polynomial.derivative (profile n) := by
  exact PowerSeries.coeff_mk _ _

private theorem inverse_P : L * P = 1 := by
  apply PowerSeries.ext
  intro n
  change cf n (L * P) = cf n 1
  rw [cf_L]
  cases n with
  | zero =>
    simp only [cf_P, profile_zero, show ¬ 1 ≤ (0 : ℕ) by omega,
      show ¬ 2 ≤ (0 : ℕ) by omega, if_false, mul_zero, sub_zero]
    simp [cf, PowerSeries.coeff_one]
  | succ n =>
    cases n with
    | zero =>
      simp only [show 1 ≤ (0 : ℕ)+1 by omega, show ¬ 2 ≤ (0 : ℕ)+1 by omega,
        if_true, if_false, Nat.add_sub_cancel, cf_P, profile_zero, profile_one, sub_self,
        mul_zero, sub_zero]
      simp [cf, PowerSeries.coeff_one, profile_one]
    | succ n =>
      have h1 : 1 ≤ n+1+1 := by omega
      have h2 : 2 ≤ n+1+1 := by omega
      have hn : n+1+1-1 = n+1 := by omega
      have hm : n+1+1-2 = n := by omega
      simp only [h1, h2, if_true, hn, hm, cf_P]
      change profile (n+2) - profile (n+1) - a * profile n = cf (n+2) 1
      rw [profile_step, cf, PowerSeries.coeff_one, if_neg (by omega)]
      unfold a y
      ring

private theorem inverse_Pz : L * Pz = (1 + 2 * C a * z) * P := by
  have h := congrArg (PowerSeries.derivative R) inverse_P
  simp only [Derivation.leibniz, Derivation.map_one_eq_zero, L, Pz, z, C,
    map_sub, PowerSeries.derivative_X, PowerSeries.derivative_C,
    Derivation.leibniz_pow, show (2 : ℕ) - 1 = 1 by decide, pow_one, mul_one,
    two_nsmul, zero_mul, add_zero] at h
  simp only [smul_eq_mul, zero_mul, mul_zero, mul_one, add_zero] at h
  dsimp [L, Pz, z, C]
  linear_combination h

private theorem inverse_Py : L * Py = z^2 * P := by
  apply PowerSeries.ext
  intro n
  change cf n (L * Py) = cf n (z^2 * P)
  rw [cf_L, cf_z_pow]
  cases n with
  | zero => simp [profile_zero]
  | succ n =>
    cases n with
    | zero => simp [profile_zero, profile_one]
    | succ n =>
      have h1 : 1 ≤ n+1+1 := by omega
      have h2 : 2 ≤ n+1+1 := by omega
      have hn : n+1+1-1 = n+1 := by omega
      have hm : n+1+1-2 = n := by omega
      simp only [h1, h2, if_true, hn, hm, cf_P, cf_Py]
      change Polynomial.derivative (profile (n+2)) - Polynomial.derivative (profile (n+1)) -
        a * Polynomial.derivative (profile n) = profile n
      simp only [profile_step, map_add, Polynomial.derivative_mul, Polynomial.derivative_one,
        Polynomial.derivative_X, zero_add, one_mul, a, y]
      ring


private noncomputable def M : R →ₗ[ℚ] ℚ := moment (fun j => (catalan j : ℚ))

private theorem M_monomial (n : ℕ) (c : ℚ) :
    M (monomial n c) = (catalan n : ℚ) * c := by
  simp [M, moment, Polynomial.lsum, Finsupp.lsum_single, smul_eq_mul]

private theorem catalan_step (n : ℕ) :
    ((n : ℚ) + 2) * (catalan (n+1) : ℚ) =
      (4 * (n : ℚ) + 2) * (catalan n : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1), ← succ_mul_catalan_eq_centralBinom n] at h
  have hc := congrArg (fun k : ℕ => (k : ℚ)) h
  push_cast at hc
  have hp : (n : ℚ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hp
  linear_combination hc

private theorem moment_annihilates (p : R) :
    M (y * (4-y) * Polynomial.derivative p + (2-2*y) * p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add] at hp hq ⊢
    linear_combination hp + hq
  | monomial n c =>
    have hfour : (4 : R) = Polynomial.C (4 : ℚ) := (map_ofNat Polynomial.C 4).symm
    have htwo : (2 : R) = Polynomial.C (2 : ℚ) := (map_ofNat Polynomial.C 2).symm
    have h₁ : y * (4-y) = Polynomial.C (4 : ℚ) * Polynomial.X - Polynomial.X ^ 2 := by
      rw [hfour, y]
      ring
    rw [h₁, htwo]
    simp only [sub_mul, mul_assoc, Polynomial.C_mul_monomial, y]
    cases n with
    | zero =>
      rw [Polynomial.derivative_monomial]
      simp only [Nat.cast_zero, mul_zero, Polynomial.monomial_zero_right,
        zero_sub, neg_zero, zero_add, map_sub, Polynomial.X_mul_monomial,
        Polynomial.C_mul_monomial, M_monomial, catalan_zero, catalan_one, Nat.cast_one,
        one_mul, sub_self]
    | succ n =>
      simp only [Polynomial.derivative_monomial_succ, map_add, map_sub, mul_assoc,
        Polynomial.X_mul_monomial, Polynomial.X_pow_mul_monomial, Polynomial.C_mul_monomial,
        M_monomial]
      have h := catalan_step (n+1)
      simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] at h
      linear_combination -c * h

private noncomputable def Q : S := 1 - 2*z - 5*z^2 + 6*z^3 + 5*z^4
private noncomputable def B : S := 2 - 4*z - 6*z^2 + 10*z^3 + 10*z^4
private noncomputable def F : S := C (y*(4-y))*Py + C (2-2*y)*P

private theorem certificate :
    z*Q*Pz + B*P + (z-2) = z^2*(z-2)*F := by
  have hL : L ≠ 0 := by
    intro h
    have hh := inverse_P
    rw [h, zero_mul] at hh
    exact zero_ne_one hh
  apply mul_left_cancel₀ hL
  have hi := inverse_P
  have hz := inverse_Pz
  have hy := inverse_Py
  simp only [Q, B, F, L, a, C, map_add, map_sub, map_mul, map_one, map_ofNat] at *
  linear_combination
    z*(1 - 2*z - 5*z^2 + 6*z^3 + 5*z^4)*hz -
      z^2*(z-2)*(PowerSeries.C (R := R) y)*(4-PowerSeries.C (R := R) y)*hy -
      (z-2)*(1-z-(1+PowerSeries.C (R := R) y)*z^2)*hi

private theorem M_cf_F (n : ℕ) : M (cf n F) = 0 := by
  rw [F, map_add (cf n), cf_C, cf_C, cf_Py, cf_P]
  exact moment_annihilates (profile n)


private theorem mcf_nat_mul (n k : ℕ) (s : S) :
    M (cf n ((k : S) * s)) = (k : ℚ) * M (cf n s) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

private theorem mcf_ofNat_mul (n k : ℕ) [k.AtLeastTwo] (s : S) :
    M (cf n (OfNat.ofNat k * s)) = OfNat.ofNat k * M (cf n s) :=
  mcf_nat_mul n k s

private theorem mcf_P (n k : ℕ) (hk : k ≤ n) :
    M (cf n (z^k * P)) = sequence (n-k) := by
  rw [cf_z_pow, if_pos hk, cf_P]
  rfl

private theorem mcf_Pz (n k : ℕ) (hk : k ≤ n) :
    M (cf n (z^(k+1) * Pz)) = ((n : ℚ)-k) * sequence (n-k) := by
  rw [cf_z_pow]
  split
  next hh =>
    have he : n - (k+1) + 1 = n - k := by omega
    change M (PowerSeries.coeff (R := R) (n-(k+1)) (PowerSeries.derivative R P)) = _
    rw [PowerSeries.coeff_derivative, he]
    have hc : ((n-(k+1) : ℕ) : R) + 1 = ((n-k : ℕ) : R) := by
      exact_mod_cast he
    rw [hc]
    change M (cf (n-k) P * ((n-k : ℕ) : R)) = _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Nat.cast_sub hk, cf_P]
    rfl
  next hh =>
    have he : n = k := by omega
    simp [he]

private theorem mcf_F (n k : ℕ) (hk : k ≤ n) :
    M (cf n (z^k * F)) = 0 := by
  rw [cf_z_pow, if_pos hk, M_cf_F]

private theorem mcf_affine (n : ℕ) (hn : 2 ≤ n) :
    M (cf n (z - 2)) = 0 := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have htwo : (2 : S) = 1 + 1 := by ring
  rw [map_sub, show cf n (2 : S) = 0 by
    rw [htwo, map_add]
    simp [cf, PowerSeries.coeff_one, h0]]
  change M (PowerSeries.coeff (R := R) n PowerSeries.X - 0) = 0
  simp [PowerSeries.coeff_X, h1]

private theorem recurrence (m : ℕ) :
    let n := (m : ℚ) + 4
    (n+2) * sequence (m+4) + 2*(-n-1) * sequence (m+3) + (4-5*n) * sequence (m+2)
      + 2*(3*n-4) * sequence (m+1) + 5*(n-2) * sequence m = 0 := by
  have hz : z*Q*Pz =
      z^(0+1)*Pz - (2 : ℕ)*(z^(1+1)*Pz) - (5 : ℕ)*(z^(2+1)*Pz) +
      (6 : ℕ)*(z^(3+1)*Pz) + (5 : ℕ)*(z^(4+1)*Pz) := by
    unfold Q
    push_cast
    ring
  have hp : B*P =
      (2 : ℕ)*(z^0*P) - (4 : ℕ)*(z^1*P) - (6 : ℕ)*(z^2*P) +
      (10 : ℕ)*(z^3*P) + (10 : ℕ)*(z^4*P) := by
    unfold B
    push_cast
    ring
  have hf : z^2*(z-2)*F = z^3*F - (2 : ℕ)*(z^2*F) := by
    push_cast
    ring
  have h : M (cf (m+4) (z*Q*Pz + B*P + (z-2))) =
      M (cf (m+4) (z^2*(z-2)*F)) :=
    congrArg (fun s => M (cf (m+4) s)) certificate
  rw [hz, hp, hf] at h
  have h0 : 0 ≤ m+4 := Nat.zero_le _
  have h1 : 1 ≤ m+4 := by omega
  have h2 : 2 ≤ m+4 := by omega
  have h3 : 3 ≤ m+4 := by omega
  have h4 : 4 ≤ m+4 := by omega
  simp only [map_add, mcf_affine _ h2] at h
  simp only [map_add, map_sub, mcf_nat_mul,
    mcf_ofNat_mul (m+4) 2, mcf_ofNat_mul (m+4) 4, mcf_ofNat_mul (m+4) 5,
    mcf_ofNat_mul (m+4) 6, mcf_ofNat_mul (m+4) 10, mcf_Pz _ _ h0, mcf_Pz _ _ h1,
    mcf_Pz _ _ h2, mcf_Pz _ _ h3, mcf_Pz _ _ h4, mcf_P _ _ h0,
    mcf_P _ _ h1, mcf_P _ _ h2, mcf_P _ _ h3, mcf_P _ _ h4,
    mcf_F _ _ h2, mcf_F _ _ h3, show m+4-1=m+3 by omega, show m+4-2=m+2 by omega,
    show m+4-3=m+1 by omega, show m+4-4=m by omega, Nat.sub_zero, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero, add_zero] at h
  dsimp
  linear_combination h

end OMA.S_oeis_a186334

theorem OMA.solution : type_of% @OMA.S_oeis_a186334.main :=
  OMA.S_oeis_a186334.recurrence
