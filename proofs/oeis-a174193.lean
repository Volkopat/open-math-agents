import OMAStatements.S_oeis_a174193
import Mathlib

/-!
# A174193: Mathar recurrence

With W = sum (2m+1) C(2m,m) x^m one has S = 1 - 2xC = W (1-4x)^2 and the polynomial part of
the numerator equals (1-4x)^2 (1-3x^2). Hence G (1-x) = R := (1-3x^2) - P1 W, where G is the
series whose coefficients give a, so consecutive coefficients of G differ by explicit
combinations of w(m). The recurrence then reduces to a rational-function identity in n using
w(m+1) = 2(2m+3)/(m+1) w(m); the cases n = 4, 5 are checked from explicit values.
-/

namespace OMA.A174193Proof
open PowerSeries

def w (m : ℕ) : ℚ := (2 * (m : ℚ) + 1) * (Nat.centralBinom m : ℚ)

noncomputable def W : PowerSeries ℚ := PowerSeries.mk w

theorem cb_succ (m : ℕ) :
    ((m : ℚ) + 1) * (Nat.centralBinom (m + 1) : ℚ) = 2 * (2 * m + 1) * Nat.centralBinom m := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ m

theorem cat_eq (m : ℕ) : ((m : ℚ) + 1) * (catalan m : ℚ) = Nat.centralBinom m := by
  exact_mod_cast succ_mul_catalan_eq_centralBinom m

theorem w_succ (m : ℕ) : w (m + 1) = 2 * (2 * (m : ℚ) + 3) / ((m : ℚ) + 1) * w m := by
  unfold w
  have h := cb_succ m
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  push_cast
  linear_combination (2 * (m : ℚ) + 3) * h

theorem w_zero : w 0 = 1 := by simp [w]

theorem S_alt : S_oeis_a174193.S = 1 - PowerSeries.C 2 * (X * S_oeis_a174193.C) := by
  unfold S_oeis_a174193.S
  rw [map_ofNat]
  ring

theorem coeff_S_succ (m : ℕ) : coeff (m + 1) S_oeis_a174193.S = -2 * (catalan m : ℚ) := by
  rw [S_alt, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_one]
  simp [S_oeis_a174193.C]

theorem coeff_S_zero : coeff 0 S_oeis_a174193.S = 1 := by
  rw [S_alt, map_sub, coeff_C_mul, coeff_zero_X_mul, coeff_one]
  simp

theorem key_w (m : ℕ) : w (m + 2) - 8 * w (m + 1) + 16 * w m = -2 * (catalan (m + 1) : ℚ) := by
  have h1 := w_succ m
  have h2 := w_succ (m + 1)
  have h3 := cat_eq (m + 1)
  have hw1 : w (m + 1) = (2 * (m : ℚ) + 3) * (Nat.centralBinom (m + 1) : ℚ) := by
    unfold w; push_cast; ring
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℚ) + 2 ≠ 0 := by positivity
  have hm3 : 2 * (m : ℚ) + 3 ≠ 0 := by positivity
  have hm : w m = ((m : ℚ) + 1) * w (m + 1) / (2 * (2 * m + 3)) := by
    rw [h1]; field_simp
  have hc : (catalan (m + 1) : ℚ) = w (m + 1) / ((2 * (m : ℚ) + 3) * (m + 2)) := by
    rw [hw1]; field_simp; push_cast at h3; linear_combination h3
  rw [show m + 2 = (m + 1) + 1 by ring, h2, hm, hc]
  push_cast
  field_simp
  ring

theorem sq_alt : ((1 : PowerSeries ℚ) - 4 * X) ^ 2 =
    1 - PowerSeries.C 8 * X + PowerSeries.C 16 * X ^ 2 := by
  rw [map_ofNat, map_ofNat]; ring

theorem S_eq : S_oeis_a174193.S = W * (1 - 4 * X) ^ 2 := by
  ext m
  rw [sq_alt, show W * (1 - PowerSeries.C 8 * X + PowerSeries.C 16 * X ^ 2) =
    W - PowerSeries.C 8 * (X * W) + PowerSeries.C 16 * (X ^ 2 * W) by ring]
  rcases m with _ | _ | m
  · rw [coeff_S_zero]; simp [W, w_zero, coeff_X_pow_mul']
  · rw [coeff_S_succ]; simp [W, w_zero, coeff_X_pow_mul', w_succ]; norm_num
  · rw [coeff_S_succ, map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul,
      coeff_X_pow_mul']
    simp only [W, coeff_mk, show 2 ≤ m + 1 + 1 by omega, if_true, show m + 1 + 1 - 2 = m by omega]
    have := key_w m
    rw [show m + 2 = m + 1 + 1 by ring] at this
    linear_combination -this

noncomputable def G : PowerSeries ℚ :=
  S_oeis_a174193.num * ((1 - X) * (1 - 4 * X) ^ 2)⁻¹

noncomputable def R : PowerSeries ℚ :=
  (1 - PowerSeries.C 3 * X ^ 2) - (W - PowerSeries.C 6 * (X ^ 1 * W) + X ^ 2 * W +
    PowerSeries.C 34 * (X ^ 3 * W) - PowerSeries.C 26 * (X ^ 4 * W) - PowerSeries.C 4 * (X ^ 5 * W))

theorem num_eq : S_oeis_a174193.num = (1 - 4 * X) ^ 2 * R := by
  unfold S_oeis_a174193.num R
  rw [S_eq]
  simp only [map_ofNat]
  ring

theorem G_mul : G * (1 - X) = R := by
  calc G * (1 - X) = R * (((1 - X) * (1 - 4 * X) ^ 2) * ((1 - X) * (1 - 4 * X) ^ 2)⁻¹) := by
        unfold G; rw [num_eq]; ring
    _ = R := by
        rw [PowerSeries.mul_inv_cancel, mul_one]
        simp

theorem G_succ (m : ℕ) : coeff (m + 1) G = coeff m G + coeff (m + 1) R := by
  rw [← G_mul, mul_sub, mul_one, map_sub, mul_comm G X, coeff_succ_X_mul]
  ring

theorem G_zero : coeff 0 G = coeff 0 R := by
  rw [← G_mul, mul_sub, mul_one, map_sub, mul_comm G X, coeff_zero_X_mul]
  ring

theorem R_coeff (m : ℕ) (hm : 5 ≤ m) : coeff m R =
    -(w m - 6 * w (m - 1) + w (m - 2) + 34 * w (m - 3) - 26 * w (m - 4) - 4 * w (m - 5)) := by
  unfold R
  have h0 : m ≠ 0 := by omega
  have h2 : m ≠ 2 := by omega
  have g1 : 1 ≤ m := by omega
  have g2 : 2 ≤ m := by omega
  have g3 : 3 ≤ m := by omega
  have g4 : 4 ≤ m := by omega
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_one, coeff_X_pow, W,
    coeff_mk, h0, h2, g1, g2, g3, g4, hm, if_true, if_false]
  ring

theorem R_shift (k : ℕ) : coeff (k + 5) R =
    -(w (k + 5) - 6 * w (k + 4) + w (k + 3) + 34 * w (k + 2) - 26 * w (k + 1) - 4 * w k) := by
  have := R_coeff (k + 5) (by omega)
  simpa using this

theorem w1 : w 1 = 6 := by rw [show (1 : ℕ) = 0 + 1 from rfl, w_succ, w_zero]; norm_num
theorem w2 : w 2 = 30 := by rw [show (2 : ℕ) = 1 + 1 from rfl, w_succ, w1]; norm_num
theorem w3 : w 3 = 140 := by rw [show (3 : ℕ) = 2 + 1 from rfl, w_succ, w2]; norm_num
theorem w4 : w 4 = 630 := by rw [show (4 : ℕ) = 3 + 1 from rfl, w_succ, w3]; norm_num
theorem w5 : w 5 = 2772 := by rw [show (5 : ℕ) = 4 + 1 from rfl, w_succ, w4]; norm_num
theorem w6 : w 6 = 12012 := by rw [show (6 : ℕ) = 5 + 1 from rfl, w_succ, w5]; norm_num
theorem w7 : w 7 = 51480 := by rw [show (7 : ℕ) = 6 + 1 from rfl, w_succ, w6]; norm_num

theorem Rsmall : coeff 0 R = 0 ∧ coeff 1 R = 0 ∧ coeff 2 R = 2 ∧ coeff 3 R = 0 ∧
    coeff 4 R = 2 ∧ coeff 5 R = 8 ∧ coeff 6 R = 34 ∧ coeff 7 R = 160 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [R, W, coeff_X_pow_mul', coeff_X_pow, coeff_one, coeff_C_mul, w_zero, w1, w2, w3, w4,
    w5, w6, w7] <;> norm_num

theorem Gsmall : coeff 2 G = 2 ∧ coeff 3 G = 2 ∧ coeff 4 G = 4 ∧ coeff 5 G = 12 ∧
    coeff 6 G = 46 ∧ coeff 7 G = 206 := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := Rsmall
  have g0 : coeff 0 G = 0 := by rw [G_zero, r0]
  have g1 : coeff 1 G = 0 := by rw [G_succ 0, g0, r1]; norm_num
  have g2 : coeff 2 G = 2 := by rw [G_succ 1, g1, r2]; norm_num
  have g3 : coeff 3 G = 2 := by rw [G_succ 2, g2, r3]; norm_num
  have g4 : coeff 4 G = 4 := by rw [G_succ 3, g3, r4]; norm_num
  have g5 : coeff 5 G = 12 := by rw [G_succ 4, g4, r5]; norm_num
  have g6 : coeff 6 G = 46 := by rw [G_succ 5, g5, r6]; norm_num
  have g7 : coeff 7 G = 206 := by rw [G_succ 6, g6, r7]; norm_num
  exact ⟨g2, g3, g4, g5, g6, g7⟩

end OMA.A174193Proof

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a174193.main := by
  have aeq : ∀ j, OMA.S_oeis_a174193.a j = coeff (j + 2) OMA.A174193Proof.G / 2 := fun j => rfl
  intro n hn
  obtain ⟨g2, g3, g4, g5, g6, g7⟩ := OMA.A174193Proof.Gsmall
  rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | h6
  · simp only [aeq]
    norm_num [g2, g3, g4, g5, g6]
  · simp only [aeq]
    norm_num [g3, g4, g5, g6, g7]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega]
    simp only [aeq]
    rw [show k + 6 + 2 = k + 8 from rfl, show k + 5 + 2 = k + 7 from rfl,
      show k + 4 + 2 = k + 6 from rfl, show k + 3 + 2 = k + 5 from rfl,
      show k + 2 + 2 = k + 4 from rfl]
    have e4 : coeff (k + 8) OMA.A174193Proof.G =
        coeff (k + 7) OMA.A174193Proof.G + coeff (k + 8) OMA.A174193Proof.R :=
      OMA.A174193Proof.G_succ (k + 7)
    have e3 : coeff (k + 7) OMA.A174193Proof.G =
        coeff (k + 6) OMA.A174193Proof.G + coeff (k + 7) OMA.A174193Proof.R :=
      OMA.A174193Proof.G_succ (k + 6)
    have e2 : coeff (k + 6) OMA.A174193Proof.G =
        coeff (k + 5) OMA.A174193Proof.G + coeff (k + 6) OMA.A174193Proof.R :=
      OMA.A174193Proof.G_succ (k + 5)
    have e1 : coeff (k + 5) OMA.A174193Proof.G =
        coeff (k + 4) OMA.A174193Proof.G + coeff (k + 5) OMA.A174193Proof.R :=
      OMA.A174193Proof.G_succ (k + 4)
    rw [e4, e3, e2, e1, OMA.A174193Proof.R_shift k,
      show k + 6 = (k + 1) + 5 from rfl, OMA.A174193Proof.R_shift (k + 1),
      show k + 7 = (k + 2) + 5 from rfl, OMA.A174193Proof.R_shift (k + 2),
      show k + 8 = (k + 3) + 5 from rfl, OMA.A174193Proof.R_shift (k + 3)]
    have hw : ∀ i : ℕ, OMA.A174193Proof.w (k + i + 1) =
        2 * (2 * ((k : ℚ) + i) + 3) / ((k : ℚ) + i + 1) * OMA.A174193Proof.w (k + i) := by
      intro i
      rw [OMA.A174193Proof.w_succ]; push_cast; ring
    have v1 := hw 0
    have v2 := hw 1
    have v3 := hw 2
    have v4 := hw 3
    have v5 := hw 4
    have v6 := hw 5
    have v7 := hw 6
    have v8 := hw 7
    simp only [add_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at v1 v2 v3 v4 v5 v6 v7 v8
    simp only [add_assoc, Nat.reduceAdd] at v1 v2 v3 v4 v5 v6 v7 v8 ⊢
    rw [v8, v7, v6, v5, v4, v3, v2, v1]
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
