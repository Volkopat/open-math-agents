import OMAStatements.S_oeis_a337912
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a337912

open OMA.S_oeis_a337912

private def u : PowerSeries (ZMod 16) :=
  PowerSeries.mk fun m => if m = 2 ∨ (3 ≤ m ∧ m % 2 = 1) then 1 else 0

private lemma coeff_u (m : ℕ) :
    PowerSeries.coeff m u = if m = 2 ∨ (3 ≤ m ∧ m % 2 = 1) then 1 else 0 := by
  simp [u]

private noncomputable def A0 : PowerSeries (ZMod 16) :=
  1 + 2 * PowerSeries.X + 8 * u

private lemma A0_const : PowerSeries.constantCoeff A0 = 1 := by
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_u]; decide
  rw [A0, map_add, map_add, map_one, map_mul, PowerSeries.constantCoeff_X, mul_zero, add_zero,
      map_mul, hu0, mul_zero, add_zero]

private lemma zmod16_ps_16 : (16 : PowerSeries (ZMod 16)) = 0 := by
  have h : (16 : ZMod 16) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 16)), h, map_zero]

private lemma one_add_2X_pow (m : ℕ) :
    ((1 : PowerSeries (ZMod 16)) + 2 * PowerSeries.X) ^ m =
      1 + (2 * (m : PowerSeries (ZMod 16))) * PowerSeries.X +
      (4 * ((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16))) * PowerSeries.X ^ 2 +
      (8 * ((Nat.choose m 3 : ℕ) : PowerSeries (ZMod 16))) * PowerSeries.X ^ 3 := by
  have h16 := zmod16_ps_16
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    have hch2 : ((Nat.choose (m + 1) 2 : ℕ) : PowerSeries (ZMod 16)) =
        ((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16)) + (m : PowerSeries (ZMod 16)) := by
      have : Nat.choose (m + 1) 2 = Nat.choose m 2 + m := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [this, Nat.cast_add]
    have hch3 : ((Nat.choose (m + 1) 3 : ℕ) : PowerSeries (ZMod 16)) =
        ((Nat.choose m 3 : ℕ) : PowerSeries (ZMod 16)) + ((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16)) := by
      have : Nat.choose (m + 1) 3 = Nat.choose m 3 + Nat.choose m 2 := by
        rw [Nat.choose_succ_succ, add_comm]
      rw [this, Nat.cast_add]
    rw [hch2, hch3, Nat.cast_succ]
    calc ((1 : PowerSeries (ZMod 16)) + 2 * (m : PowerSeries (ZMod 16)) * PowerSeries.X +
            4 * ((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16)) * PowerSeries.X ^ 2 +
            8 * ((Nat.choose m 3 : ℕ) : PowerSeries (ZMod 16)) * PowerSeries.X ^ 3) * (1 + 2 * PowerSeries.X)
        = (1 + 2 * ((m : PowerSeries (ZMod 16)) + 1) * PowerSeries.X +
            4 * (((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16)) + (m : PowerSeries (ZMod 16))) * PowerSeries.X ^ 2 +
            8 * (((Nat.choose m 3 : ℕ) : PowerSeries (ZMod 16)) + ((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16))) * PowerSeries.X ^ 3) +
            16 * (((Nat.choose m 3 : ℕ) : PowerSeries (ZMod 16)) * PowerSeries.X ^ 4) := by ring
      _ = 1 + 2 * ((m : PowerSeries (ZMod 16)) + 1) * PowerSeries.X +
            4 * (((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16)) + (m : PowerSeries (ZMod 16))) * PowerSeries.X ^ 2 +
            8 * (((Nat.choose m 3 : ℕ) : PowerSeries (ZMod 16)) + ((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16))) * PowerSeries.X ^ 3 := by
            rw [h16, zero_mul, add_zero]

private lemma A0_pow (m : ℕ) :
    A0 ^ m = (1 + 2 * PowerSeries.X) ^ m + 8 * (m : PowerSeries (ZMod 16)) * u := by
  have h16 := zmod16_ps_16
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, A0, Nat.cast_succ]
    have hX : (1 + 2 * PowerSeries.X) ^ m * (8 * u) = 8 * u := by
      rw [one_add_2X_pow]
      calc (1 + 2 * ↑m * PowerSeries.X + 4 * ↑(m.choose 2) * PowerSeries.X ^ 2 +
              8 * ↑(m.choose 3) * PowerSeries.X ^ 3) * (8 * u)
          = 8 * u + 16 * ((↑m * PowerSeries.X + 2 * ↑(m.choose 2) * PowerSeries.X ^ 2 +
              4 * ↑(m.choose 3) * PowerSeries.X ^ 3) * u) := by ring
        _ = 8 * u := by rw [h16, zero_mul, add_zero]
    calc ((1 + 2 * PowerSeries.X) ^ m + 8 * ↑m * u) * (1 + 2 * PowerSeries.X + 8 * u)
        = (1 + 2 * PowerSeries.X) ^ m * (1 + 2 * PowerSeries.X) +
            (1 + 2 * PowerSeries.X) ^ m * (8 * u) + 8 * ↑m * u +
            16 * (↑m * u * PowerSeries.X + 4 * ↑m * u ^ 2) := by ring
      _ = (1 + 2 * PowerSeries.X) ^ (m + 1) + 8 * u + 8 * ↑m * u + 0 := by
            rw [← pow_succ, hX, h16, zero_mul]
      _ = (1 + 2 * PowerSeries.X) ^ (m + 1) + 8 * (↑m + 1) * u := by ring

private lemma coeff_one_add_2X_pow (m d : ℕ) :
    PowerSeries.coeff d (((1 : PowerSeries (ZMod 16)) + 2 * PowerSeries.X) ^ m) =
      if d = 0 then 1
      else if d = 1 then 2 * (m : ZMod 16)
      else if d = 2 then 4 * (Nat.choose m 2 : ZMod 16)
      else if d = 3 then 8 * (Nat.choose m 3 : ZMod 16)
      else 0 := by
  rw [one_add_2X_pow]
  have hC : ∀ (c : ZMod 16) (p : ℕ),
      PowerSeries.coeff d ((PowerSeries.C c) * PowerSeries.X ^ p) = if d = p then c else 0 := by
    intro c p
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have h1 : (2 * (m : PowerSeries (ZMod 16))) = PowerSeries.C (2 * (m : ZMod 16)) := by
    rw [map_mul, map_natCast, map_ofNat]
  have h2 : (4 * ((Nat.choose m 2 : ℕ) : PowerSeries (ZMod 16))) =
      PowerSeries.C (4 * (Nat.choose m 2 : ZMod 16)) := by
    rw [map_mul, map_natCast, map_ofNat]
  have h3 : (8 * ((Nat.choose m 3 : ℕ) : PowerSeries (ZMod 16))) =
      PowerSeries.C (8 * (Nat.choose m 3 : ZMod 16)) := by
    rw [map_mul, map_natCast, map_ofNat]
  rw [h1, h2, h3, map_add, map_add, map_add, PowerSeries.coeff_one,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X, hC, hC]
  rcases d with _ | _ | _ | _ | d' <;> simp

private lemma choose3_mod2_periodic (z : ℕ) :
    Nat.choose (z + 4) 3 % 2 = Nat.choose z 3 % 2 := by
  have h6 : ∀ m : ℕ, 6 * Nat.choose m 3 = m * (m - 1) * (m - 2) := by
    intro m
    have := Nat.descFactorial_eq_factorial_mul_choose m 3
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.sub_zero, mul_one] at this
    norm_num at this
    linarith
  rcases z with _ | _ | z'
  · decide
  · decide
  · have ha := h6 (z' + 6)
    have hb := h6 (z' + 2)
    have hdiff : 6 * Nat.choose (z' + 6) 3 = 6 * Nat.choose (z' + 2) 3 + 12 * (z' ^ 2 + 6 * z' + 10) := by
      have h1 : (z' + 6) * (z' + 6 - 1) * (z' + 6 - 2) =
          (z' + 2) * (z' + 2 - 1) * (z' + 2 - 2) + 12 * (z' ^ 2 + 6 * z' + 10) := by
        rw [show z' + 6 - 1 = z' + 5 by omega, show z' + 6 - 2 = z' + 4 by omega,
            show z' + 2 - 1 = z' + 1 by omega, show z' + 2 - 2 = z' by omega]
        ring
      omega
    have h2 : Nat.choose (z' + 6) 3 = Nat.choose (z' + 2) 3 + 2 * (z' ^ 2 + 6 * z' + 10) := by omega
    rw [show z' + 1 + 1 + 4 = z' + 6 by omega, show z' + 1 + 1 = z' + 2 by omega, h2]
    omega

private lemma choose3_mod2_eq (z : ℕ) :
    Nat.choose z 3 % 2 = Nat.choose (z % 4) 3 % 2 := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
    by_cases hz : z < 4
    · rw [Nat.mod_eq_of_lt hz]
    · have h1 := choose3_mod2_periodic (z - 4)
      rw [show z - 4 + 4 = z by omega] at h1
      rw [h1, ih (z - 4) (by omega), show (z - 4) % 4 = z % 4 by omega]

private lemma choose2_mod4_periodic (z : ℕ) :
    Nat.choose (z + 8) 2 % 4 = Nat.choose z 2 % 4 := by
  have h1 : Nat.choose (z + 8) 2 = Nat.choose z 2 + 8 * z + 28 := by
    have h2 : ∀ m : ℕ, 2 * Nat.choose m 2 = m * (m - 1) := by
      intro m; rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
    have ha := h2 (z + 8)
    have hb := h2 z
    cases z with
    | zero => decide
    | succ z' =>
      have hprod : (z' + 1 + 8) * (z' + 1 + 8 - 1) = (z' + 1) * (z' + 1 - 1) + 2 * (8 * (z' + 1) + 28) := by
        rw [show z' + 1 + 8 - 1 = z' + 8 by omega, show z' + 1 - 1 = z' by omega]; ring
      omega
  omega

private lemma choose2_mod4_eq (z : ℕ) :
    Nat.choose z 2 % 4 = Nat.choose (z % 8) 2 % 4 := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
    by_cases hz : z < 8
    · rw [Nat.mod_eq_of_lt hz]
    · have h1 := choose2_mod4_periodic (z - 8)
      rw [show z - 8 + 8 = z by omega] at h1
      rw [h1, ih (z - 8) (by omega), show (z - 8) % 8 = z % 8 by omega]

private lemma poly_sum_mod16 (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.range (k + 1),
      PowerSeries.coeff k
        (PowerSeries.X ^ n * (1 + 2 * PowerSeries.X) ^ (n * (n - 1) / 2) +
          (-PowerSeries.X) ^ n * (1 + 2 * PowerSeries.X) ^ (n * (n + 1) / 2))) =
      if k < 3 ∨ k % 4 = 2 then (0 : ZMod 16) else 8 := by
  have hterm : ∀ n ∈ Finset.range (k + 1),
      PowerSeries.coeff k
        (PowerSeries.X ^ n * (1 + 2 * PowerSeries.X) ^ (n * (n - 1) / 2) +
          (-PowerSeries.X) ^ n * (1 + 2 * PowerSeries.X) ^ (n * (n + 1) / 2)) =
      PowerSeries.coeff (k - n) ((1 + 2 * PowerSeries.X) ^ (n * (n - 1) / 2)) +
      (-1 : ZMod 16) ^ n * PowerSeries.coeff (k - n) ((1 + 2 * PowerSeries.X) ^ (n * (n + 1) / 2)) := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [map_add, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
    have hneg : (-PowerSeries.X : PowerSeries (ZMod 16)) ^ n =
        PowerSeries.C ((-1 : ZMod 16) ^ n) * PowerSeries.X ^ n := by
      rw [neg_eq_neg_one_mul, mul_pow, ← map_one PowerSeries.C, ← map_neg, ← map_pow]
    rw [hneg, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
  rw [Finset.sum_congr rfl hterm]
  have hzero : ∀ n ∈ Finset.range (k + 1), 4 ≤ k - n →
      PowerSeries.coeff (k - n) ((1 + 2 * PowerSeries.X) ^ (n * (n - 1) / 2)) +
      (-1 : ZMod 16) ^ n * PowerSeries.coeff (k - n) ((1 + 2 * PowerSeries.X) ^ (n * (n + 1) / 2)) = 0 := by
    intro n _ h4
    rw [coeff_one_add_2X_pow, coeff_one_add_2X_pow]
    simp [show k - n ≠ 0 by omega, show k - n ≠ 1 by omega,
          show k - n ≠ 2 by omega, show k - n ≠ 3 by omega]
  rcases k with _ | _ | _ | k'
  · omega
  · simp [Finset.sum_range_succ, coeff_one_add_2X_pow]
  · simp [Finset.sum_range_succ, coeff_one_add_2X_pow]; decide
  · set K := k' + 3
    have hsub : (∑ n ∈ Finset.range (K + 1),
        (PowerSeries.coeff (K - n) ((1 + 2 * PowerSeries.X) ^ (n * (n - 1) / 2)) +
         (-1 : ZMod 16) ^ n * PowerSeries.coeff (K - n) ((1 + 2 * PowerSeries.X) ^ (n * (n + 1) / 2)))) =
      ∑ d ∈ Finset.range 4,
        (PowerSeries.coeff d ((1 + 2 * PowerSeries.X) ^ ((K - d) * (K - d - 1) / 2)) +
         (-1 : ZMod 16) ^ (K - d) * PowerSeries.coeff d ((1 + 2 * PowerSeries.X) ^ ((K - d) * (K - d + 1) / 2))) := by
      rw [show K + 1 = (K - 3) + 4 by omega, Finset.sum_range_add]
      have hpre : ∑ n ∈ Finset.range (K - 3),
          (PowerSeries.coeff (K - n) ((1 + 2 * PowerSeries.X) ^ (n * (n - 1) / 2)) +
           (-1 : ZMod 16) ^ n * PowerSeries.coeff (K - n) ((1 + 2 * PowerSeries.X) ^ (n * (n + 1) / 2))) = 0 := by
        refine Finset.sum_eq_zero fun n hn => hzero n (Finset.mem_range.mpr (by rw [Finset.mem_range] at hn; omega))
          (by rw [Finset.mem_range] at hn; omega)
      rw [hpre, zero_add]
      refine Finset.sum_bij (fun i _ => 3 - i) ?_ ?_ ?_ ?_
      · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
      · intro i1 h1 i2 h2 heq; rw [Finset.mem_range] at h1 h2; omega
      · intro d hd; rw [Finset.mem_range] at hd; exact ⟨3 - d, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i hi; rw [Finset.mem_range] at hi
        rw [show K - (K - 3 + i) = 3 - i by omega, show K - (3 - i) = K - 3 + i by omega]
    rw [hsub, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [coeff_one_add_2X_pow, Nat.sub_zero, ↓reduceIte,
      show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
      show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega]
    -- Reduce every term via periodic mod-16 shift on K!
    have htri_shift : ∀ a : ℕ, ((a + 16) * (a + 16 - 1) / 2) % 8 = (a * (a - 1) / 2) % 8 := by
      intro a
      cases a with
      | zero => decide
      | succ a' =>
        have h1 : (a' + 1 + 16) * (a' + 1 + 16 - 1) = (a' + 1) * a' + 2 * (8 * (2 * a' + 17)) := by
          rw [show a' + 1 + 16 - 1 = a' + 16 by omega]; ring
        rw [Nat.add_sub_cancel, h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.add_mul_mod_self_left]
    have hTri_shift : ∀ a : ℕ, ((a + 16) * (a + 16 + 1) / 2) % 8 = (a * (a + 1) / 2) % 8 := by
      intro a
      have h1 : (a + 16) * (a + 16 + 1) = a * (a + 1) + 2 * (8 * (2 * a + 17)) := by ring
      rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.add_mul_mod_self_left]
    have h2m : ∀ m : ℕ, (2 : ZMod 16) * (m : ZMod 16) = 2 * ((m % 8 : ℕ) : ZMod 16) := by
      intro m
      have hq : (m : ZMod 16) = 8 * ((m / 8 : ℕ) : ZMod 16) + ((m % 8 : ℕ) : ZMod 16) := by
        have := congrArg (Nat.cast (R := ZMod 16)) (Nat.div_add_mod m 8).symm
        simpa [Nat.cast_add, Nat.cast_mul] using this
      rw [hq, mul_add, ← mul_assoc]
      have h16z : (2 : ZMod 16) * 8 = 0 := by decide
      rw [h16z, zero_mul, zero_add]
    have h4m : ∀ m : ℕ, (4 : ZMod 16) * (Nat.choose m 2 : ZMod 16) =
        4 * ((Nat.choose (m % 8) 2 % 4 : ℕ) : ZMod 16) := by
      intro m
      have hq : (Nat.choose m 2 : ZMod 16) =
          4 * ((Nat.choose m 2 / 4 : ℕ) : ZMod 16) + ((Nat.choose m 2 % 4 : ℕ) : ZMod 16) := by
        have := congrArg (Nat.cast (R := ZMod 16)) (Nat.div_add_mod (Nat.choose m 2) 4).symm
        simpa [Nat.cast_add, Nat.cast_mul] using this
      rw [hq, mul_add, ← mul_assoc]
      have h16z : (4 : ZMod 16) * 4 = 0 := by decide
      rw [h16z, zero_mul, zero_add, choose2_mod4_eq]
    have h8m : ∀ m : ℕ, (8 : ZMod 16) * (Nat.choose m 3 : ZMod 16) =
        8 * ((Nat.choose (m % 4) 3 % 2 : ℕ) : ZMod 16) := by
      intro m
      have hq : (Nat.choose m 3 : ZMod 16) =
          2 * ((Nat.choose m 3 / 2 : ℕ) : ZMod 16) + ((Nat.choose m 3 % 2 : ℕ) : ZMod 16) := by
        have := congrArg (Nat.cast (R := ZMod 16)) (Nat.div_add_mod (Nat.choose m 3) 2).symm
        simpa [Nat.cast_add, Nat.cast_mul] using this
      rw [hq, mul_add, ← mul_assoc]
      have h16z : (8 : ZMod 16) * 2 = 0 := by decide
      rw [h16z, zero_mul, zero_add, choose3_mod2_eq]
    have hneg_pow : ∀ m : ℕ, (-1 : ZMod 16) ^ m = if m % 2 = 0 then 1 else -1 := by
      intro m
      have hsq1 : (-1 : ZMod 16) ^ 2 = 1 := by decide
      rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [if_pos (by omega), show j + j = 2 * j by omega, pow_mul, hsq1, one_pow]
      · rw [if_neg (by omega), pow_succ, pow_mul, hsq1, one_pow, one_mul]
    have htri_mod : ∀ a : ℕ, (a * (a - 1) / 2) % 8 = ((a % 16) * ((a % 16) - 1) / 2) % 8 := by
      intro a
      induction a using Nat.strong_induction_on with
      | h a iha =>
        by_cases ha : a < 16
        · rw [Nat.mod_eq_of_lt ha]
        · have h1 := htri_shift (a - 16)
          rw [show a - 16 + 16 = a by omega] at h1
          rw [h1, iha (a - 16) (by omega), show (a - 16) % 16 = a % 16 by omega]
    have hTri_mod : ∀ a : ℕ, (a * (a + 1) / 2) % 8 = ((a % 16) * ((a % 16) + 1) / 2) % 8 := by
      intro a
      induction a using Nat.strong_induction_on with
      | h a iha =>
        by_cases ha : a < 16
        · rw [Nat.mod_eq_of_lt ha]
        · have h1 := hTri_shift (a - 16)
          rw [show a - 16 + 16 = a by omega] at h1
          rw [h1, iha (a - 16) (by omega), show (a - 16) % 16 = a % 16 by omega]
    have htri_mod4 : ∀ a : ℕ, (a * (a - 1) / 2) % 4 = ((a % 16) * ((a % 16) - 1) / 2) % 4 := by
      intro a; have := htri_mod a; omega
    have hTri_mod4 : ∀ a : ℕ, (a * (a + 1) / 2) % 4 = ((a % 16) * ((a % 16) + 1) / 2) % 4 := by
      intro a; have := hTri_mod a; omega
    rw [h2m ((K - 1) * (K - 1 - 1) / 2), h2m ((K - 1) * (K - 1 + 1) / 2),
        h4m ((K - 2) * (K - 2 - 1) / 2), h4m ((K - 2) * (K - 2 + 1) / 2),
        h8m ((K - 3) * (K - 3 - 1) / 2), h8m ((K - 3) * (K - 3 + 1) / 2),
        htri_mod (K - 1), hTri_mod (K - 1), htri_mod (K - 2), hTri_mod (K - 2),
        htri_mod4 (K - 3), hTri_mod4 (K - 3),
        hneg_pow K, hneg_pow (K - 1), hneg_pow (K - 2), hneg_pow (K - 3)]
    have hK3 : ¬ K < 3 := by omega
    simp only [hK3, false_or]
    have hK1 : (K - 1) % 16 = (K % 16 + 15) % 16 := by omega
    have hK2 : (K - 2) % 16 = (K % 16 + 14) % 16 := by omega
    have hK3m : (K - 3) % 16 = (K % 16 + 13) % 16 := by omega
    have hK1p : (K - 1) % 2 = (K % 16 + 15) % 2 := by omega
    have hK2p : (K - 2) % 2 = (K % 16 + 14) % 2 := by omega
    have hK3p : (K - 3) % 2 = (K % 16 + 13) % 2 := by omega
    have hKp : K % 2 = (K % 16) % 2 := by omega
    have hK4 : K % 4 = (K % 16) % 4 := by omega
    rw [hK1, hK2, hK3m, hK1p, hK2p, hK3p, hKp, hK4]
    have hlt : K % 16 < 16 := Nat.mod_lt K (by decide)
    generalize K % 16 = r at hlt
    interval_cases r <;> decide

private lemma u_sum_mod16 (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.range (k + 1),
      PowerSeries.coeff k
        (PowerSeries.X ^ n * (8 * ((n * (n - 1) / 2 : ℕ) : PowerSeries (ZMod 16)) * u) +
          (-PowerSeries.X) ^ n * (8 * ((n * (n + 1) / 2 : ℕ) : PowerSeries (ZMod 16)) * u))) =
      if k < 3 ∨ k % 4 = 2 then (0 : ZMod 16) else 8 := by
  have hterm : ∀ n ∈ Finset.range (k + 1),
      PowerSeries.coeff k
        (PowerSeries.X ^ n * (8 * ((n * (n - 1) / 2 : ℕ) : PowerSeries (ZMod 16)) * u) +
          (-PowerSeries.X) ^ n * (8 * ((n * (n + 1) / 2 : ℕ) : PowerSeries (ZMod 16)) * u)) =
      if n % 2 = 1 then (8 : ZMod 16) * PowerSeries.coeff (k - n) u else 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [map_add]
    have hC1 : (8 * ((n * (n - 1) / 2 : ℕ) : PowerSeries (ZMod 16))) =
        PowerSeries.C ((8 : ZMod 16) * ((n * (n - 1) / 2 : ℕ) : ZMod 16)) := by
      rw [map_mul, map_natCast, map_ofNat]
    have hC2 : (8 * ((n * (n + 1) / 2 : ℕ) : PowerSeries (ZMod 16))) =
        PowerSeries.C ((8 : ZMod 16) * ((n * (n + 1) / 2 : ℕ) : ZMod 16)) := by
      rw [map_mul, map_natCast, map_ofNat]
    have hneg : (-PowerSeries.X : PowerSeries (ZMod 16)) ^ n =
        PowerSeries.C ((-1 : ZMod 16) ^ n) * PowerSeries.X ^ n := by
      rw [neg_eq_neg_one_mul, mul_pow, ← map_one PowerSeries.C, ← map_neg, ← map_pow]
    rw [hC1, hC2, hneg, PowerSeries.coeff_X_pow_mul', if_pos (by omega), PowerSeries.coeff_C_mul,
        mul_assoc (PowerSeries.C ((-1 : ZMod 16) ^ n)), PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow_mul', if_pos (by omega), PowerSeries.coeff_C_mul]
    have h8neg : ∀ x : ZMod 16, (-1 : ZMod 16) ^ n * (8 * x) = 8 * x := by
      intro x
      have hsq1 : (-1 : ZMod 16) ^ 2 = 1 := by decide
      rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have h1 : (-1 : ZMod 16) ^ (j + j) = 1 := by
          rw [show j + j = 2 * j by omega, pow_mul, hsq1, one_pow]
        rw [h1, one_mul]
      · have h1 : (-1 : ZMod 16) ^ (2 * j + 1) = -1 := by
          rw [pow_succ, pow_mul, hsq1, one_pow, one_mul]
        rw [h1]; revert x; decide
    rw [mul_assoc (8 : ZMod 16), mul_assoc (8 : ZMod 16), h8neg, ← mul_assoc, ← mul_assoc,
        ← add_mul, ← mul_add, ← Nat.cast_add]
    have hsum_tri : n * (n - 1) / 2 + n * (n + 1) / 2 = n * n := by
      cases n with
      | zero => simp
      | succ n' =>
        simp only [Nat.add_sub_cancel]
        have he1 : 2 ∣ (n' + 1) * n' := (Nat.even_mul_pred_self (n' + 1)).two_dvd
        have he2 : 2 ∣ (n' + 1) * (n' + 1 + 1) := by
          rcases Nat.even_or_odd n' with ⟨j, rfl⟩ | ⟨j, rfl⟩
          · exact ⟨(j + j + 1) * (j + 1), by ring⟩
          · exact ⟨(j + 1) * (2 * j + 3), by ring⟩
        rcases he1 with ⟨a, ha⟩
        rcases he2 with ⟨b, hb⟩
        rw [ha, hb, Nat.mul_div_cancel_left _ (by decide), Nat.mul_div_cancel_left _ (by decide)]
        nlinarith
    rw [hsum_tri]
    have h8n : (8 : ZMod 16) * ((n * n : ℕ) : ZMod 16) = if n % 2 = 1 then 8 else 0 := by
      have hq : ((n * n : ℕ) : ZMod 16) =
          2 * (((n * n) / 2 : ℕ) : ZMod 16) + (((n * n) % 2 : ℕ) : ZMod 16) := by
        have := congrArg (Nat.cast (R := ZMod 16)) (Nat.div_add_mod (n * n) 2).symm
        simpa [Nat.cast_add, Nat.cast_mul] using this
      rw [hq, mul_add, ← mul_assoc]
      have h16z : (8 : ZMod 16) * 2 = 0 := by decide
      rw [h16z, zero_mul, zero_add]
      by_cases hodd : n % 2 = 1
      · rw [if_pos hodd, show (n * n) % 2 = 1 by rw [Nat.mul_mod, hodd]]; simp
      · rw [if_neg hodd, show (n * n) % 2 = 0 by rw [Nat.mul_mod, show n % 2 = 0 by omega]]; simp
    rw [h8n]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  rcases k with _ | _ | _ | k'
  · omega
  · simp [Finset.sum_range_succ, coeff_u]
  · simp [Finset.sum_range_succ, coeff_u]
  · set K := k' + 3
    have hK3 : ¬ K < 3 := by omega
    simp only [hK3, false_or]
    by_cases hKodd : K % 2 = 1
    · -- K is odd ≥ 3: only n = K - 2 (which is odd!) gives coeff 2 u = 1;
      -- for all other odd n, K - n is even ≠ 2 so coeff (K - n) u = 0!
      rw [if_neg (by omega : K % 4 ≠ 2)]
      rw [Finset.sum_eq_single (K - 2)]
      · rw [if_pos (by omega : (K - 2) % 2 = 1), show K - (K - 2) = 2 by omega,
            coeff_u, if_pos (Or.inl rfl), mul_one]
      · intro n hn hne
        rw [Finset.mem_range] at hn
        split_ifs with hno
        · rw [coeff_u, if_neg (by omega), mul_zero]
        · rfl
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · -- K is even ≥ 4: write K = 2 * r with r ≥ 2.
      -- For odd n ≤ K, K - n is odd; coeff (K - n) u = 1 iff K - n ≥ 3, i.e., n ≤ K - 3!
      -- The odd numbers in [0, K - 3] are 2*j + 1 for j ∈ range (K / 2 - 1), count = K / 2 - 1.
      have hKeven : K % 2 = 0 := by omega
      have hK4 : 4 ≤ K := by omega
      have hsum_cnt : (∑ n ∈ Finset.range (K + 1),
          if n % 2 = 1 then (8 : ZMod 16) * PowerSeries.coeff (K - n) u else 0) =
          ∑ _j ∈ Finset.range (K / 2 - 1), (8 : ZMod 16) := by
        rw [show K + 1 = (K - 1) + 2 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
        rw [if_neg (by omega : (K - 1 + 1) % 2 ≠ 1), add_zero,
            if_pos (by omega : (K - 1) % 2 = 1), show K - (K - 1) = 1 by omega,
            coeff_u, if_neg (by omega), mul_zero, add_zero]
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun n _ => n / 2) ?_ ?_ ?_ ?_
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          omega
        · intro n1 h1 n2 h2 heq
          simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
          omega
        · intro j hj
          rw [Finset.mem_range] at hj
          refine ⟨2 * j + 1, ?_, by omega⟩
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn
          rw [coeff_u, if_pos (Or.inr ⟨by omega, by omega⟩), mul_one]
      rw [hsum_cnt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hq : ((K / 2 - 1 : ℕ) : ZMod 16) =
          2 * (((K / 2 - 1) / 2 : ℕ) : ZMod 16) + (((K / 2 - 1) % 2 : ℕ) : ZMod 16) := by
        have := congrArg (Nat.cast (R := ZMod 16)) (Nat.div_add_mod (K / 2 - 1) 2).symm
        simpa [Nat.cast_add, Nat.cast_mul] using this
      rw [hq, add_mul, mul_assoc, mul_comm _ (8 : ZMod 16), ← mul_assoc]
      have h16z : (2 : ZMod 16) * 8 = 0 := by decide
      rw [h16z, zero_mul, zero_add]
      by_cases hm4 : K % 4 = 2
      · rw [if_pos hm4, show (K / 2 - 1) % 2 = 0 by omega]; simp
      · rw [if_neg hm4, show (K / 2 - 1) % 2 = 1 by omega]; simp

theorem solution : type_of% @OMA.S_oeis_a337912.main := by
  intro A hA0 hEq
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 16) := PowerSeries.map (Int.castRingHom (ZMod 16))
  let a16 : PowerSeries (ZMod 16) := φ A
  have ha16_0 : PowerSeries.constantCoeff a16 = 1 := by
    dsimp only [a16, φ]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  have ha16_eq : ∀ k : ℕ, 1 ≤ k →
      (∑ n ∈ Finset.range (k + 1),
        PowerSeries.coeff k
          (PowerSeries.X ^ n * a16 ^ (n * (n - 1) / 2) +
            (-PowerSeries.X) ^ n * a16 ^ (n * (n + 1) / 2))) = 0 := by
    intro k hk
    have h := congrArg (Int.castRingHom (ZMod 16)) (hEq k)
    rw [if_neg (by omega), map_zero, map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hmap : φ (PowerSeries.X ^ n * A ^ (n * (n - 1) / 2) +
        (-PowerSeries.X) ^ n * A ^ (n * (n + 1) / 2)) =
        PowerSeries.X ^ n * a16 ^ (n * (n - 1) / 2) +
          (-PowerSeries.X) ^ n * a16 ^ (n * (n + 1) / 2) := by
      dsimp only [a16, φ]
      simp only [map_add, map_mul, map_pow, map_neg, PowerSeries.map_X]
    rw [← hmap, PowerSeries.coeff_map]
  have hA0_eq : ∀ k : ℕ, 1 ≤ k →
      (∑ n ∈ Finset.range (k + 1),
        PowerSeries.coeff k
          (PowerSeries.X ^ n * A0 ^ (n * (n - 1) / 2) +
            (-PowerSeries.X) ^ n * A0 ^ (n * (n + 1) / 2))) = 0 := by
    intro k hk
    have hsplit : ∀ n ∈ Finset.range (k + 1),
        PowerSeries.coeff k
          (PowerSeries.X ^ n * A0 ^ (n * (n - 1) / 2) +
            (-PowerSeries.X) ^ n * A0 ^ (n * (n + 1) / 2)) =
        PowerSeries.coeff k
          (PowerSeries.X ^ n * (1 + 2 * PowerSeries.X) ^ (n * (n - 1) / 2) +
            (-PowerSeries.X) ^ n * (1 + 2 * PowerSeries.X) ^ (n * (n + 1) / 2)) +
        PowerSeries.coeff k
          (PowerSeries.X ^ n * (8 * ((n * (n - 1) / 2 : ℕ) : PowerSeries (ZMod 16)) * u) +
            (-PowerSeries.X) ^ n * (8 * ((n * (n + 1) / 2 : ℕ) : PowerSeries (ZMod 16)) * u)) := by
      intro n _
      rw [A0_pow, A0_pow, ← map_add]
      congr 1; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, poly_sum_mod16 k hk, u_sum_mod16 k hk]
    split_ifs <;> decide
  -- Strong induction: coeff m a16 = coeff m A0 for all m!
  have hpow_congr : ∀ {f g : PowerSeries (ZMod 16)} {M : ℕ},
      (∀ j ≤ M, PowerSeries.coeff j f = PowerSeries.coeff j g) →
      ∀ e j, j ≤ M → PowerSeries.coeff j (f ^ e) = PowerSeries.coeff j (g ^ e) := by
    intro f g M hfg e
    induction e with
    | zero => intro j _; simp
    | succ e ihe =>
      intro j hj
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [ihe p.1 (by omega), hfg p.2 (by omega)]
  have ha16_eq_A0 : a16 = A0 := by
    ext m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff, ha16_0, A0_const]
      | succ m' =>
        set k := m' + 2
        have h1 := ha16_eq k (by omega)
        have h2 := hA0_eq k (by omega)
        rw [← h2] at h1
        -- Split n = 0, n = 1, and n ≥ 2 in Finset.range (k + 1)!
        rw [show k + 1 = (m' + 1) + 2 by omega] at h1
        conv_lhs at h1 => rw [Finset.sum_range_succ', Finset.sum_range_succ']
        conv_rhs at h1 => rw [Finset.sum_range_succ', Finset.sum_range_succ']
        have htail :
            (∑ n ∈ Finset.range (m' + 1),
              PowerSeries.coeff k
                (PowerSeries.X ^ (n + 2) * a16 ^ ((n + 2) * (n + 2 - 1) / 2) +
                  (-PowerSeries.X) ^ (n + 2) * a16 ^ ((n + 2) * (n + 2 + 1) / 2))) =
            ∑ n ∈ Finset.range (m' + 1),
              PowerSeries.coeff k
                (PowerSeries.X ^ (n + 2) * A0 ^ ((n + 2) * (n + 2 - 1) / 2) +
                  (-PowerSeries.X) ^ (n + 2) * A0 ^ ((n + 2) * (n + 2 + 1) / 2)) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_range] at hn
          have hneg : ∀ (f : PowerSeries (ZMod 16)),
              (-PowerSeries.X : PowerSeries (ZMod 16)) ^ (n + 2) * f =
              PowerSeries.C ((-1 : ZMod 16) ^ (n + 2)) * (PowerSeries.X ^ (n + 2) * f) := by
            intro f
            rw [neg_eq_neg_one_mul, mul_pow, ← map_one PowerSeries.C, ← map_neg, ← map_pow, mul_assoc]
          rw [map_add, map_add, hneg, hneg, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
              PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
              if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
          have hagree : ∀ j ≤ m', PowerSeries.coeff j a16 = PowerSeries.coeff j A0 :=
            fun j hj => ih j (by omega)
          rw [hpow_congr hagree _ (k - (n + 2)) (by omega),
              hpow_congr hagree _ (k - (n + 2)) (by omega)]
        rw [htail] at h1
        have h0a : PowerSeries.coeff k (PowerSeries.X ^ 0 * a16 ^ (0 * (0 - 1) / 2) +
            (-PowerSeries.X) ^ 0 * a16 ^ (0 * (0 + 1) / 2)) = 0 := by
          simp [PowerSeries.coeff_one, show k ≠ 0 by omega]
        have h0b : PowerSeries.coeff k (PowerSeries.X ^ 0 * A0 ^ (0 * (0 - 1) / 2) +
            (-PowerSeries.X) ^ 0 * A0 ^ (0 * (0 + 1) / 2)) = 0 := by
          simp [PowerSeries.coeff_one, show k ≠ 0 by omega]
        rw [h0a, h0b, add_zero, add_zero] at h1
        have h1a : PowerSeries.coeff k (PowerSeries.X ^ 1 * a16 ^ (1 * (1 - 1) / 2) +
            (-PowerSeries.X) ^ 1 * a16 ^ (1 * (1 + 1) / 2)) = -PowerSeries.coeff (m' + 1) a16 := by
          simp only [Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, mul_one, pow_one,
            show 1 * (1 + 1) / 2 = 1 by decide, map_add, PowerSeries.coeff_X,
            show k ≠ 1 by omega, ↓reduceIte, zero_add, neg_mul, map_neg]
          rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 16)), PowerSeries.coeff_X_pow_mul',
              if_pos (by omega), show k - 1 = m' + 1 by omega]
        have h1b : PowerSeries.coeff k (PowerSeries.X ^ 1 * A0 ^ (1 * (1 - 1) / 2) +
            (-PowerSeries.X) ^ 1 * A0 ^ (1 * (1 + 1) / 2)) = -PowerSeries.coeff (m' + 1) A0 := by
          simp only [Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, mul_one, pow_one,
            show 1 * (1 + 1) / 2 = 1 by decide, map_add, PowerSeries.coeff_X,
            show k ≠ 1 by omega, ↓reduceIte, zero_add, neg_mul, map_neg]
          rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 16)), PowerSeries.coeff_X_pow_mul',
              if_pos (by omega), show k - 1 = m' + 1 by omega]
        rw [h1a, h1b] at h1
        exact neg_inj.mp (add_left_cancel h1)
  constructor
  · intro n hn
    have h0 : ((PowerSeries.coeff (2 * n) A : ℤ) : ZMod 16) = 0 := by
      have h1 : ((PowerSeries.coeff (2 * n) A : ℤ) : ZMod 16) = PowerSeries.coeff (2 * n) A0 := by
        rw [← ha16_eq_A0]; dsimp only [a16, φ]; rw [PowerSeries.coeff_map]; rfl
      rw [h1, A0, map_add, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
          show (2 : PowerSeries (ZMod 16)) = PowerSeries.C 2 by rw [map_ofNat], PowerSeries.coeff_C_mul,
          PowerSeries.coeff_X, if_neg (by omega), mul_zero, zero_add,
          show (8 : PowerSeries (ZMod 16)) = PowerSeries.C 8 by rw [map_ofNat], PowerSeries.coeff_C_mul,
          coeff_u, if_neg (by omega), mul_zero]
    have hdvd : ((16 : ℕ) : ℤ) ∣ PowerSeries.coeff (2 * n) A :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp h0
    rcases hdvd with ⟨q, hq⟩
    norm_num at hq; omega
  · intro n hn
    have h8 : ((PowerSeries.coeff (2 * n + 1) A : ℤ) : ZMod 16) = 8 := by
      have h1 : ((PowerSeries.coeff (2 * n + 1) A : ℤ) : ZMod 16) = PowerSeries.coeff (2 * n + 1) A0 := by
        rw [← ha16_eq_A0]; dsimp only [a16, φ]; rw [PowerSeries.coeff_map]; rfl
      rw [h1, A0, map_add, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
          show (2 : PowerSeries (ZMod 16)) = PowerSeries.C 2 by rw [map_ofNat], PowerSeries.coeff_C_mul,
          PowerSeries.coeff_X, if_neg (by omega), mul_zero, zero_add,
          show (8 : PowerSeries (ZMod 16)) = PowerSeries.C 8 by rw [map_ofNat], PowerSeries.coeff_C_mul,
          coeff_u, if_pos (Or.inr ⟨by omega, by omega⟩), mul_one]
    have hdvd : ((16 : ℕ) : ℤ) ∣ PowerSeries.coeff (2 * n + 1) A - 8 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast; rw [h8]; decide
    rcases hdvd with ⟨q, hq⟩
    norm_num at hq; omega

end OMA.P_oeis_a337912

theorem OMA.solution : type_of% @OMA.S_oeis_a337912.main := OMA.P_oeis_a337912.solution
