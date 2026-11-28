import OMAStatements.S_oeis_a371710
import Mathlib

namespace OMA.S_oeis_a371710

private noncomputable def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (f n : ℚ) / (Nat.factorial n : ℚ))

private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f k * g (n - k)

private lemma egf_mul (f g : ℕ → ℤ) : egf f * egf g = egf (hmul f g) := by
  ext n
  simp only [egf, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j =>
      ((f i : ℚ) / (Nat.factorial i : ℚ)) * ((g j : ℚ) / (Nat.factorial j : ℚ))) n]
  simp only [hmul, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hch : (Nat.choose n k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) =
      (Nat.factorial n : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfnk : (Nat.factorial (n - k) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hfk, hfnk, hfn]
  rw [← hch]; ring

private lemma egf_add (f g : ℕ → ℤ) : egf f + egf g = egf (fun n => f n + g n) := by
  ext n
  simp only [egf, map_add, PowerSeries.coeff_mk, Int.cast_add, add_div]

private lemma egf_sub (f g : ℕ → ℤ) : egf f - egf g = egf (fun n => f n - g n) := by
  ext n
  simp only [egf, map_sub, PowerSeries.coeff_mk, Int.cast_sub, sub_div]

private lemma egf_X_mul (f : ℕ → ℤ) :
    PowerSeries.X * egf f = egf (fun n => if n = 0 then 0 else (n : ℤ) * f (n - 1)) := by
  ext n
  cases n with
  | zero =>
    simp [egf, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [egf, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, Nat.succ_ne_zero,
      ↓reduceIte, Nat.add_sub_cancel, Int.cast_mul, Int.cast_natCast, Nat.factorial_succ,
      Nat.cast_mul]
    have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp [h1, h2]

private lemma egf_deriv (f : ℕ → ℤ) :
    PowerSeries.derivative ℚ (egf f) = egf (fun n => f (n + 1)) := by
  ext n
  simp only [egf, PowerSeries.coeff_derivative, PowerSeries.coeff_mk, Nat.factorial_succ,
    Nat.cast_mul]
  have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [h1, h2]
  push_cast; ring

private lemma egf_inj {f g : ℕ → ℤ} (h : egf f = egf g) : f = g := by
  funext n
  have hc := congr_arg (PowerSeries.coeff n) h
  simp only [egf, PowerSeries.coeff_mk] at hc
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hq : (f n : ℚ) = (g n : ℚ) := (div_left_inj' hfn).mp hc
  exact_mod_cast hq

private def hdivpow (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | m + 1, n + 1 =>
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)

private lemma egf_hdivpow (f : ℕ → ℤ) (hf0 : f 0 = 0) :
    ∀ m : ℕ, (1 / (Nat.factorial m : ℚ)) • (egf f) ^ m = egf (hdivpow f m) := by
  intro m
  induction m with
  | zero =>
    ext n
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_smul, egf,
      PowerSeries.coeff_one, PowerSeries.coeff_mk, hdivpow]
    split_ifs with h <;> simp [h]
  | succ m ih =>
    ext n
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_zero_eq_constantCoeff,
        map_pow, egf, PowerSeries.constantCoeff_mk, hf0, Int.cast_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, zero_pow (Nat.succ_ne_zero m), mul_zero, hdivpow]
    | succ n =>
      have hderiv : PowerSeries.derivative ℚ ((1 / (Nat.factorial (m + 1) : ℚ)) • (egf f) ^ (m + 1)) =
          egf (hmul (fun k => f (k + 1)) (hdivpow f m)) := by
        have hsmul : ∀ (c : ℚ) (F : PowerSeries ℚ),
            PowerSeries.derivative ℚ (c • F) = c • PowerSeries.derivative ℚ F := by
          intro c F; ext k
          simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, smul_eq_mul]; ring
        rw [hsmul, PowerSeries.derivative_pow, Nat.add_sub_cancel, ← smul_mul_assoc]
        have hsc : (1 / (Nat.factorial (m + 1) : ℚ)) • (((m + 1 : ℕ) : PowerSeries ℚ) * (egf f) ^ m) =
            (1 / (Nat.factorial m : ℚ)) • (egf f) ^ m := by
          ext k
          rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, ← nsmul_eq_mul, map_nsmul]
          simp only [smul_eq_mul, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul]
          have h1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
          have h2 : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
          field_simp [h1, h2]
        rw [hsc, ih, egf_deriv, egf_mul,
          show hmul (hdivpow f m) (fun k => f (k + 1)) = hmul (fun k => f (k + 1)) (hdivpow f m) from by
            funext r
            have := congr_arg (PowerSeries.coeff r) (mul_comm (egf (hdivpow f m)) (egf (fun k => f (k + 1))))
            rw [egf_mul, egf_mul] at this
            simp only [egf, PowerSeries.coeff_mk] at this
            have hfr : (Nat.factorial r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
            have hq : (hmul (hdivpow f m) (fun k => f (k + 1)) r : ℚ) =
                (hmul (fun k => f (k + 1)) (hdivpow f m) r : ℚ) := (div_left_inj' hfr).mp this
            exact_mod_cast hq]
      have hc := congr_arg (PowerSeries.coeff n) hderiv
      rw [PowerSeries.coeff_derivative] at hc
      simp only [egf, PowerSeries.coeff_mk, hmul] at hc
      simp only [egf, PowerSeries.coeff_mk, hdivpow]
      rw [Nat.factorial_succ n, Nat.cast_mul]
      have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hcast : ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hcast] at hc
      have hc' : PowerSeries.coeff (n + 1) ((1 / (Nat.factorial (m + 1) : ℚ)) •
            (PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)) ^ (m + 1)) =
          ((∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℤ) * f (x + 1) * hdivpow f m (n - x) : ℤ) : ℚ) /
            (((n + 1 : ℕ) : ℚ) * (Nat.factorial n : ℚ)) := by
        rw [eq_div_iff (mul_ne_zero h1 h2), ← mul_assoc, hc, div_mul_cancel₀ _ h2]
      exact hc'

private lemma egf_pow_eq (f : ℕ → ℤ) (hf0 : f 0 = 0) (m : ℕ) :
    (egf f) ^ m = egf (fun k => (Nat.factorial m : ℤ) * hdivpow f m k) := by
  have h := congr_arg ((Nat.factorial m : ℚ) • ·) (egf_hdivpow f hf0 m)
  have hfm : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [smul_smul, mul_one_div_cancel hfm, one_smul] at h
  rw [h]
  ext k
  simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk, Int.cast_mul,
    Int.cast_natCast]
  ring

private lemma hdivpow_congr_mod3 {f1 f2 : ℕ → ℤ} (h : ∀ k, f1 k % 3 = f2 k % 3) :
    ∀ m n : ℕ, hdivpow f1 m n % 3 = hdivpow f2 m n % 3 := by
  intro m
  induction m with
  | zero => intro n; simp [hdivpow]
  | succ m ih =>
    intro n
    cases n with
    | zero => simp [hdivpow]
    | succ n =>
      simp only [hdivpow]
      rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), h (k + 1), ih (n - k)]
      conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private lemma hmul_congr_mod3_le {f1 f2 g1 g2 : ℕ → ℤ} (n : ℕ)
    (hf : ∀ k ≤ n, f1 k % 3 = f2 k % 3) (hg : ∀ k ≤ n, g1 k % 3 = g2 k % 3) :
    hmul f1 g1 n % 3 = hmul f2 g2 n % 3 := by
  simp only [hmul]
  rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), hf k hkn, hg (n - k) (by omega)]
  conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private lemma hdivpow_neg_delta1 (m n : ℕ) :
    hdivpow (fun k => if k = 1 then -1 else 0) m n = if n = m then (-1 : ℤ) ^ m else 0 := by
  have hX : egf (fun k => if k = 1 then -1 else 0) = -PowerSeries.X := by
    ext k
    simp only [egf, PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_X]
    split_ifs with h <;> simp [h]
  have hdp := egf_hdivpow (fun k => if k = 1 then -1 else 0) (by simp) m
  rw [hX, neg_pow] at hdp
  have hrhs : (1 / (Nat.factorial m : ℚ)) • ((-1 : PowerSeries ℚ) ^ m * PowerSeries.X ^ m) =
      egf (fun k => if k = m then (-1 : ℤ) ^ m else 0) := by
    ext k
    simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk]
    have hneg : (-1 : PowerSeries ℚ) ^ m = ((-1 : ℤ) ^ m : ℚ) • (1 : PowerSeries ℚ) := by
      ext r
      simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one]
      have : (-1 : PowerSeries ℚ) ^ m = PowerSeries.C ((-1 : ℚ) ^ m) := by
        rw [map_pow, map_neg, map_one]
      rw [this, PowerSeries.coeff_C]
      split_ifs <;> push_cast <;> ring
    rw [hneg, smul_mul_assoc, one_mul, PowerSeries.coeff_smul, smul_eq_mul,
      PowerSeries.coeff_X_pow]
    split_ifs with hkm
    · subst hkm; push_cast; ring
    · simp
  rw [hrhs] at hdp
  exact congr_fun (egf_inj hdp.symm) n

-- Explicit mod-3 solution: f0(x) = 1 - e^{-x} + x * (e^x + e^{-x} - 2)
private def f0 (k : ℕ) : ℤ :=
  (if k = 0 then 1 else 0) - (-1 : ℤ) ^ k +
  (if k = 0 then 0 else (k : ℤ) * (1 + (-1 : ℤ) ^ (k - 1) - if k = 1 then 2 else 0))

private lemma hmul_exp_exp (c1 c2 : ℤ) (m : ℕ) :
    hmul (fun k => c1 ^ k) (fun k => c2 ^ k) m = (c1 + c2) ^ m := by
  simp only [hmul]
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma hmul_f0_f0_mod3 (m : ℕ) :
    hmul f0 f0 m % 3 = if 2 ≤ m ∧ Even m then 2 else 0 := by
  -- Express egf f0 = 1 - Em1 + X * (E1 + Em1 - 2)
  set E1 : PowerSeries ℚ := egf (fun _ => 1)
  set Em1 : PowerSeries ℚ := egf (fun k => (-1 : ℤ) ^ k)
  set E2 : PowerSeries ℚ := egf (fun k => (2 : ℤ) ^ k)
  set Em2 : PowerSeries ℚ := egf (fun k => (-2 : ℤ) ^ k)
  have h1 : (1 : PowerSeries ℚ) = egf (fun k => if k = 0 then 1 else 0) := by
    ext k; simp only [egf, PowerSeries.coeff_one, PowerSeries.coeff_mk]; split_ifs with h <;> simp [h]
  have hf0_egf : egf f0 = (1 - Em1) + PowerSeries.X * (E1 + Em1 - (2 : ℚ) • 1) := by
    have h2 : (2 : ℚ) • (1 : PowerSeries ℚ) = egf (fun k => if k = 0 then 2 else 0) := by
      ext k; simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one, egf,
        PowerSeries.coeff_mk]; split_ifs with h <;> simp [h]
    rw [h2, h1, egf_sub, egf_add, egf_sub, egf_X_mul, egf_add]
    congr 1
    funext k
    cases k with
    | zero => simp [f0]
    | succ k => simp [f0]
  have hE1Em1 : E1 * Em1 = 1 := by
    rw [egf_mul, h1]
    congr 1; funext k
    have := hmul_exp_exp 1 (-1) k
    simp only [one_pow, add_neg_cancel] at this
    rw [this]; cases k <;> simp
  have hE1E1 : E1 * E1 = E2 := by
    rw [egf_mul]; congr 1; funext k
    simpa [one_pow] using hmul_exp_exp 1 1 k
  have hEm1Em1 : Em1 * Em1 = Em2 := by
    rw [egf_mul]; congr 1; funext k
    simpa [show (-1 : ℤ) + (-1) = -2 by norm_num] using hmul_exp_exp (-1) (-1) k
  have hsmul_C : ∀ (c : ℚ) (F : PowerSeries ℚ), c • F = PowerSeries.C c * F := by
    intro c F; ext r; simp [PowerSeries.coeff_C_mul]
  have hsq : egf f0 * egf f0 =
      (1 - (2 : ℚ) • Em1 + Em2) +
      PowerSeries.X * ((2 : ℚ) • (E1 + Em1 - (2 : ℚ) • 1) - (2 : ℚ) • (1 + Em2 - (2 : ℚ) • Em1)) +
      PowerSeries.X * (PowerSeries.X * (E2 + Em2 + (6 : ℚ) • 1 - (4 : ℚ) • E1 - (4 : ℚ) • Em1)) := by
    rw [hf0_egf]
    simp only [hsmul_C]
    have hC2 : PowerSeries.C (2 : ℚ) = 2 := map_ofNat (PowerSeries.C) 2
    have hC4 : PowerSeries.C (4 : ℚ) = 4 := map_ofNat (PowerSeries.C) 4
    have hC6 : PowerSeries.C (6 : ℚ) = 6 := map_ofNat (PowerSeries.C) 6
    rw [hC2, hC4, hC6]
    have hcalc : ((1 - Em1) + PowerSeries.X * (E1 + Em1 - 2 * 1)) *
        ((1 - Em1) + PowerSeries.X * (E1 + Em1 - 2 * 1)) =
        (1 - 2 * Em1 + Em1 * Em1) +
        PowerSeries.X * (2 * (E1 + Em1 - 2 * 1) - 2 * (E1 * Em1 + Em1 * Em1 - 2 * Em1)) +
        PowerSeries.X * (PowerSeries.X * (E1 * E1 + Em1 * Em1 + 6 * 1 - 4 * E1 - 4 * Em1 +
          2 * (E1 * Em1 - 1))) := by ring
    rw [hcalc, hE1Em1, hE1E1, hEm1Em1]
    simp only [sub_self, mul_zero, add_zero]
  -- Convert RHS of hsq to egf of an explicit integer sequence!
  let s0 : ℕ → ℤ := fun k => (if k = 0 then 1 else 0) - 2 * (-1 : ℤ) ^ k + (-2 : ℤ) ^ k
  let s1 : ℕ → ℤ := fun k =>
    2 * (1 + (-1 : ℤ) ^ k - if k = 0 then 2 else 0) -
    2 * ((if k = 0 then 1 else 0) + (-2 : ℤ) ^ k - 2 * (-1 : ℤ) ^ k)
  let s2 : ℕ → ℤ := fun k =>
    (2 : ℤ) ^ k + (-2 : ℤ) ^ k + (if k = 0 then 6 else 0) - 4 * 1 - 4 * (-1 : ℤ) ^ k
  have hs_eq : egf f0 * egf f0 =
      egf (fun k => s0 k + (if k = 0 then 0 else (k : ℤ) * s1 (k - 1)) +
        (if k = 0 then 0 else (k : ℤ) * (if k - 1 = 0 then 0 else ((k - 1 : ℕ) : ℤ) * s2 (k - 2)))) := by
    rw [hsq]
    have hsm : ∀ (c : ℤ) (g : ℕ → ℤ), (c : ℚ) • egf g = egf (fun k => c * g k) := by
      intro c g; ext k
      simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk, Int.cast_mul]
      ring
    have h0' : (1 - (2 : ℚ) • Em1 + Em2) = egf s0 := by
      rw [h1, show (2 : ℚ) = ((2 : ℤ) : ℚ) from rfl, hsm, egf_sub, egf_add]
    have h1' : (2 : ℚ) • (E1 + Em1 - (2 : ℚ) • 1) - (2 : ℚ) • (1 + Em2 - (2 : ℚ) • Em1) = egf s1 := by
      rw [h1, show (2 : ℚ) = ((2 : ℤ) : ℚ) from rfl, hsm, egf_add, egf_sub, hsm, egf_add,
        hsm, egf_sub, hsm, egf_sub]
      congr 1; funext k; simp only [s1]; split_ifs <;> ring
    have h2' : E2 + Em2 + (6 : ℚ) • 1 - (4 : ℚ) • E1 - (4 : ℚ) • Em1 = egf s2 := by
      rw [h1, show (6 : ℚ) = ((6 : ℤ) : ℚ) from rfl, show (4 : ℚ) = ((4 : ℤ) : ℚ) from rfl,
        hsm, hsm, hsm, egf_add, egf_add, egf_sub, egf_sub]
      congr 1; funext k; simp only [s2]; split_ifs <;> ring
    rw [h0', h1', h2', egf_X_mul, egf_X_mul, egf_X_mul, egf_add, egf_add]
    congr 1
  rw [egf_mul] at hs_eq
  have hval := congr_fun (egf_inj hs_eq) m
  rw [hval]
  -- Now prove s1 k % 3 = 0, s2 k % 3 = 0, and s0 k % 3 = if 2 ≤ k ∧ Even k then 2 else 0!
  have h2pow : ∀ k : ℕ, (2 : ℤ) ^ k % 3 = (-1 : ℤ) ^ k % 3 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ, pow_succ, Int.mul_emod, ih]
      conv_rhs => rw [Int.mul_emod]
      omega
  have hm2pow : ∀ k : ℕ, (-2 : ℤ) ^ k % 3 = 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ, Int.mul_emod, ih]
      norm_num
  have hs1 : ∀ k : ℕ, s1 k % 3 = 0 := by
    intro k
    simp only [s1]
    have h1 := hm2pow k
    have h2 : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := neg_one_pow_eq_or ℤ k
    rcases h2 with h2 | h2 <;> (rw [h2]; split_ifs <;> omega)
  have hs2 : ∀ k : ℕ, s2 k % 3 = 0 := by
    intro k
    simp only [s2]
    have h1 := h2pow k
    have h2 := hm2pow k
    have h3 : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := neg_one_pow_eq_or ℤ k
    rcases h3 with h3 | h3 <;> (rw [h3] at h1 ⊢; split_ifs <;> omega)
  have hs0 : s0 m % 3 = if 2 ≤ m ∧ Even m then 2 else 0 := by
    simp only [s0]
    have h1 := hm2pow m
    cases m with
    | zero => norm_num
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_sub]
      by_cases hev : Even (m + 1)
      · rw [hev.neg_one_pow]
        have hge2 : 2 ≤ m + 1 := by obtain ⟨r, hr⟩ := hev; omega
        simp only [hge2, hev, and_self, ↓reduceIte]
        omega
      · have hodd : Odd (m + 1) := Nat.not_even_iff_odd.mp hev
        rw [hodd.neg_one_pow]
        simp only [hev, and_false, ↓reduceIte]
        omega
  have ht1 : (if m = 0 then 0 else (m : ℤ) * s1 (m - 1)) % 3 = 0 := by
    split_ifs
    · norm_num
    · rw [Int.mul_emod, hs1 (m - 1)]; norm_num
  have ht2 : (if m = 0 then 0 else
      (m : ℤ) * (if m - 1 = 0 then 0 else ((m - 1 : ℕ) : ℤ) * s2 (m - 2))) % 3 = 0 := by
    split_ifs
    · norm_num
    · norm_num
    · rw [Int.mul_emod, Int.mul_emod ((m - 1 : ℕ) : ℤ), hs2 (m - 2)]; norm_num
  omega

private theorem main_proved :
    ∀ a : ℕ → ℤ,
      a 0 = 0 →
      (∀ k : ℕ,
        let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
        ∑ n ∈ Finset.range (k + 1),
          (1 / (Nat.factorial n : ℚ)) *
            PowerSeries.coeff k ((A ^ n - PowerSeries.X) ^ n) =
        if k = 0 then 1 else 0) →
      ∀ n : ℕ, 0 < n →
        a (6 * n) % 3 = 2 ∧
        a (6 * n + 1) % 3 = 0 ∧
        a (6 * n + 2) % 3 = 2 ∧
        a (6 * n + 3) % 3 = 1 ∧
        a (6 * n + 4) % 3 = 2 ∧
        a (6 * n + 5) % 3 = 2 := by
  intro a ha0 heq
  -- Express (A^n - X)^n / n! as egf (hdivpow (b_n) n) for each n
  let b : ℕ → ℕ → ℤ := fun n k =>
    (Nat.factorial n : ℤ) * hdivpow a n k - (if k = 1 then 1 else 0)
  have hsum_int : ∀ k : ℕ,
      (∑ n ∈ Finset.range (k + 1), hdivpow (b n) n k) = if k = 0 then 1 else 0 := by
    intro k
    have hk := heq k
    have hterm : ∀ n : ℕ,
        (1 / (Nat.factorial n : ℚ)) *
          PowerSeries.coeff k ((egf a ^ n - PowerSeries.X) ^ n) =
        (hdivpow (b n) n k : ℚ) / (Nat.factorial k : ℚ) := by
      intro n
      cases n with
      | zero =>
        simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_mul,
          PowerSeries.coeff_one, hdivpow]
        split_ifs with h <;> simp [h]
      | succ n =>
        have hX : (PowerSeries.X : PowerSeries ℚ) = egf (fun j => if j = 1 then 1 else 0) := by
          ext j; simp only [egf, PowerSeries.coeff_X, PowerSeries.coeff_mk]; split_ifs with h <;> simp [h]
        have hsub : egf a ^ (n + 1) - PowerSeries.X = egf (b (n + 1)) := by
          rw [egf_pow_eq a ha0 (n + 1), hX, egf_sub]
        have hb0 : b (n + 1) 0 = 0 := by simp [b, hdivpow]
        have hdp := congr_arg (PowerSeries.coeff k) (egf_hdivpow (b (n + 1)) hb0 (n + 1))
        simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk] at hdp
        rw [hsub]; exact hdp
    have hk' : (∑ n ∈ Finset.range (k + 1), (hdivpow (b n) n k : ℚ)) / (Nat.factorial k : ℚ) =
        if k = 0 then 1 else 0 := by
      rw [Finset.sum_div]
      dsimp only [egf] at hterm
      simpa only [hterm] using hk
    have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hq : ((∑ n ∈ Finset.range (k + 1), hdivpow (b n) n k : ℤ) : ℚ) =
        ((if k = 0 then (1 : ℤ) else 0 : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      split_ifs at hk' ⊢ with hkz
      · subst hkz
        simp only [Nat.factorial_zero, Nat.cast_one, div_one] at hk'
        simpa using hk'
      · exact (div_eq_zero_iff.mp hk').resolve_right hfk
    exact_mod_cast hq
  -- Evaluate hdivpow (b n) n k mod 3 for n = 0, 1, 2, and n >= 3!
  have hb_ge3 : ∀ n k : ℕ, 3 ≤ n → hdivpow (b n) n k % 3 = (if k = n then (-1 : ℤ) ^ n else 0) % 3 := by
    intro n k hn3
    have hcongr : ∀ j, b n j % 3 = (if j = 1 then -1 else 0) % 3 := by
      intro j
      simp only [b]
      have h3dvd : 3 ∣ Nat.factorial n := Nat.dvd_factorial (by omega) hn3
      obtain ⟨q, hq⟩ := h3dvd
      have : (Nat.factorial n : ℤ) * hdivpow a n j = 3 * ((q : ℤ) * hdivpow a n j) := by
        push_cast [hq]; ring
      rw [this]
      split_ifs <;> omega
    rw [hdivpow_congr_mod3 hcongr n k, hdivpow_neg_delta1]
  have hb_n2 : ∀ k : ℕ, 1 ≤ k →
      hdivpow (b 2) 2 k % 3 = (-(k : ℤ) * hmul a a (k - 1) + if k = 2 then 1 else 0) % 3 := by
    intro k hk1
    have h2 : (1 / (Nat.factorial 2 : ℚ)) • (egf a ^ 2 - PowerSeries.X) ^ 2 =
        egf (fun j => 12 * hdivpow a 4 j - (if j = 0 then 0 else (j : ℤ) * hmul a a (j - 1)) +
          if j = 2 then 1 else 0) := by
      have hexp : (1 / (Nat.factorial 2 : ℚ)) • (egf a ^ 2 - PowerSeries.X) ^ 2 =
          (12 : ℚ) • ((1 / (Nat.factorial 4 : ℚ)) • egf a ^ 4) -
          PowerSeries.X * (egf a * egf a) +
          (1 / 2 : ℚ) • (PowerSeries.X ^ 2) := by
        ext j
        simp only [PowerSeries.coeff_smul, smul_eq_mul, map_add, map_sub]
        have hring : (egf a ^ 2 - PowerSeries.X) ^ 2 =
            egf a ^ 4 - (2 : ℚ) • (PowerSeries.X * (egf a * egf a)) + PowerSeries.X ^ 2 := by
          have : (2 : ℚ) • (PowerSeries.X * (egf a * egf a)) =
              2 * (PowerSeries.X * (egf a * egf a)) := by
            ext r; simp [two_mul]
          rw [this]; ring
        rw [hring]
        simp only [map_add, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
        norm_num [Nat.factorial]
        split_ifs <;> ring
      rw [hexp, egf_hdivpow a ha0 4, egf_mul, egf_X_mul]
      have h12 : (12 : ℚ) • egf (hdivpow a 4) = egf (fun j => 12 * hdivpow a 4 j) := by
        ext j; simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk,
          Int.cast_mul, Int.cast_ofNat]; ring
      have hX2 : (1 / 2 : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 =
          egf (fun j => if j = 2 then 1 else 0) := by
        ext j
        simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow, egf,
          PowerSeries.coeff_mk]
        split_ifs with hj
        · subst hj; norm_num [Nat.factorial]
        · simp
      rw [h12, hX2, egf_sub, egf_add]
    have hX : (PowerSeries.X : PowerSeries ℚ) = egf (fun j => if j = 1 then 1 else 0) := by
      ext j; simp only [egf, PowerSeries.coeff_X, PowerSeries.coeff_mk]; split_ifs with h <;> simp [h]
    have hsub : egf a ^ 2 - PowerSeries.X = egf (b 2) := by
      rw [egf_pow_eq a ha0 2, hX, egf_sub]
    have hb0 : b 2 0 = 0 := by simp [b, hdivpow]
    have hdp := egf_hdivpow (b 2) hb0 2
    rw [← hsub, h2] at hdp
    have hval := congr_fun (egf_inj hdp.symm) k
    rw [hval]
    simp only [show k ≠ 0 by omega, ↓reduceIte]
    rw [show 12 * hdivpow a 4 k - (k : ℤ) * hmul a a (k - 1) + (if k = 2 then 1 else 0) =
      3 * (4 * hdivpow a 4 k) + (-(k : ℤ) * hmul a a (k - 1) + if k = 2 then 1 else 0) by ring]
    omega
  have hb_n1 : ∀ k : ℕ, 1 ≤ k → hdivpow (b 1) 1 k = a k - if k = 1 then 1 else 0 := by
    have hdp1 : ∀ (f : ℕ → ℤ) (m : ℕ), 1 ≤ m → hdivpow f 1 m = f m := by
      intro f m hm
      cases m with
      | zero => omega
      | succ m =>
        simp only [hdivpow]
        rw [Finset.sum_eq_single m]
        · simp
        · intro j hj hjne
          have : m - j ≠ 0 := by
            have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj); omega
          simp [this]
        · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h
    intro k hk1
    rw [hdp1 (b 1) k hk1]
    simp only [b, Nat.factorial_one, Nat.cast_one, one_mul, hdp1 a k hk1]
  -- Prove a k % 3 = f0 k % 3 for all k by strong induction!
  have ha_eq_f0 : ∀ k : ℕ, a k % 3 = f0 k % 3 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases k with _ | _ | _ | k
      · simp [ha0, f0]
      · change a 1 % 3 = f0 1 % 3
        have h1 := hsum_int 1
        simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton] at h1
        have h0 : hdivpow (b 0) 0 1 = 0 := by simp [hdivpow]
        rw [h0, zero_add, hb_n1 1 (by omega)] at h1
        simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by omega] at h1
        simp only [f0]; norm_num; omega
      · change a 2 % 3 = f0 2 % 3
        have h2 := hsum_int 2
        have h2mod := congr_arg (· % 3) h2
        simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          OfNat.ofNat_ne_zero, ↓reduceIte, Int.zero_emod] at h2mod
        have h0 : hdivpow (b 0) 0 2 = 0 := by simp [hdivpow]
        rw [h0, zero_add, hb_n1 2 (by omega)] at h2mod
        have hmul0 : hmul a a 1 = 0 := by simp [hmul, Finset.sum_range_succ, ha0]
        have hbn2 := hb_n2 2 (by omega)
        simp only [hmul0, mul_zero, zero_add, ↓reduceIte] at hbn2
        simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, sub_zero] at h2mod
        rw [Int.add_emod, hbn2] at h2mod
        simp only [f0]; omega
      · change a (k + 3) % 3 = f0 (k + 3) % 3
        have hk := hsum_int (k + 3)
        have hkmod := congr_arg (· % 3) hk
        simp only [Nat.succ_ne_zero, ↓reduceIte, Int.zero_emod] at hkmod
        rw [Finset.sum_int_mod] at hkmod
        have hsplit : (∑ n ∈ Finset.range (k + 4), hdivpow (b n) n (k + 3) % 3) =
            hdivpow (b 0) 0 (k + 3) % 3 + hdivpow (b 1) 1 (k + 3) % 3 +
            hdivpow (b 2) 2 (k + 3) % 3 +
            ∑ n ∈ Finset.Ico 3 (k + 4), hdivpow (b n) n (k + 3) % 3 := by
          have h012 : Finset.range (k + 4) =
              Finset.range 3 ∪ Finset.Ico 3 (k + 4) := by
            ext x; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
          rw [h012, Finset.sum_union (Finset.disjoint_left.mpr fun x h1 h2 => by
            simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega)]
          simp [Finset.sum_range_succ]
        rw [hsplit] at hkmod
        have h0 : hdivpow (b 0) 0 (k + 3) = 0 := by simp [hdivpow]
        have h1 : hdivpow (b 1) 1 (k + 3) = a (k + 3) := by
          rw [hb_n1 (k + 3) (by omega)]; simp [show k + 3 ≠ 1 by omega]
        have htail : ∑ n ∈ Finset.Ico 3 (k + 4), hdivpow (b n) n (k + 3) % 3 =
            (-1 : ℤ) ^ (k + 3) % 3 := by
          rw [Finset.sum_eq_single (k + 3)]
          · rw [hb_ge3 (k + 3) (k + 3) (by omega)]; simp
          · intro n hn hne
            have hn3 : 3 ≤ n := (Finset.mem_Ico.mp hn).1
            rw [hb_ge3 n (k + 3) hn3]
            simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) h
        have h2 := hb_n2 (k + 3) (by omega)
        simp only [show k + 3 ≠ 2 by omega, ↓reduceIte, add_zero,
          show k + 3 - 1 = k + 2 by omega] at h2
        have hmul_eq : hmul a a (k + 2) % 3 = hmul f0 f0 (k + 2) % 3 :=
          hmul_congr_mod3_le (k + 2) (fun j hj => ih j (by omega)) (fun j hj => ih j (by omega))
        rw [h0, h1, h2, htail] at hkmod
        have h2' : (-(k + 3 : ℤ) * hmul a a (k + 2)) % 3 =
            (-(k + 3 : ℤ) * (hmul f0 f0 (k + 2) % 3)) % 3 := by
          rw [Int.mul_emod, hmul_eq, ← Int.mul_emod]
          conv_rhs => rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
        rw [show -((k + 3 : ℕ) : ℤ) * hmul a a (k + 2) = -(k + 3 : ℤ) * hmul a a (k + 2) by
          push_cast; ring] at hkmod
        rw [h2', hmul_f0_f0_mod3 (k + 2)] at hkmod
        have hge2 : 2 ≤ k + 2 := by omega
        simp only [hge2, true_and] at hkmod
        by_cases hev : Even (k + 2)
        · have hodd : Odd (k + 3) := by obtain ⟨r, hr⟩ := hev; exact ⟨r, by omega⟩
          rw [if_pos hev, hodd.neg_one_pow] at hkmod
          simp only [f0, Nat.succ_ne_zero, ↓reduceIte, show k + 3 - 1 = k + 2 by omega,
            show k + 3 ≠ 1 by omega, sub_zero, hev.neg_one_pow, hodd.neg_one_pow]
          omega
        · have hev3 : Even (k + 3) := by
            obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hev; exact ⟨r + 1, by omega⟩
          have hodd2 : Odd (k + 2) := Nat.not_even_iff_odd.mp hev
          rw [if_neg hev, hev3.neg_one_pow] at hkmod
          simp only [f0, Nat.succ_ne_zero, ↓reduceIte, show k + 3 - 1 = k + 2 by omega,
            show k + 3 ≠ 1 by omega, sub_zero, hodd2.neg_one_pow, hev3.neg_one_pow]
          omega
  intro n hn
  have h0 := ha_eq_f0 (6 * n)
  have h1 := ha_eq_f0 (6 * n + 1)
  have h2 := ha_eq_f0 (6 * n + 2)
  have h3 := ha_eq_f0 (6 * n + 3)
  have h4 := ha_eq_f0 (6 * n + 4)
  have h5 := ha_eq_f0 (6 * n + 5)
  have he0 : Even (6 * n) := ⟨3 * n, by omega⟩
  have ho0 : Odd (6 * n - 1) := ⟨3 * n - 1, by omega⟩
  have ho1 : Odd (6 * n + 1) := ⟨3 * n, by omega⟩
  have he2 : Even (6 * n + 2) := ⟨3 * n + 1, by omega⟩
  have ho3 : Odd (6 * n + 3) := ⟨3 * n + 1, by omega⟩
  have he4 : Even (6 * n + 4) := ⟨3 * n + 2, by omega⟩
  have ho5 : Odd (6 * n + 5) := ⟨3 * n + 2, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; simp only [f0, show 6 * n ≠ 0 by omega, show 6 * n ≠ 1 by omega, ↓reduceIte,
      he0.neg_one_pow, ho0.neg_one_pow]; omega
  · rw [h1]; simp only [f0, show 6 * n + 1 ≠ 0 by omega, show 6 * n + 1 ≠ 1 by omega, ↓reduceIte,
      Nat.add_sub_cancel, ho1.neg_one_pow, he0.neg_one_pow]; omega
  · rw [h2]; simp only [f0, show 6 * n + 2 ≠ 0 by omega, show 6 * n + 2 ≠ 1 by omega, ↓reduceIte,
      show 6 * n + 2 - 1 = 6 * n + 1 by omega, he2.neg_one_pow, ho1.neg_one_pow]; omega
  · rw [h3]; simp only [f0, show 6 * n + 3 ≠ 0 by omega, show 6 * n + 3 ≠ 1 by omega, ↓reduceIte,
      show 6 * n + 3 - 1 = 6 * n + 2 by omega, ho3.neg_one_pow, he2.neg_one_pow]; omega
  · rw [h4]; simp only [f0, show 6 * n + 4 ≠ 0 by omega, show 6 * n + 4 ≠ 1 by omega, ↓reduceIte,
      show 6 * n + 4 - 1 = 6 * n + 3 by omega, he4.neg_one_pow, ho3.neg_one_pow]; omega
  · rw [h5]; simp only [f0, show 6 * n + 5 ≠ 0 by omega, show 6 * n + 5 ≠ 1 by omega, ↓reduceIte,
      show 6 * n + 5 - 1 = 6 * n + 4 by omega, ho5.neg_one_pow, he4.neg_one_pow]; omega

end OMA.S_oeis_a371710

theorem OMA.solution : type_of% @OMA.S_oeis_a371710.main :=
  OMA.S_oeis_a371710.main_proved
