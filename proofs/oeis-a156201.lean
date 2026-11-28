import OMAStatements.S_oeis_a156201
import Mathlib

namespace OMA.P_oeis_a156201

open OMA.S_oeis_a156201 Finset

/-! ### Part 1: Formal power series inverse lemmas -/

private lemma coeff_mul_eq_sum_range (f g : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * g) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n

private lemma coeff_X_mul_zero (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
  rw [coeff_mul_eq_sum_range]; simp

private lemma coeff_X_mul_succ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
  rw [coeff_mul_eq_sum_range, Finset.sum_eq_single 1]
  · simp
  · intro b _ hb; rw [PowerSeries.coeff_X, if_neg hb, zero_mul]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

private lemma coeff_invOneSub (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (invOneSub f) = invOneSubAux f n := by
  unfold invOneSub; simp

private lemma one_sub_X_mul_invOneSub (f : PowerSeries ℚ) :
    (1 - PowerSeries.X * f) * invOneSub f = 1 := by
  apply PowerSeries.ext; intro n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero =>
    rw [mul_assoc, coeff_X_mul_zero, PowerSeries.coeff_one, if_pos rfl, coeff_invOneSub]
    simp [invOneSubAux]
  | succ m =>
    rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), coeff_invOneSub, invOneSubAux,
      mul_assoc, coeff_X_mul_succ, coeff_mul_eq_sum_range]
    have hsum : ∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i f * PowerSeries.coeff (m - i) (invOneSub f) =
        ∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i f * invOneSubAux f (m - i) :=
      Finset.sum_congr rfl (fun i _ => by rw [coeff_invOneSub])
    rw [hsum, sub_self]

private lemma mul_invUnit1 (f : PowerSeries ℚ) (hc0 : PowerSeries.coeff 0 f = 1) :
    f * invUnit1 f = 1 := by
  have h1 : 1 - PowerSeries.X * PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f) = f := by
    apply PowerSeries.ext; intro n
    rw [map_sub]
    cases n with
    | zero => rw [PowerSeries.coeff_one, if_pos rfl, coeff_X_mul_zero, sub_zero, hc0]
    | succ m =>
      rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), coeff_X_mul_succ,
        PowerSeries.coeff_mk, zero_sub, neg_neg]
  unfold invUnit1
  conv_lhs => arg 1; rw [← h1]
  exact one_sub_X_mul_invOneSub _

private lemma coeff_zero_invUnit1 (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (invUnit1 f) = 1 := by
  unfold invUnit1; rw [coeff_invOneSub]; simp [invOneSubAux]

private lemma invUnit1_unique (f g : PowerSeries ℚ) (hc0 : PowerSeries.coeff 0 f = 1)
    (h : f * g = 1) : g = invUnit1 f := by
  have h1 := mul_invUnit1 f hc0
  calc
    g = 1 * g := (one_mul g).symm
    _ = (f * invUnit1 f) * g := by rw [h1]
    _ = invUnit1 f * (f * g) := by ring
    _ = invUnit1 f * 1 := by rw [h]
    _ = invUnit1 f := mul_one _

private lemma invOneSub_congr_lt (f g : PowerSeries ℚ) (m : ℕ)
    (h : ∀ i < m, PowerSeries.coeff i f = PowerSeries.coeff i g) :
    ∀ n ≤ m, PowerSeries.coeff n (invOneSub f) = PowerSeries.coeff n (invOneSub g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnm
    rw [coeff_invOneSub, coeff_invOneSub]
    cases n with
    | zero => simp [invOneSubAux]
    | succ k =>
      simp only [invOneSubAux]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hilt : i < k + 1 := Finset.mem_range.mp hi
      rw [h i (by omega)]
      congr 1
      rw [← coeff_invOneSub, ← coeff_invOneSub]
      exact ih (k - i) (by omega) (by omega)

private lemma invUnit1_congr (f g : PowerSeries ℚ) (m : ℕ)
    (h : ∀ n ≤ m, PowerSeries.coeff n f = PowerSeries.coeff n g) :
    ∀ n ≤ m, PowerSeries.coeff n (invUnit1 f) = PowerSeries.coeff n (invUnit1 g) := by
  unfold invUnit1
  refine invOneSub_congr_lt _ _ m (fun i hi => ?_)
  simp only [PowerSeries.coeff_mk]
  rw [h (i + 1) (by omega)]

private lemma mul_congr_le (f₁ f₂ g₁ g₂ : PowerSeries ℚ) (m : ℕ)
    (hf : ∀ n ≤ m, PowerSeries.coeff n f₁ = PowerSeries.coeff n f₂)
    (hg : ∀ n ≤ m, PowerSeries.coeff n g₁ = PowerSeries.coeff n g₂) :
    ∀ n ≤ m, PowerSeries.coeff n (f₁ * g₁) = PowerSeries.coeff n (f₂ * g₂) := by
  intro n hn
  rw [coeff_mul_eq_sum_range, coeff_mul_eq_sum_range]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hilt : i < n + 1 := Finset.mem_range.mp hi
  rw [hf i (by omega), hg (n - i) (by omega)]

private lemma X_sq_mul_congr (f g : PowerSeries ℚ) (m : ℕ)
    (h : ∀ n ≤ m, PowerSeries.coeff n f = PowerSeries.coeff n g) :
    ∀ n ≤ m + 2, PowerSeries.coeff n (PowerSeries.X ^ 2 * f) =
      PowerSeries.coeff n (PowerSeries.X ^ 2 * g) := by
  intro n hn
  have hsq : PowerSeries.X ^ 2 = (PowerSeries.X : PowerSeries ℚ) * PowerSeries.X := sq _
  rw [hsq, mul_assoc, mul_assoc]
  cases n with
  | zero => rw [coeff_X_mul_zero, coeff_X_mul_zero]
  | succ n1 =>
    rw [coeff_X_mul_succ, coeff_X_mul_succ]
    cases n1 with
    | zero => rw [coeff_X_mul_zero, coeff_X_mul_zero]
    | succ n2 =>
      rw [coeff_X_mul_succ, coeff_X_mul_succ]
      exact h n2 (by omega)

private lemma gladStep_congr (k : ℕ) (t₁ t₂ : PowerSeries ℚ) (m : ℕ)
    (ht : ∀ n ≤ m, PowerSeries.coeff n t₁ = PowerSeries.coeff n t₂) :
    ∀ n ≤ m + 2, PowerSeries.coeff n (gladStep k t₁) = PowerSeries.coeff n (gladStep k t₂) := by
  intro n hn
  unfold gladStep
  dsimp only
  rw [map_sub, map_sub]
  congr 1
  have hinv_t : ∀ i ≤ m, PowerSeries.coeff i (invUnit1 t₁) = PowerSeries.coeff i (invUnit1 t₂) :=
    invUnit1_congr t₁ t₂ m ht
  have hden : ∀ i ≤ m, PowerSeries.coeff i
        (PowerSeries.C ((16 * (k + 1) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 +
          (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 * invUnit1 t₁) =
      PowerSeries.coeff i
        (PowerSeries.C ((16 * (k + 1) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 +
          (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 * invUnit1 t₂) := by
    intro i hi
    rw [map_add, map_add]
    congr 1
    exact mul_congr_le _ _ _ _ m (fun _ _ => rfl) hinv_t i hi
  have hinv_den := invUnit1_congr _ _ m hden
  rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  congr 1
  exact X_sq_mul_congr _ _ m hinv_den n hn

private lemma gladFold_congr (k d : ℕ) (t₁ t₂ : PowerSeries ℚ)
    (hc0 : PowerSeries.coeff 0 t₁ = PowerSeries.coeff 0 t₂) :
    ∀ n ≤ 2 * d, PowerSeries.coeff n (gladFold k d t₁) = PowerSeries.coeff n (gladFold k d t₂) := by
  induction d generalizing k with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simpa [gladFold] using hc0
  | succ d ih =>
    intro n hn
    simp only [gladFold]
    exact gladStep_congr k _ _ (2 * d) (ih (k + 1)) n (by omega)

/-! ### Part 2: Exact numerator formula `(oeis_a156201Val n : ℚ) = 8^n * eulerVal (1/8) n` -/

/-- Integer scaled Euler value `a(n) = 8^n * E_n(1/8)`. -/
private def scaledVal : ℕ → ℤ
  | 0 => 1
  | n + 1 => 1 - ∑ k : Fin (n + 1),
      ((Nat.choose (n + 1) k.val : ℕ) : ℤ) * ((2 : ℤ) ^ (n - k.val) * (4 : ℤ) ^ (n + 1 - k.val)) * scaledVal k.val

private lemma scaledVal_cast (n : ℕ) :
    (scaledVal n : ℚ) = (8 : ℚ) ^ n * eulerVal (1 / 8 : ℚ) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [scaledVal, eulerVal]
    | succ n =>
      simp only [scaledVal, eulerVal, Int.cast_sub, Int.cast_one, Int.cast_sum, Int.cast_mul,
        Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
      rw [mul_sub, ← mul_pow]
      have h1 : ((8 : ℚ) * (1 / 8 : ℚ)) ^ (n + 1) = 1 := by norm_num
      rw [h1]
      congr 1
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hklt : k.val < n + 1 := k.isLt
      rw [ih k.val hklt]
      have hpow : (8 : ℚ) ^ (n + 1) * (1 / 2 : ℚ) =
          (2 : ℚ) ^ (n - k.val) * (4 : ℚ) ^ (n + 1 - k.val) * (8 : ℚ) ^ k.val := by
        have hsplit : (8 : ℚ) ^ (n + 1) = (8 : ℚ) ^ (n + 1 - k.val) * (8 : ℚ) ^ k.val := by
          rw [← pow_add, show n + 1 - k.val + k.val = n + 1 by omega]
        have h2m : (8 : ℚ) = 2 * 4 := by norm_num
        have h2s : (2 : ℚ) ^ (n + 1 - k.val) = (2 : ℚ) ^ (n - k.val) * 2 := by
          rw [← pow_succ, show n - k.val + 1 = n + 1 - k.val by omega]
        rw [hsplit, h2m, mul_pow, h2s]
        ring
      linear_combination (Nat.choose (n + 1) k.val : ℚ) * eulerVal (1 / 8 : ℚ) k.val * hpow.symm

private lemma scaledVal_mod_m (n : ℕ) : scaledVal n % (4 : ℤ) = 1 := by
  cases n with
  | zero => simp [scaledVal]
  | succ n =>
    simp only [scaledVal]
    have hdvd : (4 : ℤ) ∣ ∑ k : Fin (n + 1),
        ((Nat.choose (n + 1) k.val : ℕ) : ℤ) * ((2 : ℤ) ^ (n - k.val) * (4 : ℤ) ^ (n + 1 - k.val)) * scaledVal k.val := by
      refine Finset.dvd_sum (fun k _ => ?_)
      have hklt : k.val < n + 1 := k.isLt
      have hm1 : (4 : ℤ) ∣ (4 : ℤ) ^ (n + 1 - k.val) := dvd_pow_self (4 : ℤ) (by omega)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hm1 _) _) _
    rcases hdvd with ⟨q, hq⟩
    rw [hq]
    omega

private lemma scaledVal_coprime (n : ℕ) :
    Nat.Coprime (scaledVal n).natAbs (8 ^ n) := by
  refine Nat.Coprime.pow_right n ?_
  have hm_cop : Nat.Coprime (scaledVal n).natAbs 4 := by
    have hmod := scaledVal_mod_m n
    have hgcd_z : (Nat.gcd (scaledVal n).natAbs 4 : ℤ) ∣ 1 := by
      have hd1 : (Nat.gcd (scaledVal n).natAbs 4 : ℤ) ∣ scaledVal n := by
        have := Int.natCast_dvd.mpr (Nat.gcd_dvd_left (scaledVal n).natAbs 4)
        exact this
      have hd2 : (Nat.gcd (scaledVal n).natAbs 4 : ℤ) ∣ (4 : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
      have hsub : scaledVal n - (4 : ℤ) * (scaledVal n / (4 : ℤ)) = 1 := by omega
      rw [← hsub]
      exact dvd_sub hd1 (dvd_mul_of_dvd_left hd2 _)
    have hgcd_n : Nat.gcd (scaledVal n).natAbs 4 ∣ 1 := Int.natCast_dvd_natCast.mp hgcd_z
    exact Nat.eq_one_of_dvd_one hgcd_n
  have h2_cop : Nat.Coprime (scaledVal n).natAbs 2 :=
    hm_cop.coprime_dvd_right (by decide : 2 ∣ 4)
  have hmul : Nat.Coprime (scaledVal n).natAbs (2 * 4) := h2_cop.mul_right hm_cop
  simpa using hmul

private lemma val_eq_scaledVal (n : ℕ) : oeis_a156201Val n = scaledVal n := by
  unfold oeis_a156201Val
  have hq : eulerVal (1 / 8 : ℚ) n = (scaledVal n : ℚ) / ((8 ^ n : ℕ) : ℚ) := by
    have hc := scaledVal_cast n
    have hne : (8 : ℚ) ^ n ≠ 0 := by positivity
    rw [eq_div_iff (by exact_mod_cast hne)]
    push_cast; linarith
  rw [hq]
  have hpos : 0 < (8 : ℕ) ^ n := by positivity
  have hcop := scaledVal_coprime n
  let r : ℚ := { num := scaledVal n, den := 8 ^ n, den_nz := hpos.ne', reduced := hcop }
  have hrat : ((scaledVal n : ℚ) / ((8 ^ n : ℕ) : ℚ)) = r := Rat.num_div_den r
  rw [hrat]

/-! ### Part 3: Formal exponential/hyperbolic series and Laplace transform ODE -/

private noncomputable def expPS (r : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => r ^ n / (n.factorial : ℚ))

private lemma coeff_expPS (r : ℚ) (n : ℕ) :
    PowerSeries.coeff n (expPS r) = r ^ n / (n.factorial : ℚ) := by
  unfold expPS; simp

private lemma expPS_zero : expPS 0 = 1 := by
  ext n
  cases n with
  | zero => simp [coeff_expPS]
  | succ m => simp [coeff_expPS]

private lemma expPS_mul (r s : ℚ) : expPS r * expPS s = expPS (r + s) := by
  ext n
  rw [coeff_mul_eq_sum_range, coeff_expPS]
  simp_rw [coeff_expPS]
  have hbin : (r + s) ^ n = ∑ i ∈ Finset.range (n + 1), r ^ i * s ^ (n - i) * (Nat.choose n i : ℚ) :=
    add_pow r s n
  rw [hbin, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hch : (Nat.choose n i : ℚ) * (i.factorial : ℚ) * ((n - i).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hile
  have hne1 : (i.factorial : ℚ) ≠ 0 := by positivity
  have hne2 : ((n - i).factorial : ℚ) ≠ 0 := by positivity
  have hne3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp [hne1, hne2, hne3]
  rw [← hch]; ring

/-- Formal derivative on `PowerSeries ℚ`. -/
private noncomputable def derivPS (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f)

private lemma derivPS_add (f g : PowerSeries ℚ) :
    derivPS (f + g) = derivPS f + derivPS g := by
  ext n; simp [derivPS]; ring

private lemma derivPS_sub (f g : PowerSeries ℚ) :
    derivPS (f - g) = derivPS f - derivPS g := by
  ext n; simp [derivPS]; ring

private lemma derivPS_C_mul (a : ℚ) (f : PowerSeries ℚ) :
    derivPS (PowerSeries.C a * f) = PowerSeries.C a * derivPS f := by
  ext n; simp [derivPS]; ring

private lemma derivPS_mul (f g : PowerSeries ℚ) :
    derivPS (f * g) = derivPS f * g + f * derivPS g := by
  ext n
  simp only [derivPS, PowerSeries.coeff_mk, map_add]
  rw [coeff_mul_eq_sum_range, coeff_mul_eq_sum_range, coeff_mul_eq_sum_range]
  simp only [PowerSeries.coeff_mk]
  have hsum : ((n + 1 : ℕ) : ℚ) *
        ∑ i ∈ Finset.range (n + 2), PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g =
      (∑ i ∈ Finset.range (n + 2),
        ((i : ℚ) * PowerSeries.coeff i f) * PowerSeries.coeff (n + 1 - i) g) +
      (∑ i ∈ Finset.range (n + 2),
        PowerSeries.coeff i f * (((n + 1 - i : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - i) g)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hile : i ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hadd : (i : ℚ) + ((n + 1 - i : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : i + (n + 1 - i) = n + 1)
    linear_combination -(PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g) * hadd
  rw [hsum]
  congr 1
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hidx : n + 1 - (i + 1) = n - i := by omega
    rw [hidx]
  · rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hidx : n + 1 - i = (n - i) + 1 := by omega
    rw [hidx]

private lemma derivPS_pow (f : PowerSeries ℚ) (k : ℕ) :
    derivPS (f ^ k) = PowerSeries.C (k : ℚ) * f ^ (k - 1) * derivPS f := by
  induction k with
  | zero =>
    ext n; simp [derivPS, PowerSeries.coeff_one]
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k' =>
      rw [pow_succ, derivPS_mul, ih]
      simp only [Nat.add_sub_cancel]
      have hpow : f ^ k' * f = f ^ (k' + 1) := (pow_succ f k').symm
      have hcast : PowerSeries.C ((k' + 2 : ℕ) : ℚ) =
          PowerSeries.C ((k' + 1 : ℕ) : ℚ) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_one, map_ofNat]; ring
      rw [hcast]
      linear_combination PowerSeries.C ((k' + 1 : ℕ) : ℚ) * derivPS f * hpow

private lemma derivPS_expPS (r : ℚ) : derivPS (expPS r) = PowerSeries.C r * expPS r := by
  ext n
  simp only [derivPS, coeff_expPS, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    pow_succ, Nat.factorial_succ]
  have hne1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hne2 : (n.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

private noncomputable def coshM : PowerSeries ℚ :=
  PowerSeries.C (1 / 2 : ℚ) * (expPS 4 + expPS (-4))

private noncomputable def sinhM : PowerSeries ℚ :=
  PowerSeries.C (1 / 2 : ℚ) * (expPS 4 - expPS (-4))

private noncomputable def sechM : PowerSeries ℚ :=
  invUnit1 coshM

private lemma coeff_zero_coshM : PowerSeries.coeff 0 coshM = 1 := by
  simp only [coshM, PowerSeries.coeff_C_mul, map_add, coeff_expPS]; norm_num

private lemma coeff_zero_sinhM : PowerSeries.coeff 0 sinhM = 0 := by
  simp only [sinhM, PowerSeries.coeff_C_mul, map_sub, coeff_expPS]; norm_num

private lemma coeff_one_sinhM : PowerSeries.coeff 1 sinhM = 4 := by
  simp [sinhM, coeff_expPS]; norm_num

private lemma coshM_mul_sechM : coshM * sechM = 1 :=
  mul_invUnit1 coshM coeff_zero_coshM

private lemma coshM_sq_sub_sinhM_sq : coshM ^ 2 - sinhM ^ 2 = 1 := by
  unfold coshM sinhM
  have h1 : expPS (4 : ℚ) * expPS (-4 : ℚ) = 1 := by
    rw [expPS_mul]; simp [expPS_zero]
  have h2 : (PowerSeries.C (1 / 2 : ℚ) * (expPS 4 + expPS (-4))) ^ 2 -
      (PowerSeries.C (1 / 2 : ℚ) * (expPS 4 - expPS (-4))) ^ 2 =
      PowerSeries.C (1 : ℚ) * (expPS 4 * expPS (-4)) := by
    have hc : PowerSeries.C (1 / 2 : ℚ) * PowerSeries.C (1 / 2 : ℚ) * 4 = PowerSeries.C 1 := by
      rw [show (4 : PowerSeries ℚ) = PowerSeries.C 4 from rfl, ← map_mul, ← map_mul]; norm_num
    linear_combination (expPS 4 * expPS (-4)) * hc
  rw [h2, h1, map_one, one_mul]

private lemma derivPS_coshM : derivPS coshM = PowerSeries.C (4 : ℚ) * sinhM := by
  unfold coshM sinhM
  rw [derivPS_C_mul, derivPS_add, derivPS_expPS, derivPS_expPS]
  rw [map_neg]
  ring

private lemma derivPS_sinhM : derivPS sinhM = PowerSeries.C (4 : ℚ) * coshM := by
  unfold coshM sinhM
  rw [derivPS_C_mul, derivPS_sub, derivPS_expPS, derivPS_expPS]
  rw [map_neg]
  ring

private lemma derivPS_sechM : derivPS sechM = -PowerSeries.C (4 : ℚ) * sinhM * sechM ^ 2 := by
  have h0 : derivPS (coshM * sechM) = 0 := by
    rw [coshM_mul_sechM]
    ext n; simp [derivPS, PowerSeries.coeff_one]
  rw [derivPS_mul, derivPS_coshM] at h0
  calc
    derivPS sechM = 1 * derivPS sechM := (one_mul _).symm
    _ = (coshM * sechM) * derivPS sechM := by rw [coshM_mul_sechM]
    _ = sechM * (coshM * derivPS sechM) := by ring
    _ = sechM * (-(PowerSeries.C (4 : ℚ) * sinhM * sechM)) := by
        have : coshM * derivPS sechM = -(PowerSeries.C (4 : ℚ) * sinhM * sechM) := by
          linear_combination h0
        rw [this]
    _ = -PowerSeries.C (4 : ℚ) * sinhM * sechM ^ 2 := by ring

/-- Auxiliary E.G.F. `uPS k = exp(-3 * t) * sinh(4 * t)^k * sech(4 * t)^(k + 1)`. -/
private noncomputable def uPS (k : ℕ) : PowerSeries ℚ :=
  expPS (-3) * sinhM ^ k * sechM ^ (k + 1)

private lemma uPS_zero_eq_scaledVal (n : ℕ) :
    (n.factorial : ℚ) * PowerSeries.coeff n (uPS 0) = (scaledVal n : ℚ) := by
  have hrel : (expPS (8 : ℚ) + 1) * uPS 0 = PowerSeries.C 2 * expPS 1 := by
    unfold uPS
    simp only [pow_zero, mul_one, zero_add, pow_one]
    have hexp : expPS (8 : ℚ) + 1 = PowerSeries.C 2 * expPS (4 : ℚ) * coshM := by
      unfold coshM
      have h1 : expPS (4 : ℚ) * expPS (4 : ℚ) = expPS (8 : ℚ) := by
        rw [expPS_mul]; norm_num
      have h2 : expPS (4 : ℚ) * expPS (-4 : ℚ) = 1 := by
        rw [expPS_mul]; simp [expPS_zero]
      have hc : PowerSeries.C (2 : ℚ) * PowerSeries.C (1 / 2 : ℚ) = 1 := by
        rw [← map_mul]; norm_num
      calc
        expPS (8 : ℚ) + 1 = expPS 4 * expPS 4 + expPS 4 * expPS (-4) := by rw [h1, h2]
        _ = 1 * (expPS 4 * (expPS 4 + expPS (-4))) := by ring
        _ = (PowerSeries.C 2 * PowerSeries.C (1 / 2 : ℚ)) * (expPS 4 * (expPS 4 + expPS (-4))) := by rw [hc]
        _ = PowerSeries.C 2 * expPS 4 * (PowerSeries.C (1 / 2 : ℚ) * (expPS 4 + expPS (-4))) := by ring
    have hprod : expPS (4 : ℚ) * expPS (-3 : ℚ) = expPS 1 := by
      rw [expPS_mul]; norm_num
    calc
      (expPS 8 + 1) * (expPS (-3) * sechM)
        = PowerSeries.C 2 * (expPS 4 * expPS (-3)) * (coshM * sechM) := by rw [hexp]; ring
      _ = PowerSeries.C 2 * expPS 1 * 1 := by rw [hprod, coshM_mul_sechM]
      _ = PowerSeries.C 2 * expPS 1 := mul_one _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcoeff := congr_arg (PowerSeries.coeff n) hrel
    rw [add_mul, one_mul, mul_comm (expPS 8) (uPS 0), map_add, coeff_mul_eq_sum_range, PowerSeries.coeff_C_mul, coeff_expPS] at hcoeff
    simp_rw [coeff_expPS] at hcoeff
    cases n with
    | zero =>
      rw [Finset.sum_range_one] at hcoeff
      simp only [Nat.sub_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, mul_one] at hcoeff
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, scaledVal, Int.cast_one]
      linarith
    | succ n =>
      rw [Finset.sum_range_succ] at hcoeff
      simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, one_pow] at hcoeff
      have hmul := congr_arg (fun x : ℚ => (((n + 1).factorial : ℚ) / 2) * x) hcoeff
      have hrhs : (((n + 1).factorial : ℚ) / 2) * (2 * (1 / ((n + 1).factorial : ℚ))) = 1 := by
        have hne : (((n + 1).factorial : ℚ)) ≠ 0 := by positivity
        field_simp
      rw [hrhs] at hmul
      have hsum_eq : (((n + 1).factorial : ℚ) / 2) *
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k (uPS 0) * ((8 : ℚ) ^ (n + 1 - k) / ((n + 1 - k).factorial : ℚ)) =
          ∑ k ∈ Finset.range (n + 1),
            ((Nat.choose (n + 1) k : ℕ) : ℚ) * ((2 : ℚ) ^ (n - k) * (4 : ℚ) ^ (n + 1 - k)) *
              (scaledVal k : ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hklt : k < n + 1 := Finset.mem_range.mp hk
        have hih := ih k hklt
        have hch : (Nat.choose (n + 1) k : ℚ) * (k.factorial : ℚ) * ((n + 1 - k).factorial : ℚ) =
            ((n + 1).factorial : ℚ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ n + 1)
        have hpow : (8 : ℚ) ^ (n + 1 - k) = 2 * ((2 : ℚ) ^ (n - k) * (4 : ℚ) ^ (n + 1 - k)) := by
          have h2m : (8 : ℚ) = 2 * 4 := by norm_num
          have h2s : (2 : ℚ) ^ (n + 1 - k) = 2 * (2 : ℚ) ^ (n - k) := by
            rw [← pow_succ', show n - k + 1 = n + 1 - k by omega]
          rw [h2m, mul_pow, h2s]; ring
        have hne1 : (k.factorial : ℚ) ≠ 0 := by positivity
        have hne2 : ((n + 1 - k).factorial : ℚ) ≠ 0 := by positivity
        rw [← hih, hpow]
        field_simp [hne1, hne2]
        rw [← hch]; ring
      have hlhs : (((n + 1).factorial : ℚ) / 2) *
            ((∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k (uPS 0) * ((8 : ℚ) ^ (n + 1 - k) / ((n + 1 - k).factorial : ℚ))) +
              PowerSeries.coeff (n + 1) (uPS 0) + PowerSeries.coeff (n + 1) (uPS 0)) =
          (∑ k ∈ Finset.range (n + 1),
            ((Nat.choose (n + 1) k : ℕ) : ℚ) * ((2 : ℚ) ^ (n - k) * (4 : ℚ) ^ (n + 1 - k)) *
              (scaledVal k : ℚ)) +
            ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) (uPS 0) := by
        rw [← hsum_eq]; ring
      rw [hlhs] at hmul
      simp only [scaledVal, Int.cast_sub, Int.cast_one, Int.cast_sum, Int.cast_mul,
        Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
      have hfin : ∑ k : Fin (n + 1),
            ((Nat.choose (n + 1) k.val : ℕ) : ℚ) * ((2 : ℚ) ^ (n - k.val) * (4 : ℚ) ^ (n + 1 - k.val)) *
              (scaledVal k.val : ℚ) =
          ∑ k ∈ Finset.range (n + 1),
            ((Nat.choose (n + 1) k : ℕ) : ℚ) * ((2 : ℚ) ^ (n - k) * (4 : ℚ) ^ (n + 1 - k)) *
              (scaledVal k : ℚ) :=
        Fin.sum_univ_eq_sum_range (fun k =>
          ((Nat.choose (n + 1) k : ℕ) : ℚ) * ((2 : ℚ) ^ (n - k) * (4 : ℚ) ^ (n + 1 - k)) *
            (scaledVal k : ℚ)) (n + 1)
      rw [hfin]
      linarith

private lemma derivPS_uPS (k : ℕ) :
    derivPS (uPS k) =
      (if k = 0 then 0 else PowerSeries.C (((k * 4 : ℕ) : ℚ)) * uPS (k - 1)) -
        PowerSeries.C (3 : ℚ) * uPS k -
        PowerSeries.C ((((k + 1) * 4 : ℕ) : ℚ)) * uPS (k + 1) := by
  unfold uPS
  rw [derivPS_mul, derivPS_mul, derivPS_expPS, derivPS_pow, derivPS_pow, derivPS_sinhM, derivPS_sechM]
  simp only [Nat.add_sub_cancel]
  have hcs : coshM * sechM = 1 := coshM_mul_sechM
  cases k with
  | zero =>
    simp only [ite_true, pow_zero, Nat.cast_zero, map_zero, zero_mul, mul_one, one_mul,
      pow_one, zero_sub, Nat.zero_add, Nat.cast_one, map_one]
    rw [map_neg]
    ring
  | succ k' =>
    rw [if_neg (by omega : k' + 1 ≠ 0), Nat.add_sub_cancel]
    have hmid : expPS (-3) * (PowerSeries.C ((k' + 1 : ℕ) : ℚ) * sinhM ^ k' *
          (PowerSeries.C (4 : ℚ) * coshM)) * sechM ^ (k' + 2) =
        PowerSeries.C ((((k' + 1) * 4 : ℕ) : ℚ)) * (expPS (-3) * sinhM ^ k' * sechM ^ (k' + 1)) := by
      have hpow : coshM * sechM ^ (k' + 2) = sechM ^ (k' + 1) := by
        rw [pow_succ', ← mul_assoc, hcs, one_mul]
      have hcm : PowerSeries.C ((k' + 1 : ℕ) : ℚ) * PowerSeries.C (4 : ℚ) =
          PowerSeries.C ((((k' + 1) * 4 : ℕ) : ℚ)) := by
        rw [← map_mul]; push_cast; rfl
      calc
        expPS (-3) * (PowerSeries.C ((k' + 1 : ℕ) : ℚ) * sinhM ^ k' *
            (PowerSeries.C (4 : ℚ) * coshM)) * sechM ^ (k' + 2)
          = (PowerSeries.C ((k' + 1 : ℕ) : ℚ) * PowerSeries.C (4 : ℚ)) *
              (expPS (-3) * sinhM ^ k' * (coshM * sechM ^ (k' + 2))) := by ring
        _ = PowerSeries.C ((((k' + 1) * 4 : ℕ) : ℚ)) *
              (expPS (-3) * sinhM ^ k' * sechM ^ (k' + 1)) := by rw [hcm, hpow]
    have hlast : expPS (-3) * sinhM ^ (k' + 1) *
          (PowerSeries.C ((k' + 2 : ℕ) : ℚ) * sechM ^ (k' + 1) *
            (-PowerSeries.C (4 : ℚ) * sinhM * sechM ^ 2)) =
        -PowerSeries.C ((((k' + 2) * 4 : ℕ) : ℚ)) *
          (expPS (-3) * sinhM ^ (k' + 2) * sechM ^ (k' + 3)) := by
      have hcm : PowerSeries.C ((k' + 2 : ℕ) : ℚ) * PowerSeries.C (4 : ℚ) =
          PowerSeries.C ((((k' + 2) * 4 : ℕ) : ℚ)) := by
        rw [← map_mul]; push_cast; rfl
      have hps1 : sinhM ^ (k' + 1) * sinhM = sinhM ^ (k' + 2) := (pow_succ sinhM (k' + 1)).symm
      have hps2 : sechM ^ (k' + 1) * sechM ^ 2 = sechM ^ (k' + 3) := by rw [← pow_add]
      calc
        expPS (-3) * sinhM ^ (k' + 1) *
            (PowerSeries.C ((k' + 2 : ℕ) : ℚ) * sechM ^ (k' + 1) *
              (-PowerSeries.C (4 : ℚ) * sinhM * sechM ^ 2))
          = -(PowerSeries.C ((k' + 2 : ℕ) : ℚ) * PowerSeries.C (4 : ℚ)) *
              (expPS (-3) * (sinhM ^ (k' + 1) * sinhM) * (sechM ^ (k' + 1) * sechM ^ 2)) := by ring
        _ = -PowerSeries.C ((((k' + 2) * 4 : ℕ) : ℚ)) *
              (expPS (-3) * sinhM ^ (k' + 2) * sechM ^ (k' + 3)) := by rw [hcm, hps1, hps2]
    rw [add_mul, hmid, hlast, map_neg]
    ring

private lemma coeff_sinhM_pow_lt (k n : ℕ) (h : n < k) :
    PowerSeries.coeff n (sinhM ^ k) = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [pow_succ, coeff_mul_eq_sum_range]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases heq : i = n
    · subst heq; simp [coeff_zero_sinhM]
    · rw [ih i (by omega), zero_mul]

private lemma coeff_sinhM_pow_diag (k : ℕ) :
    PowerSeries.coeff k (sinhM ^ k) = (4 : ℚ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, coeff_mul_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    have h0 : ∑ i ∈ Finset.range k, PowerSeries.coeff i (sinhM ^ k) * PowerSeries.coeff (k + 1 - i) sinhM = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        rw [coeff_sinhM_pow_lt k i (Finset.mem_range.mp hi), zero_mul])
    rw [h0, zero_add, Nat.sub_self, coeff_zero_sinhM, mul_zero, add_zero,
      show k + 1 - k = 1 by omega, coeff_one_sinhM, ih, pow_succ]

private lemma coeff_uPS_lt (k n : ℕ) (h : n < k) :
    PowerSeries.coeff n (uPS k) = 0 := by
  unfold uPS
  rw [mul_assoc, coeff_mul_eq_sum_range]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h2 : PowerSeries.coeff (n - i) (sinhM ^ k * sechM ^ (k + 1)) = 0 := by
    rw [coeff_mul_eq_sum_range]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hjle : j ≤ n - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [coeff_sinhM_pow_lt k j (by omega), zero_mul]
  rw [h2, mul_zero]

private lemma coeff_uPS_diag (k : ℕ) :
    PowerSeries.coeff k (uPS k) = (4 : ℚ) ^ k := by
  unfold uPS
  have hc0_e : PowerSeries.coeff 0 (expPS (-3)) = 1 := by simp [coeff_expPS]
  have hc0_s : PowerSeries.coeff 0 (sechM ^ (k + 1)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      sechM, coeff_zero_invUnit1, one_pow]
  have hprod : PowerSeries.coeff k (sinhM ^ k * sechM ^ (k + 1)) = (4 : ℚ) ^ k := by
    rw [coeff_mul_eq_sum_range, Finset.sum_range_succ]
    have h0 : ∑ i ∈ Finset.range k, PowerSeries.coeff i (sinhM ^ k) * PowerSeries.coeff (k - i) (sechM ^ (k + 1)) = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        rw [coeff_sinhM_pow_lt k i (Finset.mem_range.mp hi), zero_mul])
    rw [h0, zero_add, Nat.sub_self, coeff_sinhM_pow_diag k, hc0_s, mul_one]
  rw [mul_assoc, coeff_mul_eq_sum_range, Finset.sum_range_succ']
  have htail : ∑ i ∈ Finset.range k,
        PowerSeries.coeff (i + 1) (expPS (-3)) *
          PowerSeries.coeff (k - (i + 1)) (sinhM ^ k * sechM ^ (k + 1)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hilt : i < k := Finset.mem_range.mp hi
    have h2 : PowerSeries.coeff (k - (i + 1)) (sinhM ^ k * sechM ^ (k + 1)) = 0 := by
      rw [coeff_mul_eq_sum_range]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hjle : j ≤ k - (i + 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [coeff_sinhM_pow_lt k j (by omega), zero_mul]
    rw [h2, mul_zero]
  rw [htail, zero_add, Nat.sub_zero, hc0_e, one_mul, hprod]

/-- Normalized Laplace transform `Uhat k`:
`coeff n (Uhat k) = ((n + k)! / (k! * 4^k)) * coeff (n + k) (uPS k)`. -/
private noncomputable def Uhat (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (((k.factorial : ℚ) * (4 : ℚ) ^ k)⁻¹) *
    (((n + k).factorial : ℚ) * PowerSeries.coeff (n + k) (uPS k)))

private lemma coeff_zero_Uhat (k : ℕ) : PowerSeries.coeff 0 (Uhat k) = 1 := by
  simp only [Uhat, PowerSeries.coeff_mk, zero_add, coeff_uPS_diag]
  have hne : (k.factorial : ℚ) * (4 : ℚ) ^ k ≠ 0 := by positivity
  exact inv_mul_cancel₀ hne

private lemma Uhat_zero_coeff (n : ℕ) :
    PowerSeries.coeff n (Uhat 0) = (scaledVal n : ℚ) := by
  simp only [Uhat, PowerSeries.coeff_mk, Nat.add_zero, Nat.factorial_zero, pow_zero,
    Nat.cast_one, mul_one, inv_one, one_mul]
  exact uPS_zero_eq_scaledVal n

private lemma Uhat_rec_zero :
    (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat 0 +
      PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 2 * Uhat 1 = 1 := by
  ext n
  have hode := derivPS_uPS 0
  rw [if_pos rfl, zero_sub] at hode
  cases n with
  | zero =>
    rw [add_mul, one_mul, map_add, map_add, mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_zero,
      mul_zero, add_zero, sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc,
      PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero,
      coeff_zero_Uhat, PowerSeries.coeff_one, if_pos rfl]
  | succ n' =>
    have hc := congr_arg (PowerSeries.coeff n') hode
    simp only [derivPS, PowerSeries.coeff_mk, map_sub, map_neg, PowerSeries.coeff_C_mul] at hc
    rw [add_mul, one_mul, map_add, map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n')]
    have hx1 : PowerSeries.coeff (n' + 1) (PowerSeries.C (3 : ℚ) * PowerSeries.X * Uhat 0) =
        (3 : ℚ) * PowerSeries.coeff n' (Uhat 0) := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_succ]
    rw [hx1]
    cases n' with
    | zero =>
      have hx2 : PowerSeries.coeff 1 (PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 2 * Uhat 1) = 0 := by
        rw [sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
          coeff_X_mul_succ, coeff_X_mul_zero, mul_zero]
      rw [hx2, add_zero]
      simp only [Uhat, PowerSeries.coeff_mk, Nat.add_zero, Nat.factorial_zero, pow_zero,
        Nat.cast_one, mul_one, inv_one, one_mul]
      have hu10 : PowerSeries.coeff 0 (uPS 1) = 0 := coeff_uPS_lt 1 0 (by omega)
      rw [hu10, mul_zero, sub_zero] at hc
      norm_num at hc ⊢
      linarith
    | succ r =>
      have hx2 : PowerSeries.coeff (r + 2) (PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 2 * Uhat 1) =
          (16 : ℚ) * PowerSeries.coeff r (Uhat 1) := by
        rw [sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
          coeff_X_mul_succ, coeff_X_mul_succ]
      rw [hx2]
      simp only [Uhat, PowerSeries.coeff_mk, Nat.add_zero, Nat.factorial_zero, pow_zero,
        Nat.cast_one, mul_one, inv_one, one_mul, Nat.factorial_one, pow_one]
      have hfac : ((r + 2).factorial : ℚ) = ((r + 2 : ℕ) : ℚ) * ((r + 1).factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hne : (4 : ℚ) ≠ 0 := by norm_num
      have hc' : ((r + 2 : ℕ) : ℚ) * PowerSeries.coeff (r + 2) (uPS 0) =
          -(3 : ℚ) * PowerSeries.coeff (r + 1) (uPS 0) -
            (4 : ℚ) * PowerSeries.coeff (r + 1) (uPS 1) := by
        push_cast at hc ⊢; linarith
      have hidx : r + 1 + 1 = r + 2 := rfl
      rw [hidx, hfac, show ((r + 2 : ℕ) : ℚ) * ((r + 1).factorial : ℚ) * PowerSeries.coeff (r + 2) (uPS 0) =
        ((r + 1).factorial : ℚ) * (((r + 2 : ℕ) : ℚ) * PowerSeries.coeff (r + 2) (uPS 0)) by ring, hc']
      field_simp [hne]
      ring

private lemma Uhat_rec_succ (k : ℕ) :
    (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat (k + 1) +
      PowerSeries.C ((16 * (k + 2) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 * Uhat (k + 2) =
      Uhat k := by
  ext n
  have hode := derivPS_uPS (k + 1)
  rw [if_neg (by omega : k + 1 ≠ 0), Nat.add_sub_cancel] at hode
  cases n with
  | zero =>
    rw [add_mul, one_mul, map_add, map_add, mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_zero,
      mul_zero, add_zero, sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc,
      PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero,
      coeff_zero_Uhat, coeff_zero_Uhat]
  | succ n' =>
    have hc := congr_arg (PowerSeries.coeff (n' + (k + 1))) hode
    simp only [derivPS, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_C_mul] at hc
    rw [add_mul, one_mul, map_add, map_add]
    have hx1 : PowerSeries.coeff (n' + 1) (PowerSeries.C (3 : ℚ) * PowerSeries.X * Uhat (k + 1)) =
        (3 : ℚ) * PowerSeries.coeff n' (Uhat (k + 1)) := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_mul_succ]
    rw [hx1]
    have hne_fac : (k.factorial : ℚ) ≠ 0 := by positivity
    have hne_k1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hne_k2 : ((k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
    have hne_m : (4 : ℚ) ≠ 0 := by norm_num
    have hne_mk : (4 : ℚ) ^ k ≠ 0 := by positivity
    cases n' with
    | zero =>
      have hx2 : PowerSeries.coeff 1
          (PowerSeries.C ((16 * (k + 2) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 * Uhat (k + 2)) = 0 := by
        rw [sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
          coeff_X_mul_succ, coeff_X_mul_zero, mul_zero]
      rw [hx2, add_zero]
      simp only [Uhat, PowerSeries.coeff_mk, zero_add]
      have hu2 : PowerSeries.coeff (k + 1) (uPS (k + 2)) = 0 := coeff_uPS_lt (k + 2) (k + 1) (by omega)
      simp only [zero_add] at hc
      rw [hu2, mul_zero, sub_zero] at hc
      have hidx : 1 + (k + 1) = (k + 1) + 1 := by omega
      have hidx2 : 1 + k = k + 1 := by omega
      rw [hidx, hidx2, Nat.factorial_succ (k + 1), Nat.factorial_succ k, pow_succ (4 : ℚ) k]
      push_cast at hc ⊢
      have hc2 : (((k : ℚ) + 1 + 1) * PowerSeries.coeff (k + 1 + 1) (uPS (k + 1))) =
          ((k : ℚ) + 1) * 4 * PowerSeries.coeff (k + 1) (uPS k) -
            3 * PowerSeries.coeff (k + 1) (uPS (k + 1)) := by
        linear_combination hc
      have hmul_lhs : ((k : ℚ) + 1 + 1) * ((k + 1).factorial : ℚ) * PowerSeries.coeff (k + 1 + 1) (uPS (k + 1)) =
          ((k + 1).factorial : ℚ) * (((k : ℚ) + 1 + 1) * PowerSeries.coeff (k + 1 + 1) (uPS (k + 1))) := by ring
      rw [Nat.factorial_succ k] at hmul_lhs
      push_cast at hmul_lhs
      have heq1 : (((k : ℚ) + 1 + 1) * (((k : ℚ) + 1) * (k.factorial : ℚ)) *
            PowerSeries.coeff (k + 1 + 1) (uPS (k + 1))) =
          (((k : ℚ) + 1) * (k.factorial : ℚ)) *
            (((k : ℚ) + 1) * 4 * PowerSeries.coeff (k + 1) (uPS k) -
              3 * PowerSeries.coeff (k + 1) (uPS (k + 1))) := by
        rw [← hc2]; ring
      rw [heq1]
      field_simp [hne_fac, hne_k1, hne_m, hne_mk]
      ring
    | succ r =>
      have hx2 : PowerSeries.coeff (r + 2)
          (PowerSeries.C ((16 * (k + 2) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 * Uhat (k + 2)) =
          ((16 * (k + 2) ^ 2 : ℕ) : ℚ) * PowerSeries.coeff r (Uhat (k + 2)) := by
        rw [sq (PowerSeries.X : PowerSeries ℚ), mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
          coeff_X_mul_succ, coeff_X_mul_succ]
      rw [hx2]
      simp only [Uhat, PowerSeries.coeff_mk]
      have hidx1 : r + 2 + (k + 1) = (r + 1 + (k + 1)) + 1 := by omega
      have hidx2 : r + 2 + k = r + 1 + (k + 1) := by omega
      have hidx3 : r + (k + 2) = r + 1 + (k + 1) := by omega
      rw [hidx1, hidx2, hidx3, Nat.factorial_succ (r + 1 + (k + 1)),
        Nat.factorial_succ (k + 1), Nat.factorial_succ k,
        pow_succ (4 : ℚ) (k + 1), pow_succ (4 : ℚ) k]
      push_cast at hc ⊢
      have hrep : (((r : ℚ) + 1 + ((k : ℚ) + 1) + 1) * PowerSeries.coeff (r + 1 + (k + 1) + 1) (uPS (k + 1))) =
          ((k : ℚ) + 1) * 4 * PowerSeries.coeff (r + 1 + (k + 1)) (uPS k) -
            3 * PowerSeries.coeff (r + 1 + (k + 1)) (uPS (k + 1)) -
            ((k : ℚ) + 2) * 4 * PowerSeries.coeff (r + 1 + (k + 1)) (uPS (k + 2)) := by
        linear_combination hc
      have heq1 : (((r : ℚ) + 1 + ((k : ℚ) + 1) + 1) * ((r + 1 + (k + 1)).factorial : ℚ) *
            PowerSeries.coeff (r + 1 + (k + 1) + 1) (uPS (k + 1))) =
          ((r + 1 + (k + 1)).factorial : ℚ) *
            (((k : ℚ) + 1) * 4 * PowerSeries.coeff (r + 1 + (k + 1)) (uPS k) -
              3 * PowerSeries.coeff (r + 1 + (k + 1)) (uPS (k + 1)) -
              ((k : ℚ) + 2) * 4 * PowerSeries.coeff (r + 1 + (k + 1)) (uPS (k + 2))) := by
        rw [← hrep]; ring
      rw [heq1]
      field_simp [hne_fac, hne_k1, hne_k2, hne_m, hne_mk]
      ring

/-! ### Part 4: Exact Gladkovskii tails `exactT k` and proof of main theorem -/

private noncomputable def exactT : ℕ → PowerSeries ℚ
  | 0 => (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat 0
  | k + 1 => (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat (k + 1) * invUnit1 (Uhat k)

private lemma coeff_zero_one_add_cX :
    PowerSeries.coeff 0 (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) = 1 := by
  simp

private lemma coeff_zero_exactT (k : ℕ) : PowerSeries.coeff 0 (exactT k) = 1 := by
  cases k with
  | zero =>
    unfold exactT
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_zero_one_add_cX, coeff_zero_Uhat, mul_one]
  | succ k' =>
    unfold exactT
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_zero_one_add_cX, coeff_zero_Uhat, coeff_zero_invUnit1, mul_one, mul_one]

private lemma exactT_step (k : ℕ) : exactT k = gladStep k (exactT (k + 1)) := by
  set a : PowerSeries ℚ := PowerSeries.C ((16 * (k + 1) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2
  set b : PowerSeries ℚ := (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2
  have hb0 : PowerSeries.coeff 0 b = 1 := by
    dsimp only [b]
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_zero_one_add_cX, one_pow]
  have ha0 : PowerSeries.coeff 0 a = 0 := by
    dsimp only [a]; rw [sq (PowerSeries.X : PowerSeries ℚ), PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero]
  have hden0 : PowerSeries.coeff 0 (a + b * invUnit1 (exactT (k + 1))) = 1 := by
    rw [map_add, ha0, zero_add, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      hb0, coeff_zero_invUnit1, mul_one]
  have hinv_den := mul_invUnit1 (a + b * invUnit1 (exactT (k + 1))) hden0
  have hinv_tk1 := mul_invUnit1 (exactT (k + 1)) (coeff_zero_exactT (k + 1))
  have hkey : exactT k * (b + a * exactT (k + 1)) = b := by
    cases k with
    | zero =>
      dsimp only [a, b, exactT]
      have hrec := Uhat_rec_zero
      have hinv0 := mul_invUnit1 (Uhat 0) (coeff_zero_Uhat 0)
      have hm1 : ((16 * (0 + 1) ^ 2 : ℕ) : ℚ) = (16 : ℚ) := by norm_num
      rw [hm1]
      calc
        (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat 0 *
            ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 +
              PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 2 *
                ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat 1 * invUnit1 (Uhat 0)))
          = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 *
              ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat 0 +
                PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 2 * Uhat 1 * (Uhat 0 * invUnit1 (Uhat 0))) := by ring
        _ = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 *
              ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat 0 +
                PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 2 * Uhat 1 * 1) := by rw [hinv0]
        _ = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 * 1 := by rw [mul_one, hrec]
        _ = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 := mul_one _
    | succ k' =>
      dsimp only [a, b, exactT]
      have hrec := Uhat_rec_succ k'
      have hinv0 := mul_invUnit1 (Uhat k') (coeff_zero_Uhat k')
      have hinv1 := mul_invUnit1 (Uhat (k' + 1)) (coeff_zero_Uhat (k' + 1))
      calc
        (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat (k' + 1) * invUnit1 (Uhat k') *
            ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 +
              PowerSeries.C ((16 * (k' + 1 + 1) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 *
                ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat (k' + 2) * invUnit1 (Uhat (k' + 1))))
          = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 * invUnit1 (Uhat k') *
              ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat (k' + 1) +
                PowerSeries.C ((16 * (k' + 2) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 * Uhat (k' + 2) *
                  (Uhat (k' + 1) * invUnit1 (Uhat (k' + 1)))) := by ring
        _ = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 * invUnit1 (Uhat k') *
              ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat (k' + 1) +
                PowerSeries.C ((16 * (k' + 2) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2 * Uhat (k' + 2) * 1) := by rw [hinv1]
        _ = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 * (Uhat k' * invUnit1 (Uhat k')) := by
              rw [mul_one, hrec]; ring
        _ = (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) ^ 2 := by rw [hinv0, mul_one]
  -- Now deduce `exactT k = 1 - a * invUnit1 (a + b * invUnit1 (exactT (k + 1)))`!
  have hmul_den : exactT k * (a + b * invUnit1 (exactT (k + 1))) = b * invUnit1 (exactT (k + 1)) := by
    calc
      exactT k * (a + b * invUnit1 (exactT (k + 1)))
        = exactT k * (b + a * exactT (k + 1)) * invUnit1 (exactT (k + 1)) := by
            linear_combination -exactT k * a * hinv_tk1
      _ = b * invUnit1 (exactT (k + 1)) := by rw [hkey]
  unfold gladStep
  dsimp only
  change exactT k = 1 - a * invUnit1 (a + b * invUnit1 (exactT (k + 1)))
  calc
    exactT k = exactT k * 1 := (mul_one _).symm
    _ = exactT k * ((a + b * invUnit1 (exactT (k + 1))) *
          invUnit1 (a + b * invUnit1 (exactT (k + 1)))) := by rw [hinv_den]
    _ = (exactT k * (a + b * invUnit1 (exactT (k + 1)))) *
          invUnit1 (a + b * invUnit1 (exactT (k + 1))) := by ring
    _ = (b * invUnit1 (exactT (k + 1))) *
          invUnit1 (a + b * invUnit1 (exactT (k + 1))) := by rw [hmul_den]
    _ = (a + b * invUnit1 (exactT (k + 1))) * invUnit1 (a + b * invUnit1 (exactT (k + 1))) -
          a * invUnit1 (a + b * invUnit1 (exactT (k + 1))) := by ring
    _ = 1 - a * invUnit1 (a + b * invUnit1 (exactT (k + 1))) := by rw [hinv_den]

private lemma gladFold_exactT (k d : ℕ) :
    gladFold k d (exactT (k + d)) = exactT k := by
  induction d generalizing k with
  | zero => simp [gladFold]
  | succ d ih =>
    simp only [gladFold]
    have hidx : k + 1 + d = k + (d + 1) := by omega
    rw [← hidx, ih (k + 1)]
    exact (exactT_step k).symm

lemma solve_oeis_a156201 :
    ∀ n N : ℕ, n ≤ 2 * N → PowerSeries.coeff n (gladGF N) = (oeis_a156201Val n : ℚ) := by
  intro n N hn
  unfold gladGF
  have hc0 : PowerSeries.coeff 0 (1 : PowerSeries ℚ) = PowerSeries.coeff 0 (exactT N) := by
    rw [PowerSeries.coeff_one, if_pos rfl, coeff_zero_exactT]
  have hcongr := gladFold_congr 0 N 1 (exactT N) hc0
  let invC := invUnit1 (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X)
  have hmul := mul_congr_le (gladFold 0 N 1) (gladFold 0 N (exactT N)) invC invC (2 * N)
    hcongr (fun _ _ => rfl) n hn
  rw [hmul]
  have hfold := gladFold_exactT 0 N
  rw [Nat.zero_add] at hfold
  rw [hfold]
  have hU0 : exactT 0 * invUnit1 (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) = Uhat 0 := by
    unfold exactT
    have hinv := mul_invUnit1 (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) coeff_zero_one_add_cX
    calc
      (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) * Uhat 0 *
          invUnit1 (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X)
        = Uhat 0 * ((1 + PowerSeries.C (3 : ℚ) * PowerSeries.X) *
            invUnit1 (1 + PowerSeries.C (3 : ℚ) * PowerSeries.X)) := by ring
      _ = Uhat 0 * 1 := by rw [hinv]
      _ = Uhat 0 := mul_one _
  rw [hU0, Uhat_zero_coeff, val_eq_scaledVal]

end OMA.P_oeis_a156201

theorem OMA.solution : type_of% @OMA.S_oeis_a156201.main :=
  OMA.P_oeis_a156201.solve_oeis_a156201
