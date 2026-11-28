import OMAStatements.S_oeis_a368631
import Mathlib

namespace OMA.S_oeis_a368631

private def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)

private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * f j * g (n - j)

private def hinv (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
    -(∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) (k + 1) : ℤ) * f (k + 1) * hinv f (n - k))

private def hdivpow (g : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, n + 1 =>
    ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * g (j + 1) * hdivpow g k (n - j)

private def hcomp (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), f k * hdivpow g k n

private lemma egf_injective {f g : ℕ → ℤ} (h : egf f = egf g) : f = g := by
  ext n
  have hn := congr_arg (PowerSeries.coeff n) h
  simp only [egf, PowerSeries.coeff_mk] at hn
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  have hq : (f n : ℚ) = (g n : ℚ) := (div_left_inj' hfac).mp hn
  exact_mod_cast hq

private lemma egf_deriv (f : ℕ → ℤ) :
    PowerSeries.derivative ℚ (egf f) = egf (fun n => f (n + 1)) := by
  ext n
  rw [PowerSeries.coeff_derivative, egf, PowerSeries.coeff_mk, egf, PowerSeries.coeff_mk]
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  field_simp

private lemma egf_mul (f g : ℕ → ℤ) : egf f * egf g = egf (hmul f g) := by
  ext n
  rw [PowerSeries.coeff_mul]
  change ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
    PowerSeries.coeff x.1 (egf f) * PowerSeries.coeff x.2 (egf g) = _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (egf f) * PowerSeries.coeff j (egf g)) n]
  simp only [egf, hmul, PowerSeries.coeff_mk, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hch := Nat.choose_mul_factorial_mul_factorial hjn
  have hchQ : (Nat.choose n j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (n - j) : ℚ) =
      (Nat.factorial n : ℚ) := by exact_mod_cast hch
  have hfj : (Nat.factorial j : ℚ) ≠ 0 := by positivity
  have hfnj : (Nat.factorial (n - j) : ℚ) ≠ 0 := by positivity
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination -(f j : ℚ) * (g (n - j) : ℚ) * hchQ

private lemma egf_mul_hinv (f : ℕ → ℤ) (hf0 : f 0 = 1) : egf f * egf (hinv f) = 1 := by
  rw [egf_mul]
  ext n
  cases n with
  | zero =>
    simp [egf, hmul, hinv, hf0]
  | succ m =>
    rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), egf, PowerSeries.coeff_mk]
    have h0 : hmul f (hinv f) (m + 1) = 0 := by
      simp only [hmul]
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, hf0, one_mul, Nat.sub_zero]
      have hsub : ∀ k ∈ Finset.range (m + 1), m + 1 - (k + 1) = m - k := fun k _ => by omega
      have hsum : ∑ k ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (k + 1) : ℤ) * f (k + 1) * hinv f (m + 1 - (k + 1)) =
          ∑ k ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (k + 1) : ℤ) * f (k + 1) * hinv f (m - k) :=
        Finset.sum_congr rfl fun k hk => by rw [hsub k hk]
      rw [hsum]
      simp only [hinv]
      ring
    rw [h0]; simp

private lemma hdivpow_zero_of_lt (g : ℕ → ℤ) : ∀ k n, n < k → hdivpow g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ m =>
      simp only [hdivpow]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [ih (m - j) (by omega), mul_zero]

private lemma hdivpow_self (g : ℕ → ℤ) (hg1 : g 1 = 1) : ∀ n, hdivpow g n n = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [hdivpow]
    rw [Finset.sum_eq_single 0]
    · simp [hg1, ih]
    · intro j hj hj0
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [hdivpow_zero_of_lt g m (m - j) (by omega), mul_zero]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ m)) h0

private lemma egf_hdivpow (g : ℕ → ℤ) (hg0 : g 0 = 0) :
    ∀ k : ℕ, egf (hdivpow g k) = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) * (egf g) ^ k := by
  intro k
  induction k with
  | zero =>
    ext n
    cases n <;> simp [egf, hdivpow, PowerSeries.coeff_one]
  | succ k ih =>
    have hderiv : PowerSeries.derivative ℚ (egf (hdivpow g (k + 1))) =
        PowerSeries.derivative ℚ (PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) * (egf g) ^ (k + 1)) := by
      rw [egf_deriv]
      have h1 : egf (fun n => hdivpow g (k + 1) (n + 1)) =
          egf (fun n => g (n + 1)) * egf (hdivpow g k) := by
        rw [egf_mul]
        rfl
      rw [h1, ih, ← egf_deriv]
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero,
        Derivation.leibniz_pow]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
      rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by ext m; simp]
      have hfac : PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) *
          PowerSeries.C ((k + 1 : ℕ) : ℚ) = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) := by
        rw [← map_mul]; congr 1
        rw [Nat.factorial_succ]; push_cast
        have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
        have h2 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
        field_simp
      calc PowerSeries.derivative ℚ (egf g) *
            (PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) * egf g ^ k)
          = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) *
              (egf g ^ k * PowerSeries.derivative ℚ (egf g)) := by ring
        _ = PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) *
              (PowerSeries.C ((k + 1 : ℕ) : ℚ) *
                (egf g ^ k * PowerSeries.derivative ℚ (egf g))) := by
            rw [← hfac]; ring
    ext n
    cases n with
    | zero =>
      simp [egf, hdivpow, hg0, zero_pow (Nat.succ_ne_zero k)]
    | succ m =>
      have h := congr_arg (PowerSeries.coeff m) hderiv
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
      have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hne h

private lemma egf_hasSubst (g : ℕ → ℤ) (hg0 : g 0 = 0) :
    PowerSeries.HasSubst (egf g) := by
  refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
  change PowerSeries.constantCoeff (egf g) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, egf, PowerSeries.coeff_mk, hg0]
  simp

private lemma subst_egf (f g : ℕ → ℤ) (hg0 : g 0 = 0) :
    PowerSeries.subst (egf g) (egf f) = egf (hcomp f g) := by
  have hs := egf_hasSubst g hg0
  ext n
  rw [PowerSeries.coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp only [egf, PowerSeries.coeff_mk, hcomp, Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := congr_arg (PowerSeries.coeff n) (egf_hdivpow g hg0 k)
    rw [PowerSeries.coeff_C_mul, egf, PowerSeries.coeff_mk] at hk
    rw [smul_eq_mul]
    calc (f k : ℚ) / (Nat.factorial k : ℚ) * PowerSeries.coeff n (egf g ^ k)
        = (f k : ℚ) * ((Nat.factorial k : ℚ)⁻¹ * PowerSeries.coeff n (egf g ^ k)) := by ring
      _ = (f k : ℚ) * ((hdivpow g k n : ℚ) / (Nat.factorial n : ℚ)) := by rw [← hk]
      _ = ((f k * hdivpow g k n : ℤ) : ℚ) / (Nat.factorial n : ℚ) := by push_cast; ring
  · intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    by_contra hnot
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hnot
    have hk0 := congr_arg (PowerSeries.coeff n) (egf_hdivpow g hg0 k)
    rw [PowerSeries.coeff_C_mul, egf, PowerSeries.coeff_mk,
      hdivpow_zero_of_lt g k n (by omega), Int.cast_zero, zero_div] at hk0
    have hfac : (Nat.factorial k : ℚ)⁻¹ ≠ 0 := by positivity
    have hpow0 : PowerSeries.coeff n (egf g ^ k) = 0 :=
      (mul_eq_zero.mp hk0.symm).resolve_left hfac
    exact hk (by rw [hpow0, smul_zero])

private lemma exp_eq_egf_one : PowerSeries.exp ℚ = egf (fun _ => 1) := by
  ext n
  rw [PowerSeries.coeff_exp, egf, PowerSeries.coeff_mk, Algebra.algebraMap_self,
    RingHom.id_apply, Int.cast_one]

private lemma X_mul_egf (f : ℕ → ℤ) :
    PowerSeries.X * egf f = egf (fun n => if n = 0 then 0 else (n : ℤ) * f (n - 1)) := by
  ext n
  cases n with
  | zero => simp [egf]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, egf, PowerSeries.coeff_mk, egf, PowerSeries.coeff_mk]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (Nat.factorial m : ℚ) ≠ 0 := by positivity
    field_simp

-- Congruence mod 3 helpers
private lemma hmul_congr_mod3 {f1 f2 g1 g2 : ℕ → ℤ} {N : ℕ}
    (hf : ∀ m ≤ N, f1 m % 3 = f2 m % 3)
    (hg : ∀ m ≤ N, g1 m % 3 = g2 m % 3) :
    ∀ n ≤ N, hmul f1 g1 n % 3 = hmul f2 g2 n % 3 := by
  intro n hn
  simp only [hmul]
  conv_lhs => rw [Finset.sum_int_mod]
  conv_rhs => rw [Finset.sum_int_mod]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 := hf j (by omega)
  have h2 := hg (n - j) (by omega)
  calc ((Nat.choose n j : ℤ) * f1 j * g1 (n - j)) % 3
      = (((Nat.choose n j : ℤ) * f1 j) % 3 * (g1 (n - j) % 3)) % 3 := Int.mul_emod _ _ _
    _ = ((((Nat.choose n j : ℤ) % 3 * (f1 j % 3)) % 3) * (g1 (n - j) % 3)) % 3 := by
          rw [Int.mul_emod (Nat.choose n j : ℤ)]
    _ = ((((Nat.choose n j : ℤ) % 3 * (f2 j % 3)) % 3) * (g2 (n - j) % 3)) % 3 := by rw [h1, h2]
    _ = (((Nat.choose n j : ℤ) * f2 j) % 3 * (g2 (n - j) % 3)) % 3 := by
          rw [← Int.mul_emod (Nat.choose n j : ℤ)]
    _ = ((Nat.choose n j : ℤ) * f2 j * g2 (n - j)) % 3 := (Int.mul_emod _ _ _).symm

private lemma hinv_congr_mod3 {f1 f2 : ℕ → ℤ} {N : ℕ}
    (hf : ∀ m ≤ N, f1 m % 3 = f2 m % 3) :
    ∀ n ≤ N, hinv f1 n % 3 = hinv f2 n % 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [hinv]
    | succ m =>
      simp only [hinv]
      have hsum : (∑ k ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (k + 1) : ℤ) * f1 (k + 1) * hinv f1 (m - k)) % 3 =
          (∑ k ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (k + 1) : ℤ) * f2 (k + 1) * hinv f2 (m - k)) % 3 := by
        conv_lhs => rw [Finset.sum_int_mod]
        conv_rhs => rw [Finset.sum_int_mod]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1 := hf (k + 1) (by omega)
        have h2 := ih (m - k) (by omega) (by omega)
        calc ((Nat.choose (m + 1) (k + 1) : ℤ) * f1 (k + 1) * hinv f1 (m - k)) % 3
            = (((Nat.choose (m + 1) (k + 1) : ℤ) * f1 (k + 1)) % 3 * (hinv f1 (m - k) % 3)) % 3 :=
                Int.mul_emod _ _ _
          _ = ((((Nat.choose (m + 1) (k + 1) : ℤ) % 3 * (f1 (k + 1) % 3)) % 3) *
                (hinv f1 (m - k) % 3)) % 3 := by rw [Int.mul_emod (Nat.choose (m + 1) (k + 1) : ℤ)]
          _ = ((((Nat.choose (m + 1) (k + 1) : ℤ) % 3 * (f2 (k + 1) % 3)) % 3) *
                (hinv f2 (m - k) % 3)) % 3 := by rw [h1, h2]
          _ = (((Nat.choose (m + 1) (k + 1) : ℤ) * f2 (k + 1)) % 3 * (hinv f2 (m - k) % 3)) % 3 := by
                rw [← Int.mul_emod (Nat.choose (m + 1) (k + 1) : ℤ)]
          _ = ((Nat.choose (m + 1) (k + 1) : ℤ) * f2 (k + 1) * hinv f2 (m - k)) % 3 :=
                (Int.mul_emod _ _ _).symm
      omega

private lemma hdivpow_congr_mod3 {g1 g2 : ℕ → ℤ} {N : ℕ}
    (hg : ∀ m ≤ N, g1 m % 3 = g2 m % 3) :
    ∀ k n, n ≤ N → hdivpow g1 k n % 3 = hdivpow g2 k n % 3 := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ m =>
      simp only [hdivpow]
      conv_lhs => rw [Finset.sum_int_mod]
      conv_rhs => rw [Finset.sum_int_mod]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 := hg (j + 1) (by omega)
      have h2 := ih (m - j) (by omega)
      calc ((Nat.choose m j : ℤ) * g1 (j + 1) * hdivpow g1 k (m - j)) % 3
          = (((Nat.choose m j : ℤ) * g1 (j + 1)) % 3 * (hdivpow g1 k (m - j) % 3)) % 3 :=
              Int.mul_emod _ _ _
        _ = ((((Nat.choose m j : ℤ) % 3 * (g1 (j + 1) % 3)) % 3) *
              (hdivpow g1 k (m - j) % 3)) % 3 := by rw [Int.mul_emod (Nat.choose m j : ℤ)]
        _ = ((((Nat.choose m j : ℤ) % 3 * (g2 (j + 1) % 3)) % 3) *
              (hdivpow g2 k (m - j) % 3)) % 3 := by rw [h1, h2]
        _ = (((Nat.choose m j : ℤ) * g2 (j + 1)) % 3 * (hdivpow g2 k (m - j) % 3)) % 3 := by
              rw [← Int.mul_emod (Nat.choose m j : ℤ)]
        _ = ((Nat.choose m j : ℤ) * g2 (j + 1) * hdivpow g2 k (m - j)) % 3 :=
              (Int.mul_emod _ _ _).symm

private lemma hmul_ones (n : ℕ) : hmul (fun _ => 1) (fun _ => 1) n = (2 : ℤ) ^ n := by
  simp only [hmul, mul_one]
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast; rfl

private lemma hinv_ones (n : ℕ) : hinv (fun _ => 1) n = (-1 : ℤ) ^ n := by
  have heq : egf (hinv (fun _ => 1)) = egf (fun k => (-1 : ℤ) ^ k) := by
    have h1 : egf (fun _ => 1) * egf (fun k => (-1 : ℤ) ^ k) = 1 := by
      rw [egf_mul]
      ext m
      cases m with
      | zero => simp [egf, hmul]
      | succ r =>
        rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero r), egf, PowerSeries.coeff_mk]
        have hzero : hmul (fun _ => 1) (fun k => (-1 : ℤ) ^ k) (r + 1) = 0 := by
          simp only [hmul, mul_one]
          have hbin := add_pow (1 : ℤ) (-1 : ℤ) (r + 1)
          simp only [add_neg_cancel, zero_pow (Nat.succ_ne_zero r), one_pow, one_mul] at hbin
          rw [hbin]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [hzero]; simp
    have h2 := egf_mul_hinv (fun _ => 1) rfl
    calc egf (hinv (fun _ => 1))
        = (egf (fun k => (-1 : ℤ) ^ k) * egf (fun _ => 1)) * egf (hinv (fun _ => 1)) := by
            rw [mul_comm (egf (fun k => (-1 : ℤ) ^ k)), h1, one_mul]
      _ = egf (fun k => (-1 : ℤ) ^ k) * (egf (fun _ => 1) * egf (hinv (fun _ => 1))) :=
            mul_assoc _ _ _
      _ = egf (fun k => (-1 : ℤ) ^ k) := by rw [h2, mul_one]
  exact congr_fun (egf_injective heq) n

private lemma pow_neg_one_mod3 (k : ℕ) : ((-1 : ℤ) ^ k) % 3 = ((2 : ℤ) ^ k) % 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Int.mul_emod, Int.mul_emod ((2 : ℤ) ^ k), ih]
    omega

private theorem main_proved :
    ∀ (a : ℕ → ℤ) (A B : PowerSeries ℚ),
      A = PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) →
      a 0 = 1 →
      A * B = 1 →
      PowerSeries.subst (PowerSeries.X * B) A =
        PowerSeries.subst (PowerSeries.X * A ^ 2) (PowerSeries.exp ℚ) →
      ∀ n : ℕ, a n % 3 = 1 := by
  intro a A B hA ha0 hAB heq
  have hA_egf : A = egf a := hA
  have hB_egf : B = egf (hinv a) := by
    have h1 := egf_mul_hinv a ha0
    calc B = (egf (hinv a) * A) * B := by rw [hA_egf, mul_comm (egf (hinv a)), h1, one_mul]
      _ = egf (hinv a) * (A * B) := mul_assoc _ _ _
      _ = egf (hinv a) := by rw [hAB, mul_one]
  set g1 : ℕ → ℤ := fun n => if n = 0 then 0 else (n : ℤ) * hinv a (n - 1)
  set g2 : ℕ → ℤ := fun n => if n = 0 then 0 else (n : ℤ) * hmul a a (n - 1)
  have hg1_0 : g1 0 = 0 := rfl
  have hg2_0 : g2 0 = 0 := rfl
  have hg1_1 : g1 1 = 1 := by simp [g1, hinv]
  have hg2_1 : g2 1 = 1 := by simp [g2, hmul, ha0]
  have hcomp_eq : hcomp a g1 = hcomp (fun _ => 1) g2 := by
    apply egf_injective
    rw [← subst_egf a g1 hg1_0, ← subst_egf (fun _ => 1) g2 hg2_0, ← exp_eq_egf_one]
    have hXB : PowerSeries.X * B = egf g1 := by rw [hB_egf, X_mul_egf]
    have hXA2 : PowerSeries.X * A ^ 2 = egf g2 := by
      rw [hA_egf, pow_two, egf_mul, X_mul_egf]
    rw [← hXB, ← hXA2, ← hA_egf]
    exact heq
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · have hprev : ∀ m ≤ n - 1, a m % 3 = ((fun _ : ℕ => (1 : ℤ)) m) % 3 := by
        intro m hm; simp [ih m (by omega)]
      have hg_mod3 : ∀ m ≤ n, g1 m % 3 = g2 m % 3 := by
        intro m hm
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · simp [g1, g2]
        · simp only [g1, g2, show m ≠ 0 by omega, ↓reduceIte]
          have hinv_m : hinv a (m - 1) % 3 = (-1 : ℤ) ^ (m - 1) % 3 := by
            rw [← hinv_ones (m - 1)]
            exact hinv_congr_mod3 hprev (m - 1) (by omega)
          have hmul_m : hmul a a (m - 1) % 3 = (2 : ℤ) ^ (m - 1) % 3 := by
            rw [← hmul_ones (m - 1)]
            exact hmul_congr_mod3 hprev hprev (m - 1) (by omega)
          rw [Int.mul_emod, Int.mul_emod (m : ℤ), hinv_m, hmul_m, pow_neg_one_mod3]
      have hce := congr_fun hcomp_eq n
      simp only [hcomp] at hce
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        hdivpow_self g1 hg1_1 n, hdivpow_self g2 hg2_1 n, mul_one, one_mul] at hce
      have hsums : (∑ k ∈ Finset.range n, a k * hdivpow g1 k n) % 3 =
          (∑ k ∈ Finset.range n, (1 : ℤ) * hdivpow g2 k n) % 3 := by
        conv_lhs => rw [Finset.sum_int_mod]
        conv_rhs => rw [Finset.sum_int_mod]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k < n := Finset.mem_range.mp hk
        rw [Int.mul_emod, Int.mul_emod (1 : ℤ), ih k hkn,
          hdivpow_congr_mod3 hg_mod3 k n le_rfl]
        simp
      have hmod := congr_arg (· % 3) hce
      rw [Int.add_emod, Int.add_emod _ 1, hsums] at hmod
      omega

end OMA.S_oeis_a368631

theorem OMA.solution : type_of% @OMA.S_oeis_a368631.main :=
  OMA.S_oeis_a368631.main_proved
