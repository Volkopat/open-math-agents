import OMAStatements.S_oeis_a277403
import Mathlib

namespace OMA.S_oeis_a277403

private def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)

private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * f j * g (n - j)

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

private lemma hdivpow_congr_mod10 {g1 g2 : ℕ → ℤ} {N : ℕ}
    (hg : ∀ m ≤ N, g1 m % 10 = g2 m % 10) :
    ∀ k n, n ≤ N → hdivpow g1 k n % 10 = hdivpow g2 k n % 10 := by
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
      calc ((Nat.choose m j : ℤ) * g1 (j + 1) * hdivpow g1 k (m - j)) % 10
          = (((Nat.choose m j : ℤ) * g1 (j + 1)) % 10 * (hdivpow g1 k (m - j) % 10)) % 10 :=
              Int.mul_emod _ _ _
        _ = ((((Nat.choose m j : ℤ) % 10 * (g1 (j + 1) % 10)) % 10) *
              (hdivpow g1 k (m - j) % 10)) % 10 := by rw [Int.mul_emod (Nat.choose m j : ℤ)]
        _ = ((((Nat.choose m j : ℤ) % 10 * (g2 (j + 1) % 10)) % 10) *
              (hdivpow g2 k (m - j) % 10)) % 10 := by rw [h1, h2]
        _ = (((Nat.choose m j : ℤ) * g2 (j + 1)) % 10 * (hdivpow g2 k (m - j) % 10)) % 10 := by
              rw [← Int.mul_emod (Nat.choose m j : ℤ)]
        _ = ((Nat.choose m j : ℤ) * g2 (j + 1) * hdivpow g2 k (m - j)) % 10 :=
              (Int.mul_emod _ _ _).symm

-- Model mod-10 sequences: A0(x) = x + x^2
private def a0 : ℕ → ℤ
  | 1 => 1
  | 2 => 2
  | _ => 0

private def g0 : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -2
  | _ => 0

private def r0 : ℕ → ℤ
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 0

private lemma hdivpow_one (g : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) : hdivpow g 1 n = g n := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [hdivpow]
    rw [Finset.sum_eq_single m]
    · simp
    · intro j hj hjm
      have hlt : j < m := by
        have := Finset.mem_range.mp hj; omega
      simp [show m - j ≠ 0 by omega]
    · intro hm; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) hm

private lemma hcomp_a0_g0_mod10 (n : ℕ) : hcomp a0 g0 n % 10 = r0 n % 10 := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | m + 7 =>
    have h0 : hcomp a0 g0 (m + 7) = 0 := by
      simp only [hcomp]
      refine Finset.sum_eq_zero fun k _ => ?_
      match k with
      | 0 => simp [a0]
      | 1 =>
        rw [hdivpow_one g0 (m + 7) (by omega)]
        simp [g0]
      | 2 =>
        have h2 : hdivpow g0 2 (m + 7) = 0 := by
          simp only [hdivpow]
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjm : j ≤ m + 6 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          by_cases hj2 : j ≤ 2
          · have hsub : m + 6 - j ≥ 4 := by omega
            have h1 : hdivpow g0 1 (m + 6 - j) = g0 (m + 6 - j) := hdivpow_one g0 _ (by omega)
            rw [h1]
            have hg0 : g0 (m + 6 - j) = 0 := by
              obtain ⟨t, ht⟩ : ∃ t, m + 6 - j = t + 4 := ⟨m + 6 - j - 4, by omega⟩
              rw [ht]; rfl
            rw [hg0, mul_zero]
          · have hg0 : g0 (j + 1) = 0 := by
              obtain ⟨t, ht⟩ : ∃ t, j + 1 = t + 4 := ⟨j + 1 - 4, by omega⟩
              rw [ht]; rfl
            rw [hg0, mul_zero, zero_mul]
        rw [h2, mul_zero]
      | r + 3 => simp [a0]
    rw [h0]; rfl

private theorem main_proved :
    ∀ (a : ℕ → ℤ) (A I : PowerSeries ℚ),
      A = PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) →
      a 0 = 0 →
      PowerSeries.constantCoeff I = 0 →
      PowerSeries.derivative ℚ I = A →
      PowerSeries.subst (PowerSeries.X - I) A = PowerSeries.X + I →
      ∀ n : ℕ, 2 < n → (10 : ℤ) ∣ a n := by
  intro a A I hA ha0 hI0 hId heq
  have hA_egf : A = egf a := hA
  set iSeq : ℕ → ℤ := fun n => if n = 0 then 0 else a (n - 1)
  have hI_egf : I = egf iSeq := by
    ext n
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hI0, ← PowerSeries.coeff_zero_eq_constantCoeff,
        egf, PowerSeries.coeff_mk]
      simp [iSeq]
    | succ m =>
      have h := congr_arg (PowerSeries.coeff m) hId
      rw [PowerSeries.coeff_derivative, hA_egf, egf, PowerSeries.coeff_mk] at h
      rw [egf, PowerSeries.coeff_mk]
      simp only [iSeq, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
      have h2 : (Nat.factorial m : ℚ) ≠ 0 := by positivity
      field_simp at h ⊢
      linarith
  set g : ℕ → ℤ := fun n => (if n = 1 then 1 else 0) - iSeq n
  set r : ℕ → ℤ := fun n => (if n = 1 then 1 else 0) + iSeq n
  have hX_egf : PowerSeries.X = egf (fun n => if n = 1 then 1 else 0) := by
    ext n
    match n with
    | 0 => simp [egf]
    | 1 => simp [egf]
    | k + 2 => simp [egf, PowerSeries.coeff_X]
  have hXg : PowerSeries.X - I = egf g := by
    rw [hX_egf, hI_egf]
    ext n
    simp only [map_sub, egf, PowerSeries.coeff_mk, g]
    push_cast; ring
  have hXr : PowerSeries.X + I = egf r := by
    rw [hX_egf, hI_egf]
    ext n
    simp only [map_add, egf, PowerSeries.coeff_mk, r]
    push_cast; ring
  have hg0 : g 0 = 0 := by simp [g, iSeq]
  have hg1 : g 1 = 1 := by simp [g, iSeq, ha0]
  have hcomp_eq : hcomp a g = r := by
    apply egf_injective
    rw [← subst_egf a g hg0, ← hXg, ← hXr, ← hA_egf]
    exact heq
  have ha1 : a 1 = 1 := by
    have := congr_fun hcomp_eq 1
    simp [hcomp, hdivpow, g, r, iSeq, ha0, Finset.sum_range_succ] at this
    exact this
  have ha2 : a 2 = 2 := by
    have := congr_fun hcomp_eq 2
    simp [hcomp, hdivpow, g, r, iSeq, ha0, ha1, Finset.sum_range_succ] at this
    omega
  have hmod10 : ∀ n : ℕ, a n % 10 = a0 n % 10 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      match n with
      | 0 => simp [ha0, a0]
      | 1 => simp [ha1, a0]
      | 2 => simp [ha2, a0]
      | m + 3 =>
        have hg_mod : ∀ k ≤ m + 3, g k % 10 = g0 k % 10 := by
          intro k hk
          match k with
          | 0 => simp [g, iSeq, g0]
          | 1 => simp [g, iSeq, ha0, g0]
          | 2 => simp [g, iSeq, ha1, g0]
          | 3 => simp [g, iSeq, ha2, g0]
          | j + 4 =>
            have hj := ih (j + 3) (by omega)
            simp only [g, iSeq, g0, show j + 4 ≠ 1 by omega, show j + 4 ≠ 0 by omega,
              ↓reduceIte, zero_sub, show j + 4 - 1 = j + 3 by omega]
            simp only [a0] at hj
            omega
        have hr_mod : r (m + 3) % 10 = r0 (m + 3) % 10 := by
          match m with
          | 0 => simp [r, iSeq, ha2, r0]
          | m' + 1 =>
            have hj := ih (m' + 3) (by omega)
            simp only [r, iSeq, r0, show m' + 1 + 3 ≠ 1 by omega, show m' + 1 + 3 ≠ 0 by omega,
              ↓reduceIte, zero_add, show m' + 1 + 3 - 1 = m' + 3 by omega]
            simp only [a0] at hj
            exact hj
        have hce := congr_fun hcomp_eq (m + 3)
        simp only [hcomp] at hce
        rw [Finset.sum_range_succ, hdivpow_self g hg1 (m + 3), mul_one] at hce
        have hsum_mod : (∑ k ∈ Finset.range (m + 3), a k * hdivpow g k (m + 3)) % 10 =
            (∑ k ∈ Finset.range (m + 3), a0 k * hdivpow g0 k (m + 3)) % 10 := by
          conv_lhs => rw [Finset.sum_int_mod]
          conv_rhs => rw [Finset.sum_int_mod]
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkm : k < m + 3 := Finset.mem_range.mp hk
          calc (a k * hdivpow g k (m + 3)) % 10
              = (a k % 10 * (hdivpow g k (m + 3) % 10)) % 10 := Int.mul_emod _ _ _
            _ = (a0 k % 10 * (hdivpow g0 k (m + 3) % 10)) % 10 := by
                  rw [ih k hkm, hdivpow_congr_mod10 hg_mod k (m + 3) le_rfl]
            _ = (a0 k * hdivpow g0 k (m + 3)) % 10 := (Int.mul_emod _ _ _).symm
        have ha0_sum : ∑ k ∈ Finset.range (m + 3), a0 k * hdivpow g0 k (m + 3) =
            hcomp a0 g0 (m + 3) := by
          symm
          simp only [hcomp]
          rw [Finset.sum_range_succ]
          simp [a0]
        have hmod := congr_arg (· % 10) hce
        rw [Int.add_emod, hsum_mod, ha0_sum, hcomp_a0_g0_mod10 (m + 3), hr_mod] at hmod
        simp only [a0]
        omega
  intro n hn
  have hm := hmod10 n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [a0, Int.zero_emod] at hm
  exact Int.dvd_of_emod_eq_zero hm

end OMA.S_oeis_a277403

theorem OMA.solution : type_of% @OMA.S_oeis_a277403.main :=
  OMA.S_oeis_a277403.main_proved
