import OMAStatements.S_mse_1940934

namespace MSE1940934

open scoped Classical ComplexConjugate
open ArithmeticFunction Complex Filter MeasureTheory Set Topology
open OMA.S_mse_1940934

/-! === Block 1: Arithmetic identity, Dirichlet series, and Mellin integral -/

lemma nonSqf_four_mul_succ (k : ℕ) : NonSqf (4 * (k + 1)) := by
  refine ⟨by positivity, fun hsq => ?_⟩
  have h2 : IsUnit (2 : ℕ) := hsq 2 ⟨k + 1, by ring⟩
  norm_num at h2

lemma nonSqf_infinite : {m : ℕ | NonSqf m}.Infinite :=
  Set.infinite_of_injective_forall_mem
    (fun _ _ h => by omega) nonSqf_four_mul_succ

/-- Signed coefficient `a m = (λ(m) - μ(m)) * m`. -/
def a (m : ℕ) : ℤ := (liouville m - moebius m) * m

lemma a_zero : a 0 = 0 := by simp [a]

lemma a_eq_ite (m : ℕ) :
    a m = if NonSqf m then (-1 : ℤ) ^ cardFactors m * m else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [a, NonSqf]
  · have hpos : 0 < m := Nat.pos_of_ne_zero hm
    by_cases hsq : Squarefree m
    · simp [a, NonSqf, hpos, hsq, liouville_apply hm]
    · simp [a, NonSqf, hpos, hsq, liouville_apply hm]

lemma abs_a_le (m : ℕ) : |a m| ≤ (m : ℤ) := by
  rw [a_eq_ite]
  split_ifs
  · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Int.natCast_nonneg m)]
  · exact Int.natCast_nonneg m

/-- Partial sum step function `A x = ∑_{m ≤ ⌊x⌋₊} a m`. -/
noncomputable def A (x : ℝ) : ℝ := ∑ m ∈ Finset.range (⌊x⌋₊ + 1), (a m : ℝ)

lemma A_nat_eq_S (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), a m = S (Nat.count NonSqf (M + 1)) := by
  rw [S]
  have hsum :
      ∑ m ∈ Finset.range (M + 1), a m =
        ∑ m ∈ (Finset.range (M + 1)).filter NonSqf, (-1 : ℤ) ^ cardFactors m * m := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun m _ => a_eq_ite m
  rw [hsum]
  symm
  refine Finset.sum_nbij q ?_ ?_ ?_ (fun _ _ => rfl)
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.nth_lt_of_lt_count hk, Nat.nth_mem_of_infinite nonSqf_infinite k⟩
  · exact (Nat.nth_strictMono nonSqf_infinite).injective.injOn
  · intro m hm
    rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hm
    refine ⟨Nat.count NonSqf m, ?_, Nat.nth_count hm.2⟩
    rw [Finset.coe_range, Set.mem_Iio]
    have hlt : Nat.count NonSqf m < Nat.count NonSqf (m + 1) := by
      rw [Nat.count_succ, if_pos hm.2]; omega
    exact lt_of_lt_of_le hlt (Nat.count_monotone NonSqf hm.1)

lemma A_eq_S (x : ℝ) : A x = (S (Nat.count NonSqf (⌊x⌋₊ + 1)) : ℝ) := by
  rw [A, ← Int.cast_sum, A_nat_eq_S]

lemma A_nonneg_of_S_nonneg {N₀ : ℕ} (hS : ∀ n ≥ N₀, 0 ≤ S n) :
    ∀ x : ℝ, (q N₀ : ℝ) ≤ x → 0 ≤ A x := by
  intro x hx
  rw [A_eq_S]
  have hfl : q N₀ ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hcnt : N₀ ≤ Nat.count NonSqf (⌊x⌋₊ + 1) := by
    calc N₀ = Nat.count NonSqf (q N₀) := (Nat.count_nth_of_infinite nonSqf_infinite N₀).symm
      _ ≤ Nat.count NonSqf (⌊x⌋₊ + 1) := Nat.count_monotone NonSqf (by omega)
  exact_mod_cast hS _ hcnt

lemma A_nonpos_of_S_nonpos {N₀ : ℕ} (hS : ∀ n ≥ N₀, S n ≤ 0) :
    ∀ x : ℝ, (q N₀ : ℝ) ≤ x → A x ≤ 0 := by
  intro x hx
  rw [A_eq_S]
  have hfl : q N₀ ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hcnt : N₀ ≤ Nat.count NonSqf (⌊x⌋₊ + 1) := by
    calc N₀ = Nat.count NonSqf (q N₀) := (Nat.count_nth_of_infinite nonSqf_infinite N₀).symm
      _ ≤ Nat.count NonSqf (⌊x⌋₊ + 1) := Nat.count_monotone NonSqf (by omega)
  exact_mod_cast hS _ hcnt

lemma A_nat_sub_prev (m : ℕ) (hm : 1 ≤ m) :
    A (m : ℝ) - A ((m - 1 : ℕ) : ℝ) = (a m : ℝ) := by
  simp only [A, Nat.floor_natCast]
  have hm1 : m - 1 + 1 = m := by omega
  rw [hm1, Finset.sum_range_succ, add_sub_cancel_left]

lemma A_const_on_Ico (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ico (m : ℝ) ((m + 1 : ℕ) : ℝ)) :
    A x = A (m : ℝ) := by
  have hfl : ⌊x⌋₊ = m := by
    rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg m) hx.1)]
    exact ⟨hx.1, by simpa using hx.2⟩
  simp [A, hfl]

lemma abs_A_le (x : ℝ) (hx : 1 ≤ x) : |A x| ≤ x ^ 2 := by
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx : ((1 : ℕ) : ℝ) ≤ x)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h1 : |A x| ≤ ∑ m ∈ Finset.range (N + 1), (m : ℝ) := by
    calc |A x| = |∑ m ∈ Finset.range (N + 1), (a m : ℝ)| := rfl
      _ ≤ ∑ m ∈ Finset.range (N + 1), |(a m : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.range (N + 1), (m : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        exact_mod_cast abs_a_le m
  have h2 : (∑ m ∈ Finset.range (N + 1), (m : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
    have hnat : (∑ m ∈ Finset.range (N + 1), m) * 2 = N * (N + 1) := by
      rw [Finset.sum_range_id_mul_two, Nat.add_sub_cancel, mul_comm]
    have hcast : (∑ m ∈ Finset.range (N + 1), (m : ℝ)) * 2 = (N : ℝ) * ((N : ℝ) + 1) := by
      simpa [Nat.cast_sum] using congr_arg (Nat.cast (R := ℝ)) hnat
    linarith
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have h3 : (N : ℝ) * ((N : ℝ) + 1) / 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have h4 : (N : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
  linarith

lemma A_measurable : Measurable A := by
  have hcomp : A = (fun n : ℕ => ∑ m ∈ Finset.range (n + 1), (a m : ℝ)) ∘ Nat.floor := rfl
  rw [hcomp]
  exact (measurable_of_countable _).comp (Monotone.measurable Nat.floor_mono)

/-- Indicator of positive perfect squares as an `ArithmeticFunction ℤ`. -/
def sqInd : ArithmeticFunction ℤ where
  toFun n := if n = 0 then 0 else if IsSquare n then 1 else 0
  map_zero' := by simp

lemma isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := fun h => hn (by simp [h])
    rw [Nat.factorization_mul hr hr, Finsupp.add_apply]
    exact ⟨r.factorization p, by ring⟩
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := h p
    omega

lemma sqInd_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    sqInd (a * b) = sqInd a * sqInd b := by
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  have hiff : IsSquare (a * b) ↔ IsSquare a ∧ IsSquare b := by
    rw [isSquare_iff_even_factorization hab0, isSquare_iff_even_factorization ha,
      isSquare_iff_even_factorization hb]
    constructor
    · intro h
      refine ⟨fun p => ?_, fun p => ?_⟩
      · specialize h p
        rw [Nat.factorization_mul ha hb, Finsupp.add_apply] at h
        by_cases hpa : a.factorization p = 0
        · simp [hpa]
        · have hpb : b.factorization p = 0 := by
            by_contra hpb
            have hdvd : p ∣ Nat.gcd a b :=
              Nat.dvd_gcd (Nat.dvd_of_factorization_pos hpa)
                (Nat.dvd_of_factorization_pos hpb)
            rw [hab.gcd_eq_one] at hdvd
            have hp := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hpa)
            exact hp.not_dvd_one hdvd
          simpa [hpb] using h
      · specialize h p
        rw [Nat.factorization_mul ha hb, Finsupp.add_apply] at h
        by_cases hpb : b.factorization p = 0
        · simp [hpb]
        · have hpa : a.factorization p = 0 := by
            by_contra hpa
            have hdvd : p ∣ Nat.gcd a b :=
              Nat.dvd_gcd (Nat.dvd_of_factorization_pos hpa)
                (Nat.dvd_of_factorization_pos hpb)
            rw [hab.gcd_eq_one] at hdvd
            have hp := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hpa)
            exact hp.not_dvd_one hdvd
          simpa [hpa] using h
    · rintro ⟨h1, h2⟩ p
      rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
      exact (h1 p).add (h2 p)
  simp only [sqInd, ArithmeticFunction.coe_mk, hab0, ha, hb, ite_false]
  by_cases h1 : IsSquare a <;> by_cases h2 : IsSquare b
  · simp [h1, h2, hiff.mpr ⟨h1, h2⟩]
  · have h12 : ¬ IsSquare (a * b) := fun h => h2 (hiff.mp h).2
    simp [h1, h2, h12]
  · have h12 : ¬ IsSquare (a * b) := fun h => h1 (hiff.mp h).1
    simp [h1, h2, h12]
  · have h12 : ¬ IsSquare (a * b) := fun h => h1 (hiff.mp h).1
    simp [h1, h2, h12]

lemma sum_neg_one_pow_range (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hk : Even k
    · have hk1 : ¬ Even (k + 1) := by
        obtain ⟨m, hm⟩ := hk; rintro ⟨r, hr⟩; omega
      rw [if_pos hk, if_neg hk1, pow_succ, hk.neg_one_pow]; ring
    · have hk1 : Even (k + 1) := by
        rcases Nat.even_or_odd k with h | ⟨m, hm⟩
        · exact absurd h hk
        · exact ⟨m + 1, by omega⟩
      have hodd : Odd k := Nat.not_even_iff_odd.mp hk
      rw [if_neg hk, if_pos hk1, pow_succ, hodd.neg_one_pow]; ring

lemma liouville_mul_zeta_eq_sqInd :
    (liouville * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) = sqInd := by
  ext n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [sqInd]
  | one => simp [sqInd, liouville_apply_one]
  | prime_pow p k hp hk =>
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    have hsum : ∑ i ∈ Finset.range (k + 1), liouville (p ^ i) =
        ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [liouville_apply (pow_ne_zero i hp.ne_zero), cardFactors_pow, cardFactors_apply_prime hp,
        mul_one]
    rw [hsum, sum_neg_one_pow_range]
    have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
    have hsq : IsSquare (p ^ k) ↔ Even k := by
      rw [isSquare_iff_even_factorization hpk0]
      constructor
      · intro h
        have hp' := h p
        rwa [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at hp'
      · intro h q
        rw [Nat.Prime.factorization_pow hp, Finsupp.single_apply]
        split_ifs
        · exact h
        · exact ⟨0, rfl⟩
    simp only [sqInd, ArithmeticFunction.coe_mk, hpk0, ite_false, hsq]
  | coprime a b ha hb hab ha' hb' =>
    rw [IsMultiplicative.map_mul_of_coprime
        (isMultiplicative_liouville.mul isMultiplicative_zeta.natCast) hab,
      ha', hb', sqInd_mul_of_coprime (zero_lt_one.trans ha).ne' (zero_lt_one.trans hb).ne' hab]

lemma LSeriesSummable_liouville {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => (liouville n : ℂ)) w := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => ?_) hw
  rw [liouville_apply hn]
  simp

lemma LSeries_sqInd_eq_zeta_two_mul {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n => (sqInd n : ℂ)) w = riemannZeta (2 * w) := by
  have hw2 : 1 < (2 * w).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hw2, LSeries]
  have hinj : Function.Injective (fun k : ℕ => k ^ 2) := fun x y h => by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hsupp : ∀ n : ℕ, n ∉ Set.range (fun k : ℕ => k ^ 2) →
      LSeries.term (fun n => (sqInd n : ℂ)) w n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hnsq : ¬ IsSquare n := by
        rintro ⟨k, hk⟩
        exact hn ⟨k, by dsimp; rw [sq, hk]⟩
      simp [sqInd, hn0, hnsq]
  rw [← hinj.tsum_eq (fun n hn => by by_contra h; exact hn (hsupp n h))]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    have h2w : 2 * w ≠ 0 := Complex.ne_zero_of_one_lt_re hw2
    simp [zero_cpow h2w]
  · have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
    have hsq : IsSquare (k ^ 2) := ⟨k, sq k⟩
    rw [LSeries.term_of_ne_zero hk2]
    simp only [sqInd, ArithmeticFunction.coe_mk, hk2, ite_false, hsq, ite_true, Int.cast_one]
    congr 1
    have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    rw [Nat.cast_pow, ← Complex.cpow_natCast (k : ℂ) 2, ← Complex.cpow_mul]
    · norm_cast
    · rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hk0.le, ← Complex.ofReal_natCast 2,
        ← Complex.ofReal_mul, Complex.ofReal_im]
      linarith [Real.pi_pos]
    · rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hk0.le, ← Complex.ofReal_natCast 2,
        ← Complex.ofReal_mul, Complex.ofReal_im]
      linarith [Real.pi_pos]

lemma LSeries_liouville_eq {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n => (liouville n : ℂ)) w = riemannZeta (2 * w) / riemannZeta w := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) w := LSeriesSummable_one_iff.mpr hw
  have hl : LSeriesSummable (fun n => (liouville n : ℂ)) w := LSeriesSummable_liouville hw
  have hconv := LSeries_convolution' hl h1
  have hcz : LSeries.convolution (fun n => (liouville n : ℂ)) (1 : ℕ → ℂ) = fun n => (sqInd n : ℂ) := by
    ext n
    rw [LSeries.convolution_one_eq_convolution_zeta, LSeries.convolution_def]
    have hmul := congr_arg (fun f : ArithmeticFunction ℤ => (f n : ℂ)) liouville_mul_zeta_eq_sqInd
    rw [ArithmeticFunction.mul_apply, Int.cast_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 : p.2 ≠ 0 := (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2
    simp [hp2]
  rw [hcz, LSeries_sqInd_eq_zeta_two_mul hw, LSeries_one_eq_riemannZeta hw] at hconv
  exact eq_div_of_mul_eq (riemannZeta_ne_zero_of_one_lt_re hw) hconv.symm

lemma tsum_a_div_cpow {w : ℂ} (hw : 1 < w.re) :
    Summable (fun m : ℕ => (a m : ℂ) / (m : ℂ) ^ (w + 1)) ∧
    ∑' m : ℕ, (a m : ℂ) / (m : ℂ) ^ (w + 1) = (riemannZeta (2 * w) - 1) / riemannZeta w := by
  have hterm : ∀ m : ℕ,
      (a m : ℂ) / (m : ℂ) ^ (w + 1) =
        LSeries.term (fun n => (liouville n : ℂ)) w m -
        LSeries.term (fun n => (moebius n : ℂ)) w m := by
    intro m
    by_cases hm : m = 0
    · subst hm; simp [a]
    · have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
      rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hm, a, Int.cast_mul, Int.cast_sub,
        Int.cast_natCast, Complex.cpow_add _ _ hmc, Complex.cpow_one,
        mul_div_mul_right _ _ hmc, sub_div]
  have hl : LSeriesSummable (fun n => (liouville n : ℂ)) w := LSeriesSummable_liouville hw
  have hm : LSeriesSummable (fun n => (moebius n : ℂ)) w :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hw
  refine ⟨(Summable.sub hl hm).congr fun m => (hterm m).symm, ?_⟩
  rw [tsum_congr hterm, Summable.tsum_sub hl hm]
  change LSeries (fun n => (liouville n : ℂ)) w - LSeries (fun n => (moebius n : ℂ)) w = _
  have hmu : LSeries (fun n => (moebius n : ℂ)) w = 1 / riemannZeta w := by
    have h := LSeries_one_mul_Lseries_moebius hw
    rw [LSeries_one_eq_riemannZeta hw] at h
    exact eq_div_of_mul_eq (riemannZeta_ne_zero_of_one_lt_re hw) (mul_comm (riemannZeta w) _ ▸ h)
  rw [LSeries_liouville_eq hw, hmu, sub_div]

lemma intervalIntegral_cpow_neg_sub_two {w : ℂ} (hw : 1 < w.re) (m : ℕ) (hm : 1 ≤ m) :
    ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (x : ℂ) ^ (-w - 2) =
      (((m : ℂ) ^ (w + 1))⁻¹ - (((m + 1 : ℕ) : ℂ) ^ (w + 1))⁻¹) / (w + 1) := by
  have hw1 : w + 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp at this
    linarith
  have hF : ∀ x ∈ Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ),
      HasDerivAt (fun t : ℝ => -((t : ℂ) ^ (-(w + 1))) / (w + 1)) ((x : ℂ) ^ (-w - 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (by exact_mod_cast hm) hx.1
    have hcp : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-(w + 1)))
        (-(w + 1) * (x : ℂ) ^ (-(w + 1) - 1)) x := by
      have h1 := ((hasDerivAt_id (x : ℂ)).cpow_const (c := -(w + 1))
        (Or.inl (by exact_mod_cast hxpos : 0 < (x : ℂ).re))).comp_ofReal
      simpa using h1
    have h2 := hcp.neg.div_const (w + 1)
    have hval : -(-(w + 1) * (x : ℂ) ^ (-(w + 1) - 1)) / (w + 1) = (x : ℂ) ^ (-w - 2) := by
      have hexp : -(w + 1) - 1 = -w - 2 := by ring
      rw [hexp]
      field_simp [hw1]
    rwa [hval] at h2
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-w - 2)) (Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (by exact_mod_cast hm) hx.1
    exact ((Complex.continuousAt_ofReal_cpow_const x (-w - 2) (Or.inr hxpos.ne')).continuousWithinAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  simp only [Complex.cpow_neg, Complex.ofReal_natCast]
  ring

lemma intervalIntegral_A_eq {w : ℂ} (hw : 1 < w.re) (M : ℕ) (hM : 1 ≤ M) :
    ∫ x in (1 : ℝ)..(M : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 2) =
      ((∑ m ∈ Finset.range M, (a m : ℂ) / (m : ℂ) ^ (w + 1)) -
        (A ((M - 1 : ℕ) : ℝ) : ℂ) / (M : ℂ) ^ (w + 1)) / (w + 1) := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp [A, a_zero]
  | succ m hm ih =>
    have hne_ae : ∀ᵐ x : ℝ ∂volume, x ≠ ((m + 1 : ℕ) : ℝ) := by
      rw [ae_iff]
      simp
    have hstep :
        ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 2) =
          (A (m : ℝ) : ℂ) * ((((m : ℂ) ^ (w + 1))⁻¹ - (((m + 1 : ℕ) : ℂ) ^ (w + 1))⁻¹) / (w + 1)) := by
      have hcongr :
          ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 2) =
            ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (A (m : ℝ) : ℂ) * (x : ℂ) ^ (-w - 2) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hne_ae] with x hx hmem
        rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ m)] at hmem
        have hIco : x ∈ Set.Ico (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
          ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 hx⟩
        rw [A_const_on_Ico m hIco]
      rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral_cpow_neg_sub_two hw m hm]
    have hint1 : IntervalIntegrable (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2)) volume 1 m := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hm)]
      refine IntegrableOn.mono_set (t := Set.Ioi (1 : ℝ)) ?_ (fun x hx => hx.1)
      have hmeas : AEStronglyMeasurable (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2))
          (volume.restrict (Set.Ioi 1)) := by
        refine (Complex.continuous_ofReal.measurable.comp A_measurable).aestronglyMeasurable.mul ?_
        exact (ContinuousOn.aestronglyMeasurable (fun x hx =>
          (Complex.continuousAt_ofReal_cpow_const x (-w - 2)
            (Or.inr (lt_trans zero_lt_one hx).ne')).continuousWithinAt) measurableSet_Ioi)
      refine (integrableOn_Ioi_rpow_of_lt (show -w.re < -1 by linarith) zero_lt_one).mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hre : (-w - 2).re = -w.re - 2 := by simp
      rw [hre]
      calc |A x| * x ^ (-w.re - 2) ≤ x ^ 2 * x ^ (-w.re - 2) :=
            mul_le_mul_of_nonneg_right (abs_A_le x (le_of_lt hx)) (Real.rpow_nonneg hx0.le _)
        _ = x ^ (-w.re) := by
            rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0]
            norm_num
    have hint2 : IntervalIntegrable (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2)) volume m
        ((m + 1 : ℕ) : ℝ) := by
      have hcongr :
          (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2)) =ᵐ[volume.restrict (Set.uIoc (m : ℝ) ((m + 1 : ℕ) : ℝ))]
            (fun x : ℝ => (A (m : ℝ) : ℂ) * (x : ℂ) ^ (-w - 2)) := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc,
          ae_restrict_of_ae hne_ae] with x hmem hx
        rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ m)] at hmem
        rw [A_const_on_Ico m ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 hx⟩]
      have hcont : IntervalIntegrable (fun x : ℝ => (A (m : ℝ) : ℂ) * (x : ℂ) ^ (-w - 2))
          volume (m : ℝ) ((m + 1 : ℕ) : ℝ) := by
        refine (ContinuousOn.intervalIntegrable fun x hx => ?_).const_mul _
        rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
        have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hm) hx.1
        exact (Complex.continuousAt_ofReal_cpow_const x (-w - 2) (Or.inr hx0.ne')).continuousWithinAt
      exact hcont.congr_ae hcongr.symm
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, ih, hstep]
    rw [Finset.sum_range_succ, Nat.add_sub_cancel]
    have hdiff : (A (m : ℝ) : ℂ) - (A ((m - 1 : ℕ) : ℝ) : ℂ) = (a m : ℂ) := by
      have h := A_nat_sub_prev m hm
      exact_mod_cast h
    simp only [div_eq_mul_inv]
    linear_combination hdiff * ((m : ℂ) ^ (w + 1))⁻¹ * (w + 1)⁻¹

lemma mellin_A_integrableOn {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi 1) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2))
      (volume.restrict (Set.Ioi 1)) := by
    refine (Complex.continuous_ofReal.measurable.comp A_measurable).aestronglyMeasurable.mul ?_
    exact (ContinuousOn.aestronglyMeasurable (fun x hx =>
      (Complex.continuousAt_ofReal_cpow_const x (-w - 2)
        (Or.inr (lt_trans zero_lt_one hx).ne')).continuousWithinAt) measurableSet_Ioi)
  refine (integrableOn_Ioi_rpow_of_lt (show -w.re < -1 by linarith) zero_lt_one).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hre : (-w - 2).re = -w.re - 2 := by simp
  rw [hre]
  calc |A x| * x ^ (-w.re - 2) ≤ x ^ 2 * x ^ (-w.re - 2) :=
        mul_le_mul_of_nonneg_right (abs_A_le x (le_of_lt hx)) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-w.re) := by
        rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0]
        norm_num

lemma mellin_A_eq {w : ℂ} (hw : 1 < w.re) :
    ∫ x in Set.Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 2) =
      (riemannZeta (2 * w) - 1) / ((w + 1) * riemannZeta w) := by
  have hint := mellin_A_integrableOn hw
  have hlhs : Tendsto (fun M : ℕ => ∫ x in (1 : ℝ)..(M : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 2))
      atTop (𝓝 (∫ x in Set.Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 2))) :=
    (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id).comp tendsto_natCast_atTop_atTop
  have ⟨hsumm, htsum⟩ := tsum_a_div_cpow hw
  have hsum_tendsto :
      Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, (a m : ℂ) / (m : ℂ) ^ (w + 1))
        atTop (𝓝 ((riemannZeta (2 * w) - 1) / riemannZeta w)) :=
    htsum ▸ hsumm.hasSum.tendsto_sum_nat
  have hbdry_tendsto :
      Tendsto (fun M : ℕ => (A ((M - 1 : ℕ) : ℝ) : ℂ) / (M : ℂ) ^ (w + 1)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero_norm' (a := fun M : ℕ => (M : ℝ) ^ (1 - w.re)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with M hM
      have hM0 : (0 : ℝ) < (M : ℝ) := by positivity
      have hM1 : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ M - 1 by omega)
      have hMle : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
      rw [Real.norm_eq_abs, abs_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast_cpow_of_pos (by omega : 0 < M)]
      have hre : (w + 1).re = w.re + 1 := by simp
      rw [hre]
      have hA : |A ((M - 1 : ℕ) : ℝ)| ≤ (M : ℝ) ^ 2 :=
        (abs_A_le _ hM1).trans (by nlinarith)
      calc |A ((M - 1 : ℕ) : ℝ)| / (M : ℝ) ^ (w.re + 1)
          ≤ (M : ℝ) ^ 2 / (M : ℝ) ^ (w.re + 1) :=
            div_le_div_of_nonneg_right hA (Real.rpow_nonneg hM0.le _)
        _ = (M : ℝ) ^ (1 - w.re) := by
            rw [← Real.rpow_natCast (M : ℝ) 2, ← Real.rpow_sub hM0]
            congr 1; ring
    · have ht := (tendsto_rpow_neg_atTop (show 0 < w.re - 1 by linarith)).comp
        tendsto_natCast_atTop_atTop
      exact ht.congr fun M => by
        change (M : ℝ) ^ (-(w.re - 1)) = (M : ℝ) ^ (1 - w.re)
        congr 1; ring
  have hrhs :
      Tendsto (fun M : ℕ =>
        ((∑ m ∈ Finset.range M, (a m : ℂ) / (m : ℂ) ^ (w + 1)) -
          (A ((M - 1 : ℕ) : ℝ) : ℂ) / (M : ℂ) ^ (w + 1)) / (w + 1))
        atTop (𝓝 (((riemannZeta (2 * w) - 1) / riemannZeta w - 0) / (w + 1))) :=
    (hsum_tendsto.sub hbdry_tendsto).div_const (w + 1)
  have heq :
      (fun M : ℕ => ∫ x in (1 : ℝ)..(M : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 2)) =ᶠ[atTop]
        (fun M : ℕ =>
          ((∑ m ∈ Finset.range M, (a m : ℂ) / (m : ℂ) ^ (w + 1)) -
            (A ((M - 1 : ℕ) : ℝ) : ℂ) / (M : ℂ) ^ (w + 1)) / (w + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact intervalIntegral_A_eq hw M hM
  have hlim := tendsto_nhds_unique (hlhs.congr' heq) hrhs
  simpa [sub_zero, div_div, mul_comm] using hlim

/-! === Block 2: Order-0 / Order-3 Euler-Maclaurin, Cauchy bounds, Landau-Tonelli, Direction 1 -/

lemma log_le_rpow_div {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    Real.log x ≤ x ^ ε / ε := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : Real.log (x ^ ε) ≤ x ^ ε - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 ε)
  rw [Real.log_rpow hx0] at h1
  rw [le_div_iff₀ hε]
  linarith

lemma log_pow_le_const_mul_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (n : ℕ) :
    (Real.log x) ^ n ≤ ((n : ℝ) / ε) ^ n * x ^ ε := by
  cases n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact Real.one_le_rpow hx hε.le
  | succ m =>
    have hm1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hε' : 0 < ε / (m + 1 : ℕ) := div_pos hε hm1
    have h1 : Real.log x ≤ x ^ (ε / (m + 1 : ℕ)) / (ε / (m + 1 : ℕ)) :=
      log_le_rpow_div hx hε'
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have hpow := pow_le_pow_left₀ hlog0 h1 (m + 1)
    rw [div_pow, ← Real.rpow_natCast (x ^ _), ← Real.rpow_mul (lt_of_lt_of_le zero_lt_one hx).le] at hpow
    have hexp : ε / (m + 1 : ℕ) * (m + 1 : ℕ) = ε := div_mul_cancel₀ ε hm1.ne'
    rw [hexp] at hpow
    have hconst : (x ^ ε) / (ε / (m + 1 : ℕ)) ^ (m + 1) =
        (((m + 1 : ℕ) : ℝ) / ε) ^ (m + 1) * x ^ ε := by
      rw [div_pow, div_div_eq_mul_div, div_pow]
      ring
    linarith

lemma hasDerivAt_ofReal_cpow_neg_add (x : ℝ) (hx : 0 < x) (k : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (x : ℂ) ^ (-(z + (k : ℂ))))
      (-(Real.log x : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ)))) s := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h1 : HasDerivAt (fun z : ℂ => -(z + (k : ℂ))) (-1) s :=
    ((hasDerivAt_id s).add_const (k : ℂ)).neg
  have h2 := h1.const_cpow (c := (x : ℂ)) (Or.inl hxne)
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
  rw [hlog] at h2
  convert h2 using 1
  ring

lemma differentiableOn_mellin_bounded {a C k : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bnd : ∀ x, a < x → ‖g x‖ ≤ C) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x in Set.Ioi a, g x * (x : ℂ) ^ (-(s + (k : ℂ))))
      {s : ℂ | 1 - k < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 - k < s₀.re := hs₀
  set δ := (s₀.re - (1 - k)) / 3
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  let F : ℂ → ℝ → ℂ := fun s x => g x * (x : ℂ) ^ (-(s + (k : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun s x => g x * (-(Real.log x : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ))))
  have hmeas_F : ∀ s : ℂ, AEStronglyMeasurable (F s) (volume.restrict (Set.Ioi a)) := by
    intro s
    refine hg_meas.aestronglyMeasurable.mul ?_
    exact ContinuousOn.aestronglyMeasurable (fun x hx =>
      (Complex.continuousAt_ofReal_cpow_const x (-(s + (k : ℂ)))
        (Or.inr (lt_trans ha0 hx).ne')).continuousWithinAt) measurableSet_Ioi
  have hmeas_F' : AEStronglyMeasurable (F' s₀) (volume.restrict (Set.Ioi a)) := by
    refine hg_meas.aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := lt_trans ha0 hx
    exact (((Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0.ne')).neg).mul
      (Complex.continuousAt_ofReal_cpow_const x (-(s₀ + (k : ℂ))) (Or.inr hx0.ne'))).continuousWithinAt
  have hF_int : Integrable (F s₀) (volume.restrict (Set.Ioi a)) := by
    have hre : -(s₀.re + k) < -1 := by linarith
    refine ((integrableOn_Ioi_rpow_of_lt hre ha0).const_mul C).mono' (hmeas_F s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans ha0 hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre' : (-(s₀ + (k : ℂ))).re = -(s₀.re + k) := by simp
    rw [hre']
    exact mul_le_mul_of_nonneg_right (hg_bnd x hx) (Real.rpow_nonneg hx0.le _)
  let bound : ℝ → ℝ := fun x => (C / δ) * x ^ (-(1 + δ))
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi a)) :=
    (integrableOn_Ioi_rpow_of_lt (show -(1 + δ) < -1 by linarith) ha0).const_mul (C / δ)
  have h_bound : ∀ᵐ x ∂(volume.restrict (Set.Ioi a)),
      ∀ s ∈ Metric.ball s₀ δ, ‖F' s x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
    have hx1 : 1 ≤ x := le_trans ha (le_of_lt hx)
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hsre : 1 + 2 * δ ≤ s.re + k := by
      have hdist : |s.re - s₀.re| < δ := by
        calc |s.re - s₀.re| = |(s - s₀).re| := by simp
          _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
          _ < δ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hs
      have := (abs_lt.mp hdist).1
      dsimp only [δ] at *
      linarith
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx1), Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre' : (-(s + (k : ℂ))).re = -(s.re + k) := by simp
    rw [hre']
    have hlog : Real.log x ≤ x ^ δ / δ := log_le_rpow_div hx1 hδ
    have hrpow : x ^ (-(s.re + k)) ≤ x ^ (-(1 + 2 * δ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc ‖g x‖ * (Real.log x * x ^ (-(s.re + k)))
        ≤ C * (x ^ δ / δ * x ^ (-(1 + 2 * δ))) := by
          refine mul_le_mul (hg_bnd x hx) ?_
            (mul_nonneg (Real.log_nonneg hx1) (Real.rpow_nonneg hx0.le _)) hC
          exact mul_le_mul hlog hrpow (Real.rpow_nonneg hx0.le _)
            (div_nonneg (Real.rpow_nonneg hx0.le _) hδ.le)
      _ = (C / δ) * (x ^ δ * x ^ (-(1 + 2 * δ))) := by ring
      _ = (C / δ) * x ^ (-(1 + δ)) := by
          rw [← Real.rpow_add hx0]; congr 2; ring
  have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioi a)),
      ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (F · x) (F' s x) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
    exact (hasDerivAt_ofReal_cpow_neg_add x (lt_trans ha0 hx) k s).const_mul (g x)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall hmeas_F) hF_int hmeas_F' h_bound hbound_int h_diff
  exact hd.2.differentiableAt.differentiableWithinAt

lemma isPreconnected_rightHalfPlane_sdiff_one :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re} \ {(1 : ℂ)}
  have hbase : (2 + I : ℂ) ∈ U := by
    refine ⟨by simp, ?_⟩
    intro h
    have := congr_arg Complex.im h
    simp at this
  have hseg : ∀ z w : ℂ, (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((1 - t : ℝ) : ℂ) * z + (t : ℂ) * w ∈ U) → JoinedIn U z w := by
    intro z w hzw
    refine ⟨{ toFun := fun t => ((1 - (t : ℝ) : ℝ) : ℂ) * z + ((t : ℝ) : ℂ) * w
              continuous_toFun := by fun_prop
              source' := by simp
              target' := by simp }, fun t => hzw t t.2.1 t.2.2⟩
  have hjoin : ∀ z ∈ U, JoinedIn U z (2 + I) := by
    intro z hz
    have hzre : 0 < z.re := hz.1
    have hzne1 : z ≠ 1 := hz.2
    by_cases hzim : z.im = 0
    · have hzre_ne : z.re ≠ 1 := fun h => hzne1 (Complex.ext h hzim)
      have h1 : JoinedIn U z ((z.re : ℂ) + I) := by
        refine hseg z ((z.re : ℂ) + I) fun t ht0 ht1 => ?_
        have hre : (((1 - t : ℝ) : ℂ) * z + (t : ℂ) * ((z.re : ℂ) + I)).re = z.re := by
          simp; ring
        refine ⟨show 0 < (((1 - t : ℝ) : ℂ) * z + (t : ℂ) * ((z.re : ℂ) + I)).re by rw [hre]; exact hzre,
          fun h => hzre_ne ?_⟩
        have := congr_arg Complex.re h
        rw [hre, Complex.one_re] at this
        exact this
      have h2 : JoinedIn U ((z.re : ℂ) + I) (2 + I) := by
        refine hseg ((z.re : ℂ) + I) (2 + I) fun t ht0 ht1 => ?_
        have hre : (((1 - t : ℝ) : ℂ) * ((z.re : ℂ) + I) + (t : ℂ) * (2 + I)).re =
            (1 - t) * z.re + 2 * t := by simp; ring
        have him : (((1 - t : ℝ) : ℂ) * ((z.re : ℂ) + I) + (t : ℂ) * (2 + I)).im = 1 := by
          simp
        refine ⟨show 0 < (((1 - t : ℝ) : ℂ) * ((z.re : ℂ) + I) + (t : ℂ) * (2 + I)).re by
            rw [hre]
            by_cases ht : t = 0
            · subst ht; linarith
            · have hpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
              nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hzre.le], fun h => ?_⟩
        have := congr_arg Complex.im h
        rw [him, Complex.one_im] at this
        norm_num at this
      exact h1.trans h2
    · have h1 : JoinedIn U z ((2 : ℂ) + (z.im : ℂ) * I) := by
        refine hseg z ((2 : ℂ) + (z.im : ℂ) * I) fun t ht0 ht1 => ?_
        have hre : (((1 - t : ℝ) : ℂ) * z + (t : ℂ) * (2 + (z.im : ℂ) * I)).re =
            (1 - t) * z.re + 2 * t := by simp; ring
        have him : (((1 - t : ℝ) : ℂ) * z + (t : ℂ) * (2 + (z.im : ℂ) * I)).im = z.im := by
          simp; ring
        refine ⟨show 0 < (((1 - t : ℝ) : ℂ) * z + (t : ℂ) * (2 + (z.im : ℂ) * I)).re by
            rw [hre]
            by_cases ht : t = 0
            · subst ht; linarith
            · have hpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
              nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hzre.le], fun h => hzim ?_⟩
        have := congr_arg Complex.im h
        rw [him, Complex.one_im] at this
        exact this
      have h2 : JoinedIn U ((2 : ℂ) + (z.im : ℂ) * I) (2 + I) := by
        refine hseg ((2 : ℂ) + (z.im : ℂ) * I) (2 + I) fun t ht0 ht1 => ?_
        have hre : (((1 - t : ℝ) : ℂ) * (2 + (z.im : ℂ) * I) + (t : ℂ) * (2 + I)).re = 2 := by
          simp; ring
        refine ⟨show 0 < (((1 - t : ℝ) : ℂ) * (2 + (z.im : ℂ) * I) + (t : ℂ) * (2 + I)).re by
            rw [hre]; norm_num, fun h => ?_⟩
        have := congr_arg Complex.re h
        rw [hre, Complex.one_re] at this
        norm_num at this
      exact h1.trans h2
  have hpc : IsPathConnected U := ⟨2 + I, hbase, fun z hz => (hjoin z hz).symm⟩
  exact hpc.isConnected.isPreconnected

lemma integral_cpow_Ioi {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.re < -1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ z) (Set.Ioi a) ∧
    ∫ x in Set.Ioi a, (x : ℂ) ^ z = -((a : ℂ) ^ (z + 1)) / (z + 1) := by
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ z) (Set.Ioi a) := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ z) (volume.restrict (Set.Ioi a)) :=
      ContinuousOn.aestronglyMeasurable (fun x hx =>
        (Complex.continuousAt_ofReal_cpow_const x z (Or.inr (lt_trans ha hx).ne')).continuousWithinAt)
        measurableSet_Ioi
    refine (integrableOn_Ioi_rpow_of_lt hz ha).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans ha hx)]
  refine ⟨hint, ?_⟩
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp at this
    linarith
  have h1 := intervalIntegral_tendsto_integral_Ioi a hint tendsto_id
  have h2 : ∀ᶠ M : ℝ in atTop,
      ∫ x in a..M, (x : ℂ) ^ z = ((M : ℂ) ^ (z + 1) - (a : ℂ) ^ (z + 1)) / (z + 1) := by
    filter_upwards [eventually_ge_atTop a] with M hM
    have hF : ∀ x ∈ Set.uIcc a M,
        HasDerivAt (fun t : ℝ => (t : ℂ) ^ (z + 1) / (z + 1)) ((x : ℂ) ^ z) x := by
      intro x hx
      rw [Set.uIcc_of_le hM] at hx
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      have hcp := (((hasDerivAt_id (x : ℂ)).cpow_const (c := z + 1)
        (Or.inl (by exact_mod_cast hx0 : 0 < (x : ℂ).re))).comp_ofReal).div_const (z + 1)
      have hval : (z + 1) * (x : ℂ) ^ (z + 1 - 1) * 1 / (z + 1) = (x : ℂ) ^ z := by
        rw [add_sub_cancel_right, mul_one]; field_simp [hz1]
      simpa only [id_eq, hval] using hcp
    have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Set.uIcc a M) := by
      intro x hx
      rw [Set.uIcc_of_le hM] at hx
      exact (Complex.continuousAt_ofReal_cpow_const x z
        (Or.inr (lt_of_lt_of_le ha hx.1).ne')).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable, sub_div]
  have hlimM : Tendsto (fun M : ℝ => (M : ℂ) ^ (z + 1)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hre : (z + 1).re < 0 := by simp; linarith
    have ht := tendsto_rpow_neg_atTop (show 0 < -(z + 1).re by linarith)
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hM, neg_neg]
  have h3 : Tendsto (fun M : ℝ => ((M : ℂ) ^ (z + 1) - (a : ℂ) ^ (z + 1)) / (z + 1))
      atTop (𝓝 ((0 - (a : ℂ) ^ (z + 1)) / (z + 1))) :=
    (hlimM.sub tendsto_const_nhds).div_const (z + 1)
  simpa using tendsto_nhds_unique (h1.congr' h2) h3

/-- Order-0 Euler-Maclaurin formula for `riemannZeta`. -/
noncomputable def em0 (s : ℂ) : ℂ :=
  1 / (s - 1) + 1 - s * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))

lemma riemannZeta_eq_em0_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = em0 s := by
  have hint_fract : IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)))
        (volume.restrict (Set.Ioi 1)) := by
      refine (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable.mul ?_
      exact ContinuousOn.aestronglyMeasurable (fun x hx =>
        (Complex.continuousAt_ofReal_cpow_const x (-(s + 1))
          (Or.inr (lt_trans zero_lt_one hx).ne')).continuousWithinAt) measurableSet_Ioi
    refine (integrableOn_Ioi_rpow_of_lt (show -(s.re + 1) < -1 by linarith) zero_lt_one).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg x), Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [hre]
    calc Int.fract x * x ^ (-(s.re + 1)) ≤ 1 * x ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (Int.fract_lt_one x).le (Real.rpow_nonneg hx0.le _)
      _ = x ^ (-(s.re + 1)) := one_mul _
  have hstep : ∀ m : ℕ, 1 ≤ m →
      (((m + 1 : ℕ) : ℂ) ^ (-s)) =
        (∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s)) -
        s * (∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
    intro m hm
    have hF : ∀ x ∈ Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ),
        HasDerivAt (fun t : ℝ => ((t - (m : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-s))
          ((x : ℂ) ^ (-s) - s * ((x - (m : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) x := by
      intro x hx
      rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
      have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hm) hx.1
      have h1 : HasDerivAt (fun t : ℝ => ((t - (m : ℝ) : ℝ) : ℂ)) 1 x := by
        simpa using ((hasDerivAt_id x).sub_const (m : ℝ)).ofReal_comp
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
        have := ((hasDerivAt_id (x : ℂ)).cpow_const (c := -s)
          (Or.inl (by exact_mod_cast hx0 : 0 < (x : ℂ).re))).comp_ofReal
        simpa using this
      have hmul := h1.mul h2
      have hval : 1 * (x : ℂ) ^ (-s) + ((x - (m : ℝ) : ℝ) : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) =
          (x : ℂ) ^ (-s) - s * ((x - (m : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
        have hexp : -s - 1 = -(s + 1) := by ring
        rw [hexp]; ring
      rwa [hval] at hmul
    have hcont1 : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
      intro x hx
      rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
      exact (Complex.continuousAt_ofReal_cpow_const x (-s)
        (Or.inr (lt_of_lt_of_le (by exact_mod_cast hm) hx.1).ne')).continuousWithinAt
    have hcont2 : ContinuousOn (fun x : ℝ => s * ((x - (m : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)))
        (Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
      intro x hx
      rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
      have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hm) hx.1
      refine ContinuousAt.continuousWithinAt ?_
      refine (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_id.sub continuousAt_const))).mul ?_
      exact Complex.continuousAt_ofReal_cpow_const x (-(s + 1)) (Or.inr hx0.ne')
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (hcont1.sub hcont2).intervalIntegrable
    rw [intervalIntegral.integral_sub hcont1.intervalIntegrable hcont2.intervalIntegrable] at hftc
    have hcongr :
        ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), s * ((x - (m : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) =
        s * ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae ?_
      have hne_ae : ∀ᵐ x : ℝ ∂volume, x ≠ ((m + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
      filter_upwards [hne_ae] with x hx hmem
      rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ m)] at hmem
      have hfl : ⌊x⌋ = (m : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast le_of_lt hmem.1,
        by exact_mod_cast lt_of_le_of_ne hmem.2 hx⟩
      have hfr : Int.fract x = x - (m : ℝ) := by simp [Int.fract, hfl]
      rw [hfr, mul_assoc]
    rw [hcongr] at hftc
    have hval : ((((m + 1 : ℕ) : ℝ) - (m : ℝ) : ℝ) : ℂ) * (((m + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
        (((m : ℝ) - (m : ℝ) : ℝ) : ℂ) * ((m : ℝ) : ℂ) ^ (-s) = (((m + 1 : ℕ) : ℂ) ^ (-s)) := by
      simp
    rw [hval] at hftc
    exact hftc.symm
  have hsumM : ∀ M : ℕ, 1 ≤ M →
      (∑ k ∈ Finset.range M, 1 / (k + 1 : ℂ) ^ s) =
        1 + (∫ x in (1 : ℝ)..(M : ℝ), (x : ℂ) ^ (-s)) -
        s * (∫ x in (1 : ℝ)..(M : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hint_cp1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume 1 m :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hm)).mpr <|
          (integral_cpow_Ioi zero_lt_one (show (-s).re < -1 by simp; linarith)).1.mono_set
            fun _ hx => hx.1
      have hint_cp2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume m ((m + 1 : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ m)).mpr <|
          (integral_cpow_Ioi zero_lt_one (show (-s).re < -1 by simp; linarith)).1.mono_set
            fun x hx => lt_of_le_of_lt (by exact_mod_cast hm) hx.1
      have hint_f1 : IntervalIntegrable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) volume 1 m :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hm)).mpr <|
          hint_fract.mono_set fun _ hx => hx.1
      have hint_f2 : IntervalIntegrable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)))
          volume m ((m + 1 : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ m)).mpr <|
          hint_fract.mono_set fun x hx => lt_of_le_of_lt (by exact_mod_cast hm) hx.1
      rw [Finset.sum_range_succ, ih, ← intervalIntegral.integral_add_adjacent_intervals hint_cp1 hint_cp2,
        ← intervalIntegral.integral_add_adjacent_intervals hint_f1 hint_f2]
      have hst := hstep m hm
      have hterm : (1 : ℂ) / ((m : ℂ) + 1) ^ s = ((m + 1 : ℕ) : ℂ) ^ (-s) := by
        rw [Nat.cast_add, Nat.cast_one, Complex.cpow_neg, one_div]
      rw [hterm, hst]
      ring
  have hsumm : Summable (fun k : ℕ => 1 / (k + 1 : ℂ) ^ s) := by
    have h := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    exact (summable_nat_add_iff 1).mpr h |>.congr fun k => by simp
  have hlhs : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, 1 / (k + 1 : ℂ) ^ s)
      atTop (𝓝 (riemannZeta s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hsumm.hasSum.tendsto_sum_nat
  have ⟨hint_cp, hval_cp⟩ := integral_cpow_Ioi zero_lt_one (show (-s).re < -1 by simp; linarith)
  have hcp_lim : Tendsto (fun M : ℕ => ∫ x in (1 : ℝ)..(M : ℝ), (x : ℂ) ^ (-s))
      atTop (𝓝 (1 / (s - 1))) := by
    have ht := (intervalIntegral_tendsto_integral_Ioi 1 hint_cp tendsto_id).comp
      tendsto_natCast_atTop_atTop
    rw [hval_cp] at ht
    have hval : -((1 : ℝ) : ℂ) ^ (-s + 1) / (-s + 1) = 1 / (s - 1) := by
      simp only [Complex.ofReal_one, Complex.one_cpow]
      have hs1 : s - 1 ≠ 0 := by
        intro h; have := congr_arg Complex.re h; simp at this; linarith
      have hs1' : -s + 1 ≠ 0 := by intro h; apply hs1; linear_combination -h
      field_simp [hs1, hs1']
      ring
    rwa [hval] at ht
  have hf_lim : Tendsto (fun M : ℕ => ∫ x in (1 : ℝ)..(M : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)))
      atTop (𝓝 (∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)))) :=
    (intervalIntegral_tendsto_integral_Ioi 1 hint_fract tendsto_id).comp tendsto_natCast_atTop_atTop
  have hrhs : Tendsto (fun M : ℕ =>
      1 + (∫ x in (1 : ℝ)..(M : ℝ), (x : ℂ) ^ (-s)) -
      s * (∫ x in (1 : ℝ)..(M : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))))
      atTop (𝓝 (em0 s)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℂ))).add hcp_lim).sub (hf_lim.const_mul s)
    simpa [em0, add_comm] using h
  exact tendsto_nhds_unique (hlhs.congr' (by filter_upwards [eventually_ge_atTop 1] with M hM; exact hsumM M hM)) hrhs

lemma riemannZeta_eq_em0 {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = em0 s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {(1 : ℂ)}
  have hU_open : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hdiff_int : DifferentiableOn ℂ (fun z : ℂ =>
      ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(z + (1 : ℝ))))
      {z : ℂ | 1 - (1 : ℝ) < z.re} :=
    differentiableOn_mellin_bounded le_rfl zero_le_one
      (Complex.continuous_ofReal.measurable.comp measurable_fract)
      (fun x _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
        exact (Int.fract_lt_one x).le)
  have hem0_diff : DifferentiableOn ℂ em0 U := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w - 1) + 1) z := by
      have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz.2
      fun_prop (disch := assumption)
    have h2 : DifferentiableAt ℂ (fun w : ℂ =>
        ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))) z := by
      have hz' : z ∈ {w : ℂ | 1 - (1 : ℝ) < w.re} := by simpa using hz.1
      have hopen : IsOpen {w : ℂ | 1 - (1 : ℝ) < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      simpa using hdiff_int.differentiableAt (hopen.mem_nhds hz')
    exact (h1.sub (differentiableAt_id.mul h2)).differentiableWithinAt
  have hζ_an : AnalyticOnNhd ℂ riemannZeta U :=
    analyticOn_riemannZeta.mono (fun z hz => hz.2)
  have hem0_an : AnalyticOnNhd ℂ em0 U := hem0_diff.analyticOnNhd hU_open
  have heq : Set.EqOn riemannZeta em0 U :=
    hζ_an.eqOn_of_preconnected_of_eventuallyEq hem0_an isPreconnected_rightHalfPlane_sdiff_one
      (show (2 : ℂ) ∈ U from ⟨by norm_num, by norm_num⟩)
      (eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))
        fun z hz => riemannZeta_eq_em0_of_one_lt_re hz)
  exact heq ⟨hs, hs1⟩

lemma riemannZeta_real_neg_on_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).re ≤ x / (x - 1) ∧ (riemannZeta (x : ℂ)).im = 0 := by
  have hne : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  rw [riemannZeta_eq_em0 (by simpa using hx0) hne, em0]
  have hint : ∫ t : ℝ in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-((x : ℂ) + 1)) =
      Complex.ofReal (∫ t : ℝ in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(x + 1))) := by
    rw [show Complex.ofReal (∫ t : ℝ in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(x + 1))) =
      ∫ t : ℝ in Set.Ioi (1 : ℝ), ((Int.fract t * t ^ (-(x + 1)) : ℝ) : ℂ) from integral_ofReal.symm]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Complex.ofReal_mul, show (-((x : ℂ) + 1)) = ((-(x + 1) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0.le]
  rw [hint]
  have hnonneg : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(x + 1)) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Int.fract_nonneg t) (Real.rpow_nonneg (lt_trans zero_lt_one ht).le _)
  have hrat : (1 : ℂ) / ((x : ℂ) - 1) + 1 = ((x / (x - 1) : ℝ) : ℂ) := by
    have hne' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1.ne
    push_cast
    field_simp [hne']
    ring
  rw [hrat, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨by nlinarith, rfl⟩

lemma riemannZeta_ne_zero_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro h
  have hre := (riemannZeta_real_neg_on_Ioo hx0 hx1).1
  rw [h, Complex.zero_re] at hre
  have hneg : x / (x - 1) < 0 := div_neg_of_pos_of_neg hx0 (by linarith)
  linarith

lemma riemannZeta_half_le_neg_one :
    (riemannZeta ((1 / 2 : ℝ) : ℂ)).re ≤ -1 ∧ (riemannZeta ((1 / 2 : ℝ) : ℂ)).im = 0 := by
  have h := riemannZeta_real_neg_on_Ioo (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hval : (1 / 2 : ℝ) / ((1 / 2 : ℝ) - 1) = -1 := by norm_num
  rw [hval] at h
  exact h

lemma norm_riemannZeta_le_em0 {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    ‖riemannZeta w‖ ≤ 1 / ‖w - 1‖ + 1 + ‖w‖ / w.re := by
  rw [riemannZeta_eq_em0 hw hw1, em0]
  have hint_bnd : ‖∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))‖ ≤ 1 / w.re := by
    have h1 := norm_integral_le_integral_norm
      (f := fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))) (μ := volume.restrict (Set.Ioi 1))
    have h2 : ∫ x in Set.Ioi (1 : ℝ), ‖((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))‖ ≤
        ∫ x in Set.Ioi (1 : ℝ), x ^ (-(w.re + 1)) := by
      refine setIntegral_mono_on ?_ (integrableOn_Ioi_rpow_of_lt (a := -(w.re + 1)) (by linarith) zero_lt_one)
        measurableSet_Ioi fun x hx => ?_
      · have hmeas : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1)))
            (volume.restrict (Set.Ioi 1)) := by
          refine (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable.mul ?_
          exact ContinuousOn.aestronglyMeasurable (fun x hx =>
            (Complex.continuousAt_ofReal_cpow_const x (-(w + 1))
              (Or.inr (lt_trans zero_lt_one hx).ne')).continuousWithinAt) measurableSet_Ioi
        exact ((integrableOn_Ioi_rpow_of_lt (a := -(w.re + 1)) (by linarith) zero_lt_one).mono' hmeas (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : 0 < x := lt_trans zero_lt_one hx
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x),
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : (-(w + 1)).re = -(w.re + 1) := by simp
          rw [hre]
          exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (Int.fract_lt_one x).le)).norm
      · have hx0 : 0 < x := lt_trans zero_lt_one hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x),
          Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : (-(w + 1)).re = -(w.re + 1) := by simp
        rw [hre]
        exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (Int.fract_lt_one x).le
    have hval := integral_Ioi_rpow_of_lt (show -(w.re + 1) < -1 by linarith) zero_lt_one
    have h3 : -(1 : ℝ) ^ (-(w.re + 1) + 1) / (-(w.re + 1) + 1) = 1 / w.re := by
      simp only [Real.one_rpow]
      have hne : w.re ≠ 0 := hw.ne'
      field_simp [hne]; ring
    linarith
  calc ‖1 / (w - 1) + 1 - w * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))‖
      ≤ ‖1 / (w - 1) + 1‖ + ‖w * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))‖ :=
        norm_sub_le _ _
    _ ≤ (‖1 / (w - 1)‖ + ‖(1 : ℂ)‖) + ‖w‖ * ‖∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))‖ := by
        rw [norm_mul]; gcongr; exact norm_add_le _ _
    _ ≤ 1 / ‖w - 1‖ + 1 + ‖w‖ / w.re := by
        rw [norm_div, norm_one]
        have h4 : ‖w‖ * ‖∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))‖ ≤
            ‖w‖ * (1 / w.re) := mul_le_mul_of_nonneg_left hint_bnd (norm_nonneg w)
        rw [mul_one_div] at h4
        linarith

lemma norm_deriv_riemannZeta_half_le (t : ℝ) :
    ‖deriv riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      24 + 16 * ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ := by
  set s₀ : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hdiff : DiffContOnCl ℂ riemannZeta (Metric.ball s₀ (1 / 4)) := by
    have hsub : Metric.closedBall s₀ (1 / 4) ⊆ {(1 : ℂ)}ᶜ := by
      intro w hw h1
      rw [Set.mem_singleton_iff] at h1
      subst h1
      have hd : ‖(1 : ℂ) - s₀‖ ≤ 1 / 4 := by simpa [dist_eq_norm] using hw
      have hre : 1 / 2 ≤ ‖(1 : ℂ) - s₀‖ := by
        have h : ((1 : ℂ) - s₀).re = 1 / 2 := by simp [s₀]; norm_num
        calc (1 / 2 : ℝ) = |((1 : ℂ) - s₀).re| := by rw [h]; norm_num
          _ ≤ ‖(1 : ℂ) - s₀‖ := Complex.abs_re_le_norm _
      linarith
    exact differentiableOn_riemannZeta.diffContOnCl_ball hsub
  have hC : ∀ w ∈ Metric.sphere s₀ (1 / 4), ‖riemannZeta w‖ ≤ 6 + 4 * ‖s₀‖ := by
    intro w hw
    have hdist : ‖w - s₀‖ = 1 / 4 := mem_sphere_iff_norm.mp hw
    have hw_re : 1 / 4 ≤ w.re := by
      have h1 : |w.re - s₀.re| ≤ 1 / 4 := by
        calc |w.re - s₀.re| = |(w - s₀).re| := by simp
          _ ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 4 := hdist
      have hs0re : s₀.re = 1 / 2 := by simp [s₀]
      linarith [(abs_le.mp h1).1]
    have hw_sub1 : 1 / 4 ≤ ‖w - 1‖ := by
      have h1 : 1 / 2 ≤ ‖s₀ - 1‖ := by
        have hre : (s₀ - 1).re = -(1 / 2) := by simp [s₀]; norm_num
        calc (1 / 2 : ℝ) = |(s₀ - 1).re| := by rw [hre]; norm_num
          _ ≤ ‖s₀ - 1‖ := Complex.abs_re_le_norm _
      have htri : ‖s₀ - 1‖ ≤ ‖w - 1‖ + ‖w - s₀‖ := by
        calc ‖s₀ - 1‖ = ‖(w - 1) - (w - s₀)‖ := by ring_nf
          _ ≤ ‖w - 1‖ + ‖w - s₀‖ := norm_sub_le _ _
      linarith
    have hw_ne1 : w ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hw_sub1; linarith
    have hw_norm : ‖w‖ ≤ ‖s₀‖ + 1 / 4 := by
      calc ‖w‖ = ‖(w - s₀) + s₀‖ := by ring_nf
        _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ = ‖s₀‖ + 1 / 4 := by rw [hdist]; ring
    have hb := norm_riemannZeta_le_em0 (by linarith : 0 < w.re) hw_ne1
    have hd1 : 1 / ‖w - 1‖ ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hd2 : ‖w‖ / w.re ≤ 4 * ‖w‖ := by rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
    linarith
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 (by norm_num : (0 : ℝ) < 1 / 4)
    hdiff hC
  rw [iteratedDeriv_one] at hc
  norm_num at hc
  linarith

lemma norm_deriv2_riemannZeta_half_le (t : ℝ) :
    ‖iteratedDeriv 2 riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      192 + 128 * ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ := by
  set s₀ : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hdiff : DiffContOnCl ℂ riemannZeta (Metric.ball s₀ (1 / 4)) := by
    have hsub : Metric.closedBall s₀ (1 / 4) ⊆ {(1 : ℂ)}ᶜ := by
      intro w hw h1
      rw [Set.mem_singleton_iff] at h1
      subst h1
      have hd : ‖(1 : ℂ) - s₀‖ ≤ 1 / 4 := by simpa [dist_eq_norm] using hw
      have hre : 1 / 2 ≤ ‖(1 : ℂ) - s₀‖ := by
        have h : ((1 : ℂ) - s₀).re = 1 / 2 := by simp [s₀]; norm_num
        calc (1 / 2 : ℝ) = |((1 : ℂ) - s₀).re| := by rw [h]; norm_num
          _ ≤ ‖(1 : ℂ) - s₀‖ := Complex.abs_re_le_norm _
      linarith
    exact differentiableOn_riemannZeta.diffContOnCl_ball hsub
  have hC : ∀ w ∈ Metric.sphere s₀ (1 / 4), ‖riemannZeta w‖ ≤ 6 + 4 * ‖s₀‖ := by
    intro w hw
    have hdist : ‖w - s₀‖ = 1 / 4 := mem_sphere_iff_norm.mp hw
    have hw_re : 1 / 4 ≤ w.re := by
      have h1 : |w.re - s₀.re| ≤ 1 / 4 := by
        calc |w.re - s₀.re| = |(w - s₀).re| := by simp
          _ ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 4 := hdist
      have hs0re : s₀.re = 1 / 2 := by simp [s₀]
      linarith [(abs_le.mp h1).1]
    have hw_sub1 : 1 / 4 ≤ ‖w - 1‖ := by
      have h1 : 1 / 2 ≤ ‖s₀ - 1‖ := by
        have hre : (s₀ - 1).re = -(1 / 2) := by simp [s₀]; norm_num
        calc (1 / 2 : ℝ) = |(s₀ - 1).re| := by rw [hre]; norm_num
          _ ≤ ‖s₀ - 1‖ := Complex.abs_re_le_norm _
      have htri : ‖s₀ - 1‖ ≤ ‖w - 1‖ + ‖w - s₀‖ := by
        calc ‖s₀ - 1‖ = ‖(w - 1) - (w - s₀)‖ := by ring_nf
          _ ≤ ‖w - 1‖ + ‖w - s₀‖ := norm_sub_le _ _
      linarith
    have hw_ne1 : w ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hw_sub1; linarith
    have hw_norm : ‖w‖ ≤ ‖s₀‖ + 1 / 4 := by
      calc ‖w‖ = ‖(w - s₀) + s₀‖ := by ring_nf
        _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ = ‖s₀‖ + 1 / 4 := by rw [hdist]; ring
    have hb := norm_riemannZeta_le_em0 (by linarith : 0 < w.re) hw_ne1
    have hd1 : 1 / ‖w - 1‖ ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hd2 : ‖w‖ / w.re ≤ 4 * ‖w‖ := by rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
    linarith
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 (by norm_num : (0 : ℝ) < 1 / 4)
    hdiff hC
  norm_num at hc
  linarith

lemma norm_deriv_riemannZeta_one_le {t : ℝ} (ht : 2 ≤ |t|) :
    ‖deriv riemannZeta ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      6 + 4 * ‖(1 : ℂ) + (t : ℂ) * I‖ := by
  set s₀ : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hdiff : DiffContOnCl ℂ riemannZeta (Metric.ball s₀ (1 / 2)) := by
    have hsub : Metric.closedBall s₀ (1 / 2) ⊆ {(1 : ℂ)}ᶜ := by
      intro w hw h1
      rw [Set.mem_singleton_iff] at h1
      subst h1
      have hd : ‖(1 : ℂ) - s₀‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hw
      have him : |t| ≤ ‖(1 : ℂ) - s₀‖ := by
        have h : ((1 : ℂ) - s₀).im = -t := by simp [s₀]
        calc |t| = |((1 : ℂ) - s₀).im| := by rw [h, abs_neg]
          _ ≤ ‖(1 : ℂ) - s₀‖ := Complex.abs_im_le_norm _
      linarith
    exact differentiableOn_riemannZeta.diffContOnCl_ball hsub
  have hC : ∀ w ∈ Metric.sphere s₀ (1 / 2), ‖riemannZeta w‖ ≤ 3 + 2 * ‖s₀‖ := by
    intro w hw
    have hdist : ‖w - s₀‖ = 1 / 2 := mem_sphere_iff_norm.mp hw
    have hw_re : 1 / 2 ≤ w.re := by
      have h1 : |w.re - s₀.re| ≤ 1 / 2 := by
        calc |w.re - s₀.re| = |(w - s₀).re| := by simp
          _ ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 2 := hdist
      have hs0re : s₀.re = 1 := by simp [s₀]
      linarith [(abs_le.mp h1).1]
    have hw_sub1 : 1 ≤ ‖w - 1‖ := by
      have h1 : 2 ≤ ‖s₀ - 1‖ := by
        have him : (s₀ - 1).im = t := by simp [s₀]
        calc (2 : ℝ) ≤ |t| := ht
          _ = |(s₀ - 1).im| := by rw [him]
          _ ≤ ‖s₀ - 1‖ := Complex.abs_im_le_norm _
      have htri : ‖s₀ - 1‖ ≤ ‖w - 1‖ + ‖w - s₀‖ := by
        calc ‖s₀ - 1‖ = ‖(w - 1) - (w - s₀)‖ := by ring_nf
          _ ≤ ‖w - 1‖ + ‖w - s₀‖ := norm_sub_le _ _
      linarith
    have hw_ne1 : w ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hw_sub1; linarith
    have hw_norm : ‖w‖ ≤ ‖s₀‖ + 1 / 2 := by
      calc ‖w‖ = ‖(w - s₀) + s₀‖ := by ring_nf
        _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ = ‖s₀‖ + 1 / 2 := by rw [hdist]; ring
    have hb := norm_riemannZeta_le_em0 (by linarith : 0 < w.re) hw_ne1
    have hd1 : 1 / ‖w - 1‖ ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hd2 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
    linarith
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 (by norm_num : (0 : ℝ) < 1 / 2)
    hdiff hC
  rw [iteratedDeriv_one] at hc
  norm_num at hc
  linarith

/-- Bernoulli polynomials `B₁..B₆` for Order-3 Euler-Maclaurin. -/
noncomputable def B1 (u : ℝ) : ℝ := u - 1 / 2
noncomputable def B2 (u : ℝ) : ℝ := u ^ 2 - u + 1 / 6
noncomputable def B3 (u : ℝ) : ℝ := u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u
noncomputable def B4 (u : ℝ) : ℝ := u ^ 4 - 2 * u ^ 3 + u ^ 2 - 1 / 30
noncomputable def B5 (u : ℝ) : ℝ := u ^ 5 - 5 / 2 * u ^ 4 + 5 / 3 * u ^ 3 - 1 / 6 * u
noncomputable def B6 (u : ℝ) : ℝ := u ^ 6 - 3 * u ^ 5 + 5 / 2 * u ^ 4 - 1 / 2 * u ^ 2 + 1 / 42

noncomputable def P6 (x : ℝ) : ℝ := B6 (Int.fract x)

lemma abs_B6_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : |B6 u| ≤ 1 / 42 := by
  set v := u * (1 - u)
  have hv0 : 0 ≤ v := mul_nonneg hu0 (by linarith)
  have hv1 : v ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hid : B6 u = 1 / 42 - 1 / 2 * v ^ 2 - v ^ 3 := by
    simp only [B6, v]; ring
  rw [hid, abs_le]
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hv3 : v ^ 3 ≤ 1 / 64 := by nlinarith
  have hv2' : v ^ 2 ≤ 1 / 16 := by nlinarith
  constructor <;> nlinarith

lemma abs_P6_le (x : ℝ) : |P6 x| ≤ 1 / 42 :=
  abs_B6_le (Int.fract_nonneg x) (Int.fract_lt_one x).le

lemma P6_measurable : Measurable P6 := by
  have hB6 : Continuous B6 := by unfold B6; fun_prop
  exact hB6.measurable.comp measurable_fract

/-- Order-3 Euler-Maclaurin main term `EM_{3, N}(s)`. -/
noncomputable def em3 (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) +
  (N : ℂ) ^ (1 - s) / (s - 1) +
  (1 / 2 : ℂ) * (N : ℂ) ^ (-s) +
  (s / 12) * (N : ℂ) ^ (-(s + 1)) -
  (s * (s + 1) * (s + 2) / 720) * (N : ℂ) ^ (-(s + 3)) +
  (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240) * (N : ℂ) ^ (-(s + 5))

/-- Order-3 Euler-Maclaurin remainder `R_6(s, N)`. -/
noncomputable def R6 (s : ℂ) (N : ℕ) : ℂ :=
  -(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720) *
    ∫ x in Set.Ioi (N : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))

/-- Derivative `EM'_{3, N}(s)` of the Order-3 Euler-Maclaurin main term. -/
noncomputable def dem3 (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, -(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
  (-(Real.log (N : ℝ) : ℂ) * (s - 1) - 1) * (N : ℂ) ^ (1 - s) / (s - 1) ^ 2 -
  (1 / 2 : ℂ) * (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) +
  (1 - s * (Real.log (N : ℝ) : ℂ)) / 12 * (N : ℂ) ^ (-(s + 1)) -
  (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
    s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) / 720 * (N : ℂ) ^ (-(s + 3)) +
  ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
    s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
    s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) / 30240 *
    (N : ℂ) ^ (-(s + 5))

lemma hasDerivAt_em3 {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs1 : s ≠ 1) :
    HasDerivAt (fun z => em3 z N) (dem3 s N) s := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlogN : Complex.log (N : ℂ) = (Real.log (N : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hN0.le]
  have hpow : ∀ (a : ℂ) (b : ℂ),
      HasDerivAt (fun z : ℂ => (N : ℂ) ^ (a - z + b))
        (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (a - s + b)) s := by
    intro a b
    have h1 : HasDerivAt (fun z : ℂ => a - z + b) (-1) s := by
      have hd := ((hasDerivAt_const s a).sub (hasDerivAt_id s)).add_const b
      simpa using hd
    have h2 := h1.const_cpow (c := (N : ℂ)) (Or.inl hNc)
    rw [hlogN] at h2
    have hval : (N : ℂ) ^ (a - s + b) * (Real.log (N : ℝ) : ℂ) * (-1) =
        -(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (a - s + b) := by ring
    rwa [hval] at h2
  have hsum : HasDerivAt (fun z : ℂ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-z))
      (∑ n ∈ Finset.Ico 1 N, -(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) s := by
    refine HasDerivAt.fun_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hlogn : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
    have h2 := (hasDerivAt_id s).neg.const_cpow (c := (n : ℂ)) (Or.inl hnc)
    rw [hlogn] at h2
    dsimp only [Pi.neg_apply, id_eq] at h2
    have hval : (n : ℂ) ^ (-s) * (Real.log (n : ℝ) : ℂ) * (-1) =
        -(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by ring
    rwa [hval] at h2
  have hN1ms : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (1 - z))
      (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (1 - s)) s := by
    simpa using hpow 1 0
  have hNms : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (-z))
      (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)) s := by
    simpa using hpow 0 0
  have hNms1 : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (-(z + 1)))
      (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 1))) s := by
    have hfun : (fun z : ℂ => (N : ℂ) ^ (0 - z + (-1))) = (fun z : ℂ => (N : ℂ) ^ (-(z + 1))) := by
      ext z; congr 1; ring
    have hval : (0 : ℂ) - s + (-1) = -(s + 1) := by ring
    simpa only [hfun, hval] using hpow 0 (-1)
  have hNms3 : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (-(z + 3)))
      (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 3))) s := by
    have hfun : (fun z : ℂ => (N : ℂ) ^ (0 - z + (-3))) = (fun z : ℂ => (N : ℂ) ^ (-(z + 3))) := by
      ext z; congr 1; ring
    have hval : (0 : ℂ) - s + (-3) = -(s + 3) := by ring
    simpa only [hfun, hval] using hpow 0 (-3)
  have hNms5 : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (-(z + 5)))
      (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 5))) s := by
    have hfun : (fun z : ℂ => (N : ℂ) ^ (0 - z + (-5))) = (fun z : ℂ => (N : ℂ) ^ (-(z + 5))) := by
      ext z; congr 1; ring
    have hval : (0 : ℂ) - s + (-5) = -(s + 5) := by ring
    simpa only [hfun, hval] using hpow 0 (-5)
  have hterm1 : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (1 - z) / (z - 1))
      ((-(Real.log (N : ℝ) : ℂ) * (s - 1) - 1) * (N : ℂ) ^ (1 - s) / (s - 1) ^ 2) s := by
    have hd := hN1ms.div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)
    dsimp only [Pi.div_apply, id_eq] at hd
    have hval : (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (1 - s) * (s - 1) - (N : ℂ) ^ (1 - s) * 1) / (s - 1) ^ 2 =
        (-(Real.log (N : ℝ) : ℂ) * (s - 1) - 1) * (N : ℂ) ^ (1 - s) / (s - 1) ^ 2 := by ring
    rwa [hval] at hd
  have hterm2 : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) * (N : ℂ) ^ (-z))
      (-((1 / 2 : ℂ) * (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s))) s := by
    have hd := hNms.const_mul (1 / 2 : ℂ)
    have hval : (1 / 2 : ℂ) * (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)) =
        -((1 / 2 : ℂ) * (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)) := by ring
    rwa [hval] at hd
  have hterm3 : HasDerivAt (fun z : ℂ => (z / 12) * (N : ℂ) ^ (-(z + 1)))
      ((1 - s * (Real.log (N : ℝ) : ℂ)) / 12 * (N : ℂ) ^ (-(s + 1))) s := by
    have hd := ((hasDerivAt_id s).div_const 12).mul hNms1
    dsimp only [Pi.mul_apply, id_eq] at hd
    have hval : (1 / 12 : ℂ) * (N : ℂ) ^ (-(s + 1)) +
        (s / 12) * (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 1))) =
        (1 - s * (Real.log (N : ℝ) : ℂ)) / 12 * (N : ℂ) ^ (-(s + 1)) := by ring
    rwa [hval] at hd
  have hp3 : HasDerivAt (fun z : ℂ => z * (z + 1) * (z + 2))
      ((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) s := by
    have h1 := ((hasDerivAt_id s).mul ((hasDerivAt_id s).add_const 1)).mul
      ((hasDerivAt_id s).add_const 2)
    dsimp only [Pi.mul_apply, id_eq] at h1
    have hval : (1 * (s + 1) + s * 1) * (s + 2) + s * (s + 1) * 1 =
        (s + 1) * (s + 2) + s * (s + 2) + s * (s + 1) := by ring
    rwa [hval] at h1
  have hterm4 : HasDerivAt (fun z : ℂ => (z * (z + 1) * (z + 2) / 720) * (N : ℂ) ^ (-(z + 3)))
      ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
        s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) / 720 * (N : ℂ) ^ (-(s + 3))) s := by
    have hd := (hp3.div_const 720).mul hNms3
    have hval : ((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) / 720 * (N : ℂ) ^ (-(s + 3)) +
        (s * (s + 1) * (s + 2) / 720) * (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 3))) =
        (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
          s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) / 720 * (N : ℂ) ^ (-(s + 3)) := by ring
    rwa [hval] at hd
  have hp5 : HasDerivAt (fun z : ℂ => z * (z + 1) * (z + 2) * (z + 3) * (z + 4))
      (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
        s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) s := by
    have h1 := (hp3.mul ((hasDerivAt_id s).add_const 3)).mul ((hasDerivAt_id s).add_const 4)
    dsimp only [Pi.mul_apply, id_eq] at h1
    have hval :
        (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) + s * (s + 1) * (s + 2) * 1) *
          (s + 4) + s * (s + 1) * (s + 2) * (s + 3) * 1 =
        ((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
          s * (s + 1) * (s + 2) * ((s + 3) + (s + 4)) := by ring
    rwa [hval] at h1
  have hterm5 : HasDerivAt
      (fun z : ℂ => (z * (z + 1) * (z + 2) * (z + 3) * (z + 4) / 30240) * (N : ℂ) ^ (-(z + 5)))
      (((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
        s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) / 30240 *
        (N : ℂ) ^ (-(s + 5))) s := by
    have hd := (hp5.div_const 30240).mul hNms5
    have hval :
        (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
          s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) / 30240 * (N : ℂ) ^ (-(s + 5)) +
        (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240) *
          (-(Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 5))) =
        ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
          s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
          s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) / 30240 *
          (N : ℂ) ^ (-(s + 5)) := by ring
    rwa [hval] at hd
  have htot := ((((hsum.add hterm1).add hterm2).add hterm3).sub hterm4).add hterm5
  have hval :
      (∑ n ∈ Finset.Ico 1 N, -(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
      (-(Real.log (N : ℝ) : ℂ) * (s - 1) - 1) * (N : ℂ) ^ (1 - s) / (s - 1) ^ 2 +
      -((1 / 2 : ℂ) * (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)) +
      (1 - s * (Real.log (N : ℝ) : ℂ)) / 12 * (N : ℂ) ^ (-(s + 1)) -
      (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
        s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) / 720 * (N : ℂ) ^ (-(s + 3)) +
      ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
        s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) / 30240 *
        (N : ℂ) ^ (-(s + 5)) = dem3 s N := by
    simp only [dem3]; ring
  rw [hval] at htot
  exact htot

lemma riemannZeta_eq_em3_add_R6_of_one_lt_re {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = em3 s N + R6 s N := by
  have hint_P6 : IntegrableOn (fun x : ℝ => (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))) (Set.Ioi (N : ℝ)) := by
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hmeas : AEStronglyMeasurable (fun x : ℝ => (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6)))
        (volume.restrict (Set.Ioi (N : ℝ))) := by
      refine (Complex.continuous_ofReal.measurable.comp P6_measurable).aestronglyMeasurable.mul ?_
      exact ContinuousOn.aestronglyMeasurable (fun x hx =>
        (Complex.continuousAt_ofReal_cpow_const x (-(s + 6))
          (Or.inr (lt_trans hN0 hx).ne')).continuousWithinAt) measurableSet_Ioi
    refine ((integrableOn_Ioi_rpow_of_lt (show -(s.re + 6) < -1 by linarith) hN0).const_mul
      (1 / 42)).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans hN0 hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-(s + 6)).re = -(s.re + 6) := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (abs_P6_le x) (Real.rpow_nonneg hx0.le _)
  -- Single-step telescoping FTC on [m, m + 1]
  let tail : ℕ → ℂ := fun m =>
    (1 / 2 : ℂ) * (m : ℂ) ^ (-s) +
    (s / 12) * (m : ℂ) ^ (-(s + 1)) -
    (s * (s + 1) * (s + 2) / 720) * (m : ℂ) ^ (-(s + 3)) +
    (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240) * (m : ℂ) ^ (-(s + 5))
  have hstep : ∀ m : ℕ, 1 ≤ m →
      (m : ℂ) ^ (-s) - tail m + tail (m + 1) =
        (∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s)) -
        (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720) *
          (∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))) := by
    intro m hm
    let Fm : ℝ → ℂ := fun x =>
      (B1 (x - m) : ℂ) * (x : ℂ) ^ (-s) +
      (s / 2) * (B2 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 1)) +
      (s * (s + 1) / 6) * (B3 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 2)) +
      (s * (s + 1) * (s + 2) / 24) * (B4 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 3)) +
      (s * (s + 1) * (s + 2) * (s + 3) / 120) * (B5 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 4)) +
      (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 720) * (B6 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 5))
    have hFm : ∀ x ∈ Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ),
        HasDerivAt Fm
          ((x : ℂ) ^ (-s) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720) *
            ((B6 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 6)))) x := by
      intro x hx
      rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
      have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hm) hx.1
      have hxp : ∀ k : ℂ, HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-(s + k)))
          (-(s + k) * (x : ℂ) ^ (-(s + (k + 1)))) x := by
        intro k
        have h1 := ((hasDerivAt_id (x : ℂ)).cpow_const (c := -(s + k))
          (Or.inl (by exact_mod_cast hx0 : 0 < (x : ℂ).re))).comp_ofReal
        have hval : (-(s + k) * (x : ℂ) ^ (-(s + k) - 1) * 1) =
            -(s + k) * (x : ℂ) ^ (-(s + (k + 1))) := by
          have hexp : -(s + k) - 1 = -(s + (k + 1)) := by ring
          rw [hexp, mul_one]
        simpa only [id_eq, hval] using h1
      have hu : HasDerivAt (fun t : ℝ => t - (m : ℝ)) 1 x := (hasDerivAt_id x).sub_const (m : ℝ)
      have hB1 : HasDerivAt (fun t : ℝ => (B1 (t - m) : ℂ)) 1 x := by
        have h : HasDerivAt (fun t : ℝ => B1 (t - m)) 1 x := by
          unfold B1; simpa using hu.sub_const (1 / 2 : ℝ)
        simpa using h.ofReal_comp
      have hB2 : HasDerivAt (fun t : ℝ => (B2 (t - m) : ℂ)) (2 * (B1 (x - m) : ℂ)) x := by
        have h : HasDerivAt (fun t : ℝ => B2 (t - m)) (2 * B1 (x - m)) x := by
          unfold B2 B1
          have hd := ((hu.pow 2).sub hu).add_const (1 / 6 : ℝ)
          have hval : ((2 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (2 - 1) * 1 - 1 = 2 * (x - (m : ℝ) - 1 / 2) := by
            norm_num; ring
          rwa [hval] at hd
        simpa using h.ofReal_comp
      have hB3 : HasDerivAt (fun t : ℝ => (B3 (t - m) : ℂ)) (3 * (B2 (x - m) : ℂ)) x := by
        have h : HasDerivAt (fun t : ℝ => B3 (t - m)) (3 * B2 (x - m)) x := by
          unfold B3 B2
          have hd := ((hu.pow 3).sub ((hu.pow 2).const_mul (3 / 2 : ℝ))).add (hu.const_mul (1 / 2 : ℝ))
          have hval : ((3 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (3 - 1) * 1 -
              (3 / 2 : ℝ) * (((2 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (2 - 1) * 1) + (1 / 2 : ℝ) * 1 =
              3 * ((x - (m : ℝ)) ^ 2 - (x - (m : ℝ)) + 1 / 6) := by norm_num; ring
          rwa [hval] at hd
        simpa using h.ofReal_comp
      have hB4 : HasDerivAt (fun t : ℝ => (B4 (t - m) : ℂ)) (4 * (B3 (x - m) : ℂ)) x := by
        have h : HasDerivAt (fun t : ℝ => B4 (t - m)) (4 * B3 (x - m)) x := by
          unfold B4 B3
          have hd := (((hu.pow 4).sub ((hu.pow 3).const_mul (2 : ℝ))).add (hu.pow 2)).sub_const (1 / 30 : ℝ)
          have hval : ((4 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (4 - 1) * 1 -
              (2 : ℝ) * (((3 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (3 - 1) * 1) +
              ((2 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (2 - 1) * 1 =
              4 * ((x - (m : ℝ)) ^ 3 - 3 / 2 * (x - (m : ℝ)) ^ 2 + 1 / 2 * (x - (m : ℝ))) := by
            norm_num; ring
          rwa [hval] at hd
        simpa using h.ofReal_comp
      have hB5 : HasDerivAt (fun t : ℝ => (B5 (t - m) : ℂ)) (5 * (B4 (x - m) : ℂ)) x := by
        have h : HasDerivAt (fun t : ℝ => B5 (t - m)) (5 * B4 (x - m)) x := by
          unfold B5 B4
          have hd := (((hu.pow 5).sub ((hu.pow 4).const_mul (5 / 2 : ℝ))).add
            ((hu.pow 3).const_mul (5 / 3 : ℝ))).sub (hu.const_mul (1 / 6 : ℝ))
          have hval : ((5 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (5 - 1) * 1 -
              (5 / 2 : ℝ) * (((4 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (4 - 1) * 1) +
              (5 / 3 : ℝ) * (((3 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (3 - 1) * 1) - (1 / 6 : ℝ) * 1 =
              5 * ((x - (m : ℝ)) ^ 4 - 2 * (x - (m : ℝ)) ^ 3 + (x - (m : ℝ)) ^ 2 - 1 / 30) := by
            norm_num; ring
          rwa [hval] at hd
        simpa using h.ofReal_comp
      have hB6 : HasDerivAt (fun t : ℝ => (B6 (t - m) : ℂ)) (6 * (B5 (x - m) : ℂ)) x := by
        have h : HasDerivAt (fun t : ℝ => B6 (t - m)) (6 * B5 (x - m)) x := by
          unfold B6 B5
          have hd := ((((hu.pow 6).sub ((hu.pow 5).const_mul (3 : ℝ))).add
            ((hu.pow 4).const_mul (5 / 2 : ℝ))).sub ((hu.pow 2).const_mul (1 / 2 : ℝ))).add_const (1 / 42 : ℝ)
          have hval : ((6 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (6 - 1) * 1 -
              (3 : ℝ) * (((5 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (5 - 1) * 1) +
              (5 / 2 : ℝ) * (((4 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (4 - 1) * 1) -
              (1 / 2 : ℝ) * (((2 : ℕ) : ℝ) * (x - (m : ℝ)) ^ (2 - 1) * 1) =
              6 * ((x - (m : ℝ)) ^ 5 - 5 / 2 * (x - (m : ℝ)) ^ 4 +
                5 / 3 * (x - (m : ℝ)) ^ 3 - 1 / 6 * (x - (m : ℝ))) := by norm_num; ring
          rwa [hval] at hd
        simpa using h.ofReal_comp
      have hxp0 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-(s + 1))) x := by
        have h := hxp 0
        rw [add_zero, zero_add] at h
        exact h
      have hd1 := hB1.fun_mul hxp0
      have hd2 := (hB2.const_mul (s / 2)).fun_mul (hxp 1)
      have hd3 := (hB3.const_mul (s * (s + 1) / 6)).fun_mul (hxp 2)
      have hd4 := (hB4.const_mul (s * (s + 1) * (s + 2) / 24)).fun_mul (hxp 3)
      have hd5 := (hB5.const_mul (s * (s + 1) * (s + 2) * (s + 3) / 120)).fun_mul (hxp 4)
      have hd6 := (hB6.const_mul (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 720)).fun_mul (hxp 5)
      have htot := ((((hd1.fun_add hd2).fun_add hd3).fun_add hd4).fun_add hd5).fun_add hd6
      have hval :
          1 * (x : ℂ) ^ (-s) + (B1 (x - m) : ℂ) * (-s * (x : ℂ) ^ (-(s + 1))) +
          ((s / 2) * (2 * (B1 (x - m) : ℂ)) * (x : ℂ) ^ (-(s + 1)) +
            (s / 2) * (B2 (x - m) : ℂ) * (-(s + 1) * (x : ℂ) ^ (-(s + (1 + 1))))) +
          ((s * (s + 1) / 6) * (3 * (B2 (x - m) : ℂ)) * (x : ℂ) ^ (-(s + 2)) +
            (s * (s + 1) / 6) * (B3 (x - m) : ℂ) * (-(s + 2) * (x : ℂ) ^ (-(s + (2 + 1))))) +
          ((s * (s + 1) * (s + 2) / 24) * (4 * (B3 (x - m) : ℂ)) * (x : ℂ) ^ (-(s + 3)) +
            (s * (s + 1) * (s + 2) / 24) * (B4 (x - m) : ℂ) * (-(s + 3) * (x : ℂ) ^ (-(s + (3 + 1))))) +
          ((s * (s + 1) * (s + 2) * (s + 3) / 120) * (5 * (B4 (x - m) : ℂ)) * (x : ℂ) ^ (-(s + 4)) +
            (s * (s + 1) * (s + 2) * (s + 3) / 120) * (B5 (x - m) : ℂ) * (-(s + 4) * (x : ℂ) ^ (-(s + (4 + 1))))) +
          ((s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 720) * (6 * (B5 (x - m) : ℂ)) * (x : ℂ) ^ (-(s + 5)) +
            (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 720) * (B6 (x - m) : ℂ) * (-(s + 5) * (x : ℂ) ^ (-(s + (5 + 1))))) =
          (x : ℂ) ^ (-s) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720) *
            ((B6 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 6))) := by
        have h12 : -(s + (1 + 1)) = -(s + 2) := by ring
        have h23 : -(s + (2 + 1)) = -(s + 3) := by ring
        have h34 : -(s + (3 + 1)) = -(s + 4) := by ring
        have h45 : -(s + (4 + 1)) = -(s + 5) := by ring
        have h56 : -(s + (5 + 1)) = -(s + 6) := by ring
        rw [h12, h23, h34, h45, h56]
        ring
      rwa [hval] at htot
    have hcont1 : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
      intro x hx
      rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
      exact (Complex.continuousAt_ofReal_cpow_const x (-s)
        (Or.inr (lt_of_lt_of_le (by exact_mod_cast hm) hx.1).ne')).continuousWithinAt
    have hcont2 : ContinuousOn (fun x : ℝ => (B6 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 6)))
        (Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
      intro x hx
      rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)] at hx
      have hB6c : Continuous (fun t : ℝ => (B6 (t - m) : ℂ)) := by
        unfold B6; fun_prop
      exact (hB6c.continuousAt.mul (Complex.continuousAt_ofReal_cpow_const x (-(s + 6))
        (Or.inr (lt_of_lt_of_le (by exact_mod_cast hm) hx.1).ne'))).continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hFm
      (hcont1.sub (hcont2.const_mul _)).intervalIntegrable
    rw [intervalIntegral.integral_sub hcont1.intervalIntegrable (hcont2.const_mul _).intervalIntegrable,
      intervalIntegral.integral_const_mul] at hftc
    have hcongr :
        ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (B6 (x - m) : ℂ) * (x : ℂ) ^ (-(s + 6)) =
        ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6)) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne_ae : ∀ᵐ x : ℝ ∂volume, x ≠ ((m + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
      filter_upwards [hne_ae] with x hx hmem
      rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ m)] at hmem
      have hfl : ⌊x⌋ = (m : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast le_of_lt hmem.1,
        by exact_mod_cast lt_of_le_of_ne hmem.2 hx⟩
      have hfr : Int.fract x = x - (m : ℝ) := by simp [Int.fract, hfl]
      rw [P6, hfr]
    rw [hcongr] at hftc
    have hbdry : Fm ((m + 1 : ℕ) : ℝ) - Fm (m : ℝ) = (m : ℂ) ^ (-s) - tail m + tail (m + 1) := by
      simp only [Fm, tail, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, sub_self,
        B1, B2, B3, B4, B5, B6, Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_one]
      norm_num
      ring
    rw [hbdry] at hftc
    exact hftc.symm
  -- Sum over m = N..M-1
  have hsumM : ∀ M : ℕ, N ≤ M →
      (∑ k ∈ Finset.Ico N M, (k : ℂ) ^ (-s)) - tail N + tail M =
        (∫ x in (N : ℝ)..(M : ℝ), (x : ℂ) ^ (-s)) -
        (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720) *
          (∫ x in (N : ℝ)..(M : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hm1 : 1 ≤ m := le_trans hN hm
      have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hint_cp1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume (N : ℝ) (m : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hm)).mpr <|
          (integral_cpow_Ioi hN0 (show (-s).re < -1 by simp; linarith)).1.mono_set fun _ hx => hx.1
      have hint_cp2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ m)).mpr <|
          (integral_cpow_Ioi hN0 (show (-s).re < -1 by simp; linarith)).1.mono_set
            fun x hx => lt_of_le_of_lt (by exact_mod_cast hm) hx.1
      have hint_p1 : IntervalIntegrable (fun x : ℝ => (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))) volume (N : ℝ) (m : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hm)).mpr <|
          hint_P6.mono_set fun _ hx => hx.1
      have hint_p2 : IntervalIntegrable (fun x : ℝ => (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6)))
          volume (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ m)).mpr <|
          hint_P6.mono_set fun x hx => lt_of_le_of_lt (by exact_mod_cast hm) hx.1
      rw [Finset.sum_Ico_succ_top hm,
        ← intervalIntegral.integral_add_adjacent_intervals hint_cp1 hint_cp2,
        ← intervalIntegral.integral_add_adjacent_intervals hint_p1 hint_p2]
      have hst := hstep m hm1
      linear_combination ih + hst
  -- Send M -> infinity
  have htail_lim : Tendsto tail atTop (𝓝 0) := by
    have hpow_lim : ∀ k : ℕ, Tendsto (fun M : ℕ => (M : ℂ) ^ (-(s + (k : ℂ)))) atTop (𝓝 0) := by
      intro k
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hre : 0 < s.re + (k : ℝ) := by positivity
      have ht := (tendsto_rpow_neg_atTop hre).comp tendsto_natCast_atTop_atTop
      refine ht.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with M hM
      rw [Function.comp_apply, Complex.norm_natCast_cpow_of_pos (by omega : 0 < M)]
      simp
    have h0 := hpow_lim 0
    have h1 := hpow_lim 1
    have h3 := hpow_lim 3
    have h5 := hpow_lim 5
    have hcomb := ((((h0.const_mul (1 / 2 : ℂ)).add (h1.const_mul (s / 12))).sub
      (h3.const_mul (s * (s + 1) * (s + 2) / 720))).add
      (h5.const_mul (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240)))
    simpa [tail] using hcomb
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ⟨hint_cp, hval_cp⟩ := integral_cpow_Ioi hN0 (show (-s).re < -1 by simp; linarith)
  have hcp_lim : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (x : ℂ) ^ (-s))
      atTop (𝓝 ((N : ℂ) ^ (1 - s) / (s - 1))) := by
    have ht := (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint_cp tendsto_id).comp
      tendsto_natCast_atTop_atTop
    rw [hval_cp] at ht
    have hval : -((N : ℝ) : ℂ) ^ (-s + 1) / (-s + 1) = (N : ℂ) ^ (1 - s) / (s - 1) := by
      rw [Complex.ofReal_natCast, show -s + 1 = 1 - s by ring]
      have hs1 : s - 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp at this; linarith
      have hs1' : 1 - s ≠ 0 := by intro h; apply hs1; linear_combination -h
      field_simp [hs1, hs1']
      ring
    rwa [hval] at ht
  have hp6_lim : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6)))
      atTop (𝓝 (∫ x in Set.Ioi (N : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6)))) :=
    (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint_P6 tendsto_id).comp tendsto_natCast_atTop_atTop
  have hsumm : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
    have h := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    refine h.congr fun n => ?_
    rw [one_div, Complex.cpow_neg]
  have hzeta_lim : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-s))
      atTop (𝓝 (riemannZeta s)) := by
    have h0 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
      rw [Nat.cast_zero, Complex.zero_cpow]
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    have htsum : riemannZeta s = ∑' n : ℕ, (n : ℂ) ^ (-s) := by
      rw [zeta_eq_tsum_one_div_nat_cpow hs]
      exact tsum_congr fun n => by rw [one_div, Complex.cpow_neg]
    rw [htsum]
    refine hsumm.hasSum.tendsto_sum_nat.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    rw [Finset.sum_range_eq_add_Ico _ hM, h0, zero_add]
  have heq :
      (fun M : ℕ => ∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-s)) =ᶠ[atTop]
        (fun M : ℕ =>
          (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + tail N - tail M +
          (∫ x in (N : ℝ)..(M : ℝ), (x : ℂ) ^ (-s)) -
          (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720) *
            (∫ x in (N : ℝ)..(M : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6)))) := by
    filter_upwards [eventually_ge_atTop N] with M hM
    have hsplit := Finset.sum_Ico_consecutive (f := fun n : ℕ => (n : ℂ) ^ (-s)) hN hM
    have hsm := hsumM M hM
    linear_combination -hsplit + hsm
  have hrhs_lim :
      Tendsto (fun M : ℕ =>
        (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + tail N - tail M +
        (∫ x in (N : ℝ)..(M : ℝ), (x : ℂ) ^ (-s)) -
        (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720) *
          (∫ x in (N : ℝ)..(M : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))))
        atTop (𝓝 (em3 s N + R6 s N)) := by
    have h := (((tendsto_const_nhds (x := (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + tail N)).sub
      htail_lim).add hcp_lim).sub
      (hp6_lim.const_mul (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720))
    convert h using 2
    simp only [em3, R6, tail]
    ring
  exact tendsto_nhds_unique (hzeta_lim.congr' heq) hrhs_lim

lemma differentiableOn_R6 {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableOn ℂ (fun s : ℂ => R6 s N) {s : ℂ | 0 < s.re} := by
  have h1 := differentiableOn_mellin_bounded (a := (N : ℝ)) (C := 1 / 42) (k := 6)
    (by exact_mod_cast hN) (by norm_num)
    (Complex.continuous_ofReal.measurable.comp P6_measurable)
    (fun x _ => by dsimp only [Function.comp_apply]; rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_P6_le x)
  have hsub : {s : ℂ | 0 < s.re} ⊆ {s : ℂ | 1 - (6 : ℝ) < s.re} := fun s hs => by
    change 0 < s.re at hs; change 1 - 6 < s.re; linarith
  have h1' : DifferentiableOn ℂ (fun s : ℂ =>
      ∫ x in Set.Ioi (N : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))) {s : ℂ | 0 < s.re} := by
    simpa using h1.mono hsub
  have hpoly : DifferentiableOn ℂ (fun s : ℂ =>
      -(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 720)) {s : ℂ | 0 < s.re} := by
    fun_prop
  exact hpoly.mul h1'

lemma riemannZeta_eq_em3_add_R6 {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = em3 s N + R6 s N := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {(1 : ℂ)}
  have hU_open : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hem3_diff : DifferentiableOn ℂ (fun z => em3 z N) U :=
    fun z hz => (hasDerivAt_em3 hN hz.2).differentiableAt.differentiableWithinAt
  have hR6_diff : DifferentiableOn ℂ (fun z => R6 z N) U :=
    (differentiableOn_R6 hN).mono (fun z hz => hz.1)
  have hζ_an : AnalyticOnNhd ℂ riemannZeta U := analyticOn_riemannZeta.mono (fun z hz => hz.2)
  have hrhs_an : AnalyticOnNhd ℂ (fun z => em3 z N + R6 z N) U :=
    (hem3_diff.add hR6_diff).analyticOnNhd hU_open
  have heq : Set.EqOn riemannZeta (fun z => em3 z N + R6 z N) U :=
    hζ_an.eqOn_of_preconnected_of_eventuallyEq hrhs_an isPreconnected_rightHalfPlane_sdiff_one
      (show (2 : ℂ) ∈ U from ⟨by norm_num, by norm_num⟩)
      (eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))
        fun z hz => riemannZeta_eq_em3_add_R6_of_one_lt_re hN hz)
  exact heq ⟨hs, hs1⟩

lemma norm_R6_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖R6 s N‖ ≤
      (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖) /
        (30240 * (s.re + 5) * (N : ℝ) ^ (s.re + 5)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [R6, norm_mul, norm_neg, norm_div]
  have hint_bnd :
      ‖∫ x in Set.Ioi (N : ℝ), (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))‖ ≤
        (1 / 42) * ((N : ℝ) ^ (-(s.re + 5)) / (s.re + 5)) := by
    have h1 := norm_integral_le_integral_norm
      (f := fun x : ℝ => (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))) (μ := volume.restrict (Set.Ioi (N : ℝ)))
    have h2 : ∫ x in Set.Ioi (N : ℝ), ‖(P6 x : ℂ) * (x : ℂ) ^ (-(s + 6))‖ ≤
        ∫ x in Set.Ioi (N : ℝ), (1 / 42 : ℝ) * x ^ (-(s.re + 6)) := by
      refine setIntegral_mono_on ?_
        ((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 6)) (by linarith) hN0).const_mul (1 / 42))
        measurableSet_Ioi fun x hx => ?_
      · have hmeas : AEStronglyMeasurable (fun x : ℝ => (P6 x : ℂ) * (x : ℂ) ^ (-(s + 6)))
            (volume.restrict (Set.Ioi (N : ℝ))) := by
          refine (Complex.continuous_ofReal.measurable.comp P6_measurable).aestronglyMeasurable.mul ?_
          exact ContinuousOn.aestronglyMeasurable (fun x hx =>
            (Complex.continuousAt_ofReal_cpow_const x (-(s + 6))
              (Or.inr (lt_trans hN0 hx).ne')).continuousWithinAt) measurableSet_Ioi
        exact (((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 6)) (by linarith) hN0).const_mul (1 / 42)).mono' hmeas (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : 0 < x := lt_trans hN0 hx
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : (-(s + 6)).re = -(s.re + 6) := by simp
          rw [hre]
          exact mul_le_mul_of_nonneg_right (abs_P6_le x) (Real.rpow_nonneg hx0.le _))).norm
      · have hx0 : 0 < x := lt_trans hN0 hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : (-(s + 6)).re = -(s.re + 6) := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (abs_P6_le x) (Real.rpow_nonneg hx0.le _)
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (show -(s.re + 6) < -1 by linarith) hN0] at h2
    have hval : -((N : ℝ) ^ (-(s.re + 6) + 1)) / (-(s.re + 6) + 1) =
        (N : ℝ) ^ (-(s.re + 5)) / (s.re + 5) := by
      have hne : s.re + 5 ≠ 0 := by linarith
      have hexp : -(s.re + 6) + 1 = -(s.re + 5) := by ring
      rw [hexp, neg_div_neg_eq]
    linarith
  have hprod : ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5)‖ =
      ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ := by
    simp only [norm_mul]
  rw [hprod]
  have h720 : ‖(720 : ℂ)‖ = 720 := by norm_num
  rw [h720]
  have hmul := mul_le_mul_of_nonneg_left hint_bnd (by positivity :
    0 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ / 720)
  have hrew :
      (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ / 720) *
        (1 / 42 * ((N : ℝ) ^ (-(s.re + 5)) / (s.re + 5))) =
      (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖) /
        (30240 * (s.re + 5) * (N : ℝ) ^ (s.re + 5)) := by
    rw [Real.rpow_neg hN0.le]
    have hne1 : s.re + 5 ≠ 0 := by linarith
    have hne2 : (N : ℝ) ^ (s.re + 5) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    field_simp [hne1, hne2]
    ring
  linarith

lemma norm_deriv_riemannZeta_sub_dem3_le {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖deriv riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) - dem3 ((1 / 2 : ℂ) + (t : ℂ) * I) N‖ ≤
      ((‖(1 / 2 : ℂ) + (t : ℂ) * I‖ + 1 / 4) *
       (‖(1 / 2 : ℂ) + (t : ℂ) * I + 1‖ + 1 / 4) *
       (‖(1 / 2 : ℂ) + (t : ℂ) * I + 2‖ + 1 / 4) *
       (‖(1 / 2 : ℂ) + (t : ℂ) * I + 3‖ + 1 / 4) *
       (‖(1 / 2 : ℂ) + (t : ℂ) * I + 4‖ + 1 / 4) *
       (‖(1 / 2 : ℂ) + (t : ℂ) * I + 5‖ + 1 / 4)) / (39690 * (N : ℝ) ^ 5) := by
  set s₀ : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hs₀_ne1 : s₀ ≠ 1 := by
    intro h; have := congr_arg Complex.re h; simp [s₀] at this
  have hev : riemannZeta =ᶠ[𝓝 s₀] (fun z => em3 z N + R6 z N) := by
    have hU : IsOpen ({z : ℂ | 0 < z.re} \ {(1 : ℂ)}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    refine eventuallyEq_of_mem (hU.mem_nhds ⟨by simp [s₀], hs₀_ne1⟩) fun z hz =>
      riemannZeta_eq_em3_add_R6 hN hz.1 hz.2
  have hderiv_eq : deriv riemannZeta s₀ - dem3 s₀ N = deriv (fun z => R6 z N) s₀ := by
    rw [hev.deriv_eq]
    have hd1 : DifferentiableAt ℂ (fun z => em3 z N) s₀ := (hasDerivAt_em3 hN hs₀_ne1).differentiableAt
    have hd2 : DifferentiableAt ℂ (fun z => R6 z N) s₀ :=
      (differentiableOn_R6 hN).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp [s₀]))
    rw [deriv_fun_add hd1 hd2, (hasDerivAt_em3 hN hs₀_ne1).deriv]
    ring
  rw [hderiv_eq]
  have hdiff : DiffContOnCl ℂ (fun z => R6 z N) (Metric.ball s₀ (1 / 4)) := by
    have hsub : Metric.closedBall s₀ (1 / 4) ⊆ {z : ℂ | 0 < z.re} := by
      intro w hw
      have hd : |w.re - s₀.re| ≤ 1 / 4 := by
        calc |w.re - s₀.re| = |(w - s₀).re| := by simp
          _ ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
          _ ≤ 1 / 4 := by simpa [dist_eq_norm] using hw
      have hs0re : s₀.re = 1 / 2 := by simp [s₀]
      change 0 < w.re
      linarith [(abs_le.mp hd).1]
    exact (differentiableOn_R6 hN).diffContOnCl_ball hsub
  let P : ℝ :=
    (‖s₀‖ + 1 / 4) * (‖s₀ + 1‖ + 1 / 4) * (‖s₀ + 2‖ + 1 / 4) *
    (‖s₀ + 3‖ + 1 / 4) * (‖s₀ + 4‖ + 1 / 4) * (‖s₀ + 5‖ + 1 / 4)
  have hC : ∀ w ∈ Metric.sphere s₀ (1 / 4), ‖R6 w N‖ ≤ P / (30240 * (21 / 4) * (N : ℝ) ^ 5) := by
    intro w hw
    have hdist : ‖w - s₀‖ = 1 / 4 := mem_sphere_iff_norm.mp hw
    have hw_re : 1 / 4 ≤ w.re := by
      have hd : |w.re - s₀.re| ≤ 1 / 4 := by
        calc |w.re - s₀.re| = |(w - s₀).re| := by simp
          _ ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 4 := hdist
      have hs0re : s₀.re = 1 / 2 := by simp [s₀]
      linarith [(abs_le.mp hd).1]
    have hle := norm_R6_le hN (by linarith : 0 < w.re)
    have hsh : ∀ k : ℂ, ‖w + k‖ ≤ ‖s₀ + k‖ + 1 / 4 := fun k => by
      calc ‖w + k‖ = ‖(w - s₀) + (s₀ + k)‖ := by ring_nf
        _ ≤ ‖w - s₀‖ + ‖s₀ + k‖ := norm_add_le _ _
        _ = ‖s₀ + k‖ + 1 / 4 := by rw [hdist]; ring
    have hnum : ‖w‖ * ‖w + 1‖ * ‖w + 2‖ * ‖w + 3‖ * ‖w + 4‖ * ‖w + 5‖ ≤ P := by
      have h0 : ‖w‖ ≤ ‖s₀‖ + 1 / 4 := by simpa using hsh 0
      have h1 := hsh 1; have h2 := hsh 2; have h3 := hsh 3; have h4 := hsh 4; have h5 := hsh 5
      dsimp only [P]
      gcongr
    have hden1 : (21 / 4 : ℝ) ≤ w.re + 5 := by linarith
    have hden2 : (N : ℝ) ^ 5 ≤ (N : ℝ) ^ (w.re + 5) := by
      rw [← Real.rpow_natCast (N : ℝ) 5]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
    have hden : 30240 * (21 / 4) * (N : ℝ) ^ 5 ≤ 30240 * (w.re + 5) * (N : ℝ) ^ (w.re + 5) := by
      gcongr
    exact hle.trans (div_le_div₀ (by dsimp only [P]; positivity) hnum (by positivity) hden)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 (by norm_num : (0 : ℝ) < 1 / 4)
    hdiff hC
  rw [iteratedDeriv_one] at hc
  have hconst : (1 : ℕ).factorial * (P / (30240 * (21 / 4) * (N : ℝ) ^ 5)) / (1 / 4 : ℝ) ^ 1 =
      P / (39690 * (N : ℝ) ^ 5) := by
    norm_num; ring
  linarith

/-! === Landau-Tonelli Extension Theorem and Direction 1 -/

lemma landau_iteratedDeriv {f : ℝ → ℝ} (hf_meas : Measurable f)
    {X₀ : ℝ} (hX₀ : 1 ≤ X₀) (hf_nonneg : ∀ x, X₀ ≤ x → 0 ≤ f x)
    {σ₀ : ℝ} (hconv : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun x : ℝ => f x * x ^ (-σ - 2)) (Set.Ioi X₀)) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-z - 2)) {z : ℂ | σ₀ < z.re} ∧
    ∀ n : ℕ,
      (∀ w : ℂ, σ₀ < w.re →
        IntegrableOn (fun x : ℝ => (f x : ℂ) * (Real.log x : ℂ) ^ n * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀)) ∧
      (∀ w : ℂ, σ₀ < w.re →
        iteratedDeriv n (fun z : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-z - 2)) w =
          (-1 : ℂ) ^ n * ∫ x in Set.Ioi X₀, (f x : ℂ) * (Real.log x : ℂ) ^ n * (x : ℂ) ^ (-w - 2)) := by
  have hX₀0 : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  have hint_all : ∀ (k : ℕ) (w : ℂ), σ₀ < w.re →
      IntegrableOn (fun x : ℝ => (f x : ℂ) * (Real.log x : ℂ) ^ k * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀) := by
    intro k w hw
    set σ₁ := (σ₀ + w.re) / 2
    have hσ₁ : σ₀ < σ₁ := by dsimp only [σ₁]; linarith
    have hε : 0 < w.re - σ₁ := by dsimp only [σ₁]; linarith
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => (f x : ℂ) * (Real.log x : ℂ) ^ k * (x : ℂ) ^ (-w - 2))
        (volume.restrict (Set.Ioi X₀)) := by
      refine ((Complex.continuous_ofReal.measurable.comp hf_meas).aestronglyMeasurable.mul ?_).mul ?_
      · exact ContinuousOn.aestronglyMeasurable (fun x hx =>
          ((Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_log (lt_trans hX₀0 hx).ne')).pow k).continuousWithinAt)
          measurableSet_Ioi
      · exact ContinuousOn.aestronglyMeasurable (fun x hx =>
          (Complex.continuousAt_ofReal_cpow_const x (-w - 2)
            (Or.inr (lt_trans hX₀0 hx).ne')).continuousWithinAt) measurableSet_Ioi
    refine ((hconv σ₁ hσ₁).const_mul (((k : ℝ) / (w.re - σ₁)) ^ k)).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_trans hX₀ (le_of_lt hx)
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hfx : 0 ≤ f x := hf_nonneg x (le_of_lt hx)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfx,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-w - 2).re = -w.re - 2 := by simp
    rw [hre]
    have hlp := log_pow_le_const_mul_rpow hx1 hε k
    calc f x * (Real.log x) ^ k * x ^ (-w.re - 2)
        ≤ f x * (((k : ℝ) / (w.re - σ₁)) ^ k * x ^ (w.re - σ₁)) * x ^ (-w.re - 2) := by
          gcongr
      _ = ((k : ℝ) / (w.re - σ₁)) ^ k * (f x * (x ^ (w.re - σ₁) * x ^ (-w.re - 2))) := by ring
      _ = ((k : ℝ) / (w.re - σ₁)) ^ k * (f x * x ^ (-σ₁ - 2)) := by
          rw [← Real.rpow_add hx0]; congr 3; ring
  have hderiv_step : ∀ (k : ℕ) (w : ℂ), σ₀ < w.re →
      HasDerivAt (fun z : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (Real.log x : ℂ) ^ k * (x : ℂ) ^ (-z - 2))
        (-∫ x in Set.Ioi X₀, (f x : ℂ) * (Real.log x : ℂ) ^ (k + 1) * (x : ℂ) ^ (-w - 2)) w := by
    intro k w hw
    set σ₁ := (σ₀ + w.re) / 2
    set rad := (w.re - σ₁) / 3
    have hσ₁ : σ₀ < σ₁ := by dsimp only [σ₁]; linarith
    have hrad : 0 < rad := by dsimp only [rad, σ₁]; linarith
    let F : ℂ → ℝ → ℂ := fun z x => (f x : ℂ) * (Real.log x : ℂ) ^ k * (x : ℂ) ^ (-z - 2)
    let F' : ℂ → ℝ → ℂ := fun z x => -((f x : ℂ) * (Real.log x : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 2))
    have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi X₀)) := by
      intro z
      refine ((Complex.continuous_ofReal.measurable.comp hf_meas).aestronglyMeasurable.mul ?_).mul ?_
      · exact ContinuousOn.aestronglyMeasurable (fun x hx =>
          ((Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_log (lt_trans hX₀0 hx).ne')).pow k).continuousWithinAt)
          measurableSet_Ioi
      · exact ContinuousOn.aestronglyMeasurable (fun x hx =>
          (Complex.continuousAt_ofReal_cpow_const x (-z - 2)
            (Or.inr (lt_trans hX₀0 hx).ne')).continuousWithinAt) measurableSet_Ioi
    have hmeas_F' : AEStronglyMeasurable (F' w) (volume.restrict (Set.Ioi X₀)) :=
      (hint_all (k + 1) w hw).aestronglyMeasurable.neg
    let Ck : ℝ := (((k + 1 : ℕ) : ℝ) / (2 * rad)) ^ (k + 1)
    let bound : ℝ → ℝ := fun x => Ck * (f x * x ^ (-σ₁ - 2))
    have hbound_int : Integrable bound (volume.restrict (Set.Ioi X₀)) :=
      (hconv σ₁ hσ₁).const_mul Ck
    have h_bound : ∀ᵐ x ∂(volume.restrict (Set.Ioi X₀)),
        ∀ z ∈ Metric.ball w rad, ‖F' z x‖ ≤ bound x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
      have hx1 : 1 ≤ x := le_trans hX₀ (le_of_lt hx)
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hfx : 0 ≤ f x := hf_nonneg x (le_of_lt hx)
      have hzre : σ₁ + 2 * rad ≤ z.re := by
        have hdist : |z.re - w.re| < rad := by
          calc |z.re - w.re| = |(z - w).re| := by simp
            _ ≤ ‖z - w‖ := Complex.abs_re_le_norm _
            _ < rad := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
        have := (abs_lt.mp hdist).1
        dsimp only [rad, σ₁] at *
        linarith
      rw [show F' z x = -((f x : ℂ) * (Real.log x : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 2)) from rfl,
        norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfx,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hre : (-z - 2).re = -z.re - 2 := by simp
      rw [hre]
      have hlp := log_pow_le_const_mul_rpow hx1 (show 0 < 2 * rad by linarith) (k + 1)
      have hrpow : x ^ (-z.re - 2) ≤ x ^ (-(σ₁ + 2 * rad) - 2) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      calc f x * (Real.log x) ^ (k + 1) * x ^ (-z.re - 2)
          ≤ f x * (Ck * x ^ (2 * rad)) * x ^ (-(σ₁ + 2 * rad) - 2) := by
            gcongr
        _ = Ck * (f x * (x ^ (2 * rad) * x ^ (-(σ₁ + 2 * rad) - 2))) := by ring
        _ = Ck * (f x * x ^ (-σ₁ - 2)) := by
            rw [← Real.rpow_add hx0]; congr 3; ring
    have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioi X₀)),
        ∀ z ∈ Metric.ball w rad, HasDerivAt (F · x) (F' z x) z := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
      have hd := (hasDerivAt_ofReal_cpow_neg_add x (lt_trans hX₀0 hx) 2 z).const_mul
        ((f x : ℂ) * (Real.log x : ℂ) ^ k)
      have hfun : (fun u : ℂ => (f x : ℂ) * (Real.log x : ℂ) ^ k * (x : ℂ) ^ (-(u + (2 : ℝ)))) =
          (fun u : ℂ => F u x) := by
        ext u; simp only [F]; congr 2; push_cast; ring
      have hval : (f x : ℂ) * (Real.log x : ℂ) ^ k * (-(Real.log x : ℂ) * (x : ℂ) ^ (-(z + (2 : ℝ)))) =
          F' z x := by
        simp only [F', pow_succ, Complex.ofReal_ofNat]
        have hexp : -(z + 2) = -z - 2 := by ring
        rw [hexp]; ring
      rwa [hfun, hval] at hd
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w hrad)
      (Eventually.of_forall hmeas_F) (hint_all k w hw) hmeas_F' h_bound hbound_int h_diff
    simpa [F', integral_neg] using hd.2
  refine ⟨fun w hw => ?_, ?_⟩
  · have h0 := hderiv_step 0 w hw
    have hfun : (fun z : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (Real.log x : ℂ) ^ 0 * (x : ℂ) ^ (-z - 2)) =
        (fun z : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-z - 2)) := by
      ext z; simp
    rw [hfun] at h0
    exact h0.differentiableAt.differentiableWithinAt
  · intro n
    refine ⟨hint_all n, ?_⟩
    induction n with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hev : iteratedDeriv k (fun z : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-z - 2))
          =ᶠ[𝓝 w] (fun z : ℂ => (-1 : ℂ) ^ k *
            ∫ x in Set.Ioi X₀, (f x : ℂ) * (Real.log x : ℂ) ^ k * (x : ℂ) ^ (-z - 2)) :=
        eventuallyEq_of_mem (hopen.mem_nhds hw) ih
      rw [hev.deriv_eq, ((hderiv_step k w hw).const_mul ((-1 : ℂ) ^ k)).deriv, pow_succ]
      ring

lemma landau_mellin_nonneg {f : ℝ → ℝ} (hf_meas : Measurable f)
    {X₀ : ℝ} (hX₀ : 1 ≤ X₀) (hf_nonneg : ∀ x, X₀ ≤ x → 0 ≤ f x)
    (hf_bnd : ∀ x, 1 ≤ x → |f x| ≤ x ^ 2)
    (h_ext : ∀ σ : ℝ, 1 / 2 < σ →
      (∀ w : ℂ, σ < w.re →
        IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀)) →
      ∃ ε > 0, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (σ : ℂ) ε) ∧
        ∀ w ∈ Metric.ball (σ : ℂ) ε, σ < w.re →
          (∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-w - 2)) = G w) :
    (∀ w : ℂ, 1 / 2 < w.re →
      IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀)) ∧
    DifferentiableOn ℂ (fun w : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-w - 2))
      {w : ℂ | 1 / 2 < w.re} := by
  have hX₀0 : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  let S_conv : Set ℝ := {σ : ℝ | 1 / 2 ≤ σ ∧ IntegrableOn (fun x : ℝ => f x * x ^ (-σ - 2)) (Set.Ioi X₀)}
  have h2_mem : (2 : ℝ) ∈ S_conv := by
    refine ⟨by norm_num, ?_⟩
    have hmeas : AEStronglyMeasurable (fun x : ℝ => f x * x ^ (-(2 : ℝ) - 2))
        (volume.restrict (Set.Ioi X₀)) :=
      hf_meas.aestronglyMeasurable.mul
        (ContinuousOn.aestronglyMeasurable (fun x hx =>
          (continuousAt_id.rpow_const (Or.inl (lt_trans hX₀0 hx).ne')).continuousWithinAt)
          measurableSet_Ioi)
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hX₀0).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_trans hX₀ (le_of_lt hx)
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc |f x| * x ^ (-(2 : ℝ) - 2) ≤ x ^ 2 * x ^ (-(2 : ℝ) - 2) :=
          mul_le_mul_of_nonneg_right (hf_bnd x hx1) (Real.rpow_nonneg hx0.le _)
      _ = x ^ (-2 : ℝ) := by rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0]; norm_num
  have hbdd : BddBelow S_conv := ⟨1 / 2, fun _ h => h.1⟩
  set σ₀ := sInf S_conv
  have hσ₀_ge : 1 / 2 ≤ σ₀ := le_csInf ⟨2, h2_mem⟩ fun _ h => h.1
  have hconv_real : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun x : ℝ => f x * x ^ (-σ - 2)) (Set.Ioi X₀) := by
    intro σ hσ
    obtain ⟨σ₁, hσ₁_mem, hσ₁_lt⟩ := (csInf_lt_iff hbdd ⟨2, h2_mem⟩).mp hσ
    have hmeas : AEStronglyMeasurable (fun x : ℝ => f x * x ^ (-σ - 2))
        (volume.restrict (Set.Ioi X₀)) :=
      hf_meas.aestronglyMeasurable.mul
        (ContinuousOn.aestronglyMeasurable (fun x hx =>
          (continuousAt_id.rpow_const (Or.inl (lt_trans hX₀0 hx).ne')).continuousWithinAt)
          measurableSet_Ioi)
    refine hσ₁_mem.2.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_trans hX₀ (le_of_lt hx)
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf_nonneg x (le_of_lt hx)),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) (hf_nonneg x (le_of_lt hx))
  have hconv_cplx : ∀ w : ℂ, σ₀ < w.re →
      IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀) := by
    intro w hw
    simpa using ((landau_iteratedDeriv hf_meas hX₀ hf_nonneg hconv_real).2 0).1 w hw
  have hσ₀_eq : σ₀ = 1 / 2 := by
    by_contra hne
    have hgt : 1 / 2 < σ₀ := lt_of_le_of_ne hσ₀_ge (Ne.symm hne)
    obtain ⟨ε₀, hε₀, G, hG_diff, hG_eq⟩ := h_ext σ₀ hgt hconv_cplx
    set ε := min ε₀ (σ₀ - 1 / 2)
    have hε : 0 < ε := lt_min hε₀ (by linarith)
    set a : ℝ := σ₀ + ε / 4
    set sstar : ℝ := σ₀ - ε / 8
    have ha_gt : σ₀ < a := by dsimp only [a]; linarith
    have hsstar_ge : 1 / 2 ≤ sstar := by
      have : ε ≤ σ₀ - 1 / 2 := min_le_right _ _
      dsimp only [sstar]; linarith
    have hsstar_lt : sstar < σ₀ := by dsimp only [sstar]; linarith
    have hball_sub : Metric.ball (a : ℂ) (ε / 2) ⊆ Metric.ball (σ₀ : ℂ) ε₀ := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have h1 : ‖(a : ℂ) - (σ₀ : ℂ)‖ = ε / 4 := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith : 0 < a - σ₀)]
        dsimp only [a]; ring
      have hε_le : ε ≤ ε₀ := min_le_left _ _
      calc ‖z - (σ₀ : ℂ)‖ = ‖(z - (a : ℂ)) + ((a : ℂ) - (σ₀ : ℂ))‖ := by ring_nf
        _ ≤ ‖z - (a : ℂ)‖ + ‖(a : ℂ) - (σ₀ : ℂ)‖ := norm_add_le _ _
        _ < ε / 2 + ε / 4 := by linarith
        _ < ε₀ := by linarith
    have hsstar_mem : (sstar : ℂ) ∈ Metric.ball (a : ℂ) (ε / 2) := by
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hval : sstar - a = -(3 * ε / 8) := by dsimp only [sstar, a]; ring
      rw [hval, abs_neg, abs_of_pos (by linarith)]
      linarith
    have hG_taylor := Complex.hasSum_taylorSeries_on_ball (hG_diff.mono hball_sub) hsstar_mem
    have hderiv_G : ∀ n : ℕ, iteratedDeriv n G (a : ℂ) =
        (-1 : ℂ) ^ n * ∫ x in Set.Ioi X₀, (f x : ℂ) * (Real.log x : ℂ) ^ n * (x : ℂ) ^ (-(a : ℂ) - 2) := by
      intro n
      have hU_open : IsOpen (Metric.ball (σ₀ : ℂ) ε₀ ∩ {z : ℂ | σ₀ < z.re}) :=
        Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
      have ha_mem : (a : ℂ) ∈ Metric.ball (σ₀ : ℂ) ε₀ ∩ {z : ℂ | σ₀ < z.re} := by
        refine ⟨hball_sub (Metric.mem_ball_self (by linarith)), by simpa using ha_gt⟩
      have hev : G =ᶠ[𝓝 (a : ℂ)] (fun z : ℂ => ∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-z - 2)) :=
        eventuallyEq_of_mem (hU_open.mem_nhds ha_mem) fun z hz => (hG_eq z hz.1 hz.2).symm
      rw [hev.iteratedDeriv_eq n]
      exact ((landau_iteratedDeriv hf_meas hX₀ hf_nonneg hconv_real).2 n).2 (a : ℂ) (by simpa using ha_gt)
    have hterm_real : ∀ n : ℕ,
        ((n.factorial : ℂ)⁻¹ • ((sstar : ℂ) - (a : ℂ)) ^ n • iteratedDeriv n G (a : ℂ)) =
          Complex.ofReal (∫ x : ℝ in Set.Ioi X₀,
            f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2)) := by
      intro n
      rw [hderiv_G n, smul_eq_mul, smul_eq_mul]
      have hsign : ((sstar : ℂ) - (a : ℂ)) ^ n * (-1 : ℂ) ^ n = (((a - sstar) ^ n : ℝ) : ℂ) := by
        rw [← mul_pow]
        push_cast
        congr 1; ring
      have h1 : (n.factorial : ℂ)⁻¹ * (((sstar : ℂ) - (a : ℂ)) ^ n *
          ((-1 : ℂ) ^ n * ∫ x in Set.Ioi X₀, (f x : ℂ) * (Real.log x : ℂ) ^ n * (x : ℂ) ^ (-(a : ℂ) - 2))) =
          ∫ x in Set.Ioi X₀, (f x : ℂ) *
            (((((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) : ℝ) : ℂ) * (x : ℂ) ^ (-(a : ℂ) - 2) := by
        rw [← mul_assoc (((sstar : ℂ) - (a : ℂ)) ^ n), hsign, ← mul_assoc, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        push_cast
        rw [mul_pow]
        ring
      rw [h1, show Complex.ofReal (∫ x : ℝ in Set.Ioi X₀,
          f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2)) =
        ∫ x : ℝ in Set.Ioi X₀, ((f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2) : ℝ) : ℂ)
        from integral_ofReal.symm]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 < x := lt_trans hX₀0 hx
      rw [Complex.ofReal_mul, Complex.ofReal_mul,
        show (-(a : ℂ) - 2) = ((-a - 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hx0.le]
    have hsum_re : HasSum (fun n : ℕ =>
        ∫ x in Set.Ioi X₀, f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2))
        (G (sstar : ℂ)).re := by
      have h := Complex.hasSum_re (hG_taylor.congr_fun fun n => (hterm_real n).symm)
      simpa using h
    -- Apply Tonelli (lintegral_tsum)
    have hfn_meas : ∀ n : ℕ, Measurable (fun x : ℝ =>
        ENNReal.ofReal (f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2))) := by
      intro n
      exact ENNReal.measurable_ofReal.comp
        ((hf_meas.mul ((((measurable_const.mul Real.measurable_log).pow_const n).div_const _))).mul
          (measurable_id.pow_const _))
    have hterm_lint : ∀ n : ℕ,
        ∫⁻ x in Set.Ioi X₀,
          ENNReal.ofReal (f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2)) =
        ENNReal.ofReal (∫ x in Set.Ioi X₀,
          f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2)) := by
      intro n
      have hint_n : IntegrableOn (fun x : ℝ =>
          f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2)) (Set.Ioi X₀) := by
        have hc := ((landau_iteratedDeriv hf_meas hX₀ hf_nonneg hconv_real).2 n).1 (a : ℂ) (by simpa using ha_gt)
        have hre := hc.re.const_mul ((a - sstar) ^ n / (n.factorial : ℝ))
        refine hre.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := lt_trans hX₀0 hx
        have hval : ((f x : ℂ) * (Real.log x : ℂ) ^ n * (x : ℂ) ^ (-(a : ℂ) - 2)).re =
            f x * (Real.log x) ^ n * x ^ (-a - 2) := by
          have : (x : ℂ) ^ (-(a : ℂ) - 2) = ((x ^ (-a - 2) : ℝ) : ℂ) := by
            rw [show (-(a : ℂ) - 2) = ((-a - 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hx0.le]
          rw [this]
          norm_cast
        change (a - sstar) ^ n / (n.factorial : ℝ) *
          ((f x : ℂ) * (Real.log x : ℂ) ^ n * (x : ℂ) ^ (-(a : ℂ) - 2)).re = _
        rw [hval, mul_pow]
        ring
      symm
      refine ofReal_integral_eq_lintegral_ofReal hint_n ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 ≤ x := le_trans hX₀ (le_of_lt hx)
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hfx : 0 ≤ f x := hf_nonneg x (le_of_lt hx)
      have has : 0 ≤ a - sstar := by linarith
      have hlg : 0 ≤ Real.log x := Real.log_nonneg hx1
      positivity
    have hlint_eq :
        ∫⁻ x in Set.Ioi X₀, ENNReal.ofReal (f x * x ^ (-sstar - 2)) =
          ENNReal.ofReal (G (sstar : ℂ)).re := by
      have hpw : ∀ x ∈ Set.Ioi X₀,
          ENNReal.ofReal (f x * x ^ (-sstar - 2)) =
            ∑' n : ℕ, ENNReal.ofReal
              (f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2)) := by
        intro x hx
        have hx1 : 1 ≤ x := le_trans hX₀ (le_of_lt hx)
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
        have hfx : 0 ≤ f x := hf_nonneg x (le_of_lt hx)
        have has : 0 ≤ a - sstar := by linarith
        have hlg : 0 ≤ Real.log x := Real.log_nonneg hx1
        have hexp_sum : HasSum (fun n : ℕ =>
            f x * (((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-a - 2))
            (f x * x ^ (-sstar - 2)) := by
          have he0 : HasSum (fun n : ℕ => ((a - sstar) * Real.log x) ^ n / (n.factorial : ℝ))
              (Real.exp ((a - sstar) * Real.log x)) := by
            rw [Real.exp_eq_exp_ℝ]
            simpa [div_eq_inv_mul, smul_eq_mul] using
              NormedSpace.expSeries_div_hasSum_exp ((a - sstar) * Real.log x)
          have he := (he0.mul_left (f x)).mul_right (x ^ (-a - 2))
          have hval : f x * Real.exp ((a - sstar) * Real.log x) * x ^ (-a - 2) =
              f x * x ^ (-sstar - 2) := by
            rw [mul_comm (a - sstar), ← Real.rpow_def_of_pos hx0, mul_assoc, ← Real.rpow_add hx0]
            congr 2; ring
          simpa [hval] using he
        rw [← hexp_sum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hexp_sum.summable]
      rw [setLIntegral_congr_fun measurableSet_Ioi hpw,
        lintegral_tsum (fun n => (hfn_meas n).aemeasurable)]
      simp_rw [hterm_lint]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => setIntegral_nonneg measurableSet_Ioi fun x hx => by
        have hx1 : 1 ≤ x := le_trans hX₀ (le_of_lt hx)
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
        have hfx : 0 ≤ f x := hf_nonneg x (le_of_lt hx)
        have has : 0 ≤ a - sstar := by linarith
        have hlg : 0 ≤ Real.log x := Real.log_nonneg hx1
        positivity) hsum_re.summable, hsum_re.tsum_eq]
    have hsstar_int : IntegrableOn (fun x : ℝ => f x * x ^ (-sstar - 2)) (Set.Ioi X₀) := by
      have hmeas : AEStronglyMeasurable (fun x : ℝ => f x * x ^ (-sstar - 2))
          (volume.restrict (Set.Ioi X₀)) :=
        hf_meas.aestronglyMeasurable.mul
          (ContinuousOn.aestronglyMeasurable (fun x hx =>
            (continuousAt_id.rpow_const (Or.inl (lt_trans hX₀0 hx).ne')).continuousWithinAt)
            measurableSet_Ioi)
      refine ⟨hmeas, ?_⟩
      rw [HasFiniteIntegral]
      have heq : ∫⁻ x in Set.Ioi X₀, ‖f x * x ^ (-sstar - 2)‖ₑ =
          ∫⁻ x in Set.Ioi X₀, ENNReal.ofReal (f x * x ^ (-sstar - 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hnn : 0 ≤ f x * x ^ (-sstar - 2) :=
          mul_nonneg (hf_nonneg x (le_of_lt hx)) (Real.rpow_nonneg (lt_trans hX₀0 hx).le _)
        rw [Real.enorm_eq_ofReal hnn]
      rw [heq, hlint_eq]
      exact ENNReal.ofReal_lt_top
    have hsstar_mem : sstar ∈ S_conv := ⟨hsstar_ge, hsstar_int⟩
    have hle : σ₀ ≤ sstar := csInf_le hbdd hsstar_mem
    linarith
  rw [hσ₀_eq] at hconv_cplx hconv_real
  exact ⟨hconv_cplx, (landau_iteratedDeriv hf_meas hX₀ hf_nonneg hconv_real).1⟩

/-- Finite-range Mellin integral `∫_{1}^{X₀} f(x) x^{-w-2} dx` is entire. -/
lemma differentiable_finite_mellin {f : ℝ → ℝ} (hf_meas : Measurable f)
    {X₀ : ℝ} (hX₀ : 1 ≤ X₀) (hf_bnd : ∀ x, 1 ≤ x → |f x| ≤ x ^ 2) :
    Differentiable ℂ (fun w : ℂ => ∫ x in Set.Ioc (1 : ℝ) X₀, (f x : ℂ) * (x : ℂ) ^ (-w - 2)) := by
  intro w₀
  let F : ℂ → ℝ → ℂ := fun w x => (f x : ℂ) * (x : ℂ) ^ (-w - 2)
  let F' : ℂ → ℝ → ℂ := fun w x => -((f x : ℂ) * (Real.log x : ℂ) * (x : ℂ) ^ (-w - 2))
  have hmeas_F : ∀ w : ℂ, AEStronglyMeasurable (F w) (volume.restrict (Set.Ioc 1 X₀)) := fun w =>
    (Complex.continuous_ofReal.measurable.comp hf_meas).aestronglyMeasurable.mul
      (ContinuousOn.aestronglyMeasurable (fun x hx =>
        (Complex.continuousAt_ofReal_cpow_const x (-w - 2)
          (Or.inr (lt_trans zero_lt_one hx.1).ne')).continuousWithinAt) measurableSet_Ioc)
  have hmeas_F' : AEStronglyMeasurable (F' w₀) (volume.restrict (Set.Ioc 1 X₀)) := by
    refine ((Complex.continuous_ofReal.measurable.comp hf_meas).aestronglyMeasurable.mul ?_).mul ?_ |>.neg
    · exact ContinuousOn.aestronglyMeasurable (fun x hx =>
        (Complex.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_log (lt_trans zero_lt_one hx.1).ne')).continuousWithinAt) measurableSet_Ioc
    · exact ContinuousOn.aestronglyMeasurable (fun x hx =>
        (Complex.continuousAt_ofReal_cpow_const x (-w₀ - 2)
          (Or.inr (lt_trans zero_lt_one hx.1).ne')).continuousWithinAt) measurableSet_Ioc
  set M : ℝ := X₀ ^ 2 * Real.log X₀ * X₀ ^ (|w₀.re| + 3) + X₀ ^ 2 * X₀ ^ (|w₀.re| + 3)
  have hF_int : Integrable (F w₀) (volume.restrict (Set.Ioc 1 X₀)) := by
    refine (integrableOn_const (hs := measure_Ioc_lt_top.ne) (C := M)).mono' (hmeas_F w₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx.1
    have hx0 : 0 < x := lt_trans zero_lt_one hx.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-w₀ - 2).re = -w₀.re - 2 := by simp
    rw [hre]
    have h1 : |f x| ≤ X₀ ^ 2 := (hf_bnd x hx1).trans (by nlinarith [hx.2])
    have h2 : x ^ (-w₀.re - 2) ≤ X₀ ^ (|w₀.re| + 3) := by
      calc x ^ (-w₀.re - 2) ≤ x ^ (|w₀.re| + 3) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [neg_le_abs w₀.re])
        _ ≤ X₀ ^ (|w₀.re| + 3) := Real.rpow_le_rpow hx0.le hx.2 (by positivity)
    have h3 : 0 ≤ X₀ ^ 2 * Real.log X₀ * X₀ ^ (|w₀.re| + 3) := by
      have : 0 ≤ Real.log X₀ := Real.log_nonneg hX₀
      positivity
    nlinarith [mul_le_mul h1 h2 (Real.rpow_nonneg hx0.le _) (by positivity)]
  have h_bound : ∀ᵐ x ∂(volume.restrict (Set.Ioc 1 X₀)),
      ∀ w ∈ Metric.ball w₀ 1, ‖F' w x‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx w hw
    have hx1 : 1 ≤ x := le_of_lt hx.1
    have hx0 : 0 < x := lt_trans zero_lt_one hx.1
    have hwre : -w.re - 2 ≤ |w₀.re| + 3 := by
      have hdist : |w.re - w₀.re| < 1 := by
        calc |w.re - w₀.re| = |(w - w₀).re| := by simp
          _ ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
          _ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      linarith [(abs_lt.mp hdist).1, neg_le_abs w₀.re]
    rw [show F' w x = -((f x : ℂ) * (Real.log x : ℂ) * (x : ℂ) ^ (-w - 2)) from rfl,
      norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-w - 2).re = -w.re - 2 := by simp
    rw [hre]
    have h1 : |f x| ≤ X₀ ^ 2 := (hf_bnd x hx1).trans (by nlinarith [hx.2])
    have h2 : Real.log x ≤ Real.log X₀ := Real.log_le_log hx0 hx.2
    have h3 : x ^ (-w.re - 2) ≤ X₀ ^ (|w₀.re| + 3) := by
      calc x ^ (-w.re - 2) ≤ x ^ (|w₀.re| + 3) := Real.rpow_le_rpow_of_exponent_le hx1 hwre
        _ ≤ X₀ ^ (|w₀.re| + 3) := Real.rpow_le_rpow hx0.le hx.2 (by positivity)
    have h4 : |f x| * Real.log x ≤ X₀ ^ 2 * Real.log X₀ :=
      mul_le_mul h1 h2 (Real.log_nonneg hx1) (by positivity)
    have h5 : |f x| * Real.log x * x ^ (-w.re - 2) ≤ X₀ ^ 2 * Real.log X₀ * X₀ ^ (|w₀.re| + 3) :=
      mul_le_mul h4 h3 (Real.rpow_nonneg hx0.le _) (mul_nonneg (by positivity) (Real.log_nonneg hX₀))
    have h6 : 0 ≤ X₀ ^ 2 * X₀ ^ (|w₀.re| + 3) := by positivity
    linarith
  have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioc 1 X₀)),
      ∀ w ∈ Metric.ball w₀ 1, HasDerivAt (F · x) (F' w x) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx w _
    have hd := (hasDerivAt_ofReal_cpow_neg_add x (lt_trans zero_lt_one hx.1) 2 w).const_mul (f x : ℂ)
    have hfun : (fun u : ℂ => (f x : ℂ) * (x : ℂ) ^ (-(u + (2 : ℝ)))) = (fun u : ℂ => F u x) := by
      ext u; simp only [F]; congr 2; push_cast; ring
    have hval : (f x : ℂ) * (-(Real.log x : ℂ) * (x : ℂ) ^ (-(w + (2 : ℝ)))) = F' w x := by
      simp only [F', Complex.ofReal_ofNat]
      have hexp : -(w + 2) = -w - 2 := by ring
      rw [hexp]; ring
    rwa [hfun, hval] at hd
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ zero_lt_one)
    (Eventually.of_forall hmeas_F) hF_int hmeas_F' h_bound
    (integrableOn_const (hs := measure_Ioc_lt_top.ne) (C := M)) h_diff).2.differentiableAt

/-- Analytic continuation of `M_hol(w) = (w - 1) * (1 - ζ(2w)) / ((w + 1) * riemannZeta₁ w)`. -/
noncomputable def Mhol (w : ℂ) : ℂ :=
  (w - 1) * (1 - riemannZeta (2 * w)) / ((w + 1) * riemannZeta₁ w)

lemma riemannZeta₁_ne_zero_of_real_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) :
    riemannZeta₁ (σ : ℂ) ≠ 0 := by
  rcases lt_trichotomy σ 1 with hlt | rfl | hgt
  · have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast hlt.ne
    have hz := riemannZeta_ne_zero_of_Ioo (by linarith) hlt
    rw [riemannZeta_eq_inv_sub_mul hne] at hz
    exact right_ne_zero_of_mul hz
  · simp
  · have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast hgt.ne'
    have hz := riemannZeta_ne_zero_of_one_lt_re (s := (σ : ℂ)) (by simpa using hgt)
    rw [riemannZeta_eq_inv_sub_mul hne] at hz
    exact right_ne_zero_of_mul hz

lemma differentiableAt_Mhol_of_real_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ ε > 0, DifferentiableOn ℂ Mhol (Metric.ball (σ : ℂ) ε) := by
  have hcont : ContinuousAt riemannZeta₁ (σ : ℂ) := differentiable_riemannZeta₁.continuous.continuousAt
  have hne : riemannZeta₁ (σ : ℂ) ≠ 0 := riemannZeta₁_ne_zero_of_real_gt_half hσ
  have hev : ∀ᶠ w in 𝓝 (σ : ℂ), riemannZeta₁ w ≠ 0 := hcont.eventually_ne hne
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.eventually_nhds_iff.mp hev
  set ε := min ε₁ (σ - 1 / 2)
  have hε : 0 < ε := lt_min hε₁ (by linarith)
  refine ⟨ε, hε, fun w hw => ?_⟩
  have hdist : ‖w - (σ : ℂ)‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hwre : 1 / 2 < w.re := by
    have h1 : |w.re - σ| < ε := by
      calc |w.re - σ| = |(w - (σ : ℂ)).re| := by simp
        _ ≤ ‖w - (σ : ℂ)‖ := Complex.abs_re_le_norm _
        _ < ε := hdist
    have : ε ≤ σ - 1 / 2 := min_le_right _ _
    linarith [(abs_lt.mp h1).1]
  have h2w : 2 * w ≠ 1 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have hw1 : w + 1 ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have hz1 : riemannZeta₁ w ≠ 0 := hball₁ (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
  have hd_num : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * (1 - riemannZeta (2 * z))) w := by
    have hζ2 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) w :=
      (differentiableAt_riemannZeta h2w).comp w (differentiableAt_id.const_mul 2)
    exact (differentiableAt_id.sub_const 1).mul ((differentiableAt_const 1).sub hζ2)
  have hd_den : DifferentiableAt ℂ (fun z : ℂ => (z + 1) * riemannZeta₁ z) w :=
    (differentiableAt_id.add_const 1).mul differentiable_riemannZeta₁.differentiableAt
  exact (hd_num.div hd_den (mul_ne_zero hw1 hz1)).differentiableWithinAt

lemma mellin_A_split {X₀ : ℝ} (hX₀ : 1 ≤ X₀) {w : ℂ} (hw : 1 < w.re) :
    (∫ x in Set.Ioi X₀, (A x : ℂ) * (x : ℂ) ^ (-w - 2)) +
      (∫ x in Set.Ioc (1 : ℝ) X₀, (A x : ℂ) * (x : ℂ) ^ (-w - 2)) =
      (riemannZeta (2 * w) - 1) / ((w + 1) * riemannZeta w) := by
  have hint := mellin_A_integrableOn hw
  have hunion : Set.Ioc (1 : ℝ) X₀ ∪ Set.Ioi X₀ = Set.Ioi 1 := Set.Ioc_union_Ioi_eq_Ioi hX₀
  have hdisj : Disjoint (Set.Ioc (1 : ℝ) X₀) (Set.Ioi X₀) :=
    Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1.2 h2
  have hint1 : IntegrableOn (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioc 1 X₀) :=
    hint.mono_set (fun _ hx => hx.1)
  have hint2 : IntegrableOn (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀) :=
    hint.mono_set (fun x hx => lt_of_le_of_lt hX₀ hx)
  rw [add_comm, ← setIntegral_union hdisj measurableSet_Ioi hint1 hint2, hunion, mellin_A_eq hw]

lemma landau_A_extension {s : ℝ} (hs : s = 1 ∨ s = -1) {X₀ : ℝ} (hX₀ : 1 ≤ X₀)
    (hnonneg : ∀ x, X₀ ≤ x → 0 ≤ s * A x) :
    (∀ w : ℂ, 1 / 2 < w.re →
      IntegrableOn (fun x : ℝ => ((s * A x : ℝ) : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀)) ∧
    (∀ w : ℂ, 1 / 2 < w.re → w ≠ 1 → riemannZeta w ≠ 0 →
      (∫ x in Set.Ioi X₀, ((s * A x : ℝ) : ℂ) * (x : ℂ) ^ (-w - 2)) =
        (s : ℂ) * ((riemannZeta (2 * w) - 1) / ((w + 1) * riemannZeta w)) -
        ∫ x in Set.Ioc (1 : ℝ) X₀, ((s * A x : ℝ) : ℂ) * (x : ℂ) ^ (-w - 2)) := by
  let f : ℝ → ℝ := fun x => s * A x
  have hf_meas : Measurable f := measurable_const.mul A_measurable
  have hf_bnd : ∀ x, 1 ≤ x → |f x| ≤ x ^ 2 := by
    intro x hx
    have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [show f x = s * A x from rfl, abs_mul, hsabs, one_mul]
    exact abs_A_le x hx
  let E : ℂ → ℂ := fun w => ∫ x in Set.Ioc (1 : ℝ) X₀, (f x : ℂ) * (x : ℂ) ^ (-w - 2)
  have hE_diff : Differentiable ℂ E := differentiable_finite_mellin hf_meas hX₀ hf_bnd
  let I : ℂ → ℂ := fun w => ∫ x in Set.Ioi X₀, (f x : ℂ) * (x : ℂ) ^ (-w - 2)
  have hid_on_half : ∀ σ : ℝ, 1 / 2 ≤ σ →
      (∀ w : ℂ, σ < w.re → IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀)) →
      DifferentiableOn ℂ I {w : ℂ | σ < w.re} →
      ∀ w : ℂ, σ < w.re →
        (w + 1) * riemannZeta₁ w * (I w + E w) = (s : ℂ) * ((w - 1) * (riemannZeta (2 * w) - 1)) := by
    intro σ hσ _ hI_diff w hw
    let H : ℂ → ℂ := fun z =>
      (z + 1) * riemannZeta₁ z * (I z + E z) - (s : ℂ) * ((z - 1) * (riemannZeta (2 * z) - 1))
    let V : Set ℂ := {z : ℂ | σ < z.re}
    have hV_open : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
    have hV_conn : IsPreconnected V := (convex_halfSpace_re_gt σ).isPreconnected
    have hH_diff : DifferentiableOn ℂ H V := by
      intro z hz
      have h2z : 2 * z ≠ 1 := by
        intro h; have := congr_arg Complex.re h; simp at this; change σ < z.re at hz; linarith
      have hd1 : DifferentiableWithinAt ℂ (fun u => (u + 1) * riemannZeta₁ u * (I u + E u)) V z :=
        ((differentiableAt_id.add_const 1).mul differentiable_riemannZeta₁.differentiableAt).differentiableWithinAt.mul
          ((hI_diff z hz).add hE_diff.differentiableAt.differentiableWithinAt)
      have hd2 : DifferentiableAt ℂ (fun u => (s : ℂ) * ((u - 1) * (riemannZeta (2 * u) - 1))) z := by
        have hζ2 : DifferentiableAt ℂ (fun u => riemannZeta (2 * u)) z :=
          (differentiableAt_riemannZeta h2z).comp z (differentiableAt_id.const_mul 2)
        exact ((differentiableAt_id.sub_const 1).mul (hζ2.sub_const 1)).const_mul (s : ℂ)
      exact hd1.sub hd2.differentiableWithinAt
    have hH_zero_gt : ∀ z : ℂ, max σ 1 < z.re → H z = 0 := by
      intro z hz
      have hz1 : 1 < z.re := lt_of_le_of_lt (le_max_right _ _) hz
      have hz_ne1 : z ≠ 1 := by intro h; rw [h] at hz1; norm_num at hz1
      have hsplit := mellin_A_split hX₀ hz1
      have hIE : I z + E z = (s : ℂ) * ((riemannZeta (2 * z) - 1) / ((z + 1) * riemannZeta z)) := by
        have hIeq : I z = (s : ℂ) * ∫ x in Set.Ioi X₀, (A x : ℂ) * (x : ℂ) ^ (-z - 2) := by
          simp only [I, f, Complex.ofReal_mul, mul_assoc, integral_const_mul]
        have hEeq : E z = (s : ℂ) * ∫ x in Set.Ioc (1 : ℝ) X₀, (A x : ℂ) * (x : ℂ) ^ (-z - 2) := by
          simp only [E, f, Complex.ofReal_mul, mul_assoc, integral_const_mul]
        rw [hIeq, hEeq, ← mul_add, hsplit]
      have hz_ne0 : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz1
      have hzp1 : z + 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp at this; linarith
      have hz1_eq : riemannZeta₁ z = (z - 1) * riemannZeta z := by
        rw [riemannZeta_eq_inv_sub_mul hz_ne1]
        have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
        field_simp [hsub]
      simp only [H, hIE, hz1_eq]
      field_simp [hzp1, hz_ne0]
      ring
    have hbase : ((max σ 1 + 1 : ℝ) : ℂ) ∈ V := by
      change σ < ((max σ 1 + 1 : ℝ) : ℂ).re
      simp; linarith [le_max_left σ 1]
    have hH_an : AnalyticOnNhd ℂ H V := hH_diff.analyticOnNhd hV_open
    have hzero := hH_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hV_conn hbase
      (eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show max σ 1 < ((max σ 1 + 1 : ℝ) : ℂ).re by simp)) hH_zero_gt)
    exact sub_eq_zero.mp (hzero hw)
  have h_ext : ∀ σ : ℝ, 1 / 2 < σ →
      (∀ w : ℂ, σ < w.re → IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-w - 2)) (Set.Ioi X₀)) →
      ∃ ε > 0, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (σ : ℂ) ε) ∧
        ∀ w ∈ Metric.ball (σ : ℂ) ε, σ < w.re → I w = G w := by
    intro σ hσ hconv_cplx
    have hconv_real : ∀ σ' : ℝ, σ < σ' → IntegrableOn (fun x : ℝ => f x * x ^ (-σ' - 2)) (Set.Ioi X₀) := by
      intro σ' hσ'
      have hc := (hconv_cplx (σ' : ℂ) (by simpa using hσ')).re
      refine hc.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans (lt_of_lt_of_le zero_lt_one hX₀) hx
      have hval : (x : ℂ) ^ (-(σ' : ℂ) - 2) = ((x ^ (-σ' - 2) : ℝ) : ℂ) := by
        rw [show (-(σ' : ℂ) - 2) = ((-σ' - 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hx0.le]
      change ((f x : ℂ) * (x : ℂ) ^ (-(σ' : ℂ) - 2)).re = _
      rw [hval]; norm_cast
    have hI_diff : DifferentiableOn ℂ I {w : ℂ | σ < w.re} :=
      (landau_iteratedDeriv hf_meas hX₀ hnonneg hconv_real).1
    obtain ⟨ε₁, hε₁, hM_diff⟩ := differentiableAt_Mhol_of_real_gt_half hσ
    have hcont : ContinuousAt riemannZeta₁ (σ : ℂ) := differentiable_riemannZeta₁.continuous.continuousAt
    obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.eventually_nhds_iff.mp
      (hcont.eventually_ne (riemannZeta₁_ne_zero_of_real_gt_half hσ))
    set ε := min (min ε₁ ε₂) (σ - 1 / 2)
    have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (by linarith)
    refine ⟨ε, hε, fun w => -(s : ℂ) * Mhol w - E w, ?_, ?_⟩
    · refine ((hM_diff.mono (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)))).const_mul
        (-(s : ℂ))).sub hE_diff.differentiableOn
    · intro w hw hwre
      have hz1 : riemannZeta₁ w ≠ 0 :=
        hball₂ (lt_of_lt_of_le (Metric.mem_ball.mp hw) (le_trans (min_le_left _ _) (min_le_right _ _)))
      have hw1 : w + 1 ≠ 0 := by
        intro h; have := congr_arg Complex.re h; simp at this; linarith
      have hid := hid_on_half σ hσ.le hconv_cplx hI_diff w hwre
      have hval : I w + E w = -(s : ℂ) * Mhol w := by
        rw [Mhol]
        apply mul_left_cancel₀ (mul_ne_zero hw1 hz1)
        rw [hid]
        field_simp [hw1, hz1]
        ring
      linear_combination hval
  obtain ⟨hint_all, hdiff_all⟩ := landau_mellin_nonneg hf_meas hX₀ hnonneg hf_bnd h_ext
  refine ⟨hint_all, fun w hw hw1 hζ => ?_⟩
  have hid := hid_on_half (1 / 2) le_rfl hint_all hdiff_all w hw
  have hz1_eq : riemannZeta₁ w = (w - 1) * riemannZeta w := by
    rw [riemannZeta_eq_inv_sub_mul hw1]
    have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    field_simp [hsub]
  have hwp1 : w + 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp at this; linarith
  have hwsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  rw [hz1_eq] at hid
  have hIE : I w + E w = (s : ℂ) * ((riemannZeta (2 * w) - 1) / ((w + 1) * riemannZeta w)) := by
    apply mul_left_cancel₀ (mul_ne_zero hwp1 (mul_ne_zero hwsub hζ))
    calc (w + 1) * ((w - 1) * riemannZeta w) * (I w + E w)
        = (s : ℂ) * ((w - 1) * (riemannZeta (2 * w) - 1)) := hid
      _ = (w + 1) * ((w - 1) * riemannZeta w) *
            ((s : ℂ) * ((riemannZeta (2 * w) - 1) / ((w + 1) * riemannZeta w))) := by
          field_simp [hwp1, hwsub, hζ]
  linear_combination hIE

/-- Direction 1 (`<1>2<2>3`): `{n : ℕ | S n < 0}.Infinite`. -/
theorem S_neg_infinite : {n : ℕ | S n < 0}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, 0 ≤ S n := by
    by_cases hne : {n : ℕ | S n < 0}.Nonempty
    · refine ⟨hfin.toFinset.max' (hfin.toFinset_nonempty.mpr hne) + 1, fun n hn => ?_⟩
      by_contra hlt
      push Not at hlt
      have hmem : n ∈ hfin.toFinset := hfin.mem_toFinset.mpr hlt
      have hle := Finset.le_max' hfin.toFinset n hmem
      omega
    · refine ⟨0, fun n _ => ?_⟩
      by_contra hlt
      push Not at hlt
      exact hne ⟨n, hlt⟩
  set X₀ : ℝ := (q N₀ : ℝ)
  have hq_pos : 1 ≤ q N₀ := (Nat.nth_mem_of_infinite nonSqf_infinite N₀).1
  have hX₀ : 1 ≤ X₀ := by dsimp only [X₀]; exact_mod_cast hq_pos
  have hAnonneg : ∀ x, X₀ ≤ x → 0 ≤ (1 : ℝ) * A x := fun x hx => by
    rw [one_mul]; exact A_nonneg_of_S_nonneg hN₀ x hx
  have ⟨_, heq⟩ := landau_A_extension (Or.inl rfl) hX₀ hAnonneg
  -- Bound E(w) on (1/2, 1) uniformly below by -C
  set C : ℝ := X₀ ^ 3
  have hE_ge : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 →
      -C ≤ (∫ x in Set.Ioc (1 : ℝ) X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)).re := by
    intro σ hσ0 hσ1
    have hnorm : ‖∫ x in Set.Ioc (1 : ℝ) X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)‖ ≤ C := by
      have h1 := norm_integral_le_integral_norm
        (f := fun x : ℝ => (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2))
        (μ := volume.restrict (Set.Ioc 1 X₀))
      have h2 : ∫ x in Set.Ioc (1 : ℝ) X₀,
          ‖(((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)‖ ≤
          ∫ _ in Set.Ioc (1 : ℝ) X₀, X₀ ^ 2 := by
        refine setIntegral_mono_on ?_ (integrableOn_const (hs := measure_Ioc_lt_top.ne))
          measurableSet_Ioc fun x hx => ?_
        · have hmeas : AEStronglyMeasurable
              (fun x : ℝ => (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2))
              (volume.restrict (Set.Ioc 1 X₀)) :=
            (Complex.continuous_ofReal.measurable.comp (measurable_const.mul A_measurable)).aestronglyMeasurable.mul
              (ContinuousOn.aestronglyMeasurable (fun x hx =>
                (Complex.continuousAt_ofReal_cpow_const x (-(σ : ℂ) - 2)
                  (Or.inr (lt_trans zero_lt_one hx.1).ne')).continuousWithinAt) measurableSet_Ioc)
          refine ((integrableOn_const (hs := measure_Ioc_lt_top.ne) (C := X₀ ^ 2)).mono' hmeas ?_).norm
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          have hx1 : 1 ≤ x := le_of_lt hx.1
          have hx0 : 0 < x := lt_trans zero_lt_one hx.1
          rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : (-(σ : ℂ) - 2).re = -σ - 2 := by simp
          rw [hre]
          have hr1 : x ^ (-σ - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
          have hA : |A x| ≤ X₀ ^ 2 := (abs_A_le x hx1).trans (by nlinarith [hx.2])
          exact mul_le_of_le_one_right (abs_nonneg _) hr1 |>.trans hA
        · have hx1 : 1 ≤ x := le_of_lt hx.1
          have hx0 : 0 < x := lt_trans zero_lt_one hx.1
          rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : (-(σ : ℂ) - 2).re = -σ - 2 := by simp
          rw [hre]
          have hr1 : x ^ (-σ - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
          have hA : |A x| ≤ X₀ ^ 2 := (abs_A_le x hx1).trans (by nlinarith [hx.2])
          exact mul_le_of_le_one_right (abs_nonneg _) hr1 |>.trans hA
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)] at h2
      have h3 : (X₀ - 1) * X₀ ^ 2 ≤ X₀ ^ 3 := by nlinarith
      dsimp only [C]
      linarith
    have hre := Complex.abs_re_le_norm (∫ x in Set.Ioc (1 : ℝ) X₀,
      (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2))
    linarith [(abs_le.mp (hre.trans hnorm)).1]
  -- For σ in (1/2, 1): ((σ+1) * ζ(σ)).re * (I(σ) + E(σ)).re = (ζ(2σ) - 1).re
  -- Since I(σ).re ≥ 0 and E(σ).re ≥ -C and ζ(σ) < 0, we get (ζ(2σ) - 1).re ≤ -C * (σ+1) * ζ(σ).re
  have hupper : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 →
      (riemannZeta (2 * (σ : ℂ)) - 1).re ≤ -C * (σ + 1) * (riemannZeta (σ : ℂ)).re := by
    intro σ hσ0 hσ1
    have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne
    have hζne : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_Ioo (by linarith) hσ1
    have hIE := heq (σ : ℂ) (by simpa using hσ0) hne hζne
    have hI_nonneg : 0 ≤ (∫ x in Set.Ioi X₀,
        (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)).re := by
      have hreal : ∫ x : ℝ in Set.Ioi X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2) =
          Complex.ofReal (∫ x : ℝ in Set.Ioi X₀, A x * x ^ (-σ - 2)) := by
        rw [show Complex.ofReal (∫ x : ℝ in Set.Ioi X₀, A x * x ^ (-σ - 2)) =
          ∫ x : ℝ in Set.Ioi X₀, ((A x * x ^ (-σ - 2) : ℝ) : ℂ) from integral_ofReal.symm]
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 < x := lt_of_lt_of_le (by linarith) (le_of_lt hx)
        rw [one_mul, Complex.ofReal_mul,
          show (-(σ : ℂ) - 2) = ((-σ - 2 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hx0.le]
      rw [hreal, Complex.ofReal_re]
      exact setIntegral_nonneg measurableSet_Ioi fun x hx =>
        mul_nonneg (A_nonneg_of_S_nonneg hN₀ x (le_of_lt hx))
          (Real.rpow_nonneg (lt_of_lt_of_le (by linarith) (le_of_lt hx)).le _)
    have hsum_ge : -C ≤
        (∫ x in Set.Ioi X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)).re +
        (∫ x in Set.Ioc (1 : ℝ) X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)).re := by
      linarith [hE_ge σ hσ0 hσ1]
    have hζ_neg := riemannZeta_real_neg_on_Ioo (by linarith : 0 < σ) hσ1
    have hζ_re_neg : (riemannZeta (σ : ℂ)).re < 0 :=
      lt_of_le_of_lt hζ_neg.1 (div_neg_of_pos_of_neg (by linarith) (by linarith))
    have hmul_eq : riemannZeta (2 * (σ : ℂ)) - 1 =
        ((σ : ℂ) + 1) * riemannZeta (σ : ℂ) *
          ((∫ x in Set.Ioi X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)) +
           (∫ x in Set.Ioc (1 : ℝ) X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2))) := by
      have hsp1 : (σ : ℂ) + 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp at this; linarith
      have h1 : (∫ x in Set.Ioi X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)) +
          (∫ x in Set.Ioc (1 : ℝ) X₀, (((1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 2)) =
          (riemannZeta (2 * (σ : ℂ)) - 1) / (((σ : ℂ) + 1) * riemannZeta (σ : ℂ)) := by
        rw [hIE]; simp
      rw [h1]
      field_simp [hsp1, hζne]
    have hre_eq := congr_arg Complex.re hmul_eq
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, hζ_neg.2, mul_zero, sub_zero, zero_add,
      zero_mul] at hre_eq
    rw [hre_eq]
    have hfac_neg : (σ + 1) * (riemannZeta (σ : ℂ)).re < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hζ_re_neg
    nlinarith
  -- Now let σ -> (1/2)+: (2σ - 1) * (ζ(2σ) - 1).re -> 1, while (2σ - 1) * (-C*(σ+1)*ζ(σ).re) -> 0!
  have ht_pos : Tendsto (fun σ : ℝ => (2 * σ - 1) * (riemannZeta (2 * (σ : ℂ)) - 1).re)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 1) := by
    have hmap : Tendsto (fun σ : ℝ => (2 * (σ : ℂ))) (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous (fun σ : ℝ => 2 * (σ : ℂ)) := by fun_prop
        have ht : Tendsto (fun σ : ℝ => 2 * (σ : ℂ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (2 * ((1 / 2 : ℝ) : ℂ))) :=
          (hc.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        simpa using ht
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        intro h; have := congr_arg Complex.re h; simp at this; linarith [Set.mem_Ioi.mp hσ]
    have hres := riemannZeta_residue_one.comp hmap
    have hsub : Tendsto (fun σ : ℝ => (2 * (σ : ℂ) - 1) * (riemannZeta (2 * (σ : ℂ)) - 1))
        (𝓝[>] (1 / 2 : ℝ)) (𝓝 (1 - 0)) := by
      have h0 : Tendsto (fun σ : ℝ => (2 * (σ : ℂ) - 1)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
        have hc : Continuous (fun σ : ℝ => 2 * (σ : ℂ) - 1) := by fun_prop
        have ht : Tendsto (fun σ : ℝ => 2 * (σ : ℂ) - 1) (𝓝[>] (1 / 2 : ℝ))
            (𝓝 (2 * ((1 / 2 : ℝ) : ℂ) - 1)) :=
          (hc.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        simpa using ht
      simpa [mul_sub] using hres.sub h0
    have hre := (Complex.continuous_re.continuousAt.tendsto.comp hsub)
    simp only [sub_zero, Complex.one_re] at hre
    exact hre.congr fun σ => by simp [Function.comp_apply]
  have ht_zero : Tendsto (fun σ : ℝ => (2 * σ - 1) * (-C * (σ + 1) * (riemannZeta (σ : ℂ)).re))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun σ : ℝ => (2 * σ - 1) * (-C * (σ + 1) * (riemannZeta (σ : ℂ)).re))
        (1 / 2 : ℝ) := by
      have hζc : ContinuousAt (fun σ : ℝ => (riemannZeta (σ : ℂ)).re) (1 / 2 : ℝ) := by
        have h1 := (differentiableAt_riemannZeta (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num)).continuousAt
        exact Complex.continuous_re.continuousAt.comp (h1.comp Complex.continuous_ofReal.continuousAt)
      exact ((continuous_const.mul continuous_id).sub continuous_const).continuousAt.mul
        ((continuous_const.mul (continuous_id.add continuous_const)).continuousAt.mul hζc)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev_le : (fun σ : ℝ => (2 * σ - 1) * (riemannZeta (2 * (σ : ℂ)) - 1).re) ≤ᶠ[𝓝[>] (1 / 2 : ℝ)]
      (fun σ : ℝ => (2 * σ - 1) * (-C * (σ + 1) * (riemannZeta (σ : ℂ)).re)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with σ hσ0 hσ1
    have h2 : 0 < 2 * σ - 1 := by linarith [Set.mem_Ioi.mp hσ0]
    exact mul_le_mul_of_nonneg_left (hupper σ hσ0 hσ1) h2.le
  have hcontra := le_of_tendsto_of_tendsto ht_pos ht_zero hev_le
  linarith

/-! === Block 3: Elementary Gamma-shift ratio lemma, critical-line reality, and quadratic form -/

lemma log_sq_le_sub_sq {u : ℝ} (hu : 0 < u) :
    (Real.log u) ^ 2 ≤ (u - 1) ^ 2 + (u⁻¹ - 1) ^ 2 := by
  by_cases h1 : 1 ≤ u
  · have hlog0 : 0 ≤ Real.log u := Real.log_nonneg h1
    have hlog1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu
    nlinarith [sq_nonneg (u⁻¹ - 1)]
  · push Not at h1
    have hu1 : 1 ≤ u⁻¹ := (one_le_inv₀ hu).mpr h1.le
    have hlog0 : 0 ≤ Real.log u⁻¹ := Real.log_nonneg hu1
    have hlog1 : Real.log u⁻¹ ≤ u⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
    rw [Real.log_inv] at hlog0 hlog1
    nlinarith [sq_nonneg (u - 1)]

lemma abs_log_le_add_inv {u : ℝ} (hu : 0 < u) :
    |Real.log u| ≤ u + u⁻¹ := by
  have huinv : 0 < u⁻¹ := inv_pos.mpr hu
  by_cases h1 : 1 ≤ u
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith [Real.log_le_sub_one_of_pos hu]
  · push Not at h1
    have hlog_neg : Real.log u ≤ 0 := Real.log_nonpos hu.le h1.le
    rw [abs_of_nonpos hlog_neg, ← Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos huinv]

lemma norm_exp_I_sub_exp_I_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * I) - Complex.exp ((y : ℂ) * I)‖ ≤ |x - y| := by
  have hd : ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (I * Complex.exp ((u : ℂ) * I)) Set.univ u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) u :=
      (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const I
    have h2 := h1.cexp
    have hval : Complex.exp ((u : ℂ) * I) * (1 * I) = I * Complex.exp ((u : ℂ) * I) := by ring
    rw [hval] at h2
    exact h2.hasDerivWithinAt
  have hbnd : ∀ u ∈ (Set.univ : Set ℝ), ‖I * Complex.exp ((u : ℂ) * I)‖ ≤ (1 : ℝ) := by
    intro u _
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbnd convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

lemma norm_cpow_I_sub_cpow_I_le {t : ℝ} (ht : 0 < t) (b₁ b₂ : ℝ) :
    ‖(t : ℂ) ^ ((b₁ : ℂ) * I) - (t : ℂ) ^ ((b₂ : ℂ) * I)‖ ≤ |b₁ - b₂| * |Real.log t| := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hcp : ∀ b : ℝ, (t : ℂ) ^ ((b : ℂ) * I) = Complex.exp (((b * Real.log t : ℝ) : ℂ) * I) := by
    intro b
    rw [Complex.cpow_def_of_ne_zero htne, ← Complex.ofReal_log ht.le]
    congr 1; push_cast; ring
  rw [hcp b₁, hcp b₂]
  have h := norm_exp_I_sub_exp_I_le (b₁ * Real.log t) (b₂ * Real.log t)
  rwa [← sub_mul, abs_mul] at h

lemma real_Gamma_moment_up {a : ℝ} (ha : 2 < a) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2 =
      (1 / a) * Real.Gamma a := by
  have ha0 : 0 < a := by linarith
  have h0 := Real.GammaIntegral_convergent (s := a) ha0
  have h1 := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
  have h2 := Real.GammaIntegral_convergent (s := a + 2) (by linarith)
  have hexp : ∀ t ∈ Set.Ioi (0 : ℝ),
      Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2 =
        (1 / a ^ 2) * (Real.exp (-t) * t ^ (a + 2 - 1)) -
        (2 / a) * (Real.exp (-t) * t ^ (a + 1 - 1)) +
        (Real.exp (-t) * t ^ (a - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have ht1 : t ^ (a + 1 - 1) = t ^ (a - 1) * t := by
      rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
    have ht2 : t ^ (a + 2 - 1) = t ^ (a - 1) * t ^ 2 := by
      rw [show a + 2 - 1 = (a - 1) + (2 : ℕ) by norm_num; ring, Real.rpow_add ht0, Real.rpow_natCast]
    rw [ht1, ht2]
    field_simp [ha0.ne']
    ring
  have h12 : IntegrableOn (fun x : ℝ =>
      (1 / a ^ 2) * (Real.exp (-x) * x ^ (a + 2 - 1)) -
      (2 / a) * (Real.exp (-x) * x ^ (a + 1 - 1))) (Set.Ioi 0) :=
    (h2.const_mul (1 / a ^ 2)).sub (h1.const_mul (2 / a))
  rw [setIntegral_congr_fun measurableSet_Ioi hexp,
    integral_add h12 h0,
    integral_sub (h2.const_mul (1 / a ^ 2)) (h1.const_mul (2 / a)),
    integral_const_mul, integral_const_mul,
    ← Real.Gamma_eq_integral (by linarith : 0 < a + 2),
    ← Real.Gamma_eq_integral (by linarith : 0 < a + 1),
    ← Real.Gamma_eq_integral ha0,
    show a + 2 = (a + 1) + 1 by ring,
    Real.Gamma_add_one (by linarith : a + 1 ≠ 0),
    Real.Gamma_add_one ha0.ne']
  field_simp [ha0.ne']
  ring

lemma real_Gamma_moment_down {a : ℝ} (ha : 2 < a) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2 =
      ((a + 2) / ((a - 1) * (a - 2))) * Real.Gamma a := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have ha2 : 0 < a - 2 := by linarith
  have h0 := Real.GammaIntegral_convergent (s := a) ha0
  have hm1 := Real.GammaIntegral_convergent (s := a - 1) ha1
  have hm2 := Real.GammaIntegral_convergent (s := a - 2) ha2
  have hexp : ∀ t ∈ Set.Ioi (0 : ℝ),
      Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2 =
        a ^ 2 * (Real.exp (-t) * t ^ (a - 2 - 1)) -
        (2 * a) * (Real.exp (-t) * t ^ (a - 1 - 1)) +
        (Real.exp (-t) * t ^ (a - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have htm1 : t ^ (a - 1) = t ^ (a - 1 - 1) * t := by
      conv_lhs => rw [show a - 1 = (a - 1 - 1) + 1 by ring]
      rw [Real.rpow_add ht0, Real.rpow_one]
    have htm2 : t ^ (a - 1) = t ^ (a - 2 - 1) * t ^ 2 := by
      conv_lhs => rw [show a - 1 = (a - 2 - 1) + (2 : ℕ) by norm_num; ring]
      rw [Real.rpow_add ht0, Real.rpow_natCast]
    have h1 : t ^ (a - 1) * (a / t) ^ 2 = a ^ 2 * t ^ (a - 2 - 1) := by
      rw [htm2]; field_simp [ht0.ne']
    have h2 : t ^ (a - 1) * (2 * (a / t)) = 2 * a * t ^ (a - 1 - 1) := by
      rw [htm1]; field_simp [ht0.ne']
    calc Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2
        = Real.exp (-t) * (t ^ (a - 1) * (a / t) ^ 2 - t ^ (a - 1) * (2 * (a / t)) + t ^ (a - 1)) := by ring
      _ = Real.exp (-t) * (a ^ 2 * t ^ (a - 2 - 1) - 2 * a * t ^ (a - 1 - 1) + t ^ (a - 1)) := by
          rw [h1, h2]
      _ = _ := by ring
  have h12 : IntegrableOn (fun x : ℝ =>
      a ^ 2 * (Real.exp (-x) * x ^ (a - 2 - 1)) -
      (2 * a) * (Real.exp (-x) * x ^ (a - 1 - 1))) (Set.Ioi 0) :=
    (hm2.const_mul (a ^ 2)).sub (hm1.const_mul (2 * a))
  rw [setIntegral_congr_fun measurableSet_Ioi hexp,
    integral_add h12 h0,
    integral_sub (hm2.const_mul (a ^ 2)) (hm1.const_mul (2 * a)),
    integral_const_mul, integral_const_mul,
    ← Real.Gamma_eq_integral ha2,
    ← Real.Gamma_eq_integral ha1,
    ← Real.Gamma_eq_integral ha0]
  have hg1 : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    have h := Real.Gamma_add_one ha1.ne'
    rwa [sub_add_cancel] at h
  have hg2 : Real.Gamma (a - 1) = (a - 2) * Real.Gamma (a - 2) := by
    have h := Real.Gamma_add_one ha2.ne'
    rwa [show a - 2 + 1 = a - 1 by ring] at h
  have hga1 : Real.Gamma (a - 1) = Real.Gamma a / (a - 1) := by
    rw [hg1, mul_div_cancel_left₀ _ ha1.ne']
  have hga2 : Real.Gamma (a - 2) = Real.Gamma a / ((a - 1) * (a - 2)) := by
    rw [hg1, hg2]; field_simp [ha1.ne', ha2.ne']
  rw [hga1, hga2]
  field_simp [ha1.ne', ha2.ne']
  ring

lemma norm_Gamma_shift_lower {b : ℝ} (hb : |b| ≤ 21) :
    (1 / 4 : ℝ) * Real.Gamma (4001 / 4) ≤ ‖Complex.Gamma ((4001 / 4 : ℂ) + (b : ℂ) * I)‖ := by
  set a : ℝ := 4001 / 4
  have ha : 2 < a := by dsimp only [a]; norm_num
  have ha0 : 0 < a := by linarith
  have hre_pos : 0 < ((a : ℂ) + (b : ℂ) * I).re := by simp [ha0]
  have ha_c : (4001 / 4 : ℂ) = (a : ℂ) := by dsimp only [a]; push_cast; rfl
  rw [ha_c]
  have hnorm_eq : ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * I)‖ =
      ‖(a : ℂ) ^ (-(b : ℂ) * I) * Complex.Gamma ((a : ℂ) + (b : ℂ) * I)‖ := by
    rw [norm_mul]
    have h1 : ‖(a : ℂ) ^ (-(b : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ha0]
      simp
    rw [h1, one_mul]
  rw [hnorm_eq]
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [Complex.Gamma_eq_integral hre_pos, Complex.GammaIntegral, ← integral_const_mul]
  have hint_c : IntegrableOn (fun t : ℝ => (a : ℂ) ^ (-(b : ℂ) * I) *
      (((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((a : ℂ) + (b : ℂ) * I - 1))) (Set.Ioi 0) :=
    (Complex.GammaIntegral_convergent hre_pos).const_mul _
  have hre_int :
      ((∫ t : ℝ in Set.Ioi 0, (a : ℂ) ^ (-(b : ℂ) * I) *
        (((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((a : ℂ) + (b : ℂ) * I - 1))).re) =
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ (a - 1) * Real.cos (b * Real.log (t / a)) := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_c]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hsplit : (t : ℂ) ^ ((a : ℂ) + (b : ℂ) * I - 1) =
        ((t ^ (a - 1) : ℝ) : ℂ) * (t : ℂ) ^ ((b : ℂ) * I) := by
      rw [show (a : ℂ) + (b : ℂ) * I - 1 = (((a - 1 : ℝ) : ℂ)) + (b : ℂ) * I by push_cast; ring,
        Complex.cpow_add _ _ htne, ← Complex.ofReal_cpow ht0.le]
    have hphase : (a : ℂ) ^ (-(b : ℂ) * I) * (t : ℂ) ^ ((b : ℂ) * I) =
        Complex.exp (((b * Real.log (t / a) : ℝ) : ℂ) * I) := by
      rw [Complex.cpow_def_of_ne_zero hane, Complex.cpow_def_of_ne_zero htne, ← Complex.exp_add,
        ← Complex.ofReal_log ha0.le, ← Complex.ofReal_log ht0.le, Real.log_div ht0.ne' ha0.ne']
      congr 1; push_cast; ring
    have hrew : (a : ℂ) ^ (-(b : ℂ) * I) *
        (((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((a : ℂ) + (b : ℂ) * I - 1)) =
        (((Real.exp (-t) * t ^ (a - 1) : ℝ) : ℂ)) *
          Complex.exp (((b * Real.log (t / a) : ℝ) : ℂ) * I) := by
      rw [hsplit, Complex.ofReal_mul]
      linear_combination (Real.exp (-t) : ℂ) * ((t ^ (a - 1) : ℝ) : ℂ) * hphase
    rw [Complex.reCLM_apply, hrew, Complex.exp_ofReal_mul_I, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre_int]
  have hlow_int : IntegrableOn (fun t : ℝ =>
      Real.exp (-t) * t ^ (a - 1) -
        (b ^ 2 / 2) * (Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2 +
          Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2)) (Set.Ioi 0) := by
    have h0 := Real.GammaIntegral_convergent (s := a) ha0
    have h1 := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
    have h2 := Real.GammaIntegral_convergent (s := a + 2) (by linarith)
    have hm1 := Real.GammaIntegral_convergent (s := a - 1) (by linarith)
    have hm2 := Real.GammaIntegral_convergent (s := a - 2) (by linarith)
    have hup : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2) (Set.Ioi 0) := by
      refine IntegrableOn.congr_fun
        (((h2.const_mul (1 / a ^ 2)).sub (h1.const_mul (2 / a))).add h0) ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have ht1 : t ^ (a + 1 - 1) = t ^ (a - 1) * t := by
        rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
      have ht2 : t ^ (a + 2 - 1) = t ^ (a - 1) * t ^ 2 := by
        rw [show a + 2 - 1 = (a - 1) + ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add ht0, Real.rpow_natCast]
      dsimp only [Pi.add_apply, Pi.sub_apply]
      rw [ht1, ht2]; field_simp [ha0.ne']; ring
    have hdn : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2) (Set.Ioi 0) := by
      refine IntegrableOn.congr_fun
        (((hm2.const_mul (a ^ 2)).sub (hm1.const_mul (2 * a))).add h0) ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have htm1 : t ^ (a - 1) = t ^ (a - 1 - 1) * t := by
        calc t ^ (a - 1) = t ^ ((a - 1 - 1) + 1) := by congr 1; ring
          _ = t ^ (a - 1 - 1) * t := by rw [Real.rpow_add ht0, Real.rpow_one]
      have htm2 : t ^ (a - 1) = t ^ (a - 2 - 1) * t ^ 2 := by
        calc t ^ (a - 1) = t ^ ((a - 2 - 1) + ((2 : ℕ) : ℝ)) := by congr 1; push_cast; ring
          _ = t ^ (a - 2 - 1) * t ^ 2 := by rw [Real.rpow_add ht0, Real.rpow_natCast]
      dsimp only [Pi.add_apply, Pi.sub_apply]
      have h1' : t ^ (a - 1) * (a / t) ^ 2 = a ^ 2 * t ^ (a - 2 - 1) := by
        rw [htm2]; field_simp [ht0.ne']
      have h2' : t ^ (a - 1) * (2 * (a / t)) = 2 * a * t ^ (a - 1 - 1) := by
        rw [htm1]; field_simp [ht0.ne']
      calc a ^ 2 * (Real.exp (-t) * t ^ (a - 2 - 1)) -
            2 * a * (Real.exp (-t) * t ^ (a - 1 - 1)) + Real.exp (-t) * t ^ (a - 1)
          = Real.exp (-t) * (a ^ 2 * t ^ (a - 2 - 1) - 2 * a * t ^ (a - 1 - 1) + t ^ (a - 1)) := by ring
        _ = Real.exp (-t) * (t ^ (a - 1) * (a / t) ^ 2 - t ^ (a - 1) * (2 * (a / t)) + t ^ (a - 1)) := by
            rw [← h1', ← h2']
        _ = _ := by ring
    exact h0.sub ((hup.add hdn).const_mul (b ^ 2 / 2))
  have hcos_int : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1) * Real.cos (b * Real.log (t / a)))
      (Set.Ioi 0) := by
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) * t ^ (a - 1) * Real.cos (b * Real.log (t / a)))
        (volume.restrict (Set.Ioi 0)) :=
      (Real.GammaIntegral_convergent ha0).aestronglyMeasurable.mul
        (Real.continuous_cos.measurable.comp (measurable_const.mul
          (Real.measurable_log.comp (measurable_id.div_const a)))).aestronglyMeasurable
    refine (Real.GammaIntegral_convergent ha0).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _))]
    exact mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)) (Real.abs_cos_le_one _)
  have hmono : ∫ t : ℝ in Set.Ioi 0,
      (Real.exp (-t) * t ^ (a - 1) -
        (b ^ 2 / 2) * (Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2 +
          Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2)) ≤
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ (a - 1) * Real.cos (b * Real.log (t / a)) := by
    refine setIntegral_mono_on hlow_int hcos_int measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hu : 0 < t / a := div_pos ht0 ha0
    have hcos := Real.one_sub_sq_div_two_le_cos (x := b * Real.log (t / a))
    have hlog := log_sq_le_sub_sq hu
    have hinv : (t / a)⁻¹ = a / t := inv_div t a
    rw [hinv] at hlog
    have hfac : 0 ≤ Real.exp (-t) * t ^ (a - 1) := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
    have hbound : 1 - (b ^ 2 / 2) * ((t / a - 1) ^ 2 + (a / t - 1) ^ 2) ≤ Real.cos (b * Real.log (t / a)) := by
      have h1 : (b * Real.log (t / a)) ^ 2 / 2 ≤ (b ^ 2 / 2) * ((t / a - 1) ^ 2 + (a / t - 1) ^ 2) := by
        rw [mul_pow]; nlinarith [sq_nonneg b]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hbound hfac
    linarith
  have heval : ∫ t : ℝ in Set.Ioi 0,
      (Real.exp (-t) * t ^ (a - 1) -
        (b ^ 2 / 2) * (Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2 +
          Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2)) =
      (1 - (b ^ 2 / 2) * (1 / a + (a + 2) / ((a - 1) * (a - 2)))) * Real.Gamma a := by
    have hup_int : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2) (Set.Ioi 0) := by
      have h0 := Real.GammaIntegral_convergent (s := a) ha0
      have h1 := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
      have h2 := Real.GammaIntegral_convergent (s := a + 2) (by linarith)
      refine IntegrableOn.congr_fun
        (((h2.const_mul (1 / a ^ 2)).sub (h1.const_mul (2 / a))).add h0) ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have ht1 : t ^ (a + 1 - 1) = t ^ (a - 1) * t := by
        rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
      have ht2 : t ^ (a + 2 - 1) = t ^ (a - 1) * t ^ 2 := by
        rw [show a + 2 - 1 = (a - 1) + ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add ht0, Real.rpow_natCast]
      dsimp only [Pi.add_apply, Pi.sub_apply]
      rw [ht1, ht2]; field_simp [ha0.ne']; ring
    have hdn_int : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2) (Set.Ioi 0) := by
      have h0 := Real.GammaIntegral_convergent (s := a) ha0
      have hm1 := Real.GammaIntegral_convergent (s := a - 1) (by linarith)
      have hm2 := Real.GammaIntegral_convergent (s := a - 2) (by linarith)
      refine IntegrableOn.congr_fun
        (((hm2.const_mul (a ^ 2)).sub (hm1.const_mul (2 * a))).add h0) ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have htm1 : t ^ (a - 1) = t ^ (a - 1 - 1) * t := by
        calc t ^ (a - 1) = t ^ ((a - 1 - 1) + 1) := by congr 1; ring
          _ = t ^ (a - 1 - 1) * t := by rw [Real.rpow_add ht0, Real.rpow_one]
      have htm2 : t ^ (a - 1) = t ^ (a - 2 - 1) * t ^ 2 := by
        calc t ^ (a - 1) = t ^ ((a - 2 - 1) + ((2 : ℕ) : ℝ)) := by congr 1; push_cast; ring
          _ = t ^ (a - 2 - 1) * t ^ 2 := by rw [Real.rpow_add ht0, Real.rpow_natCast]
      dsimp only [Pi.add_apply, Pi.sub_apply]
      have h1' : t ^ (a - 1) * (a / t) ^ 2 = a ^ 2 * t ^ (a - 2 - 1) := by
        rw [htm2]; field_simp [ht0.ne']
      have h2' : t ^ (a - 1) * (2 * (a / t)) = 2 * a * t ^ (a - 1 - 1) := by
        rw [htm1]; field_simp [ht0.ne']
      calc a ^ 2 * (Real.exp (-t) * t ^ (a - 2 - 1)) -
            2 * a * (Real.exp (-t) * t ^ (a - 1 - 1)) + Real.exp (-t) * t ^ (a - 1)
          = Real.exp (-t) * (a ^ 2 * t ^ (a - 2 - 1) - 2 * a * t ^ (a - 1 - 1) + t ^ (a - 1)) := by ring
        _ = Real.exp (-t) * (t ^ (a - 1) * (a / t) ^ 2 - t ^ (a - 1) * (2 * (a / t)) + t ^ (a - 1)) := by
            rw [← h1', ← h2']
        _ = _ := by ring
    have hsum_int : IntegrableOn (fun t : ℝ =>
        Real.exp (-t) * t ^ (a - 1) * (t / a - 1) ^ 2 +
          Real.exp (-t) * t ^ (a - 1) * (a / t - 1) ^ 2) (Set.Ioi 0) := hup_int.add hdn_int
    rw [integral_sub (Real.GammaIntegral_convergent ha0) (hsum_int.const_mul (b ^ 2 / 2)),
      integral_const_mul, integral_add hup_int hdn_int,
      ← Real.Gamma_eq_integral ha0, real_Gamma_moment_up ha, real_Gamma_moment_down ha]
    ring
  rw [heval] at hmono
  have hGamma_pos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha0
  have hb2 : b ^ 2 ≤ 441 := by nlinarith [abs_le.mp hb]
  have hcoef : (1 / 4 : ℝ) ≤ 1 - (b ^ 2 / 2) * (1 / a + (a + 2) / ((a - 1) * (a - 2))) := by
    have hnum : (1 / a + (a + 2) / ((a - 1) * (a - 2))) ≤ 3 / 1000 := by
      dsimp only [a]; norm_num
    have hpos : 0 ≤ 1 / a + (a + 2) / ((a - 1) * (a - 2)) := by
      dsimp only [a]; norm_num
    nlinarith
  nlinarith

lemma norm_Gamma_shift_diff {b₁ b₂ : ℝ} (hd : |b₁ - b₂| ≤ 5 / 10 ^ 7) :
    ‖Complex.Gamma ((4001 / 4 : ℂ) + (b₁ : ℂ) * I) -
      Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I)‖ ≤
      (4001 / 4000000 : ℝ) * Real.Gamma (4001 / 4) := by
  set a : ℝ := 4001 / 4
  have ha0 : 0 < a := by dsimp only [a]; norm_num
  have hre1 : 0 < ((a : ℂ) + (b₁ : ℂ) * I).re := by simp [ha0]
  have hre2 : 0 < ((a : ℂ) + (b₂ : ℂ) * I).re := by simp [ha0]
  have ha_c : (4001 / 4 : ℂ) = (a : ℂ) := by dsimp only [a]; push_cast; rfl
  rw [ha_c]
  rw [Complex.Gamma_eq_integral hre1, Complex.Gamma_eq_integral hre2, Complex.GammaIntegral,
    Complex.GammaIntegral,
    ← integral_sub (Complex.GammaIntegral_convergent hre1) (Complex.GammaIntegral_convergent hre2)]
  have h1 := norm_integral_le_integral_norm
    (f := fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((a : ℂ) + (b₁ : ℂ) * I - 1) -
      ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((a : ℂ) + (b₂ : ℂ) * I - 1))
    (μ := volume.restrict (Set.Ioi 0))
  have hup := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
  have hdn := Real.GammaIntegral_convergent (s := a - 1) (by dsimp only [a]; norm_num)
  have h2 : ∫ t : ℝ in Set.Ioi 0,
      ‖((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((a : ℂ) + (b₁ : ℂ) * I - 1) -
        ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((a : ℂ) + (b₂ : ℂ) * I - 1)‖ ≤
      ∫ t : ℝ in Set.Ioi 0,
        |b₁ - b₂| * (Real.exp (-t) * t ^ (a + 1 - 1) + Real.exp (-t) * t ^ (a - 1 - 1)) := by
    refine setIntegral_mono_on
      ((Complex.GammaIntegral_convergent hre1).sub (Complex.GammaIntegral_convergent hre2)).norm
      ((hup.add hdn).const_mul |b₁ - b₂|) measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hspl : ∀ b : ℝ, (t : ℂ) ^ ((a : ℂ) + (b : ℂ) * I - 1) =
        ((t ^ (a - 1) : ℝ) : ℂ) * (t : ℂ) ^ ((b : ℂ) * I) := fun b => by
      rw [show (a : ℂ) + (b : ℂ) * I - 1 = ((a - 1 : ℝ) : ℂ) + (b : ℂ) * I by push_cast; ring,
        Complex.cpow_add _ _ htne, ← Complex.ofReal_cpow ht0.le]
    rw [hspl b₁, hspl b₂, ← mul_sub, ← mul_sub, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    have hcp := (norm_cpow_I_sub_cpow_I_le ht0 b₁ b₂).trans
      (mul_le_mul_of_nonneg_left (abs_log_le_add_inv ht0) (abs_nonneg _))
    have ht1 : t ^ (a - 1) * t = t ^ (a + 1 - 1) := by
      rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
    have htm1 : t ^ (a - 1) * t⁻¹ = t ^ (a - 1 - 1) := by
      rw [show a - 1 - 1 = (a - 1) + (-1) by ring, Real.rpow_add ht0, Real.rpow_neg_one]
    have hfac : 0 ≤ Real.exp (-t) * t ^ (a - 1) := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
    calc Real.exp (-t) * (t ^ (a - 1) * ‖(t : ℂ) ^ ((b₁ : ℂ) * I) - (t : ℂ) ^ ((b₂ : ℂ) * I)‖)
        = (Real.exp (-t) * t ^ (a - 1)) * ‖(t : ℂ) ^ ((b₁ : ℂ) * I) - (t : ℂ) ^ ((b₂ : ℂ) * I)‖ := by ring
      _ ≤ (Real.exp (-t) * t ^ (a - 1)) * (|b₁ - b₂| * (t + t⁻¹)) :=
          mul_le_mul_of_nonneg_left hcp hfac
      _ = |b₁ - b₂| * (Real.exp (-t) * (t ^ (a - 1) * t) + Real.exp (-t) * (t ^ (a - 1) * t⁻¹)) := by ring
      _ = _ := by rw [ht1, htm1]
  rw [integral_const_mul, integral_add hup hdn,
    ← Real.Gamma_eq_integral (by linarith : 0 < a + 1),
    ← Real.Gamma_eq_integral (by dsimp only [a]; norm_num : 0 < a - 1)] at h2
  have hg_up : Real.Gamma (a + 1) = a * Real.Gamma a := Real.Gamma_add_one ha0.ne'
  have hg_dn : Real.Gamma (a - 1) = Real.Gamma a / (a - 1) := by
    have h := Real.Gamma_add_one (show a - 1 ≠ 0 by dsimp only [a]; norm_num)
    rw [sub_add_cancel] at h
    rw [h, mul_div_cancel_left₀ _ (show a - 1 ≠ 0 by dsimp only [a]; norm_num)]
  rw [hg_up, hg_dn] at h2
  have hGamma_pos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha0
  have hsum_le : a * Real.Gamma a + Real.Gamma a / (a - 1) ≤ 2 * a * Real.Gamma a := by
    have h1' : 1 / (a - 1) ≤ a := by dsimp only [a]; norm_num
    nlinarith [show Real.Gamma a / (a - 1) = (1 / (a - 1)) * Real.Gamma a by ring]
  have hbound : |b₁ - b₂| * (a * Real.Gamma a + Real.Gamma a / (a - 1)) ≤
      (4001 / 4000000 : ℝ) * Real.Gamma a := by
    calc |b₁ - b₂| * (a * Real.Gamma a + Real.Gamma a / (a - 1))
        ≤ (5 / 10 ^ 7) * (2 * a * Real.Gamma a) :=
          mul_le_mul hd hsum_le (by positivity) (by norm_num)
      _ = (4001 / 4000000 : ℝ) * Real.Gamma a := by dsimp only [a]; ring
  linarith

lemma Gamma_add_nat (s : ℂ) (n : ℕ) (h : ∀ j < n, s + (j : ℂ) ≠ 0) :
    Complex.Gamma (s + (n : ℂ)) = (∏ j ∈ Finset.range n, (s + (j : ℂ))) * Complex.Gamma s := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (h k (Nat.lt_succ_self k)),
      ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), Finset.prod_range_succ]
    ring

lemma norm_prod_sub_one_le {n : ℕ} (z : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hz : ∀ j < n, ‖z j - 1‖ ≤ r) :
    ‖(∏ j ∈ Finset.range n, z j) - 1‖ ≤ (1 + r) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, pow_succ]
    set P := ∏ j ∈ Finset.range k, z j
    have hP : ‖P - 1‖ ≤ (1 + r) ^ k - 1 := ih (fun j hj => hz j (Nat.lt_succ_of_lt hj))
    have hzk : ‖z k - 1‖ ≤ r := hz k (Nat.lt_succ_self k)
    have hPnorm : ‖P‖ ≤ (1 + r) ^ k := by
      calc ‖P‖ = ‖(P - 1) + 1‖ := by ring_nf
        _ ≤ ‖P - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ ((1 + r) ^ k - 1) + 1 := by rw [norm_one]; linarith
        _ = (1 + r) ^ k := by ring
    calc ‖P * z k - 1‖ = ‖P * (z k - 1) + (P - 1)‖ := by ring_nf
      _ ≤ ‖P * (z k - 1)‖ + ‖P - 1‖ := norm_add_le _ _
      _ = ‖P‖ * ‖z k - 1‖ + ‖P - 1‖ := by rw [norm_mul]
      _ ≤ (1 + r) ^ k * r + ((1 + r) ^ k - 1) := by
          gcongr
      _ = (1 + r) ^ k * (1 + r) - 1 := by ring

lemma one_add_two_e6_pow_le : ∀ k : ℕ, k ≤ 1000 →
    (1 + 2 / (10 ^ 6 : ℝ)) ^ k ≤ 1 + (3 * (k : ℝ)) / 10 ^ 6 := by
  intro k
  induction k with
  | zero => intro _; norm_num
  | succ m ih =>
    intro hm
    have hm' : m ≤ 1000 := by omega
    have h1 := ih hm'
    have hmR : (m : ℝ) ≤ 1000 := by exact_mod_cast hm'
    rw [pow_succ, Nat.cast_succ]
    calc (1 + 2 / (10 ^ 6 : ℝ)) ^ m * (1 + 2 / (10 ^ 6 : ℝ))
        ≤ (1 + 3 * (m : ℝ) / 10 ^ 6) * (1 + 2 / (10 ^ 6 : ℝ)) := by nlinarith
      _ ≤ 1 + 3 * ((m : ℝ) + 1) / 10 ^ 6 := by nlinarith

/-- Elementary `M = 1000` Gamma-shift ratio bound (`<1>5<2>1`):
    `|Gammaℝ(1/2 + i*t₁) / Gammaℝ(1/2 + i*t₂) - 1| ≤ 1/100`
    whenever `|t₁|, |t₂| ≤ 42` and `|t₁ - t₂| ≤ 10⁻⁶`. -/
lemma norm_GammaR_ratio_sub_one_le {t₁ t₂ : ℝ} (ht₁ : |t₁| ≤ 42) (ht₂ : |t₂| ≤ 42)
    (hd : |t₁ - t₂| ≤ 1 / 10 ^ 6) :
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t₁ : ℂ) * I) /
      Complex.Gammaℝ ((1 / 2 : ℂ) + (t₂ : ℂ) * I) - 1‖ ≤ 1 / 100 := by
  set b₁ : ℝ := t₁ / 2
  set b₂ : ℝ := t₂ / 2
  have hb₁ : |b₁| ≤ 21 := by dsimp only [b₁]; rw [abs_div, abs_two]; linarith
  have hb₂ : |b₂| ≤ 21 := by dsimp only [b₂]; rw [abs_div, abs_two]; linarith
  have hbd : |b₁ - b₂| ≤ 5 / 10 ^ 7 := by
    dsimp only [b₁, b₂]
    rw [← sub_div, abs_div, abs_two]
    linarith
  have hhalf : ∀ t : ℝ, ((1 / 2 : ℂ) + (t : ℂ) * I) / 2 = (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I := fun t => by
    push_cast; ring
  have hne_j : ∀ (b : ℝ) (j : ℕ), (1 / 4 : ℂ) + (b : ℂ) * I + (j : ℂ) ≠ 0 := fun b j h => by
    have := congr_arg Complex.re h
    simp at this
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  -- Shift by 1000 using Gamma_add_nat
  have hG1 := Gamma_add_nat ((1 / 4 : ℂ) + (b₁ : ℂ) * I) 1000 (fun j _ => hne_j b₁ j)
  have hG2 := Gamma_add_nat ((1 / 4 : ℂ) + (b₂ : ℂ) * I) 1000 (fun j _ => hne_j b₂ j)
  have hshift_eq : ∀ b : ℝ, (1 / 4 : ℂ) + (b : ℂ) * I + (1000 : ℕ) = (4001 / 4 : ℂ) + (b : ℂ) * I := fun b => by
    push_cast; ring
  rw [hshift_eq b₁] at hG1
  rw [hshift_eq b₂] at hG2
  have hlow := norm_Gamma_shift_lower hb₂
  have hG2_shift_ne : Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    have hpos : 0 < Real.Gamma (4001 / 4) := Real.Gamma_pos_of_pos (by norm_num)
    linarith
  have hP1_ne : (∏ j ∈ Finset.range 1000, ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hne_j b₁ j
  have hP2_ne : (∏ j ∈ Finset.range 1000, ((1 / 4 : ℂ) + (b₂ : ℂ) * I + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hne_j b₂ j
  have hG2_ne : Complex.Gamma ((1 / 4 : ℂ) + (b₂ : ℂ) * I) ≠ 0 := by
    intro h; rw [h, mul_zero] at hG2; exact hG2_shift_ne hG2
  -- Factor the ratio Gammaℝ(1/2 + t₁ I) / Gammaℝ(1/2 + t₂ I) = F_pi * F_prod * F_tail
  let Fpi : ℂ := (Real.pi : ℂ) ^ (-((b₁ - b₂ : ℝ) : ℂ) * I)
  let Fprod : ℂ := ∏ j ∈ Finset.range 1000,
    (((1 / 4 : ℂ) + (b₂ : ℂ) * I + (j : ℂ)) / ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)))
  let Ftail : ℂ := Complex.Gamma ((4001 / 4 : ℂ) + (b₁ : ℂ) * I) /
    Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I)
  have hfactor :
      Complex.Gammaℝ ((1 / 2 : ℂ) + (t₁ : ℂ) * I) / Complex.Gammaℝ ((1 / 2 : ℂ) + (t₂ : ℂ) * I) =
        Fpi * Fprod * Ftail := by
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, hhalf t₁, hhalf t₂]
    have hpi_rat : (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + (t₁ : ℂ) * I) / 2) /
        (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + (t₂ : ℂ) * I) / 2) = Fpi := by
      have hpine : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      rw [← Complex.cpow_sub _ _ hpine]
      dsimp only [Fpi, b₁, b₂]
      congr 1; push_cast; ring
    have hgam_rat : Complex.Gamma ((1 / 4 : ℂ) + (b₁ : ℂ) * I) /
        Complex.Gamma ((1 / 4 : ℂ) + (b₂ : ℂ) * I) = Fprod * Ftail := by
      dsimp only [Fprod, Ftail]
      rw [Finset.prod_div_distrib]
      have h1 : Complex.Gamma ((1 / 4 : ℂ) + (b₁ : ℂ) * I) =
          Complex.Gamma ((4001 / 4 : ℂ) + (b₁ : ℂ) * I) /
            ∏ j ∈ Finset.range 1000, ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)) :=
        eq_div_of_mul_eq hP1_ne (mul_comm (∏ j ∈ Finset.range 1000, ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ))) _ ▸ hG1.symm)
      have h2 : Complex.Gamma ((1 / 4 : ℂ) + (b₂ : ℂ) * I) =
          Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I) /
            ∏ j ∈ Finset.range 1000, ((1 / 4 : ℂ) + (b₂ : ℂ) * I + (j : ℂ)) :=
        eq_div_of_mul_eq hP2_ne (mul_comm (∏ j ∈ Finset.range 1000, ((1 / 4 : ℂ) + (b₂ : ℂ) * I + (j : ℂ))) _ ▸ hG2.symm)
      rw [h1, h2]
      field_simp [hP1_ne, hP2_ne, hG2_shift_ne]
    rw [mul_div_mul_comm, hpi_rat, hgam_rat, mul_assoc]
  rw [hfactor]
  -- Bound each of |Fpi - 1|, |Fprod - 1|, |Ftail - 1|
  have hFpi : ‖Fpi - 1‖ ≤ 1 / 100000 := by
    have h1 : Fpi - 1 = (Real.pi : ℂ) ^ ((-(b₁ - b₂) : ℝ) * I) - (Real.pi : ℂ) ^ ((0 : ℝ) * I) := by
      simp [Fpi]
    rw [h1]
    have h2 := norm_cpow_I_sub_cpow_I_le Real.pi_pos (-(b₁ - b₂)) 0
    have hlogpi : |Real.log Real.pi| ≤ 3 := by
      rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi]))]
      linarith [Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_lt_four]
    have h3 : |-(b₁ - b₂) - 0| * |Real.log Real.pi| ≤ (5 / 10 ^ 7) * 3 := by
      rw [sub_zero, abs_neg]
      exact mul_le_mul hbd hlogpi (abs_nonneg _) (by norm_num)
    linarith
  have hFprod : ‖Fprod - 1‖ ≤ 3 / 1000 := by
    have hfac : ∀ j : ℕ, j < 1000 →
        ‖((1 / 4 : ℂ) + (b₂ : ℂ) * I + (j : ℂ)) / ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)) - 1‖ ≤
          2 / (10 ^ 6 : ℝ) := by
      intro j _
      have hne := hne_j b₁ j
      have hsub : ((1 / 4 : ℂ) + (b₂ : ℂ) * I + (j : ℂ)) / ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)) - 1 =
          (((b₂ - b₁ : ℝ) : ℂ) * I) / ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)) := by
        rw [div_sub_one hne]; push_cast; ring
      rw [hsub, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        abs_sub_comm]
      have hden : (1 / 4 : ℝ) ≤ ‖(1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)‖ := by
        have hre : ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)).re = 1 / 4 + (j : ℝ) := by simp
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        calc (1 / 4 : ℝ) ≤ 1 / 4 + (j : ℝ) := by linarith
          _ = ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)).re := hre.symm
          _ ≤ ‖(1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)‖ := Complex.re_le_norm _
      calc |b₁ - b₂| / ‖(1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)‖
          ≤ (5 / 10 ^ 7) / (1 / 4) := div_le_div₀ (by norm_num) hbd (by norm_num) hden
        _ = 2 / (10 ^ 6 : ℝ) := by norm_num
    have hp := norm_prod_sub_one_le
      (fun j : ℕ => ((1 / 4 : ℂ) + (b₂ : ℂ) * I + (j : ℂ)) / ((1 / 4 : ℂ) + (b₁ : ℂ) * I + (j : ℂ)))
      (by norm_num) hfac
    have hpow := one_add_two_e6_pow_le 1000 le_rfl
    have hpow' : (1 + 2 / (10 ^ 6 : ℝ)) ^ 1000 - 1 ≤ 3 / 1000 :=
      sub_le_iff_le_add.mpr (hpow.trans (by norm_num))
    dsimp only [Fprod]
    exact hp.trans hpow'
  have hFtail : ‖Ftail - 1‖ ≤ 41 / 10000 := by
    have hsub : Ftail - 1 = (Complex.Gamma ((4001 / 4 : ℂ) + (b₁ : ℂ) * I) -
        Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I)) /
        Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I) := by
      dsimp only [Ftail]; exact div_sub_one hG2_shift_ne
    rw [hsub, norm_div]
    have hdiff := norm_Gamma_shift_diff hbd
    have hGpos : 0 < Real.Gamma (4001 / 4) := Real.Gamma_pos_of_pos (by norm_num)
    calc ‖Complex.Gamma ((4001 / 4 : ℂ) + (b₁ : ℂ) * I) - Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I)‖ /
          ‖Complex.Gamma ((4001 / 4 : ℂ) + (b₂ : ℂ) * I)‖
        ≤ ((4001 / 4000000 : ℝ) * Real.Gamma (4001 / 4)) / ((1 / 4 : ℝ) * Real.Gamma (4001 / 4)) :=
          div_le_div₀ (by positivity) hdiff (by positivity) hlow
      _ = 4001 / 1000000 := by field_simp [hGpos.ne']; norm_num
      _ ≤ 41 / 10000 := by norm_num
  have hnorm_prod : ‖Fpi * Fprod - 1‖ ≤ 4 / 1000 := by
    have hFpi_norm : ‖Fpi‖ ≤ 1 + 1 / 100000 := by
      calc ‖Fpi‖ = ‖(Fpi - 1) + 1‖ := by ring_nf
        _ ≤ ‖Fpi - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + 1 / 100000 := by rw [norm_one]; linarith
    calc ‖Fpi * Fprod - 1‖ = ‖Fpi * (Fprod - 1) + (Fpi - 1)‖ := by ring_nf
      _ ≤ ‖Fpi‖ * ‖Fprod - 1‖ + ‖Fpi - 1‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ (1 + 1 / 100000) * (3 / 1000) + 1 / 100000 := by
          have : ‖Fpi‖ * ‖Fprod - 1‖ ≤ (1 + 1 / 100000) * (3 / 1000) :=
            mul_le_mul hFpi_norm hFprod (norm_nonneg _) (by norm_num)
          linarith
      _ ≤ 4 / 1000 := by norm_num
  have hnorm_fp : ‖Fpi * Fprod‖ ≤ 1 + 4 / 1000 := by
    calc ‖Fpi * Fprod‖ = ‖(Fpi * Fprod - 1) + 1‖ := by ring_nf
      _ ≤ ‖Fpi * Fprod - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 4 / 1000 := by rw [norm_one]; linarith
  calc ‖Fpi * Fprod * Ftail - 1‖ = ‖(Fpi * Fprod) * (Ftail - 1) + (Fpi * Fprod - 1)‖ := by ring_nf
    _ ≤ ‖Fpi * Fprod‖ * ‖Ftail - 1‖ + ‖Fpi * Fprod - 1‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ (1 + 4 / 1000) * (41 / 10000) + 4 / 1000 := by
        have : ‖Fpi * Fprod‖ * ‖Ftail - 1‖ ≤ (1 + 4 / 1000) * (41 / 10000) :=
          mul_le_mul hnorm_fp hFtail (norm_nonneg _) (by norm_num)
        linarith
    _ ≤ 1 / 100 := by norm_num

/-- Reality of `completedRiemannZeta` on the critical line `Re(s) = 1/2`. -/
lemma GammaR_conj (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · have hpi : (Real.pi : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
    rw [show -(conj s) / 2 = conj (-s / 2) by simp [map_div₀, map_ofNat],
      Complex.cpow_conj _ _ hpi, Complex.conj_ofReal]
  · rw [show conj s / 2 = conj (s / 2) by simp [map_div₀, map_ofNat], Complex.Gamma_conj]

lemma completedRiemannZeta_critical_im (t : ℝ) :
    (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)).im = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by intro h; have := congr_arg Complex.re h; simp [s] at this
  have h1ms : conj s = 1 - s := by
    apply Complex.ext
    · simp [s]; norm_num
    · simp [s]
  have hΓne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s])
  have hdef : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hΓne]
  have hs'0 : conj s ≠ 0 := by rw [map_ne_zero]; exact hs0
  have hΓne' : Complex.Gammaℝ (conj s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s])
  have hdef' : completedRiemannZeta (conj s) = Complex.Gammaℝ (conj s) * riemannZeta (conj s) := by
    rw [riemannZeta_def_of_ne_zero hs'0, mul_div_cancel₀ _ hΓne']
  have hconj : conj (completedRiemannZeta s) = completedRiemannZeta s := by
    calc conj (completedRiemannZeta s) = conj (Complex.Gammaℝ s) * conj (riemannZeta s) := by
          rw [hdef, map_mul]
      _ = Complex.Gammaℝ (conj s) * riemannZeta (conj s) := by rw [← GammaR_conj, ← riemannZeta_conj]
      _ = completedRiemannZeta (conj s) := hdef'.symm
      _ = completedRiemannZeta (1 - s) := by rw [h1ms]
      _ = completedRiemannZeta s := completedRiemannZeta_one_sub s
  have him := congr_arg Complex.im hconj
  simp at him
  linarith

/-- Existence of a critical-line zero via sign change of `completedRiemannZeta` and Gamma-shift bound. -/
lemma exists_zero_of_ratio_neg {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (ht₁ : |t₁| ≤ 42) (ht₂ : |t₂| ≤ 42)
    (hd : t₂ - t₁ ≤ 1 / 10 ^ 6)
    (hζ₂ : riemannZeta ((1 / 2 : ℂ) + (t₂ : ℂ) * I) ≠ 0)
    (hrat : (riemannZeta ((1 / 2 : ℂ) + (t₁ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (t₂ : ℂ) * I)).re +
      (1 / 100) * ‖riemannZeta ((1 / 2 : ℂ) + (t₁ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (t₂ : ℂ) * I)‖ < 0) :
    ∃ γ ∈ Set.Icc t₁ t₂, riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 := by
  let L : ℝ → ℝ := fun t => (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)).re
  have hL_cont : Continuous L := by
    have hdL : ∀ t : ℝ, ContinuousAt (fun u : ℝ => completedRiemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)) t := by
      intro t
      have hs0 : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
        intro h; have := congr_arg Complex.re h; simp at this
      have hs1 : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 1 := by
        intro h; have := congr_arg Complex.re h; simp at this
      have h1 := (differentiableAt_completedZeta hs0 hs1).continuousAt
      have h2 : Continuous (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) := by fun_prop
      exact h1.comp (f := fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) h2.continuousAt
    exact Complex.continuous_re.comp (continuous_iff_continuousAt.mpr hdL)
  have hL_eq : ∀ t : ℝ, completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) = (L t : ℂ) := fun t => by
    apply Complex.ext
    · simp [L]
    · rw [Complex.ofReal_im]; exact completedRiemannZeta_critical_im t
  have hL_mul : ∀ t : ℝ, (L t : ℂ) =
      Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I) * riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    intro t
    rw [← hL_eq t]
    have hs0 : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
    have hΓne : Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hΓne]
  have hL2_ne : L t₂ ≠ 0 := by
    intro h
    have h1 := hL_mul t₂
    rw [h, Complex.ofReal_zero] at h1
    have hΓne : Complex.Gammaℝ ((1 / 2 : ℂ) + (t₂ : ℂ) * I) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
    exact mul_ne_zero hΓne hζ₂ h1.symm
  have hdiv_neg : L t₁ / L t₂ < 0 := by
    have hdabs : |t₁ - t₂| ≤ 1 / 10 ^ 6 := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h12)]; exact hd
    have hgam := norm_GammaR_ratio_sub_one_le ht₁ ht₂ hdabs
    set g_rat : ℂ := Complex.Gammaℝ ((1 / 2 : ℂ) + (t₁ : ℂ) * I) /
      Complex.Gammaℝ ((1 / 2 : ℂ) + (t₂ : ℂ) * I)
    set q : ℂ := riemannZeta ((1 / 2 : ℂ) + (t₁ : ℂ) * I) /
      riemannZeta ((1 / 2 : ℂ) + (t₂ : ℂ) * I)
    have hrat_eq : ((L t₁ / L t₂ : ℝ) : ℂ) = g_rat * q := by
      push_cast
      rw [hL_mul t₁, hL_mul t₂]
      dsimp only [g_rat, q]
      ring
    have hre_eq : L t₁ / L t₂ = (g_rat * q).re := by
      have := congr_arg Complex.re hrat_eq
      simpa using this
    rw [hre_eq]
    have hdecomp : (g_rat * q).re = q.re + ((g_rat - 1) * q).re := by
      have h : g_rat * q = q + (g_rat - 1) * q := by ring
      rw [h, Complex.add_re]
    rw [hdecomp]
    have hbound : ((g_rat - 1) * q).re ≤ (1 / 100) * ‖q‖ := by
      calc ((g_rat - 1) * q).re ≤ ‖(g_rat - 1) * q‖ := Complex.re_le_norm _
        _ = ‖g_rat - 1‖ * ‖q‖ := norm_mul _ _
        _ ≤ (1 / 100) * ‖q‖ := mul_le_mul_of_nonneg_right hgam (norm_nonneg q)
    linarith
  have hzero : ∃ γ ∈ Set.Icc t₁ t₂, L γ = 0 := by
    rcases lt_or_gt_of_ne hL2_ne with h2neg | h2pos
    · have h1pos : 0 < L t₁ := by
        by_contra h1le
        push Not at h1le
        have := div_nonneg_of_nonpos h1le h2neg.le
        linarith
      exact intermediate_value_Icc' h12 hL_cont.continuousOn ⟨h2neg.le, h1pos.le⟩
    · have h1neg : L t₁ < 0 := by
        by_contra h1ge
        push Not at h1ge
        have := div_nonneg h1ge h2pos.le
        linarith
      exact intermediate_value_Icc h12 hL_cont.continuousOn ⟨h1neg.le, h2pos.le⟩
  obtain ⟨γ, hγ_mem, hγ_zero⟩ := hzero
  refine ⟨γ, hγ_mem, ?_⟩
  have h1 := hL_mul γ
  rw [hγ_zero, Complex.ofReal_zero] at h1
  have hΓne : Complex.Gammaℝ ((1 / 2 : ℂ) + (γ : ℂ) * I) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  exact (mul_eq_zero.mp h1.symm).resolve_left hΓne

/-! === The `δ → 0+` Hermitian Quadratic-Form Inequality (`<1>4`) -/

/-- Exact residue `R₀ = -1 / (3 * ζ(1/2).re)`. -/
noncomputable def R0 : ℝ := -(1 / (3 * (riemannZeta ((1 / 2 : ℝ) : ℂ)).re))

/-- Exact residue `r(γ) = (1 - ζ(1 + 2iγ)) / ((3/2 + iγ) * ζ'(1/2 + iγ))`. -/
noncomputable def resAt (γ : ℝ) : ℂ :=
  (1 - riemannZeta ((1 : ℂ) + (2 * γ : ℂ) * I)) /
    (((3 / 2 : ℂ) + (γ : ℂ) * I) * deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I))

lemma mellin_B_conj {X₀ : ℝ} (hX₀ : 1 ≤ X₀) (w : ℂ) :
    (∫ x in Set.Ioi X₀, (((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-(conj w) - 2)) =
      conj (∫ x in Set.Ioi X₀, (((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-w - 2)) := by
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hX₀) (le_of_lt hx)
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx0.le]; exact Real.pi_pos.ne
  rw [show -(conj w) - 2 = conj (-w - 2) by simp [map_ofNat], Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- Main contradiction engine (`<1>4`): if `S n ≤ 0` eventually, then for any finite indexed
    set of points in `ℤ^4`, weights `w`, and 4 simple critical-line zeros `γ`, the limiting
    Hermitian quadratic form is nonnegative. -/
theorem quadratic_form_nonneg_of_S_eventually_nonpos
    {N₀ : ℕ} (hS : ∀ n ≥ N₀, S n ≤ 0)
    (γ : Fin 4 → ℝ)
    (hγ_pos : ∀ k : Fin 4, 0 < γ k)
    (hγ_zero : ∀ k : Fin 4, riemannZeta ((1 / 2 : ℂ) + (γ k : ℂ) * I) = 0)
    (hγ_simple : ∀ k : Fin 4, deriv riemannZeta ((1 / 2 : ℂ) + (γ k : ℂ) * I) ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pts : ι → ℤ × ℤ × ℤ × ℤ)
    (hpts_inj : Function.Injective pts)
    (w : ι → ℂ)
    (h_nonunit : ∀ i j : ι,
      let d := (pts i).1 - (pts j).1
      let d1 := (pts i).2.1 - (pts j).2.1
      let d2 := (pts i).2.2.1 - (pts j).2.2.1
      let d3 := (pts i).2.2.2 - (pts j).2.2.2
      (d, d1, d2, d3) ≠ (0, 0, 0, 0) →
      (d, d1, d2, d3) ≠ (1, 0, 0, 0) → (d, d1, d2, d3) ≠ (-1, 0, 0, 0) →
      (d, d1, d2, d3) ≠ (0, 1, 0, 0) → (d, d1, d2, d3) ≠ (0, -1, 0, 0) →
      (d, d1, d2, d3) ≠ (0, 0, 1, 0) → (d, d1, d2, d3) ≠ (0, 0, -1, 0) →
      (d, d1, d2, d3) ≠ (0, 0, 0, 1) → (d, d1, d2, d3) ≠ (0, 0, 0, -1) →
      let t := (d : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3
      t ≠ 0 ∧ riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0) :
    0 ≤ R0 * (∑ i : ι, ‖w i‖ ^ 2) +
      2 * (∑ k : Fin 4,
        (resAt (γ k) *
          ∑ i : ι, ∑ j : ι,
            if (pts i).1 - (pts j).1 = (if k = 0 then 1 else 0) ∧
               (pts i).2.1 - (pts j).2.1 = (if k = 1 then 1 else 0) ∧
               (pts i).2.2.1 - (pts j).2.2.1 = (if k = 2 then 1 else 0) ∧
               (pts i).2.2.2 - (pts j).2.2.2 = (if k = 3 then 1 else 0)
            then w j * conj (w i) else 0).re) := by
  set X₀ : ℝ := (q N₀ : ℝ)
  have hq_pos : 1 ≤ q N₀ := (Nat.nth_mem_of_infinite nonSqf_infinite N₀).1
  have hX₀ : 1 ≤ X₀ := by dsimp only [X₀]; exact_mod_cast hq_pos
  have hX₀0 : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  have hBnonneg : ∀ x, X₀ ≤ x → 0 ≤ (-1 : ℝ) * A x := fun x hx => by
    have := A_nonpos_of_S_nonpos hS x hx
    linarith
  obtain ⟨hB_int, hB_eq⟩ := landau_A_extension (Or.inr rfl) hX₀ hBnonneg
  let IB : ℂ → ℂ := fun z => ∫ x in Set.Ioi X₀, (((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-z - 2)
  let EB : ℂ → ℂ := fun z => ∫ x in Set.Ioc (1 : ℝ) X₀, (((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-z - 2)
  have hEB_diff : Differentiable ℂ EB :=
    differentiable_finite_mellin (measurable_const.mul A_measurable) hX₀ (fun x hx => by
      show |(-1 : ℝ) * A x| ≤ x ^ 2
      rw [abs_mul, abs_neg, abs_one, one_mul]; exact abs_A_le x hx)
  have hEB_lim : ∀ t : ℝ, Tendsto (fun δ : ℝ => (δ : ℂ) * EB ((1 / 2 : ℂ) + (δ : ℂ) - (t : ℂ) * I))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro t
    have hcont : Continuous (fun δ : ℝ => (δ : ℂ) * EB ((1 / 2 : ℂ) + (δ : ℂ) - (t : ℂ) * I)) :=
      Complex.continuous_ofReal.mul
        (hEB_diff.continuous.comp ((continuous_const.add Complex.continuous_ofReal).sub continuous_const))
    have ht : Tendsto (fun δ : ℝ => (δ : ℂ) * EB ((1 / 2 : ℂ) + (δ : ℂ) - (t : ℂ) * I))
        (𝓝[>] (0 : ℝ)) (𝓝 (((0 : ℝ) : ℂ) * EB ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) - (t : ℂ) * I))) :=
      (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa using ht
  -- Pointwise limits of δ * IB(1/2 + δ - i*t) as δ -> 0+
  have hlim_zero :
      Tendsto (fun δ : ℝ => (δ : ℂ) * IB ((1 / 2 : ℂ) + (δ : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (R0 : ℂ)) := by
    have hζhalf_ne : riemannZeta ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      intro h; have hre := riemannZeta_half_le_neg_one.1; rw [h, Complex.zero_re] at hre; linarith
    have hζhalf_eq : riemannZeta ((1 / 2 : ℝ) : ℂ) = ((riemannZeta ((1 / 2 : ℝ) : ℂ)).re : ℂ) := by
      apply Complex.ext
      · simp
      · rw [Complex.ofReal_im]; exact riemannZeta_half_le_neg_one.2
    have hR0_eq : (R0 : ℂ) = (-1 / 2 : ℂ) / ((3 / 2 : ℂ) * riemannZeta ((1 / 2 : ℝ) : ℂ)) := by
      rw [hζhalf_eq, R0]
      push_cast
      have hre_ne : ((riemannZeta ((1 / 2 : ℝ) : ℂ)).re : ℂ) ≠ 0 := by
        intro h; exact hζhalf_ne (by rw [hζhalf_eq, h])
      field_simp [hre_ne]
    have hnum : Tendsto (fun δ : ℝ => (δ : ℂ) * (1 - riemannZeta (2 * ((1 / 2 : ℂ) + (δ : ℂ)))))
        (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2 : ℂ)) := by
      have hmap : Tendsto (fun δ : ℝ => 1 + 2 * (δ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have hc : Continuous (fun δ : ℝ => (1 : ℂ) + 2 * (δ : ℂ)) := by fun_prop
          simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with δ hδ
          intro h; have := congr_arg Complex.re h; simp at this; linarith [Set.mem_Ioi.mp hδ]
      have hres := riemannZeta_residue_one.comp hmap
      have h0 : Tendsto (fun δ : ℝ => (δ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      have hcomb : Tendsto (fun δ : ℝ => (δ : ℂ) - (1 / 2 : ℂ) * ((1 + 2 * (δ : ℂ) - 1) * riemannZeta (1 + 2 * (δ : ℂ))))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 - (1 / 2 : ℂ) * 1)) := h0.sub (hres.const_mul (1 / 2 : ℂ))
      have hrew : (0 - (1 / 2 : ℂ) * 1) = (-1 / 2 : ℂ) := by ring
      rw [hrew] at hcomb
      refine hcomb.congr fun δ => ?_
      have h2 : 2 * ((1 / 2 : ℂ) + (δ : ℂ)) = 1 + 2 * (δ : ℂ) := by ring
      rw [h2]; ring
    have hden : Tendsto (fun δ : ℝ => (((1 / 2 : ℂ) + (δ : ℂ)) + 1) * riemannZeta ((1 / 2 : ℂ) + (δ : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((3 / 2 : ℂ) * riemannZeta ((1 / 2 : ℝ) : ℂ))) := by
      have h1 : Tendsto (fun δ : ℝ => ((1 / 2 : ℂ) + (δ : ℂ)) + 1) (𝓝[>] (0 : ℝ)) (𝓝 (3 / 2 : ℂ)) := by
        have hc : Continuous (fun δ : ℝ => ((1 / 2 : ℂ) + (δ : ℂ)) + 1) := by fun_prop
        have ht : Tendsto (fun δ : ℝ => ((1 / 2 : ℂ) + (δ : ℂ)) + 1) (𝓝[>] (0 : ℝ))
            (𝓝 (((1 / 2 : ℂ) + ((0 : ℝ) : ℂ)) + 1)) :=
          (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        convert ht using 2; norm_num
      have h2 : Tendsto (fun δ : ℝ => riemannZeta ((1 / 2 : ℂ) + (δ : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 (riemannZeta ((1 / 2 : ℝ) : ℂ))) := by
        have hζc := (differentiableAt_riemannZeta (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num)).continuousAt
        have hc : Continuous (fun δ : ℝ => (1 / 2 : ℂ) + (δ : ℂ)) := by fun_prop
        have hmap0 : Tendsto (fun δ : ℝ => (1 / 2 : ℂ) + (δ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) : ℂ)) := by
          have ht : Tendsto (fun δ : ℝ => (1 / 2 : ℂ) + (δ : ℂ)) (𝓝[>] (0 : ℝ))
              (𝓝 ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ))) :=
            (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
          simpa using ht
        exact hζc.tendsto.comp hmap0
      exact h1.mul h2
    have hden_ne : (3 / 2 : ℂ) * riemannZeta ((1 / 2 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) hζhalf_ne
    have hEB0 : Tendsto (fun δ : ℝ => (δ : ℂ) * EB ((1 / 2 : ℂ) + (δ : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (hEB_lim 0).congr fun δ => by simp
    have hquot := (hnum.div hden hden_ne).sub hEB0
    rw [sub_zero, ← hR0_eq] at hquot
    refine hquot.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with δ hδ0 hδ1
    have hδpos : 0 < δ := Set.mem_Ioi.mp hδ0
    have hre : 1 / 2 < ((1 / 2 : ℂ) + (δ : ℂ)).re := by simp; linarith
    have hne1 : (1 / 2 : ℂ) + (δ : ℂ) ≠ 1 := by
      intro h; have := congr_arg Complex.re h; simp at this; linarith [Set.mem_Iio.mp hδ1]
    have hζne : riemannZeta ((1 / 2 : ℂ) + (δ : ℂ)) ≠ 0 := by
      have hreal : (1 / 2 : ℂ) + (δ : ℂ) = ((1 / 2 + δ : ℝ) : ℂ) := by push_cast; ring
      rw [hreal]
      exact riemannZeta_ne_zero_of_Ioo (by linarith) (by linarith [Set.mem_Iio.mp hδ1])
    have heq := hB_eq _ hre hne1 hζne
    have heq' : IB ((1 / 2 : ℂ) + (δ : ℂ)) = (1 - riemannZeta (2 * ((1 / 2 : ℂ) + (δ : ℂ)))) /
        (((1 / 2 : ℂ) + (δ : ℂ) + 1) * riemannZeta ((1 / 2 : ℂ) + (δ : ℂ))) -
        EB ((1 / 2 : ℂ) + (δ : ℂ)) := by
      dsimp only [IB, EB]; rw [heq]; push_cast; ring
    dsimp only [Pi.sub_apply, Pi.div_apply]
    rw [heq']; ring
  have hlim_neg_gamma : ∀ k : Fin 4,
      Tendsto (fun δ : ℝ => (δ : ℂ) * IB ((1 / 2 : ℂ) + (δ : ℂ) - (-(γ k) : ℂ) * I))
        (𝓝[>] (0 : ℝ)) (𝓝 (resAt (γ k))) := by
    intro k
    set ρ : ℂ := (1 / 2 : ℂ) + (γ k : ℂ) * I
    have hρ1 : ρ ≠ 1 := by intro h; have := congr_arg Complex.re h; simp [ρ] at this
    have h2ρ1 : 2 * ρ ≠ 1 := by
      intro h; have := congr_arg Complex.im h; simp [ρ] at this; linarith [hγ_pos k]
    have hρp1 : ρ + 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp [ρ] at this; norm_num at this
    have hdζ : HasDerivAt riemannZeta (deriv riemannZeta ρ) ρ :=
      (differentiableAt_riemannZeta hρ1).hasDerivAt
    have hslope : Tendsto (fun δ : ℝ => riemannZeta (ρ + (δ : ℂ)) / (δ : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv riemannZeta ρ)) := by
      have h1 := hasDerivAt_iff_tendsto_slope.mp hdζ
      have hmap : Tendsto (fun δ : ℝ => ρ + (δ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] ρ) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have hc : Continuous (fun δ : ℝ => ρ + (δ : ℂ)) := by fun_prop
          simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with δ hδ
          intro h; have := congr_arg Complex.re h; simp at this; linarith [Set.mem_Ioi.mp hδ]
      have h2 := h1.comp hmap
      refine h2.congr fun δ => ?_
      have hρz : riemannZeta ρ = 0 := hγ_zero k
      simp [Function.comp_apply, slope_def_field, hρz]
    have hζ_ev_ne : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), riemannZeta (ρ + (δ : ℂ)) ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin, hslope.eventually_ne (hγ_simple k)] with δ hδ hne h0
      rw [h0, zero_div] at hne
      exact hne rfl
    have hnum : Tendsto (fun δ : ℝ => 1 - riemannZeta (2 * (ρ + (δ : ℂ))))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 - riemannZeta (2 * ρ))) := by
      have hζc := (differentiableAt_riemannZeta h2ρ1).continuousAt
      have hc : Continuous (fun δ : ℝ => 2 * (ρ + (δ : ℂ))) := by fun_prop
      have hmap2 : Tendsto (fun δ : ℝ => 2 * (ρ + (δ : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (2 * ρ)) := by
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_const_nhds.sub (hζc.tendsto.comp hmap2)
    have hden : Tendsto (fun δ : ℝ => (ρ + (δ : ℂ) + 1) * (riemannZeta (ρ + (δ : ℂ)) / (δ : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((ρ + 1) * deriv riemannZeta ρ)) := by
      have h1 : Tendsto (fun δ : ℝ => ρ + (δ : ℂ) + 1) (𝓝[>] (0 : ℝ)) (𝓝 (ρ + 1)) := by
        have hc : Continuous (fun δ : ℝ => ρ + (δ : ℂ) + 1) := by fun_prop
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      exact h1.mul hslope
    have hquot := (hnum.div hden (mul_ne_zero hρp1 (hγ_simple k))).sub (hEB_lim (-(γ k)))
    rw [sub_zero] at hquot
    have hres_eq : (1 - riemannZeta (2 * ρ)) / ((ρ + 1) * deriv riemannZeta ρ) = resAt (γ k) := by
      have h2ρ : 2 * ρ = (1 : ℂ) + (2 * γ k : ℂ) * I := by dsimp only [ρ]; ring
      have hρ1' : ρ + 1 = (3 / 2 : ℂ) + (γ k : ℂ) * I := by dsimp only [ρ]; ring
      rw [h2ρ, hρ1']; rfl
    rw [hres_eq] at hquot
    refine hquot.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hζ_ev_ne] with δ hδ hζne
    have hδpos : 0 < δ := Set.mem_Ioi.mp hδ
    have hδne : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδpos.ne'
    have harg : (1 / 2 : ℂ) + (δ : ℂ) - (-(γ k) : ℂ) * I = ρ + (δ : ℂ) := by
      dsimp only [ρ]; ring
    have hEBarg : (1 / 2 : ℂ) + (δ : ℂ) - ((-(γ k) : ℝ) : ℂ) * I = ρ + (δ : ℂ) := by
      dsimp only [ρ]; push_cast; ring
    have hre : 1 / 2 < (ρ + (δ : ℂ)).re := by simp [ρ]; linarith
    have hne1 : ρ + (δ : ℂ) ≠ 1 := by
      intro h; have := congr_arg Complex.im h; simp [ρ] at this; linarith [hγ_pos k]
    have heq := hB_eq (ρ + (δ : ℂ)) hre hne1 hζne
    have heq' : IB (ρ + (δ : ℂ)) = (1 - riemannZeta (2 * (ρ + (δ : ℂ)))) /
        ((ρ + (δ : ℂ) + 1) * riemannZeta (ρ + (δ : ℂ))) - EB (ρ + (δ : ℂ)) := by
      dsimp only [IB, EB]; rw [heq]; push_cast; ring
    dsimp only [Pi.sub_apply, Pi.div_apply]
    rw [harg, hEBarg, heq']
    have hρp1d : ρ + (δ : ℂ) + 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp [ρ] at this; linarith
    field_simp [hδne, hζne, hρp1d]
  have hlim_pos_gamma : ∀ k : Fin 4,
      Tendsto (fun δ : ℝ => (δ : ℂ) * IB ((1 / 2 : ℂ) + (δ : ℂ) - (γ k : ℂ) * I))
        (𝓝[>] (0 : ℝ)) (𝓝 (conj (resAt (γ k)))) := by
    intro k
    have hconj_t := (Complex.continuous_conj.continuousAt.tendsto.comp (hlim_neg_gamma k))
    refine hconj_t.congr fun δ => ?_
    simp only [Function.comp_apply, map_mul, Complex.conj_ofReal]
    congr 1
    have harg : (1 / 2 : ℂ) + (δ : ℂ) - (γ k : ℂ) * I = conj ((1 / 2 : ℂ) + (δ : ℂ) - (-(γ k) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [harg]
    exact (mellin_B_conj hX₀ _).symm
  have hlim_other : ∀ t : ℝ, t ≠ 0 → riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 →
      Tendsto (fun δ : ℝ => (δ : ℂ) * IB ((1 / 2 : ℂ) + (δ : ℂ) - (t : ℂ) * I))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro t ht0 hζt
    set s₀ : ℂ := (1 / 2 : ℂ) - (t : ℂ) * I
    have hs₀_ne1 : s₀ ≠ 1 := by intro h; have := congr_arg Complex.re h; simp [s₀] at this
    have h2s₀_ne1 : 2 * s₀ ≠ 1 := by intro h; have := congr_arg Complex.im h; simp [s₀] at this; exact ht0 this
    have hs₀_p1 : s₀ + 1 ≠ 0 := by intro h; have := congr_arg Complex.re h; simp [s₀] at this; norm_num at this
    have hζs₀_ne : riemannZeta s₀ ≠ 0 := by
      have hc : s₀ = conj ((1 / 2 : ℂ) + (t : ℂ) * I) := by apply Complex.ext <;> simp [s₀]
      rw [hc, riemannZeta_conj, map_ne_zero]
      exact hζt
    have hζ_cont : ContinuousAt riemannZeta s₀ := (differentiableAt_riemannZeta hs₀_ne1).continuousAt
    have hmap : Tendsto (fun δ : ℝ => s₀ + (δ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 s₀) := by
      have hc : Continuous (fun δ : ℝ => s₀ + (δ : ℂ)) := by fun_prop
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hζ_ev_ne : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), riemannZeta (s₀ + (δ : ℂ)) ≠ 0 :=
      (hζ_cont.tendsto.comp hmap).eventually_ne hζs₀_ne
    have hM_lim : Tendsto (fun δ : ℝ => (1 - riemannZeta (2 * (s₀ + (δ : ℂ)))) /
        ((s₀ + (δ : ℂ) + 1) * riemannZeta (s₀ + (δ : ℂ))))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 - riemannZeta (2 * s₀)) / ((s₀ + 1) * riemannZeta s₀))) := by
      have hnum : Tendsto (fun δ : ℝ => 1 - riemannZeta (2 * (s₀ + (δ : ℂ))))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 - riemannZeta (2 * s₀))) := by
        have hζ2c := (differentiableAt_riemannZeta h2s₀_ne1).continuousAt
        have hc : Continuous (fun δ : ℝ => 2 * (s₀ + (δ : ℂ))) := by fun_prop
        have hmap2 : Tendsto (fun δ : ℝ => 2 * (s₀ + (δ : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (2 * s₀)) := by
          simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        exact tendsto_const_nhds.sub (hζ2c.tendsto.comp hmap2)
      have hden : Tendsto (fun δ : ℝ => (s₀ + (δ : ℂ) + 1) * riemannZeta (s₀ + (δ : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 ((s₀ + 1) * riemannZeta s₀)) :=
        (hmap.add tendsto_const_nhds).mul (hζ_cont.tendsto.comp hmap)
      exact hnum.div hden (mul_ne_zero hs₀_p1 hζs₀_ne)
    have h0 : Tendsto (fun δ : ℝ => (δ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have htot := (h0.mul hM_lim).sub (hEB_lim t)
    simp only [zero_mul, sub_zero] at htot
    refine htot.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hζ_ev_ne] with δ hδ hζne
    have hδpos : 0 < δ := Set.mem_Ioi.mp hδ
    have harg : (1 / 2 : ℂ) + (δ : ℂ) - (t : ℂ) * I = s₀ + (δ : ℂ) := by dsimp only [s₀]; ring
    have hre : 1 / 2 < (s₀ + (δ : ℂ)).re := by simp [s₀]; linarith
    have hne1 : s₀ + (δ : ℂ) ≠ 1 := by intro h; have := congr_arg Complex.im h; simp [s₀] at this; exact ht0 this
    have heq := hB_eq (s₀ + (δ : ℂ)) hre hne1 hζne
    have heq' : IB (s₀ + (δ : ℂ)) = (1 - riemannZeta (2 * (s₀ + (δ : ℂ)))) /
        ((s₀ + (δ : ℂ) + 1) * riemannZeta (s₀ + (δ : ℂ))) - EB (s₀ + (δ : ℂ)) := by
      dsimp only [IB, EB]; rw [heq]; push_cast; ring
    rw [harg, heq']; ring
  -- Define x_pt and expand the nonnegative integral for δ > 0
  let xpt : ι → ℝ := fun i =>
    ((pts i).1 : ℝ) * γ 0 + ((pts i).2.1 : ℝ) * γ 1 +
    ((pts i).2.2.1 : ℝ) * γ 2 + ((pts i).2.2.2 : ℝ) * γ 3
  let Qfun : ℝ → ℝ := fun δ =>
    (∑ i : ι, ∑ j : ι, w i * conj (w j) *
      ((δ : ℂ) * IB ((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I))).re
  have hQ_nonneg : ∀ δ : ℝ, 0 < δ → 0 ≤ Qfun δ := by
    intro δ hδ
    have hint_pair : ∀ i j : ι,
        IntegrableOn (fun x : ℝ => w i * conj (w j) * (δ : ℂ) *
          ((((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I) - 2)))
          (Set.Ioi X₀) := fun i j =>
      (hB_int _ (by simp; linarith)).const_mul _
    have hsum_int :
        (∑ i : ι, ∑ j : ι, w i * conj (w j) *
          ((δ : ℂ) * IB ((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I))) =
        ∫ x in Set.Ioi X₀,
          ∑ i : ι, ∑ j : ι, w i * conj (w j) * (δ : ℂ) *
            ((((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I) - 2)) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint_pair i j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => hint_pair i j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [IB]
      rw [← mul_assoc, ← integral_const_mul]
    have hreal_int :
        (∫ x in Set.Ioi X₀,
          ∑ i : ι, ∑ j : ι, w i * conj (w j) * (δ : ℂ) *
            ((((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I) - 2))) =
        Complex.ofReal (∫ x : ℝ in Set.Ioi X₀,
          δ * ((-1 : ℝ) * A x) * x ^ (-(5 / 2 + δ)) *
            ‖∑ i : ι, w i * (x : ℂ) ^ ((xpt i : ℂ) * I)‖ ^ 2) := by
      rw [show Complex.ofReal (∫ x : ℝ in Set.Ioi X₀,
            δ * ((-1 : ℝ) * A x) * x ^ (-(5 / 2 + δ)) *
              ‖∑ i : ι, w i * (x : ℂ) ^ ((xpt i : ℂ) * I)‖ ^ 2) =
          ∫ x : ℝ in Set.Ioi X₀,
            ((δ * ((-1 : ℝ) * A x) * x ^ (-(5 / 2 + δ)) *
              ‖∑ i : ι, w i * (x : ℂ) ^ ((xpt i : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) from integral_ofReal.symm]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 < x := lt_trans hX₀0 hx
      have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
      have hcp_split : ∀ i j : ι,
          (x : ℂ) ^ (-((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I) - 2) =
            ((x ^ (-(5 / 2 + δ)) : ℝ) : ℂ) * ((x : ℂ) ^ ((xpt i : ℂ) * I) * conj ((x : ℂ) ^ ((xpt j : ℂ) * I))) := by
        intro i j
        have harg : (x : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg hx0.le]; exact Real.pi_pos.ne
        have hcj : conj ((x : ℂ) ^ ((xpt j : ℂ) * I)) = (x : ℂ) ^ (-((xpt j : ℂ) * I)) := by
          have h := Complex.cpow_conj (x : ℂ) ((xpt j : ℂ) * I) harg
          rw [Complex.conj_ofReal] at h
          rw [← h]; congr 1; simp
        rw [hcj, ← Complex.cpow_add _ _ hxne, Complex.ofReal_cpow hx0.le, ← Complex.cpow_add _ _ hxne]
        congr 1; push_cast; ring
      have hnorm_sq : (‖∑ i : ι, w i * (x : ℂ) ^ ((xpt i : ℂ) * I)‖ ^ 2 : ℂ) =
          (∑ i : ι, w i * (x : ℂ) ^ ((xpt i : ℂ) * I)) *
            conj (∑ j : ι, w j * (x : ℂ) ^ ((xpt j : ℂ) * I)) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        norm_cast
      calc (∑ i : ι, ∑ j : ι, w i * conj (w j) * (δ : ℂ) *
              ((((-1 : ℝ) * A x : ℝ) : ℂ) * (x : ℂ) ^ (-((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I) - 2)))
          = (δ : ℂ) * (((-1 : ℝ) * A x : ℝ) : ℂ) * ((x ^ (-(5 / 2 + δ)) : ℝ) : ℂ) *
              (∑ i : ι, ∑ j : ι, (w i * (x : ℂ) ^ ((xpt i : ℂ) * I)) *
                (conj (w j) * conj ((x : ℂ) ^ ((xpt j : ℂ) * I)))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hcp_split i j]; ring
        _ = (δ : ℂ) * (((-1 : ℝ) * A x : ℝ) : ℂ) * ((x ^ (-(5 / 2 + δ)) : ℝ) : ℂ) *
              ((∑ i : ι, w i * (x : ℂ) ^ ((xpt i : ℂ) * I)) *
                conj (∑ j : ι, w j * (x : ℂ) ^ ((xpt j : ℂ) * I))) := by
            congr 1
            rw [map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by rw [map_mul]
        _ = _ := by rw [← hnorm_sq]; push_cast; rfl
    dsimp only [Qfun]
    rw [hsum_int, hreal_int, Complex.ofReal_re]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      have hx0 : 0 < x := lt_trans hX₀0 hx
      have hB : 0 ≤ (-1 : ℝ) * A x := hBnonneg x (le_of_lt hx)
      positivity
  -- Compute the limit of Qfun δ as δ -> 0+
  let limTerm : ι → ι → ℂ := fun i j =>
    let d0 := (pts i).1 - (pts j).1
    let d1 := (pts i).2.1 - (pts j).2.1
    let d2 := (pts i).2.2.1 - (pts j).2.2.1
    let d3 := (pts i).2.2.2 - (pts j).2.2.2
    if (d0, d1, d2, d3) = (0, 0, 0, 0) then (R0 : ℂ)
    else if (d0, d1, d2, d3) = (-1, 0, 0, 0) then resAt (γ 0)
    else if (d0, d1, d2, d3) = (1, 0, 0, 0) then conj (resAt (γ 0))
    else if (d0, d1, d2, d3) = (0, -1, 0, 0) then resAt (γ 1)
    else if (d0, d1, d2, d3) = (0, 1, 0, 0) then conj (resAt (γ 1))
    else if (d0, d1, d2, d3) = (0, 0, -1, 0) then resAt (γ 2)
    else if (d0, d1, d2, d3) = (0, 0, 1, 0) then conj (resAt (γ 2))
    else if (d0, d1, d2, d3) = (0, 0, 0, -1) then resAt (γ 3)
    else if (d0, d1, d2, d3) = (0, 0, 0, 1) then conj (resAt (γ 3))
    else 0
  have hterm_lim : ∀ i j : ι,
      Tendsto (fun δ : ℝ => w i * conj (w j) *
        ((δ : ℂ) * IB ((1 / 2 : ℂ) + (δ : ℂ) - ((xpt i - xpt j : ℝ) : ℂ) * I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (w i * conj (w j) * limTerm i j)) := by
    intro i j
    refine Tendsto.const_mul (w i * conj (w j)) ?_
    set d0 := (pts i).1 - (pts j).1
    set d1 := (pts i).2.1 - (pts j).2.1
    set d2 := (pts i).2.2.1 - (pts j).2.2.1
    set d3 := (pts i).2.2.2 - (pts j).2.2.2
    have hxsub : xpt i - xpt j =
        (d0 : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3 := by
      dsimp only [xpt, d0, d1, d2, d3]; push_cast; ring
    dsimp only [limTerm]
    by_cases h0 : (d0, d1, d2, d3) = (0, 0, 0, 0)
    · rw [if_pos h0]
      rcases Prod.mk.inj h0 with ⟨e0, h0'⟩
      rcases Prod.mk.inj h0' with ⟨e1, h0''⟩
      rcases Prod.mk.inj h0'' with ⟨e2, e3⟩
      rw [hxsub, e0, e1, e2, e3]; simpa using hlim_zero
    · rw [if_neg h0]
      by_cases hm0 : (d0, d1, d2, d3) = (-1, 0, 0, 0)
      · rw [if_pos hm0]
        rcases Prod.mk.inj hm0 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
        rw [hxsub, e0, e1, e2, e3]; simpa using hlim_neg_gamma 0
      · rw [if_neg hm0]
        by_cases hp0 : (d0, d1, d2, d3) = (1, 0, 0, 0)
        · rw [if_pos hp0]
          rcases Prod.mk.inj hp0 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
          rw [hxsub, e0, e1, e2, e3]; simpa using hlim_pos_gamma 0
        · rw [if_neg hp0]
          by_cases hm1 : (d0, d1, d2, d3) = (0, -1, 0, 0)
          · rw [if_pos hm1]
            rcases Prod.mk.inj hm1 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
            rw [hxsub, e0, e1, e2, e3]; simpa using hlim_neg_gamma 1
          · rw [if_neg hm1]
            by_cases hp1 : (d0, d1, d2, d3) = (0, 1, 0, 0)
            · rw [if_pos hp1]
              rcases Prod.mk.inj hp1 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
              rw [hxsub, e0, e1, e2, e3]; simpa using hlim_pos_gamma 1
            · rw [if_neg hp1]
              by_cases hm2 : (d0, d1, d2, d3) = (0, 0, -1, 0)
              · rw [if_pos hm2]
                rcases Prod.mk.inj hm2 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                rw [hxsub, e0, e1, e2, e3]; simpa using hlim_neg_gamma 2
              · rw [if_neg hm2]
                by_cases hp2 : (d0, d1, d2, d3) = (0, 0, 1, 0)
                · rw [if_pos hp2]
                  rcases Prod.mk.inj hp2 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                  rw [hxsub, e0, e1, e2, e3]; simpa using hlim_pos_gamma 2
                · rw [if_neg hp2]
                  by_cases hm3 : (d0, d1, d2, d3) = (0, 0, 0, -1)
                  · rw [if_pos hm3]
                    rcases Prod.mk.inj hm3 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                    rw [hxsub, e0, e1, e2, e3]; simpa using hlim_neg_gamma 3
                  · rw [if_neg hm3]
                    by_cases hp3 : (d0, d1, d2, d3) = (0, 0, 0, 1)
                    · rw [if_pos hp3]
                      rcases Prod.mk.inj hp3 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                      rw [hxsub, e0, e1, e2, e3]; simpa using hlim_pos_gamma 3
                    · rw [if_neg hp3]
                      have hnu := h_nonunit i j h0 hp0 hm0 hp1 hm1 hp2 hm2 hp3 hm3
                      rw [hxsub]
                      exact hlim_other _ hnu.1 hnu.2
  have hQ_lim : Tendsto Qfun (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i : ι, ∑ j : ι, w i * conj (w j) * limTerm i j).re) := by
    have hsum := tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => hterm_lim i j
    exact Complex.continuous_re.continuousAt.tendsto.comp hsum
  have hlim_nonneg : 0 ≤ (∑ i : ι, ∑ j : ι, w i * conj (w j) * limTerm i j).re :=
    ge_of_tendsto hQ_lim (by filter_upwards [self_mem_nhdsWithin] with δ hδ; exact hQ_nonneg δ (Set.mem_Ioi.mp hδ))
  -- Identify the limiting double sum with the claimed quadratic form
  have hsplit_sum :
      (∑ i : ι, ∑ j : ι, w i * conj (w j) * limTerm i j).re =
        R0 * (∑ i : ι, ‖w i‖ ^ 2) +
        2 * (∑ k : Fin 4,
          (resAt (γ k) *
            ∑ i : ι, ∑ j : ι,
              if (pts i).1 - (pts j).1 = (if k = 0 then 1 else 0) ∧
                 (pts i).2.1 - (pts j).2.1 = (if k = 1 then 1 else 0) ∧
                 (pts i).2.2.1 - (pts j).2.2.1 = (if k = 2 then 1 else 0) ∧
                 (pts i).2.2.2 - (pts j).2.2.2 = (if k = 3 then 1 else 0)
              then w j * conj (w i) else 0).re) := by
    -- Split limTerm i j as sum of 9 disjoint indicators (fast O(9) case split!)
    have hlim_decomp : ∀ i j : ι,
        limTerm i j =
          (if i = j then (R0 : ℂ) else 0) +
          (if (pts i).1 - (pts j).1 = -1 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then resAt (γ 0) else 0) +
          (if (pts i).1 - (pts j).1 = 1 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then conj (resAt (γ 0)) else 0) +
          (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = -1 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then resAt (γ 1) else 0) +
          (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 1 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then conj (resAt (γ 1)) else 0) +
          (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = -1 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then resAt (γ 2) else 0) +
          (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = 1 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then conj (resAt (γ 2)) else 0) +
          (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = -1 then resAt (γ 3) else 0) +
          (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 1 then conj (resAt (γ 3)) else 0) := by
      intro i j
      set d0 := (pts i).1 - (pts j).1
      set d1 := (pts i).2.1 - (pts j).2.1
      set d2 := (pts i).2.2.1 - (pts j).2.2.1
      set d3 := (pts i).2.2.2 - (pts j).2.2.2
      have hij_iff : (d0, d1, d2, d3) = (0, 0, 0, 0) ↔ i = j := by
        constructor
        · intro h
          apply hpts_inj
          rcases Prod.mk.inj h with ⟨h0, h'⟩; rcases Prod.mk.inj h' with ⟨h1, h''⟩; rcases Prod.mk.inj h'' with ⟨h2, h3⟩
          exact Prod.ext (sub_eq_zero.mp h0) (Prod.ext (sub_eq_zero.mp h1) (Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h3)))
        · rintro rfl; simp [d0, d1, d2, d3]
      change (if (d0, d1, d2, d3) = (0, 0, 0, 0) then (R0 : ℂ)
        else if (d0, d1, d2, d3) = (-1, 0, 0, 0) then resAt (γ 0)
        else if (d0, d1, d2, d3) = (1, 0, 0, 0) then conj (resAt (γ 0))
        else if (d0, d1, d2, d3) = (0, -1, 0, 0) then resAt (γ 1)
        else if (d0, d1, d2, d3) = (0, 1, 0, 0) then conj (resAt (γ 1))
        else if (d0, d1, d2, d3) = (0, 0, -1, 0) then resAt (γ 2)
        else if (d0, d1, d2, d3) = (0, 0, 1, 0) then conj (resAt (γ 2))
        else if (d0, d1, d2, d3) = (0, 0, 0, -1) then resAt (γ 3)
        else if (d0, d1, d2, d3) = (0, 0, 0, 1) then conj (resAt (γ 3))
        else 0) = _
      by_cases h0 : (d0, d1, d2, d3) = (0, 0, 0, 0)
      · have hij := hij_iff.mp h0
        rcases Prod.mk.inj h0 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
        simp [hij, e0, e1, e2, e3]
      · have hne : i ≠ j := fun h => h0 (hij_iff.mpr h)
        rw [if_neg h0, if_neg hne, zero_add]
        by_cases hm0 : (d0, d1, d2, d3) = (-1, 0, 0, 0)
        · rcases Prod.mk.inj hm0 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
          simp [e0, e1, e2, e3]
        · rw [if_neg hm0]
          by_cases hp0 : (d0, d1, d2, d3) = (1, 0, 0, 0)
          · rcases Prod.mk.inj hp0 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
            simp [e0, e1, e2, e3]
          · rw [if_neg hp0]
            by_cases hm1 : (d0, d1, d2, d3) = (0, -1, 0, 0)
            · rcases Prod.mk.inj hm1 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
              simp [e0, e1, e2, e3]
            · rw [if_neg hm1]
              by_cases hp1 : (d0, d1, d2, d3) = (0, 1, 0, 0)
              · rcases Prod.mk.inj hp1 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                simp [e0, e1, e2, e3]
              · rw [if_neg hp1]
                by_cases hm2 : (d0, d1, d2, d3) = (0, 0, -1, 0)
                · rcases Prod.mk.inj hm2 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                  simp [e0, e1, e2, e3]
                · rw [if_neg hm2]
                  by_cases hp2 : (d0, d1, d2, d3) = (0, 0, 1, 0)
                  · rcases Prod.mk.inj hp2 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                    simp [e0, e1, e2, e3]
                  · rw [if_neg hp2]
                    by_cases hm3 : (d0, d1, d2, d3) = (0, 0, 0, -1)
                    · rcases Prod.mk.inj hm3 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                      simp [e0, e1, e2, e3]
                    · rw [if_neg hm3]
                      by_cases hp3 : (d0, d1, d2, d3) = (0, 0, 0, 1)
                      · rcases Prod.mk.inj hp3 with ⟨e0, h'⟩; rcases Prod.mk.inj h' with ⟨e1, h''⟩; rcases Prod.mk.inj h'' with ⟨e2, e3⟩
                        simp [e0, e1, e2, e3]
                      · rw [if_neg hp3]
                        have hneq : ∀ a0 a1 a2 a3 : ℤ, (d0, d1, d2, d3) ≠ (a0, a1, a2, a3) →
                            ¬ (d0 = a0 ∧ d1 = a1 ∧ d2 = a2 ∧ d3 = a3) := by
                          rintro a0 a1 a2 a3 h ⟨rfl, rfl, rfl, rfl⟩; exact h rfl
                        rw [if_neg (hneq (-1) 0 0 0 hm0), if_neg (hneq 1 0 0 0 hp0),
                            if_neg (hneq 0 (-1) 0 0 hm1), if_neg (hneq 0 1 0 0 hp1),
                            if_neg (hneq 0 0 (-1) 0 hm2), if_neg (hneq 0 0 1 0 hp2),
                            if_neg (hneq 0 0 0 (-1) hm3), if_neg (hneq 0 0 0 1 hp3)]
                        simp
    have hdiag : (∑ i : ι, ∑ j : ι, w i * conj (w j) * (if i = j then (R0 : ℂ) else 0)).re =
        R0 * ∑ i : ι, ‖w i‖ ^ 2 := by
      have h1 : (∑ i : ι, ∑ j : ι, w i * conj (w j) * (if i = j then (R0 : ℂ) else 0)) =
          (R0 : ℂ) * ∑ i : ι, ((‖w i‖ ^ 2 : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : ∑ j : ι, w i * conj (w j) * (if i = j then (R0 : ℂ) else 0) =
            w i * conj (w i) * (R0 : ℂ) := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [Ne.symm hji]
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]
      rw [h1, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hedge : ∀ (e0 e1 e2 e3 : ℤ) (r : ℂ),
        (∑ i : ι, ∑ j : ι, w i * conj (w j) *
            (if (pts i).1 - (pts j).1 = -e0 ∧ (pts i).2.1 - (pts j).2.1 = -e1 ∧
                (pts i).2.2.1 - (pts j).2.2.1 = -e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = -e3
             then r else 0) +
          ∑ i : ι, ∑ j : ι, w i * conj (w j) *
            (if (pts i).1 - (pts j).1 = e0 ∧ (pts i).2.1 - (pts j).2.1 = e1 ∧
                (pts i).2.2.1 - (pts j).2.2.1 = e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = e3
             then conj r else 0)).re =
        2 * (r * ∑ i : ι, ∑ j : ι,
            if (pts i).1 - (pts j).1 = e0 ∧ (pts i).2.1 - (pts j).2.1 = e1 ∧
               (pts i).2.2.1 - (pts j).2.2.1 = e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = e3
            then w j * conj (w i) else 0).re := by
      intro e0 e1 e2 e3 r
      let T : ℂ := r * ∑ i : ι, ∑ j : ι,
        if (pts i).1 - (pts j).1 = e0 ∧ (pts i).2.1 - (pts j).2.1 = e1 ∧
           (pts i).2.2.1 - (pts j).2.2.1 = e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = e3
        then w j * conj (w i) else 0
      have h1 : (∑ i : ι, ∑ j : ι, w i * conj (w j) *
          (if (pts i).1 - (pts j).1 = -e0 ∧ (pts i).2.1 - (pts j).2.1 = -e1 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = -e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = -e3
           then r else 0)) = T := by
        dsimp only [T]
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hcond : ((pts j).1 - (pts i).1 = -e0 ∧ (pts j).2.1 - (pts i).2.1 = -e1 ∧
            (pts j).2.2.1 - (pts i).2.2.1 = -e2 ∧ (pts j).2.2.2 - (pts i).2.2.2 = -e3) ↔
            ((pts i).1 - (pts j).1 = e0 ∧ (pts i).2.1 - (pts j).2.1 = e1 ∧
            (pts i).2.2.1 - (pts j).2.2.1 = e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = e3) := by
          constructor <;> rintro ⟨a0, a1, a2, a3⟩ <;> exact ⟨by omega, by omega, by omega, by omega⟩
        by_cases hc : (pts i).1 - (pts j).1 = e0 ∧ (pts i).2.1 - (pts j).2.1 = e1 ∧
            (pts i).2.2.1 - (pts j).2.2.1 = e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = e3
        · rw [if_pos (hcond.mpr hc), if_pos hc]; ring
        · rw [if_neg (mt hcond.mp hc), if_neg hc]; ring
      have h2 : (∑ i : ι, ∑ j : ι, w i * conj (w j) *
          (if (pts i).1 - (pts j).1 = e0 ∧ (pts i).2.1 - (pts j).2.1 = e1 ∧
              (pts i).2.2.1 - (pts j).2.2.1 = e2 ∧ (pts i).2.2.2 - (pts j).2.2.2 = e3
           then conj r else 0)) = conj T := by
        dsimp only [T]
        rw [map_mul, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · rw [map_mul, Complex.conj_conj]; ring
        · simp
      rw [h1, h2, Complex.add_re, Complex.conj_re]
      ring
    have hexpand :
        (∑ i : ι, ∑ j : ι, w i * conj (w j) * limTerm i j) =
          (∑ i : ι, ∑ j : ι, w i * conj (w j) * (if i = j then (R0 : ℂ) else 0)) +
          ((∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = -1 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then resAt (γ 0) else 0)) +
           (∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = 1 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then conj (resAt (γ 0)) else 0))) +
          ((∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = -1 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then resAt (γ 1) else 0)) +
           (∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 1 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then conj (resAt (γ 1)) else 0))) +
          ((∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = -1 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then resAt (γ 2) else 0)) +
           (∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = 1 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0 then conj (resAt (γ 2)) else 0))) +
          ((∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = -1 then resAt (γ 3) else 0)) +
           (∑ i : ι, ∑ j : ι, w i * conj (w j) *
              (if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
                  (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 1 then conj (resAt (γ 3)) else 0))) := by
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hlim_decomp i j]
      ring
    rw [hexpand, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, hdiag,
      show (∑ k : Fin 4,
          (resAt (γ k) *
            ∑ i : ι, ∑ j : ι,
              if (pts i).1 - (pts j).1 = (if k = 0 then 1 else 0) ∧
                 (pts i).2.1 - (pts j).2.1 = (if k = 1 then 1 else 0) ∧
                 (pts i).2.2.1 - (pts j).2.2.1 = (if k = 2 then 1 else 0) ∧
                 (pts i).2.2.2 - (pts j).2.2.2 = (if k = 3 then 1 else 0)
              then w j * conj (w i) else 0).re) =
        (resAt (γ 0) * ∑ i : ι, ∑ j : ι,
            if (pts i).1 - (pts j).1 = 1 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
               (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0
            then w j * conj (w i) else 0).re +
        (resAt (γ 1) * ∑ i : ι, ∑ j : ι,
            if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 1 ∧
               (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0
            then w j * conj (w i) else 0).re +
        (resAt (γ 2) * ∑ i : ι, ∑ j : ι,
            if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
               (pts i).2.2.1 - (pts j).2.2.1 = 1 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 0
            then w j * conj (w i) else 0).re +
        (resAt (γ 3) * ∑ i : ι, ∑ j : ι,
            if (pts i).1 - (pts j).1 = 0 ∧ (pts i).2.1 - (pts j).2.1 = 0 ∧
               (pts i).2.2.1 - (pts j).2.2.1 = 0 ∧ (pts i).2.2.2 - (pts j).2.2.2 = 1
            then w j * conj (w i) else 0).re by
        rw [Fin.sum_univ_four]; simp]
    have he0 := hedge 1 0 0 0 (resAt (γ 0))
    have he1 := hedge 0 1 0 0 (resAt (γ 1))
    have he2 := hedge 0 0 1 0 (resAt (γ 2))
    have he3 := hedge 0 0 0 1 (resAt (γ 3))
    simp only [neg_zero] at he0 he1 he2 he3
    rw [he0, he1, he2, he3]
    ring
  linarith

/-! === Block 4: Pure-kernel interval arithmetic engine and certified positivity contradiction -/

def Sval : ℤ := 10000000000000

lemma Sval_int_pos : (0 : ℤ) < Sval := by decide

lemma Sval_pos : (0 : ℝ) < (Sval : ℝ) := by
  have : (0 : ℤ) < Sval := Sval_int_pos
  exact_mod_cast this

def ediv (a b : ℤ) : ℤ := a / b
def cdiv (a b : ℤ) : ℤ := (a + b - 1) / b

lemma mul_ediv_le_self (a : ℤ) {b : ℤ} (hb : 0 < b) : b * ediv a b ≤ a := by
  have h1 := Int.mul_ediv_add_emod a b
  have h2 := Int.emod_nonneg a hb.ne'
  dsimp only [ediv]; omega

lemma self_lt_mul_ediv_add (a : ℤ) {b : ℤ} (hb : 0 < b) : a < b * ediv a b + b := by
  have h1 := Int.mul_ediv_add_emod a b
  have h2 := Int.emod_lt_of_pos a hb
  dsimp only [ediv]; omega

lemma self_le_mul_cdiv (a : ℤ) {b : ℤ} (hb : 0 < b) : a ≤ b * cdiv a b := by
  have h1 := Int.mul_ediv_add_emod (a + b - 1) b
  have h2 := Int.emod_lt_of_pos (a + b - 1) hb
  dsimp only [cdiv]; omega

lemma ediv_le_div (a : ℤ) {b : ℤ} (hb : 0 < b) : (ediv a b : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  have h : (b * ediv a b : ℤ) ≤ a := mul_ediv_le_self a hb
  have h' : (b : ℝ) * (ediv a b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  linarith

lemma abs_ediv_sub_div_le_one (a : ℤ) {b : ℤ} (hb : 0 < b) :
    |(ediv a b : ℝ) - (a : ℝ) / (b : ℝ)| ≤ 1 := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h1 := ediv_le_div a hb
  have h2 : (a : ℝ) < (b : ℝ) * (ediv a b : ℝ) + (b : ℝ) := by
    have := self_lt_mul_ediv_add a hb
    exact_mod_cast this
  have h3 : (a : ℝ) / (b : ℝ) - 1 ≤ (ediv a b : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hb']; linarith
  rw [abs_le]; constructor <;> linarith

lemma div_le_cdiv (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ (cdiv a b : ℝ) := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have h : a ≤ (b * cdiv a b : ℤ) := self_le_mul_cdiv a hb
  have h' : (a : ℝ) ≤ (b : ℝ) * (cdiv a b : ℝ) := by exact_mod_cast h
  linarith

structure Ival where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

structure Cval where
  re : Ival
  im : Ival
  deriving DecidableEq

def Ival.mem (I : Ival) (x : ℝ) : Prop :=
  (I.lo : ℝ) / (Sval : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) / (Sval : ℝ)

def Cval.mem (C : Cval) (z : ℂ) : Prop :=
  C.re.mem z.re ∧ C.im.mem z.im

def strictInt {α : Type} (x : ℤ) (k : ℤ → α) : α :=
  match x with
  | Int.ofNat n => k (Int.ofNat n)
  | Int.negSucc n => k (Int.negSucc n)

lemma strictInt_eq {α : Type} (x : ℤ) (k : ℤ → α) : strictInt x k = k x := by
  cases x <;> rfl

def strictIval {α : Type} (x : Ival) (k : Ival → α) : α :=
  match x with
  | ⟨Int.ofNat a, Int.ofNat b⟩ => k ⟨Int.ofNat a, Int.ofNat b⟩
  | ⟨Int.ofNat a, Int.negSucc b⟩ => k ⟨Int.ofNat a, Int.negSucc b⟩
  | ⟨Int.negSucc a, Int.ofNat b⟩ => k ⟨Int.negSucc a, Int.ofNat b⟩
  | ⟨Int.negSucc a, Int.negSucc b⟩ => k ⟨Int.negSucc a, Int.negSucc b⟩

lemma strictIval_eq {α : Type} (x : Ival) (k : Ival → α) : strictIval x k = k x := by
  rcases x with ⟨a | a, b | b⟩ <;> rfl

def strictCval {α : Type} (z : Cval) (k : Cval → α) : α :=
  strictIval z.re fun r => strictIval z.im fun i => k ⟨r, i⟩

lemma strictCval_eq {α : Type} (z : Cval) (k : Cval → α) : strictCval z k = k z := by
  rcases z with ⟨r, i⟩
  simp [strictCval, strictIval_eq]

def min2 (a b : ℤ) : ℤ :=
  strictInt a fun a => strictInt b fun b => if a ≤ b then a else b

def max2 (a b : ℤ) : ℤ :=
  strictInt a fun a => strictInt b fun b => if a ≤ b then b else a

lemma min2_eq (a b : ℤ) : min2 a b = min a b := by
  simp [min2, strictInt_eq, min_def]

lemma max2_eq (a b : ℤ) : max2 a b = max a b := by
  simp only [max2, strictInt_eq, max_def]

def ivConst (n : ℤ) : Ival := ⟨n * Sval, n * Sval⟩
def ivRat (p q : ℤ) : Ival := ⟨ediv (p * Sval) q, cdiv (p * Sval) q⟩
def ivAdd (a b : Ival) : Ival := ⟨a.lo + b.lo, a.hi + b.hi⟩
def ivSub (a b : Ival) : Ival := ⟨a.lo - b.hi, a.hi - b.lo⟩
def ivNeg (a : Ival) : Ival := ⟨-a.hi, -a.lo⟩

def ivMul (a b : Ival) : Ival :=
  strictIval a fun a => strictIval b fun b =>
  strictInt (a.lo * b.lo) fun p1 =>
  strictInt (a.lo * b.hi) fun p2 =>
  strictInt (a.hi * b.lo) fun p3 =>
  strictInt (a.hi * b.hi) fun p4 =>
  ⟨ediv (min2 (min2 p1 p2) (min2 p3 p4)) Sval, cdiv (max2 (max2 p1 p2) (max2 p3 p4)) Sval⟩

def ivMulInt (k : ℤ) (a : Ival) : Ival :=
  if 0 ≤ k then ⟨k * a.lo, k * a.hi⟩ else ⟨k * a.hi, k * a.lo⟩

def ivDivNat (a : Ival) (q : ℕ) : Ival := ⟨ediv a.lo (q : ℤ), cdiv a.hi (q : ℤ)⟩
def ivInvPos (b : Ival) : Ival := ⟨ediv (Sval * Sval) b.hi, cdiv (Sval * Sval) b.lo⟩

def ivSq (a : Ival) : Ival :=
  strictIval a fun a =>
  if 0 ≤ a.lo then ⟨ediv (a.lo * a.lo) Sval, cdiv (a.hi * a.hi) Sval⟩
  else if a.hi ≤ 0 then ⟨ediv (a.hi * a.hi) Sval, cdiv (a.lo * a.lo) Sval⟩
  else ⟨0, cdiv (max2 (a.lo * a.lo) (a.hi * a.hi)) Sval⟩

def ivAbsHi (a : Ival) : ℤ :=
  strictIval a fun a => max2 (max2 a.lo (-a.lo)) (max2 a.hi (-a.hi))

lemma ivConst_mem (n : ℤ) : (ivConst n).mem (n : ℝ) := by
  have hS := Sval_pos.ne'
  constructor <;> dsimp only [ivConst] <;> push_cast <;> rw [mul_div_cancel_right₀ _ hS]

lemma ivRat_mem (p : ℤ) {q : ℤ} (hq : 0 < q) : (ivRat p q).mem ((p : ℝ) / (q : ℝ)) := by
  have hS := Sval_pos
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · have h1 := ediv_le_div (p * Sval) hq
    push_cast at h1
    rw [div_le_iff₀ hS]
    calc (ediv (p * Sval) q : ℝ) ≤ (p : ℝ) * (Sval : ℝ) / (q : ℝ) := h1
      _ = (p : ℝ) / (q : ℝ) * (Sval : ℝ) := by ring
  · have h2 := div_le_cdiv (p * Sval) hq
    push_cast at h2
    rw [le_div_iff₀ hS]
    calc (p : ℝ) / (q : ℝ) * (Sval : ℝ) = (p : ℝ) * (Sval : ℝ) / (q : ℝ) := by ring
      _ ≤ (cdiv (p * Sval) q : ℝ) := h2

lemma ivAdd_mem {a b : Ival} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) :
    (ivAdd a b).mem (x + y) := by
  constructor
  · dsimp only [ivAdd]; push_cast; rw [add_div]; linarith [ha.1, hb.1]
  · dsimp only [ivAdd]; push_cast; rw [add_div]; linarith [ha.2, hb.2]

lemma ivSub_mem {a b : Ival} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) :
    (ivSub a b).mem (x - y) := by
  constructor
  · dsimp only [ivSub]; push_cast; rw [sub_div]; linarith [ha.1, hb.2]
  · dsimp only [ivSub]; push_cast; rw [sub_div]; linarith [ha.2, hb.1]

lemma ivNeg_mem {a : Ival} {x : ℝ} (ha : a.mem x) : (ivNeg a).mem (-x) := by
  constructor
  · dsimp only [ivNeg]; push_cast; rw [neg_div]; linarith [ha.2]
  · dsimp only [ivNeg]; push_cast; rw [neg_div]; linarith [ha.1]

lemma ivMul_mem {a b : Ival} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) :
    (ivMul a b).mem (x * y) := by
  have hS := Sval_pos
  have hx1 : (a.lo : ℝ) ≤ x * (Sval : ℝ) := (div_le_iff₀ hS).mp ha.1
  have hx2 : x * (Sval : ℝ) ≤ (a.hi : ℝ) := (le_div_iff₀ hS).mp ha.2
  have hy1 : (b.lo : ℝ) ≤ y * (Sval : ℝ) := (div_le_iff₀ hS).mp hb.1
  have hy2 : y * (Sval : ℝ) ≤ (b.hi : ℝ) := (le_div_iff₀ hS).mp hb.2
  set sx := x * (Sval : ℝ)
  set sy := y * (Sval : ℝ)
  set m : ℤ := min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
  set M : ℤ := max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))
  have hm1 : (m : ℝ) ≤ (a.lo : ℝ) * (b.lo : ℝ) := by exact_mod_cast (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : (m : ℝ) ≤ (a.lo : ℝ) * (b.hi : ℝ) := by exact_mod_cast (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : (m : ℝ) ≤ (a.hi : ℝ) * (b.lo : ℝ) := by exact_mod_cast (min_le_right _ _).trans (min_le_left _ _)
  have hm4 : (m : ℝ) ≤ (a.hi : ℝ) * (b.hi : ℝ) := by exact_mod_cast (min_le_right _ _).trans (min_le_right _ _)
  have hM1 : (a.lo : ℝ) * (b.lo : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : (a.lo : ℝ) * (b.hi : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_right _ _).trans (le_max_left _ _)
  have hM3 : (a.hi : ℝ) * (b.lo : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
  have hM4 : (a.hi : ℝ) * (b.hi : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)
  have hprod_lo : (m : ℝ) ≤ sx * sy := by
    by_cases hy : 0 ≤ sy
    · have h1 : (a.lo : ℝ) * sy ≤ sx * sy := mul_le_mul_of_nonneg_right hx1 hy
      by_cases halo : 0 ≤ (a.lo : ℝ)
      · exact (hm1.trans (mul_le_mul_of_nonneg_left hy1 halo)).trans h1
      · exact (hm2.trans (mul_le_mul_of_nonpos_left hy2 (le_of_not_ge halo))).trans h1
    · have h1 : (a.hi : ℝ) * sy ≤ sx * sy := mul_le_mul_of_nonpos_right hx2 (le_of_not_ge hy)
      by_cases hahi : 0 ≤ (a.hi : ℝ)
      · exact (hm3.trans (mul_le_mul_of_nonneg_left hy1 hahi)).trans h1
      · exact (hm4.trans (mul_le_mul_of_nonpos_left hy2 (le_of_not_ge hahi))).trans h1
  have hprod_hi : sx * sy ≤ (M : ℝ) := by
    by_cases hy : 0 ≤ sy
    · have h1 : sx * sy ≤ (a.hi : ℝ) * sy := mul_le_mul_of_nonneg_right hx2 hy
      by_cases hahi : 0 ≤ (a.hi : ℝ)
      · exact h1.trans ((mul_le_mul_of_nonneg_left hy2 hahi).trans hM4)
      · exact h1.trans ((mul_le_mul_of_nonpos_left hy1 (le_of_not_ge hahi)).trans hM3)
    · have h1 : sx * sy ≤ (a.lo : ℝ) * sy := mul_le_mul_of_nonpos_right hx1 (le_of_not_ge hy)
      by_cases halo : 0 ≤ (a.lo : ℝ)
      · exact h1.trans ((mul_le_mul_of_nonneg_left hy2 halo).trans hM2)
      · exact h1.trans ((mul_le_mul_of_nonpos_left hy1 (le_of_not_ge halo)).trans hM1)
  have hmul_eq : ivMul a b = ⟨ediv m Sval, cdiv M Sval⟩ := by
    simp only [ivMul, strictIval_eq, strictInt_eq, min2_eq, max2_eq, m, M]
  rw [hmul_eq]
  constructor
  · have h1 := ediv_le_div m Sval_int_pos
    rw [div_le_iff₀ hS]
    calc (ediv m Sval : ℝ) ≤ (m : ℝ) / (Sval : ℝ) := h1
      _ ≤ (sx * sy) / (Sval : ℝ) := div_le_div_of_nonneg_right hprod_lo hS.le
      _ = x * y * (Sval : ℝ) := by dsimp only [sx, sy]; field_simp [hS.ne']
  · have h2 := div_le_cdiv M Sval_int_pos
    rw [le_div_iff₀ hS]
    calc x * y * (Sval : ℝ) = (sx * sy) / (Sval : ℝ) := by dsimp only [sx, sy]; field_simp [hS.ne']
      _ ≤ (M : ℝ) / (Sval : ℝ) := div_le_div_of_nonneg_right hprod_hi hS.le
      _ ≤ (cdiv M Sval : ℝ) := h2

lemma ivMulInt_mem (k : ℤ) {a : Ival} {x : ℝ} (ha : a.mem x) :
    (ivMulInt k a).mem ((k : ℝ) * x) := by
  dsimp only [ivMulInt]
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    constructor
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left ha.1 hk'
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left ha.2 hk'
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk)
    constructor
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left ha.2 hk'
    · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left ha.1 hk'

lemma ivDivNat_mem {a : Ival} {x : ℝ} (ha : a.mem x) {q : ℕ} (hq : 0 < q) :
    (ivDivNat a q).mem (x / (q : ℝ)) := by
  have hS := Sval_pos
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · have h1 := ediv_le_div a.lo hqZ
    calc (ediv a.lo (q : ℤ) : ℝ) / (Sval : ℝ)
        ≤ ((a.lo : ℝ) / (q : ℝ)) / (Sval : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hS.le
          simpa using h1
      _ = ((a.lo : ℝ) / (Sval : ℝ)) / (q : ℝ) := by ring
      _ ≤ x / (q : ℝ) := div_le_div_of_nonneg_right ha.1 hqR.le
  · have h2 := div_le_cdiv a.hi hqZ
    calc x / (q : ℝ)
        ≤ ((a.hi : ℝ) / (Sval : ℝ)) / (q : ℝ) := div_le_div_of_nonneg_right ha.2 hqR.le
      _ = ((a.hi : ℝ) / (q : ℝ)) / (Sval : ℝ) := by ring
      _ ≤ (cdiv a.hi (q : ℤ) : ℝ) / (Sval : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hS.le
          simpa using h2

lemma ivInvPos_mem {b : Ival} {y : ℝ} (hb : b.mem y) (hpos : 0 < b.lo) :
    0 < y ∧ (ivInvPos b).mem y⁻¹ := by
  have hS := Sval_pos
  have hlo : (0 : ℝ) < (b.lo : ℝ) := by exact_mod_cast hpos
  have hy_pos : 0 < y := lt_of_lt_of_le (div_pos hlo hS) hb.1
  have hhi : (0 : ℝ) < (b.hi : ℝ) := by
    have : (b.lo : ℝ) / (Sval : ℝ) ≤ (b.hi : ℝ) / (Sval : ℝ) := hb.1.trans hb.2
    have : (b.lo : ℝ) ≤ (b.hi : ℝ) := by rwa [div_le_div_iff_of_pos_right hS] at this
    linarith
  have hhiZ : (0 : ℤ) < b.hi := by exact_mod_cast hhi
  refine ⟨hy_pos, ?_, ?_⟩
  · have h1 := ediv_le_div (Sval * Sval) hhiZ
    push_cast at h1
    calc (ediv (Sval * Sval) b.hi : ℝ) / (Sval : ℝ)
        ≤ ((Sval : ℝ) * (Sval : ℝ) / (b.hi : ℝ)) / (Sval : ℝ) := div_le_div_of_nonneg_right h1 hS.le
      _ = ((b.hi : ℝ) / (Sval : ℝ))⁻¹ := by field_simp [hS.ne', hhi.ne']
      _ ≤ y⁻¹ := inv_anti₀ hy_pos hb.2
  · have h2 := div_le_cdiv (Sval * Sval) hpos
    push_cast at h2
    calc y⁻¹ ≤ ((b.lo : ℝ) / (Sval : ℝ))⁻¹ := inv_anti₀ (div_pos hlo hS) hb.1
      _ = ((Sval : ℝ) * (Sval : ℝ) / (b.lo : ℝ)) / (Sval : ℝ) := by field_simp [hS.ne', hlo.ne']
      _ ≤ (cdiv (Sval * Sval) b.lo : ℝ) / (Sval : ℝ) := div_le_div_of_nonneg_right h2 hS.le

lemma ivSq_mem {a : Ival} {x : ℝ} (ha : a.mem x) : (ivSq a).mem (x * x) := by
  have hS := Sval_pos
  have hx1 : (a.lo : ℝ) ≤ x * (Sval : ℝ) := (div_le_iff₀ hS).mp ha.1
  have hx2 : x * (Sval : ℝ) ≤ (a.hi : ℝ) := (le_div_iff₀ hS).mp ha.2
  simp only [ivSq, strictIval_eq, max2_eq]
  split_ifs with h1 h2
  · have h1' : (0 : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast h1
    constructor
    · have hed := ediv_le_div (a.lo * a.lo) Sval_int_pos
      push_cast at hed
      rw [div_le_iff₀ hS]
      calc (ediv (a.lo * a.lo) Sval : ℝ) ≤ ((a.lo : ℝ) * (a.lo : ℝ)) / (Sval : ℝ) := hed
        _ ≤ ((x * (Sval : ℝ)) * (x * (Sval : ℝ))) / (Sval : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul hx1 hx1 h1' (by linarith)) hS.le
        _ = x * x * (Sval : ℝ) := by field_simp [hS.ne']
    · have hcd := div_le_cdiv (a.hi * a.hi) Sval_int_pos
      push_cast at hcd
      rw [le_div_iff₀ hS]
      calc x * x * (Sval : ℝ) = ((x * (Sval : ℝ)) * (x * (Sval : ℝ))) / (Sval : ℝ) := by
            field_simp [hS.ne']
        _ ≤ ((a.hi : ℝ) * (a.hi : ℝ)) / (Sval : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul hx2 hx2 (by linarith) (by linarith)) hS.le
        _ ≤ (cdiv (a.hi * a.hi) Sval : ℝ) := hcd
  · have h2' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast h2
    constructor
    · have hed := ediv_le_div (a.hi * a.hi) Sval_int_pos
      push_cast at hed
      rw [div_le_iff₀ hS]
      calc (ediv (a.hi * a.hi) Sval : ℝ) ≤ ((a.hi : ℝ) * (a.hi : ℝ)) / (Sval : ℝ) := hed
        _ ≤ ((x * (Sval : ℝ)) * (x * (Sval : ℝ))) / (Sval : ℝ) :=
            div_le_div_of_nonneg_right (by nlinarith) hS.le
        _ = x * x * (Sval : ℝ) := by field_simp [hS.ne']
    · have hcd := div_le_cdiv (a.lo * a.lo) Sval_int_pos
      push_cast at hcd
      rw [le_div_iff₀ hS]
      calc x * x * (Sval : ℝ) = ((x * (Sval : ℝ)) * (x * (Sval : ℝ))) / (Sval : ℝ) := by
            field_simp [hS.ne']
        _ ≤ ((a.lo : ℝ) * (a.lo : ℝ)) / (Sval : ℝ) :=
            div_le_div_of_nonneg_right (by nlinarith) hS.le
        _ ≤ (cdiv (a.lo * a.lo) Sval : ℝ) := hcd
  · constructor
    · rw [Int.cast_zero, zero_div]; exact mul_self_nonneg x
    · set M : ℤ := max (a.lo * a.lo) (a.hi * a.hi)
      have hM1 : (a.lo : ℝ) * (a.lo : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left (a.lo * a.lo) (a.hi * a.hi)
      have hM2 : (a.hi : ℝ) * (a.hi : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_right (a.lo * a.lo) (a.hi * a.hi)
      have hsq : (x * (Sval : ℝ)) * (x * (Sval : ℝ)) ≤ (M : ℝ) := by
        by_cases hx : 0 ≤ x * (Sval : ℝ)
        · exact (mul_le_mul hx2 hx2 hx (by linarith)).trans hM2
        · exact (by nlinarith : (x * (Sval : ℝ)) * (x * (Sval : ℝ)) ≤ (a.lo : ℝ) * (a.lo : ℝ)).trans hM1
      have hcd := div_le_cdiv M Sval_int_pos
      rw [le_div_iff₀ hS]
      calc x * x * (Sval : ℝ) = ((x * (Sval : ℝ)) * (x * (Sval : ℝ))) / (Sval : ℝ) := by
            field_simp [hS.ne']
        _ ≤ (M : ℝ) / (Sval : ℝ) := div_le_div_of_nonneg_right hsq hS.le
        _ ≤ (cdiv M Sval : ℝ) := hcd

lemma ivSq_lo_nonneg (a : Ival) : 0 ≤ (ivSq a).lo := by
  simp only [ivSq, strictIval_eq]
  split_ifs with h1 h2
  · exact Int.ediv_nonneg (mul_self_nonneg a.lo) Sval_int_pos.le
  · exact Int.ediv_nonneg (mul_self_nonneg a.hi) Sval_int_pos.le
  · exact le_rfl

lemma abs_le_ivAbsHi {a : Ival} {x : ℝ} (ha : a.mem x) :
    |x| ≤ (ivAbsHi a : ℝ) / (Sval : ℝ) := by
  have hS := Sval_pos
  set M : ℤ := max (max a.lo (-a.lo)) (max a.hi (-a.hi))
  have heq : ivAbsHi a = M := by
    simp [ivAbsHi, strictIval_eq, max2_eq, M]
  rw [heq, abs_le]
  have h1 : (-a.lo : ℤ) ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have h2 : a.hi ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h1' : -(a.lo : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
  have h2' : (a.hi : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
  constructor
  · have : -((M : ℝ) / (Sval : ℝ)) ≤ (a.lo : ℝ) / (Sval : ℝ) := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hS.le
    linarith [ha.1]
  · exact ha.2.trans (div_le_div_of_nonneg_right h2' hS.le)

def cvAdd (z w : Cval) : Cval := ⟨ivAdd z.re w.re, ivAdd z.im w.im⟩
def cvSub (z w : Cval) : Cval := ⟨ivSub z.re w.re, ivSub z.im w.im⟩
def cvNeg (z : Cval) : Cval := ⟨ivNeg z.re, ivNeg z.im⟩

def cvMul (z w : Cval) : Cval :=
  ⟨ivSub (ivMul z.re w.re) (ivMul z.im w.im),
   ivAdd (ivMul z.re w.im) (ivMul z.im w.re)⟩

def cvSq (z : Cval) : Cval :=
  strictCval z fun z => ⟨ivSub (ivSq z.re) (ivSq z.im), ivMulInt 2 (ivMul z.re z.im)⟩

def cvScale (r : Ival) (z : Cval) : Cval := ⟨ivMul r z.re, ivMul r z.im⟩
def cvDivNat (z : Cval) (q : ℕ) : Cval := ⟨ivDivNat z.re q, ivDivNat z.im q⟩
def cvNormSq (z : Cval) : Ival := ivAdd (ivSq z.re) (ivSq z.im)
def cvNormL1Hi (z : Cval) : ℤ := ivAbsHi z.re + ivAbsHi z.im

def cvInv (z : Cval) : Cval :=
  let invN2 := ivInvPos (cvNormSq z)
  ⟨ivMul z.re invN2, ivMul (ivNeg z.im) invN2⟩

def cvDiv (z w : Cval) : Cval := cvMul z (cvInv w)

def cvExpand (z : Cval) (e : ℤ) : Cval :=
  ⟨⟨z.re.lo - e, z.re.hi + e⟩, ⟨z.im.lo - e, z.im.hi + e⟩⟩

lemma cvAdd_mem {C D : Cval} {z w : ℂ} (hC : C.mem z) (hD : D.mem w) :
    (cvAdd C D).mem (z + w) :=
  ⟨by simpa [cvAdd] using ivAdd_mem hC.1 hD.1, by simpa [cvAdd] using ivAdd_mem hC.2 hD.2⟩

lemma cvSub_mem {C D : Cval} {z w : ℂ} (hC : C.mem z) (hD : D.mem w) :
    (cvSub C D).mem (z - w) :=
  ⟨by simpa [cvSub] using ivSub_mem hC.1 hD.1, by simpa [cvSub] using ivSub_mem hC.2 hD.2⟩

lemma cvNeg_mem {C : Cval} {z : ℂ} (hC : C.mem z) : (cvNeg C).mem (-z) :=
  ⟨by simpa [cvNeg] using ivNeg_mem hC.1, by simpa [cvNeg] using ivNeg_mem hC.2⟩

lemma cvMul_mem {C D : Cval} {z w : ℂ} (hC : C.mem z) (hD : D.mem w) :
    (cvMul C D).mem (z * w) :=
  ⟨by simpa [cvMul, Complex.mul_re] using ivSub_mem (ivMul_mem hC.1 hD.1) (ivMul_mem hC.2 hD.2),
   by simpa [cvMul, Complex.mul_im] using ivAdd_mem (ivMul_mem hC.1 hD.2) (ivMul_mem hC.2 hD.1)⟩

lemma cvSq_mem {C : Cval} {z : ℂ} (hC : C.mem z) : (cvSq C).mem (z * z) := by
  simp only [cvSq, strictCval_eq]
  refine ⟨?_, ?_⟩
  · simpa [Complex.mul_re] using ivSub_mem (ivSq_mem hC.1) (ivSq_mem hC.2)
  · have him : (z * z).im = (2 : ℝ) * (z.re * z.im) := by simp [Complex.mul_im]; ring
    rw [him]
    simpa using ivMulInt_mem 2 (ivMul_mem hC.1 hC.2)

lemma cvScale_mem {R : Ival} {C : Cval} {r : ℝ} {z : ℂ} (hR : R.mem r) (hC : C.mem z) :
    (cvScale R C).mem ((r : ℂ) * z) :=
  ⟨by simpa [cvScale, Complex.mul_re] using ivMul_mem hR hC.1,
   by simpa [cvScale, Complex.mul_im] using ivMul_mem hR hC.2⟩

lemma cvDivNat_mem {C : Cval} {z : ℂ} (hC : C.mem z) {q : ℕ} (hq : 0 < q) :
    (cvDivNat C q).mem (z / (q : ℂ)) := by
  have hre : (z / (q : ℂ)).re = z.re / (q : ℝ) := by
    rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_re]
  have him : (z / (q : ℂ)).im = z.im / (q : ℝ) := by
    rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_im]
  exact ⟨by rw [hre]; exact ivDivNat_mem hC.1 hq, by rw [him]; exact ivDivNat_mem hC.2 hq⟩

lemma cvNormSq_mem {C : Cval} {z : ℂ} (hC : C.mem z) :
    (cvNormSq C).mem (Complex.normSq z) := by
  simpa [cvNormSq, Complex.normSq_apply] using ivAdd_mem (ivSq_mem hC.1) (ivSq_mem hC.2)

lemma norm_le_cvNormL1Hi {C : Cval} {z : ℂ} (hC : C.mem z) :
    ‖z‖ ≤ (cvNormL1Hi C : ℝ) / (Sval : ℝ) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im z
  have h2 := abs_le_ivAbsHi hC.1
  have h3 := abs_le_ivAbsHi hC.2
  dsimp only [cvNormL1Hi]
  push_cast
  rw [add_div]
  linarith

lemma cvNormL1Hi_mem_upper {C : Cval} {z : ℂ} (hC : C.mem z) :
    Ival.mem ⟨0, cvNormL1Hi C⟩ ‖z‖ :=
  ⟨by rw [Int.cast_zero, zero_div]; exact norm_nonneg z, norm_le_cvNormL1Hi hC⟩

lemma cvInv_mem {C : Cval} {z : ℂ} (hC : C.mem z) (hpos : 0 < (cvNormSq C).lo) :
    z ≠ 0 ∧ (cvInv C).mem z⁻¹ := by
  have ⟨hnpos, hinv⟩ := ivInvPos_mem (cvNormSq_mem hC) hpos
  have hzne : z ≠ 0 := by intro h; rw [h, _root_.map_zero] at hnpos; linarith
  refine ⟨hzne, ?_, ?_⟩
  · have hre : z⁻¹.re = z.re * (Complex.normSq z)⁻¹ := by
      rw [Complex.inv_re, div_eq_mul_inv]
    rw [hre]; exact ivMul_mem hC.1 hinv
  · have him : z⁻¹.im = (-z.im) * (Complex.normSq z)⁻¹ := by
      rw [Complex.inv_im, neg_div, div_eq_mul_inv, neg_mul]
    rw [him]; exact ivMul_mem (ivNeg_mem hC.2) hinv

lemma cvDiv_mem {C D : Cval} {z w : ℂ} (hC : C.mem z) (hD : D.mem w)
    (hpos : 0 < (cvNormSq D).lo) :
    w ≠ 0 ∧ (cvDiv C D).mem (z / w) := by
  obtain ⟨hwne, hinv⟩ := cvInv_mem hD hpos
  exact ⟨hwne, by rw [div_eq_mul_inv]; exact cvMul_mem hC hinv⟩

lemma cvExpand_mem {C : Cval} {w z : ℂ} {e : ℤ} (hC : C.mem w)
    (herr : ‖z - w‖ ≤ (e : ℝ) / (Sval : ℝ)) : (cvExpand C e).mem z := by
  have hre0 : |z.re - w.re| ≤ ‖z - w‖ := by simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
  have him0 : |z.im - w.im| ≤ ‖z - w‖ := by simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - w)
  have hre : |z.re - w.re| ≤ (e : ℝ) / (Sval : ℝ) := hre0.trans herr
  have him : |z.im - w.im| ≤ (e : ℝ) / (Sval : ℝ) := him0.trans herr
  rw [abs_le] at hre him
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp only [cvExpand] <;> push_cast
  · rw [sub_div]; linarith [hC.1.1, hre.1]
  · rw [add_div]; linarith [hC.1.2, hre.2]
  · rw [sub_div]; linarith [hC.2.1, him.1]
  · rw [add_div]; linarith [hC.2.2, him.2]

/-! == Elementary functions (`exp`, scalar-midpoint quadrant-reduced `exp(i·θ)`) -/

def piHalfMid : ℤ := 15707963267949

def ivExpSmallAux : ℕ → Ival → Ival → Ival
  | 0, _, acc => acc
  | k + 1, u, acc =>
      strictIval (ivAdd (ivConst 1) (ivDivNat (ivMul u acc) (k + 1))) fun next =>
      ivExpSmallAux k u next

def ivExpSmall (u : Ival) : Ival :=
  let acc := ivExpSmallAux 15 u (ivConst 1)
  ⟨acc.lo - 1, acc.hi + 1⟩

noncomputable def realExpHorner : ℕ → ℝ → ℝ → ℝ
  | 0, _, acc => acc
  | k + 1, x, acc => realExpHorner k x (1 + x * acc / ((k + 1 : ℕ) : ℝ))

lemma ivExpSmallAux_mem (k : ℕ) {u acc : Ival} {x y : ℝ} (hu : u.mem x) (hacc : acc.mem y) :
    (ivExpSmallAux k u acc).mem (realExpHorner k x y) := by
  induction k generalizing acc y with
  | zero => exact hacc
  | succ k ih =>
    simp only [ivExpSmallAux, strictIval_eq, realExpHorner]
    refine ih (ivAdd_mem (by simpa using ivConst_mem 1)
      (ivDivNat_mem (ivMul_mem hu hacc) (Nat.succ_pos k)))

lemma realExpHorner_15 (x : ℝ) :
    realExpHorner 15 x 1 = ∑ m ∈ Finset.range 16, x ^ m / (m.factorial : ℝ) := by
  simp only [realExpHorner, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring

lemma ivExpSmall_mem {u : Ival} {x : ℝ} (hu : u.mem x) (hx : |x| ≤ 7 / 10) :
    (ivExpSmall u).mem (Real.exp x) := by
  have hhorner := ivExpSmallAux_mem 15 hu (by simpa using ivConst_mem 1)
  rw [realExpHorner_15] at hhorner
  have hb := Real.exp_bound (x := x) (by linarith) (n := 16) (by norm_num)
  have herr : |Real.exp x - ∑ m ∈ Finset.range 16, x ^ m / (m.factorial : ℝ)| ≤ 1 / (Sval : ℝ) := by
    calc |Real.exp x - ∑ m ∈ Finset.range 16, x ^ m / (m.factorial : ℝ)|
        ≤ |x| ^ 16 * ((Nat.succ 16 : ℝ) / ((Nat.factorial 16 : ℝ) * (16 : ℝ))) := hb
      _ ≤ (7 / 10 : ℝ) ^ 16 * ((Nat.succ 16 : ℝ) / ((Nat.factorial 16 : ℝ) * (16 : ℝ))) := by
          gcongr
      _ ≤ 1 / (Sval : ℝ) := by norm_num [Sval, Nat.factorial]
  rw [abs_le] at herr
  constructor <;> dsimp only [ivExpSmall] <;> push_cast
  · rw [sub_div]; linarith [hhorner.1, herr.1]
  · rw [add_div]; linarith [hhorner.2, herr.2]

def scCosHorner : ℕ → ℤ → ℤ → ℤ
  | 0, _, acc => acc
  | j + 1, u2, acc =>
      strictInt (Sval - ediv (u2 * acc) ((((2 * j + 1) * (2 * j + 2) : ℕ) : ℤ) * Sval)) fun next =>
      scCosHorner j u2 next

def scSinHorner : ℕ → ℤ → ℤ → ℤ
  | 0, _, acc => acc
  | j + 1, u2, acc =>
      strictInt (Sval - ediv (u2 * acc) ((((2 * j + 2) * (2 * j + 3) : ℕ) : ℤ) * Sval)) fun next =>
      scSinHorner j u2 next

noncomputable def realCosHorner : ℕ → ℝ → ℝ → ℝ
  | 0, _, acc => acc
  | j + 1, x2, acc => realCosHorner j x2 (1 - x2 * acc / (((2 * j + 1) * (2 * j + 2) : ℕ) : ℝ))

noncomputable def realSinHorner : ℕ → ℝ → ℝ → ℝ
  | 0, _, acc => acc
  | j + 1, x2, acc => realSinHorner j x2 (1 - x2 * acc / (((2 * j + 2) * (2 * j + 3) : ℕ) : ℝ))

lemma scHorner_step_err {u2 accI : ℤ} {x2 accR : ℝ} {d : ℕ}
    (hd : 2 ≤ d) (hx2_nonneg : 0 ≤ x2) (hx2_le : x2 ≤ 16 / 25)
    (hu2_nonneg : 0 ≤ u2) (hu2_le : (u2 : ℝ) / (Sval : ℝ) ≤ 16 / 25)
    (hu2_err : |(u2 : ℝ) / (Sval : ℝ) - x2| ≤ 1 / (Sval : ℝ))
    (haccR : 0 ≤ accR ∧ accR ≤ 1)
    (hacc_err : |(accI : ℝ) / (Sval : ℝ) - accR| ≤ 4 / (Sval : ℝ)) :
    (0 ≤ 1 - x2 * accR / (d : ℝ) ∧ 1 - x2 * accR / (d : ℝ) ≤ 1) ∧
    |((Sval - ediv (u2 * accI) ((d : ℤ) * Sval) : ℤ) : ℝ) / (Sval : ℝ) -
      (1 - x2 * accR / (d : ℝ))| ≤ 4 / (Sval : ℝ) := by
  have hS := Sval_pos
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hdS_pos : (0 : ℤ) < (d : ℤ) * Sval := mul_pos (by exact_mod_cast (by omega : 0 < d)) Sval_int_pos
  have hterm_nonneg : 0 ≤ x2 * accR / (d : ℝ) := div_nonneg (mul_nonneg hx2_nonneg haccR.1) hdpos.le
  have hterm_le : x2 * accR / (d : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hdpos]
    nlinarith [haccR.2]
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  have hed := abs_ediv_sub_div_le_one (u2 * accI) hdS_pos
  have hu2R_nonneg : (0 : ℝ) ≤ (u2 : ℝ) / (Sval : ℝ) := div_nonneg (by exact_mod_cast hu2_nonneg) hS.le
  have hsplit :
      ((Sval - ediv (u2 * accI) ((d : ℤ) * Sval) : ℤ) : ℝ) / (Sval : ℝ) - (1 - x2 * accR / (d : ℝ)) =
      -(((ediv (u2 * accI) ((d : ℤ) * Sval) : ℝ) - ((u2 * accI : ℤ) : ℝ) / (((d : ℤ) * Sval : ℤ) : ℝ)) / (Sval : ℝ)) -
      (((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
        ((u2 : ℝ) / (Sval : ℝ) - x2) * accR) / (d : ℝ) := by
    push_cast
    field_simp [hS.ne', hdpos.ne']
    ring
  rw [hsplit]
  have h1 : |(((ediv (u2 * accI) ((d : ℤ) * Sval) : ℝ) -
      ((u2 * accI : ℤ) : ℝ) / (((d : ℤ) * Sval : ℤ) : ℝ)) / (Sval : ℝ))| ≤ 1 / (Sval : ℝ) := by
    rw [abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_right hed hS.le
  have h2 : |(((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
      ((u2 : ℝ) / (Sval : ℝ) - x2) * accR) / (d : ℝ)| ≤ 2 / (Sval : ℝ) := by
    rw [abs_div, abs_of_pos hdpos]
    have hnum : |((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
        ((u2 : ℝ) / (Sval : ℝ) - x2) * accR| ≤ 4 / (Sval : ℝ) := by
      calc |((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
              ((u2 : ℝ) / (Sval : ℝ) - x2) * accR|
          ≤ |((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR)| +
            |((u2 : ℝ) / (Sval : ℝ) - x2) * accR| := abs_add_le _ _
        _ = ((u2 : ℝ) / (Sval : ℝ)) * |(accI : ℝ) / (Sval : ℝ) - accR| +
            |(u2 : ℝ) / (Sval : ℝ) - x2| * accR := by
            rw [abs_mul, abs_mul, abs_of_nonneg hu2R_nonneg, abs_of_nonneg haccR.1]
        _ ≤ (16 / 25) * (4 / (Sval : ℝ)) + (1 / (Sval : ℝ)) * 1 := by
            have ha := mul_le_mul hu2_le hacc_err (abs_nonneg _) (by norm_num)
            have hb := mul_le_mul hu2_err haccR.2 haccR.1 (by positivity)
            linarith
        _ ≤ 4 / (Sval : ℝ) := by
            rw [show (16 / 25 : ℝ) * (4 / (Sval : ℝ)) + (1 / (Sval : ℝ)) * 1 = (89 / 25) / (Sval : ℝ) by ring]
            exact div_le_div_of_nonneg_right (by norm_num) hS.le
    calc |((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
            ((u2 : ℝ) / (Sval : ℝ) - x2) * accR| / (d : ℝ)
        ≤ (4 / (Sval : ℝ)) / 2 := div_le_div₀ (by positivity) hnum (by norm_num) hdR
      _ = 2 / (Sval : ℝ) := by ring
  calc |-(((ediv (u2 * accI) ((d : ℤ) * Sval) : ℝ) - ((u2 * accI : ℤ) : ℝ) / (((d : ℤ) * Sval : ℤ) : ℝ)) / (Sval : ℝ)) -
          (((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
            ((u2 : ℝ) / (Sval : ℝ) - x2) * accR) / (d : ℝ)|
      ≤ |-(((ediv (u2 * accI) ((d : ℤ) * Sval) : ℝ) - ((u2 * accI : ℤ) : ℝ) / (((d : ℤ) * Sval : ℤ) : ℝ)) / (Sval : ℝ))| +
        |(((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
            ((u2 : ℝ) / (Sval : ℝ) - x2) * accR) / (d : ℝ)| := abs_sub _ _
    _ = |(((ediv (u2 * accI) ((d : ℤ) * Sval) : ℝ) - ((u2 * accI : ℤ) : ℝ) / (((d : ℤ) * Sval : ℤ) : ℝ)) / (Sval : ℝ))| +
        |(((u2 : ℝ) / (Sval : ℝ)) * ((accI : ℝ) / (Sval : ℝ) - accR) +
            ((u2 : ℝ) / (Sval : ℝ) - x2) * accR) / (d : ℝ)| := by rw [abs_neg]
    _ ≤ 1 / (Sval : ℝ) + 2 / (Sval : ℝ) := add_le_add h1 h2
    _ ≤ 4 / (Sval : ℝ) := by rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hS.le

lemma scCosHorner_err (j : ℕ) {u2 accI : ℤ} {x2 accR : ℝ}
    (hx2_nonneg : 0 ≤ x2) (hx2_le : x2 ≤ 16 / 25)
    (hu2_nonneg : 0 ≤ u2) (hu2_le : (u2 : ℝ) / (Sval : ℝ) ≤ 16 / 25)
    (hu2_err : |(u2 : ℝ) / (Sval : ℝ) - x2| ≤ 1 / (Sval : ℝ))
    (haccR : 0 ≤ accR ∧ accR ≤ 1)
    (hacc_err : |(accI : ℝ) / (Sval : ℝ) - accR| ≤ 4 / (Sval : ℝ)) :
    |(scCosHorner j u2 accI : ℝ) / (Sval : ℝ) - realCosHorner j x2 accR| ≤ 4 / (Sval : ℝ) := by
  induction j generalizing accI accR with
  | zero => exact hacc_err
  | succ j ih =>
    simp only [scCosHorner, strictInt_eq, realCosHorner]
    have hstep := scHorner_step_err (d := (2 * j + 1) * (2 * j + 2))
      (by nlinarith) hx2_nonneg hx2_le hu2_nonneg hu2_le hu2_err haccR hacc_err
    exact ih hstep.1 hstep.2

lemma scSinHorner_err (j : ℕ) {u2 accI : ℤ} {x2 accR : ℝ}
    (hx2_nonneg : 0 ≤ x2) (hx2_le : x2 ≤ 16 / 25)
    (hu2_nonneg : 0 ≤ u2) (hu2_le : (u2 : ℝ) / (Sval : ℝ) ≤ 16 / 25)
    (hu2_err : |(u2 : ℝ) / (Sval : ℝ) - x2| ≤ 1 / (Sval : ℝ))
    (haccR : 0 ≤ accR ∧ accR ≤ 1)
    (hacc_err : |(accI : ℝ) / (Sval : ℝ) - accR| ≤ 4 / (Sval : ℝ)) :
    |(scSinHorner j u2 accI : ℝ) / (Sval : ℝ) - realSinHorner j x2 accR| ≤ 4 / (Sval : ℝ) := by
  induction j generalizing accI accR with
  | zero => exact hacc_err
  | succ j ih =>
    simp only [scSinHorner, strictInt_eq, realSinHorner]
    have hstep := scHorner_step_err (d := (2 * j + 2) * (2 * j + 3))
      (by nlinarith) hx2_nonneg hx2_le hu2_nonneg hu2_le hu2_err haccR hacc_err
    exact ih hstep.1 hstep.2

lemma complex_expI_poly16 (x : ℝ) :
    ((realCosHorner 7 (x * x) 1 : ℝ) : ℂ) + ((x * realSinHorner 7 (x * x) 1 : ℝ) : ℂ) * I =
      ∑ m ∈ Finset.range 16, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) := by
  simp only [realCosHorner, realSinHorner, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  apply Complex.ext
  · simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  · simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring

def cvExpI (theta : Ival) : Cval :=
  strictIval theta fun theta =>
  strictInt (ediv (theta.lo + theta.hi) 2) fun m =>
  strictInt (cdiv (theta.hi - theta.lo + 1) 2) fun rad =>
  strictInt (if 0 ≤ m then ediv (m + ediv piHalfMid 2) piHalfMid
             else -ediv (-m + ediv piHalfMid 2) piHalfMid) fun q =>
  strictInt (m - q * piHalfMid) fun r =>
  strictInt (ediv (r * r) Sval) fun u2 =>
  strictInt (scCosHorner 7 u2 Sval) fun c =>
  strictInt (ediv (r * scSinHorner 7 u2 Sval) Sval) fun s =>
  strictInt (rad + (if 0 ≤ q then q else -q) + 12) fun err =>
  match q % 4 with
  | 0 => ⟨⟨c - err, c + err⟩, ⟨s - err, s + err⟩⟩
  | 1 => ⟨⟨-s - err, -s + err⟩, ⟨c - err, c + err⟩⟩
  | 2 => ⟨⟨-c - err, -c + err⟩, ⟨-s - err, -s + err⟩⟩
  | _ => ⟨⟨s - err, s + err⟩, ⟨-c - err, -c + err⟩⟩

lemma cvExpI_mem {theta : Ival} {θ : ℝ} (hθ : theta.mem θ) :
    (cvExpI theta).mem (Complex.exp ((θ : ℂ) * I)) := by
  have hS := Sval_pos
  set m : ℤ := ediv (theta.lo + theta.hi) 2
  set rad : ℤ := cdiv (theta.hi - theta.lo + 1) 2
  set q : ℤ := if 0 ≤ m then ediv (m + ediv piHalfMid 2) piHalfMid
               else -ediv (-m + ediv piHalfMid 2) piHalfMid
  set r : ℤ := m - q * piHalfMid
  set u2 : ℤ := ediv (r * r) Sval
  set c : ℤ := scCosHorner 7 u2 Sval
  set s : ℤ := ediv (r * scSinHorner 7 u2 Sval) Sval
  set err : ℤ := rad + (if 0 ≤ q then q else -q) + 12
  have hm_lo : 2 * m ≤ theta.lo + theta.hi := mul_ediv_le_self _ (by omega)
  have hm_hi : theta.lo + theta.hi ≤ 2 * m + 1 := by
    have := self_lt_mul_ediv_add (theta.lo + theta.hi) (by omega : (0 : ℤ) < 2)
    dsimp only [m]; omega
  have hrad_ge : theta.hi - theta.lo + 1 ≤ 2 * rad := self_le_mul_cdiv _ (by omega)
  have hθ_m : |θ - (m : ℝ) / (Sval : ℝ)| ≤ (rad : ℝ) / (Sval : ℝ) := by
    have h1 : (theta.lo : ℝ) ≤ θ * (Sval : ℝ) := (div_le_iff₀ hS).mp hθ.1
    have h2 : θ * (Sval : ℝ) ≤ (theta.hi : ℝ) := (le_div_iff₀ hS).mp hθ.2
    have hml : 2 * (m : ℝ) ≤ (theta.lo : ℝ) + (theta.hi : ℝ) := by exact_mod_cast hm_lo
    have hmh : (theta.lo : ℝ) + (theta.hi : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hm_hi
    have hrg : (theta.hi : ℝ) - (theta.lo : ℝ) + 1 ≤ 2 * (rad : ℝ) := by exact_mod_cast hrad_ge
    rw [abs_le]
    constructor
    · rw [← neg_div, le_sub_iff_add_le, ← add_div, div_le_iff₀ hS]; linarith
    · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hS]; linarith
  have hr_bd : -7853981633975 ≤ r ∧ r ≤ 7853981633975 := by
    dsimp only [r, q]
    split_ifs with hm
    · have h1 := Int.mul_ediv_add_emod (m + ediv piHalfMid 2) piHalfMid
      have h2 := Int.emod_nonneg (m + ediv piHalfMid 2) (by decide : piHalfMid ≠ 0)
      have h3 := Int.emod_lt_of_pos (m + ediv piHalfMid 2) (by decide : 0 < piHalfMid)
      dsimp only [ediv, piHalfMid] at h1 h2 h3 ⊢; omega
    · have h1 := Int.mul_ediv_add_emod (-m + ediv piHalfMid 2) piHalfMid
      have h2 := Int.emod_nonneg (-m + ediv piHalfMid 2) (by decide : piHalfMid ≠ 0)
      have h3 := Int.emod_lt_of_pos (-m + ediv piHalfMid 2) (by decide : 0 < piHalfMid)
      dsimp only [ediv, piHalfMid] at h1 h2 h3 ⊢; omega
  set x : ℝ := (r : ℝ) / (Sval : ℝ)
  have hx_abs : |x| ≤ 4 / 5 := by
    rw [abs_le]
    have h1 : (-7853981633975 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_bd.1
    have h2 : (r : ℝ) ≤ (7853981633975 : ℝ) := by exact_mod_cast hr_bd.2
    constructor <;> dsimp only [x]
    · rw [le_div_iff₀ hS]; dsimp only [Sval]; norm_num; linarith
    · rw [div_le_iff₀ hS]; dsimp only [Sval]; norm_num; linarith
  have hx2_nonneg : 0 ≤ x * x := mul_self_nonneg x
  have hx2_le : x * x ≤ 16 / 25 := by
    have := abs_le.mp hx_abs; nlinarith
  have hu2_nonneg : 0 ≤ u2 := Int.ediv_nonneg (mul_self_nonneg r) Sval_int_pos.le
  have hu2_err : |(u2 : ℝ) / (Sval : ℝ) - x * x| ≤ 1 / (Sval : ℝ) := by
    have hed := abs_ediv_sub_div_le_one (r * r) Sval_int_pos
    have hid : (u2 : ℝ) / (Sval : ℝ) - x * x =
        ((ediv (r * r) Sval : ℝ) - ((r * r : ℤ) : ℝ) / (Sval : ℝ)) / (Sval : ℝ) := by
      dsimp only [u2, x]; push_cast; field_simp [hS.ne']
    rw [hid, abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_right hed hS.le
  have hu2_le : (u2 : ℝ) / (Sval : ℝ) ≤ 16 / 25 := by
    have hed := ediv_le_div (r * r) Sval_int_pos
    have hid : ((r * r : ℤ) : ℝ) / (Sval : ℝ) / (Sval : ℝ) = x * x := by
      dsimp only [x]; push_cast; field_simp [hS.ne']
    calc (u2 : ℝ) / (Sval : ℝ) ≤ (((r * r : ℤ) : ℝ) / (Sval : ℝ)) / (Sval : ℝ) :=
          div_le_div_of_nonneg_right hed hS.le
      _ = x * x := hid
      _ ≤ 16 / 25 := hx2_le
  have hacc0 : |(Sval : ℝ) / (Sval : ℝ) - 1| ≤ 4 / (Sval : ℝ) := by
    rw [div_self hS.ne', sub_self, abs_zero]; positivity
  have hc_poly := scCosHorner_err 7 hx2_nonneg hx2_le hu2_nonneg hu2_le hu2_err ⟨by norm_num, le_rfl⟩ hacc0
  have hs_poly0 := scSinHorner_err 7 hx2_nonneg hx2_le hu2_nonneg hu2_le hu2_err ⟨by norm_num, le_rfl⟩ hacc0
  have hs_poly : |(s : ℝ) / (Sval : ℝ) - x * realSinHorner 7 (x * x) 1| ≤ 5 / (Sval : ℝ) := by
    have hed := abs_ediv_sub_div_le_one (r * scSinHorner 7 u2 Sval) Sval_int_pos
    have hid : (s : ℝ) / (Sval : ℝ) - x * realSinHorner 7 (x * x) 1 =
        ((ediv (r * scSinHorner 7 u2 Sval) Sval : ℝ) -
          ((r * scSinHorner 7 u2 Sval : ℤ) : ℝ) / (Sval : ℝ)) / (Sval : ℝ) +
        x * ((scSinHorner 7 u2 Sval : ℝ) / (Sval : ℝ) - realSinHorner 7 (x * x) 1) := by
      dsimp only [s, x]; push_cast; field_simp [hS.ne']; ring
    rw [hid]
    calc |((ediv (r * scSinHorner 7 u2 Sval) Sval : ℝ) -
              ((r * scSinHorner 7 u2 Sval : ℤ) : ℝ) / (Sval : ℝ)) / (Sval : ℝ) +
            x * ((scSinHorner 7 u2 Sval : ℝ) / (Sval : ℝ) - realSinHorner 7 (x * x) 1)|
        ≤ |((ediv (r * scSinHorner 7 u2 Sval) Sval : ℝ) -
              ((r * scSinHorner 7 u2 Sval : ℤ) : ℝ) / (Sval : ℝ)) / (Sval : ℝ)| +
          |x * ((scSinHorner 7 u2 Sval : ℝ) / (Sval : ℝ) - realSinHorner 7 (x * x) 1)| := abs_add_le _ _
      _ ≤ 1 / (Sval : ℝ) + (4 / 5) * (4 / (Sval : ℝ)) := by
          have h1 : |((ediv (r * scSinHorner 7 u2 Sval) Sval : ℝ) -
              ((r * scSinHorner 7 u2 Sval : ℤ) : ℝ) / (Sval : ℝ)) / (Sval : ℝ)| ≤ 1 / (Sval : ℝ) := by
            rw [abs_div, abs_of_pos hS]; exact div_le_div_of_nonneg_right hed hS.le
          have h2 : |x * ((scSinHorner 7 u2 Sval : ℝ) / (Sval : ℝ) - realSinHorner 7 (x * x) 1)| ≤
              (4 / 5) * (4 / (Sval : ℝ)) := by
            rw [abs_mul]; exact mul_le_mul hx_abs hs_poly0 (abs_nonneg _) (by norm_num)
          linarith
      _ ≤ 5 / (Sval : ℝ) := by
          rw [show (1 : ℝ) / (Sval : ℝ) + (4 / 5) * (4 / (Sval : ℝ)) = (21 / 5) / (Sval : ℝ) by ring]
          exact div_le_div_of_nonneg_right (by norm_num) hS.le
  -- Compare polynomial with Complex.exp (x * I)
  have hnorm_xI : ‖(x : ℂ) * I‖ = |x| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have htail := Complex.exp_bound' (x := (x : ℂ) * I) (n := 16) (by rw [hnorm_xI]; linarith)
  rw [← complex_expI_poly16 x, hnorm_xI] at htail
  have htail_bd : ‖Complex.exp ((x : ℂ) * I) -
      (((realCosHorner 7 (x * x) 1 : ℝ) : ℂ) + ((x * realSinHorner 7 (x * x) 1 : ℝ) : ℂ) * I)‖ ≤
      1 / (Sval : ℝ) := by
    calc _ ≤ |x| ^ 16 / (Nat.factorial 16 : ℝ) * 2 := htail
      _ ≤ (4 / 5 : ℝ) ^ 16 / (Nat.factorial 16 : ℝ) * 2 := by gcongr
      _ ≤ 1 / (Sval : ℝ) := by norm_num [Sval, Nat.factorial]
  have hre_tail : |(Complex.exp ((x : ℂ) * I)).re - realCosHorner 7 (x * x) 1| ≤ 1 / (Sval : ℝ) := by
    have h1 := Complex.abs_re_le_norm (Complex.exp ((x : ℂ) * I) -
      (((realCosHorner 7 (x * x) 1 : ℝ) : ℂ) + ((x * realSinHorner 7 (x * x) 1 : ℝ) : ℂ) * I))
    simpa using h1.trans htail_bd
  have him_tail : |(Complex.exp ((x : ℂ) * I)).im - x * realSinHorner 7 (x * x) 1| ≤ 1 / (Sval : ℝ) := by
    have h1 := Complex.abs_im_le_norm (Complex.exp ((x : ℂ) * I) -
      (((realCosHorner 7 (x * x) 1 : ℝ) : ℂ) + ((x * realSinHorner 7 (x * x) 1 : ℝ) : ℂ) * I))
    simpa using h1.trans htail_bd
  have hc_err : |(Complex.exp ((x : ℂ) * I)).re - (c : ℝ) / (Sval : ℝ)| ≤ 5 / (Sval : ℝ) := by
    have htri := abs_add_le ((Complex.exp ((x : ℂ) * I)).re - realCosHorner 7 (x * x) 1)
      (realCosHorner 7 (x * x) 1 - (c : ℝ) / (Sval : ℝ))
    rw [abs_sub_comm (realCosHorner 7 (x * x) 1)] at htri
    have hid : (Complex.exp ((x : ℂ) * I)).re - (c : ℝ) / (Sval : ℝ) =
        ((Complex.exp ((x : ℂ) * I)).re - realCosHorner 7 (x * x) 1) +
        (realCosHorner 7 (x * x) 1 - (c : ℝ) / (Sval : ℝ)) := by ring
    have hsum5 : (1 : ℝ) / (Sval : ℝ) + 4 / (Sval : ℝ) = 5 / (Sval : ℝ) := by ring
    dsimp only [c] at hid htri ⊢
    rw [hid]; linarith [htri, hre_tail, hc_poly, hsum5]
  have hs_err : |(Complex.exp ((x : ℂ) * I)).im - (s : ℝ) / (Sval : ℝ)| ≤ 6 / (Sval : ℝ) := by
    have htri := abs_add_le ((Complex.exp ((x : ℂ) * I)).im - x * realSinHorner 7 (x * x) 1)
      (x * realSinHorner 7 (x * x) 1 - (s : ℝ) / (Sval : ℝ))
    rw [abs_sub_comm (x * realSinHorner 7 (x * x) 1)] at htri
    have hid : (Complex.exp ((x : ℂ) * I)).im - (s : ℝ) / (Sval : ℝ) =
        ((Complex.exp ((x : ℂ) * I)).im - x * realSinHorner 7 (x * x) 1) +
        (x * realSinHorner 7 (x * x) 1 - (s : ℝ) / (Sval : ℝ)) := by ring
    have hsum6 : (1 : ℝ) / (Sval : ℝ) + 5 / (Sval : ℝ) = 6 / (Sval : ℝ) := by ring
    rw [hid]; linarith [htri, him_tail, hs_poly, hsum6]
  -- Compare exp(θ * I) with exp((x + q * π/2) * I)
  have hpi_err : |(piHalfMid : ℝ) / (Sval : ℝ) - Real.pi / 2| ≤ 1 / (Sval : ℝ) := by
    have h1 := Real.pi_gt_d20
    have h2 := Real.pi_lt_d20
    rw [abs_le]; dsimp only [piHalfMid, Sval]
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  have hθ_shift : |θ - (x + (q : ℝ) * (Real.pi / 2))| ≤
      ((rad + (if 0 ≤ q then q else -q) : ℤ) : ℝ) / (Sval : ℝ) := by
    have hqabs : |(q : ℝ)| = (((if 0 ≤ q then q else -q) : ℤ) : ℝ) := by
      split_ifs with hq
      · exact abs_of_nonneg (by exact_mod_cast hq)
      · rw [Int.cast_neg]; exact abs_of_neg (by exact_mod_cast (lt_of_not_ge hq))
    have hid : θ - (x + (q : ℝ) * (Real.pi / 2)) =
        (θ - (m : ℝ) / (Sval : ℝ)) + (q : ℝ) * ((piHalfMid : ℝ) / (Sval : ℝ) - Real.pi / 2) := by
      dsimp only [x, r]; push_cast; field_simp [hS.ne']; ring
    rw [hid]
    calc |(θ - (m : ℝ) / (Sval : ℝ)) + (q : ℝ) * ((piHalfMid : ℝ) / (Sval : ℝ) - Real.pi / 2)|
        ≤ |θ - (m : ℝ) / (Sval : ℝ)| + |(q : ℝ)| * |(piHalfMid : ℝ) / (Sval : ℝ) - Real.pi / 2| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (rad : ℝ) / (Sval : ℝ) + |(q : ℝ)| * (1 / (Sval : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hpi_err (abs_nonneg (q : ℝ))
          linarith
      _ = ((rad + (if 0 ≤ q then q else -q) : ℤ) : ℝ) / (Sval : ℝ) := by
          rw [hqabs]; push_cast; ring
  have hexp_diff : ‖Complex.exp ((θ : ℂ) * I) -
      Complex.exp (((x + (q : ℝ) * (Real.pi / 2) : ℝ) : ℂ) * I)‖ ≤
      ((rad + (if 0 ≤ q then q else -q) : ℤ) : ℝ) / (Sval : ℝ) :=
    (norm_exp_I_sub_exp_I_le θ (x + (q : ℝ) * (Real.pi / 2))).trans hθ_shift
  have hexp_rot : Complex.exp (((x + (q : ℝ) * (Real.pi / 2) : ℝ) : ℂ) * I) =
      Complex.exp ((((q % 4 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) * I) * Complex.exp ((x : ℂ) * I) := by
    rw [← Complex.exp_add]
    have hqsplit : q = 4 * (q / 4) + q % 4 := (Int.mul_ediv_add_emod q 4).symm
    have hper : Complex.exp (((x + (q : ℝ) * (Real.pi / 2) : ℝ) : ℂ) * I) =
        Complex.exp (((((q % 4 : ℤ) : ℝ) * (Real.pi / 2) + x : ℝ) : ℂ) * I +
          ((q / 4 : ℤ) : ℂ) * (2 * Real.pi * I)) := by
      congr 1
      have hqR : (q : ℂ) = 4 * ((q / 4 : ℤ) : ℂ) + ((q % 4 : ℤ) : ℂ) := by exact_mod_cast hqsplit
      push_cast; rw [hqR]; ring
    rw [hper, Complex.exp_periodic.int_mul (q / 4)]
    congr 1; push_cast; ring
  have hmod_cases : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by
    have h1 := Int.emod_nonneg q (by omega : (4 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos q (by omega : (0 : ℤ) < 4)
    omega
  have hrew : cvExpI theta = match q % 4 with
      | 0 => ⟨⟨c - err, c + err⟩, ⟨s - err, s + err⟩⟩
      | 1 => ⟨⟨-s - err, -s + err⟩, ⟨c - err, c + err⟩⟩
      | 2 => ⟨⟨-c - err, -c + err⟩, ⟨-s - err, -s + err⟩⟩
      | _ => ⟨⟨s - err, s + err⟩, ⟨-c - err, -c + err⟩⟩ := by
    simp only [cvExpI, strictIval_eq, strictInt_eq, m, rad, q, r, u2, c, s, err]
  rw [hrew]
  have hre_diff := (Complex.abs_re_le_norm _).trans hexp_diff
  have him_diff := (Complex.abs_im_le_norm _).trans hexp_diff
  rw [hexp_rot] at hre_diff him_diff
  have h56 : (5 : ℝ) / (Sval : ℝ) ≤ 6 / (Sval : ℝ) := div_le_div_of_nonneg_right (by norm_num) hS.le
  have herr_ge : ((rad + (if 0 ≤ q then q else -q) : ℤ) : ℝ) / (Sval : ℝ) + 6 / (Sval : ℝ) ≤
      (err : ℝ) / (Sval : ℝ) := by
    have h612 : (6 : ℝ) / (Sval : ℝ) ≤ 12 / (Sval : ℝ) := div_le_div_of_nonneg_right (by norm_num) hS.le
    have hsplit : (err : ℝ) / (Sval : ℝ) =
        ((rad + (if 0 ≤ q then q else -q) : ℤ) : ℝ) / (Sval : ℝ) + 12 / (Sval : ℝ) := by
      dsimp only [err]; rw [Int.cast_add, add_div]; norm_cast
    linarith
  rcases hmod_cases with hm | hm | hm | hm
  · rw [hm] at hre_diff him_diff ⊢
    simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul,
      Complex.sub_re, Complex.sub_im] at hre_diff him_diff
    rw [abs_le] at hre_diff him_diff hc_err hs_err
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast
    · rw [sub_div]; linarith
    · rw [add_div]; linarith
    · rw [sub_div]; linarith
    · rw [add_div]; linarith
  · rw [hm] at hre_diff him_diff ⊢
    have hpiI : Complex.exp ((((1 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) * I) = I := by
      simp [Complex.exp_pi_div_two_mul_I]
    rw [hpiI] at hre_diff him_diff
    simp only [Complex.sub_re, Complex.sub_im, Complex.I_mul] at hre_diff him_diff
    rw [abs_le] at hre_diff him_diff hc_err hs_err
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast
    · rw [sub_div, neg_div]; linarith
    · rw [add_div, neg_div]; linarith
    · rw [sub_div]; linarith
    · rw [add_div]; linarith
  · rw [hm] at hre_diff him_diff ⊢
    have hpiI : Complex.exp ((((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) * I) = -1 := by
      have : (((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) = Real.pi := by push_cast; ring
      rw [this, Complex.exp_pi_mul_I]
    rw [hpiI] at hre_diff him_diff
    simp only [neg_one_mul, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im] at hre_diff him_diff
    rw [abs_le] at hre_diff him_diff hc_err hs_err
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast
    · rw [sub_div, neg_div]; linarith
    · rw [add_div, neg_div]; linarith
    · rw [sub_div, neg_div]; linarith
    · rw [add_div, neg_div]; linarith
  · rw [hm] at hre_diff him_diff ⊢
    have hpiI : Complex.exp ((((3 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) * I) = -I := by
      have : ((((3 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : ℂ) * I =
          (Real.pi : ℂ) * I + (Real.pi : ℂ) / 2 * I := by push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]; ring
    rw [hpiI] at hre_diff him_diff
    simp only [neg_mul, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.I_mul, neg_neg] at hre_diff him_diff
    rw [abs_le] at hre_diff him_diff hc_err hs_err
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast
    · rw [sub_div]; linarith
    · rw [add_div]; linarith
    · rw [sub_div, neg_div]; linarith
    · rw [add_div, neg_div]; linarith

def invSqrtVal (n : ℕ) : ℤ :=
  (if n < 80 then
    (if n < 40 then
      (if n < 20 then
        (if n < 10 then
          (if n < 5 then
            (if n < 2 then
              (if n < 1 then 0 else 10000000000000)
              else
              (if n < 3 then 7071067811865 else (if n < 4 then 5773502691896 else 5000000000000)))
            else
            (if n < 7 then
              (if n < 6 then 4472135954999 else 4082482904638)
              else
              (if n < 8 then 3779644730092 else (if n < 9 then 3535533905932 else 3333333333333))))
          else
          (if n < 15 then
            (if n < 12 then
              (if n < 11 then 3162277660168 else 3015113445777)
              else
              (if n < 13 then 2886751345948 else (if n < 14 then 2773500981126 else 2672612419124)))
            else
            (if n < 17 then
              (if n < 16 then 2581988897471 else 2500000000000)
              else
              (if n < 18 then 2425356250363 else (if n < 19 then 2357022603955 else 2294157338705)))))
        else
        (if n < 30 then
          (if n < 25 then
            (if n < 22 then
              (if n < 21 then 2236067977499 else 2182178902359)
              else
              (if n < 23 then 2132007163556 else (if n < 24 then 2085144140570 else 2041241452319)))
            else
            (if n < 27 then
              (if n < 26 then 2000000000000 else 1961161351381)
              else
              (if n < 28 then 1924500897298 else (if n < 29 then 1889822365046 else 1856953381770))))
          else
          (if n < 35 then
            (if n < 32 then
              (if n < 31 then 1825741858350 else 1796053020267)
              else
              (if n < 33 then 1767766952966 else (if n < 34 then 1740776559556 else 1714985851425)))
            else
            (if n < 37 then
              (if n < 36 then 1690308509457 else 1666666666666)
              else
              (if n < 38 then 1643989873053 else (if n < 39 then 1622214211307 else 1601281538050))))))
      else
      (if n < 60 then
        (if n < 50 then
          (if n < 45 then
            (if n < 42 then
              (if n < 41 then 1581138830084 else 1561737618886)
              else
              (if n < 43 then 1543033499620 else (if n < 44 then 1524985703326 else 1507556722888)))
            else
            (if n < 47 then
              (if n < 46 then 1490711984999 else 1474419561548)
              else
              (if n < 48 then 1458649914978 else (if n < 49 then 1443375672974 else 1428571428571))))
          else
          (if n < 55 then
            (if n < 52 then
              (if n < 51 then 1414213562373 else 1400280084028)
              else
              (if n < 53 then 1386750490563 else (if n < 54 then 1373605639486 else 1360827634879)))
            else
            (if n < 57 then
              (if n < 56 then 1348399724926 else 1336306209562)
              else
              (if n < 58 then 1324532357065 else (if n < 59 then 1313064328597 else 1301889109808)))))
        else
        (if n < 70 then
          (if n < 65 then
            (if n < 62 then
              (if n < 61 then 1290994448735 else 1280368799328)
              else
              (if n < 63 then 1270001270001 else (if n < 64 then 1259881576697 else 1250000000000)))
            else
            (if n < 67 then
              (if n < 66 then 1240347345892 else 1230914909793)
              else
              (if n < 68 then 1221694443563 else (if n < 69 then 1212678125181 else 1203858530857))))
          else
          (if n < 75 then
            (if n < 72 then
              (if n < 71 then 1195228609334 else 1186781658193)
              else
              (if n < 73 then 1178511301977 else (if n < 74 then 1170411471961 else 1162476387438)))
            else
            (if n < 77 then
              (if n < 76 then 1154700538379 else 1147078669352)
              else
              (if n < 78 then 1139605764596 else (if n < 79 then 1132277034144 else 1125087900926)))))))
    else
    (if n < 120 then
      (if n < 100 then
        (if n < 90 then
          (if n < 85 then
            (if n < 82 then
              (if n < 81 then 1118033988749 else 1111111111111)
              else
              (if n < 83 then 1104315260748 else (if n < 84 then 1097642599896 else 1091089451179)))
            else
            (if n < 87 then
              (if n < 86 then 1084652289093 else 1078327732034)
              else
              (if n < 88 then 1072112534837 else (if n < 89 then 1066003581778 else 1059997880006))))
          else
          (if n < 95 then
            (if n < 92 then
              (if n < 91 then 1054092553389 else 1048284836721)
              else
              (if n < 93 then 1042572070285 else (if n < 94 then 1036951694730 else 1031421246258)))
            else
            (if n < 97 then
              (if n < 96 then 1025978352085 else 1020620726159)
              else
              (if n < 98 then 1015346165133 else (if n < 99 then 1010152544552 else 1005037815259)))))
        else
        (if n < 110 then
          (if n < 105 then
            (if n < 102 then
              (if n < 101 then 1000000000000 else 995037190209)
              else
              (if n < 103 then 990147542976 else (if n < 104 then 985329278164 else 980580675690)))
            else
            (if n < 107 then
              (if n < 106 then 975900072948 else 971285862357)
              else
              (if n < 108 then 966736489045 else (if n < 109 then 962250448649 else 957826285221))))
          else
          (if n < 115 then
            (if n < 112 then
              (if n < 111 then 953462589245 else 949157995752)
              else
              (if n < 113 then 944911182523 else (if n < 114 then 940720868383 else 936585811581)))
            else
            (if n < 117 then
              (if n < 116 then 932504808240 else 928476690885)
              else
              (if n < 118 then 924500327042 else (if n < 119 then 920574617898 else 916698497028))))))
      else
      (if n < 140 then
        (if n < 130 then
          (if n < 125 then
            (if n < 122 then
              (if n < 121 then 912870929175 else 909090909090)
              else
              (if n < 123 then 905357460425 else (if n < 124 then 901669634667 else 898026510133)))
            else
            (if n < 127 then
              (if n < 126 then 894427190999 else 890870806374)
              else
              (if n < 128 then 887356509416 else (if n < 129 then 883883476483 else 880450906325))))
          else
          (if n < 135 then
            (if n < 132 then
              (if n < 131 then 877058019307 else 873704056661)
              else
              (if n < 133 then 870388279778 else (if n < 134 then 867109969524 else 863868425581)))
            else
            (if n < 137 then
              (if n < 136 then 860662965823 else 857492925712)
              else
              (if n < 138 then 854357657716 else (if n < 139 then 851256530758 else 848188929679)))))
        else
        (if n < 150 then
          (if n < 145 then
            (if n < 142 then
              (if n < 141 then 845154254728 else 842151921066)
              else
              (if n < 143 then 839181358296 else (if n < 144 then 836242010007 else 833333333333)))
            else
            (if n < 147 then
              (if n < 146 then 830454798537 else 827605888602)
              else
              (if n < 148 then 824786098842 else (if n < 149 then 821994936526 else 819231920519))))
          else
          (if n < 155 then
            (if n < 152 then
              (if n < 151 then 816496580927 else 813788458771)
              else
              (if n < 153 then 811107105653 else (if n < 154 then 808452083454 else 805822964025)))
            else
            (if n < 158 then
              (if n < 156 then 803219328902 else (if n < 157 then 800640769025 else 798086884467))
              else
              (if n < 159 then 795557284175 else (if n < 160 then 793051585718 else 790569415042))))))))

def lnVal (n : ℕ) : ℤ :=
  (if n < 80 then
    (if n < 40 then
      (if n < 20 then
        (if n < 10 then
          (if n < 5 then
            (if n < 2 then
              (if n < 1 then 0 else 0)
              else
              (if n < 3 then 6931471805599 else (if n < 4 then 10986122886681 else 13862943611199)))
            else
            (if n < 7 then
              (if n < 6 then 16094379124341 else 17917594692281)
              else
              (if n < 8 then 19459101490553 else (if n < 9 then 20794415416798 else 21972245773362))))
          else
          (if n < 15 then
            (if n < 12 then
              (if n < 11 then 23025850929940 else 23978952727984)
              else
              (if n < 13 then 24849066497880 else (if n < 14 then 25649493574615 else 26390573296153)))
            else
            (if n < 17 then
              (if n < 16 then 27080502011022 else 27725887222398)
              else
              (if n < 18 then 28332133440562 else (if n < 19 then 28903717578962 else 29444389791664)))))
        else
        (if n < 30 then
          (if n < 25 then
            (if n < 22 then
              (if n < 21 then 29957322735540 else 30445224377234)
              else
              (if n < 23 then 30910424533583 else (if n < 24 then 31354942159291 else 31780538303479)))
            else
            (if n < 27 then
              (if n < 26 then 32188758248682 else 32580965380215)
              else
              (if n < 28 then 32958368660043 else (if n < 29 then 33322045101752 else 33672958299865))))
          else
          (if n < 35 then
            (if n < 32 then
              (if n < 31 then 34011973816622 else 34339872044851)
              else
              (if n < 33 then 34657359027997 else (if n < 34 then 34965075614665 else 35263605246162)))
            else
            (if n < 37 then
              (if n < 36 then 35553480614894 else 35835189384561)
              else
              (if n < 38 then 36109179126442 else (if n < 39 then 36375861597264 else 36635616461296))))))
      else
      (if n < 60 then
        (if n < 50 then
          (if n < 45 then
            (if n < 42 then
              (if n < 41 then 36888794541139 else 37135720667043)
              else
              (if n < 43 then 37376696182834 else (if n < 44 then 37612001156936 else 37841896339183)))
            else
            (if n < 47 then
              (if n < 46 then 38066624897703 else 38286413964891)
              else
              (if n < 48 then 38501476017101 else (if n < 49 then 38712010109079 else 38918202981106))))
          else
          (if n < 55 then
            (if n < 52 then
              (if n < 51 then 39120230054281 else 39318256327243)
              else
              (if n < 53 then 39512437185814 else (if n < 54 then 39702919135521 else 39889840465643)))
            else
            (if n < 57 then
              (if n < 56 then 40073331852325 else 40253516907352)
              else
              (if n < 58 then 40430512678346 else (if n < 59 then 40604430105464 else 40775374439057)))))
        else
        (if n < 70 then
          (if n < 65 then
            (if n < 62 then
              (if n < 61 then 40943445622221 else 41108738641733)
              else
              (if n < 63 then 41271343850451 else (if n < 64 then 41431347263915 else 41588830833597)))
            else
            (if n < 67 then
              (if n < 66 then 41743872698956 else 41896547420264)
              else
              (if n < 68 then 42046926193910 else (if n < 69 then 42195077051761 else 42341065045973))))
          else
          (if n < 75 then
            (if n < 72 then
              (if n < 71 then 42484952420494 else 42626798770413)
              else
              (if n < 73 then 42766661190161 else (if n < 74 then 42904594411484 else 43040650932042)))
            else
            (if n < 77 then
              (if n < 76 then 43174881135363 else 43307333402863)
              else
              (if n < 78 then 43438054218537 else (if n < 79 then 43567088266896 else 43694478524670)))))))
    else
    (if n < 120 then
      (if n < 100 then
        (if n < 90 then
          (if n < 85 then
            (if n < 82 then
              (if n < 81 then 43820266346739 else 43944491546724)
              else
              (if n < 83 then 44067192472643 else (if n < 84 then 44188406077966 else 44308167988433)))
            else
            (if n < 87 then
              (if n < 86 then 44426512564903 else 44543472962535)
              else
              (if n < 88 then 44659081186546 else (if n < 89 then 44773368144782 else 44886363697321))))
          else
          (if n < 95 then
            (if n < 92 then
              (if n < 91 then 44998096703303 else 45108595065168)
              else
              (if n < 93 then 45217885770490 else (if n < 94 then 45325994931533 else 45432947822700)))
            else
            (if n < 97 then
              (if n < 96 then 45538768916005 else 45643481914678)
              else
              (if n < 98 then 45747109785034 else (if n < 99 then 45849674786706 else 45951198501346)))))
        else
        (if n < 110 then
          (if n < 105 then
            (if n < 102 then
              (if n < 101 then 46051701859881 else 46151205168413)
              else
              (if n < 103 then 46249728132843 else (if n < 104 then 46347289882296 else 46443908991414)))
            else
            (if n < 107 then
              (if n < 106 then 46539603501575 else 46634390941121)
              else
              (if n < 108 then 46728288344619 else (if n < 109 then 46821312271242 else 46913478822291))))
          else
          (if n < 115 then
            (if n < 112 then
              (if n < 111 then 47004803657924 else 47095302013123)
              else
              (if n < 113 then 47184988712951 else (if n < 114 then 47273878187123 else 47361984483945)))
            else
            (if n < 117 then
              (if n < 116 then 47449321283632 else 47535901911064)
              else
              (if n < 118 then 47621739347978 else (if n < 119 then 47706846244657 else 47791234931115))))))
      else
      (if n < 140 then
        (if n < 130 then
          (if n < 125 then
            (if n < 122 then
              (if n < 121 then 47874917427820 else 47957905455967)
              else
              (if n < 123 then 48040210447333 else (if n < 124 then 48121843553724 else 48202815656050)))
            else
            (if n < 127 then
              (if n < 126 then 48283137373023 else 48362819069515)
              else
              (if n < 128 then 48441870864586 else (if n < 129 then 48520302639196 else 48598124043617))))
          else
          (if n < 135 then
            (if n < 132 then
              (if n < 131 then 48675344504556 else 48751973232012)
              else
              (if n < 133 then 48828019225864 else (if n < 134 then 48903491282218 else 48978397999509)))
            else
            (if n < 137 then
              (if n < 136 then 49052747784384 else 49126548857361)
              else
              (if n < 138 then 49199809258281 else (if n < 139 then 49272536851572 else 49344739331307)))))
        else
        (if n < 150 then
          (if n < 145 then
            (if n < 142 then
              (if n < 141 then 49416424226093 else 49487598903782)
              else
              (if n < 143 then 49558270576013 else (if n < 144 then 49628446302599 else 49698132995760)))
            else
            (if n < 147 then
              (if n < 146 then 49767337424206 else 49836066217083)
              else
              (if n < 148 then 49904325867787 else (if n < 149 then 49972122737641 else 50039463059455))))
          else
          (if n < 155 then
            (if n < 152 then
              (if n < 151 then 50106352940963 else 50172798368149)
              else
              (if n < 153 then 50238805208463 else (if n < 154 then 50304379213924 else 50369526024136)))
            else
            (if n < 158 then
              (if n < 156 then 50434251169192 else (if n < 157 then 50498560072495 else 50562458053483))
              else
              (if n < 159 then 50625950330270 else (if n < 160 then 50689042022202 else 50751738152338))))))))

def certPtVal (n : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  (if n < 34 then
    (if n < 17 then
      (if n < 8 then
        (if n < 4 then
          (if n < 2 then
            (if n < 1 then (0, 0, 0, 1) else (0, 0, 1, 1))
            else
            (if n < 3 then (0, 1, 0, 1) else (0, 1, 1, 1)))
          else
          (if n < 6 then
            (if n < 5 then (1, 0, 0, 0) else (1, 0, 0, 1))
            else
            (if n < 7 then (1, 0, 0, 2) else (1, 0, 1, 0))))
        else
        (if n < 12 then
          (if n < 10 then
            (if n < 9 then (1, 0, 1, 1) else (1, 0, 1, 2))
            else
            (if n < 11 then (1, 1, 0, 0) else (1, 1, 0, 1)))
          else
          (if n < 14 then
            (if n < 13 then (1, 1, 0, 2) else (1, 1, 1, 0))
            else
            (if n < 15 then
              (1, 1, 1, 1)
              else
              (if n < 16 then (1, 1, 1, 2) else (2, 0, 0, 0))))))
      else
      (if n < 25 then
        (if n < 21 then
          (if n < 19 then
            (if n < 18 then (2, 0, 0, 1) else (2, 0, 0, 2))
            else
            (if n < 20 then (2, 0, 1, 0) else (2, 0, 1, 1)))
          else
          (if n < 23 then
            (if n < 22 then (2, 0, 1, 2) else (2, 1, 0, 0))
            else
            (if n < 24 then (2, 1, 0, 1) else (2, 1, 0, 2))))
        else
        (if n < 29 then
          (if n < 27 then
            (if n < 26 then (2, 1, 1, 0) else (2, 1, 1, 1))
            else
            (if n < 28 then (2, 1, 1, 2) else (3, 0, 0, 0)))
          else
          (if n < 31 then
            (if n < 30 then (3, 0, 0, 1) else (3, 0, 0, 2))
            else
            (if n < 32 then
              (3, 0, 1, 0)
              else
              (if n < 33 then (3, 0, 1, 1) else (3, 0, 1, 2)))))))
    else
    (if n < 51 then
      (if n < 42 then
        (if n < 38 then
          (if n < 36 then
            (if n < 35 then (3, 1, 0, 0) else (3, 1, 0, 1))
            else
            (if n < 37 then (3, 1, 0, 2) else (3, 1, 1, 0)))
          else
          (if n < 40 then
            (if n < 39 then (3, 1, 1, 1) else (3, 1, 1, 2))
            else
            (if n < 41 then (4, 0, 0, 0) else (4, 0, 0, 1))))
        else
        (if n < 46 then
          (if n < 44 then
            (if n < 43 then (4, 0, 0, 2) else (4, 0, 1, 0))
            else
            (if n < 45 then (4, 0, 1, 1) else (4, 0, 1, 2)))
          else
          (if n < 48 then
            (if n < 47 then (4, 1, 0, 0) else (4, 1, 0, 1))
            else
            (if n < 49 then
              (4, 1, 0, 2)
              else
              (if n < 50 then (4, 1, 1, 0) else (4, 1, 1, 1))))))
      else
      (if n < 59 then
        (if n < 55 then
          (if n < 53 then
            (if n < 52 then (4, 1, 1, 2) else (5, 0, 0, 0))
            else
            (if n < 54 then (5, 0, 0, 1) else (5, 0, 0, 2)))
          else
          (if n < 57 then
            (if n < 56 then (5, 0, 1, 0) else (5, 0, 1, 1))
            else
            (if n < 58 then (5, 0, 1, 2) else (5, 1, 0, 0))))
        else
        (if n < 63 then
          (if n < 61 then
            (if n < 60 then (5, 1, 0, 1) else (5, 1, 0, 2))
            else
            (if n < 62 then (5, 1, 1, 0) else (5, 1, 1, 1)))
          else
          (if n < 65 then
            (if n < 64 then (5, 1, 1, 2) else (6, 0, 0, 1))
            else
            (if n < 66 then
              (6, 0, 1, 1)
              else
              (if n < 67 then (6, 1, 0, 1) else (6, 1, 1, 1))))))))

def certWtVal (n : ℕ) : ℤ × ℤ :=
  (if n < 34 then
    (if n < 17 then
      (if n < 8 then
        (if n < 4 then
          (if n < 2 then
            (if n < 1 then (-43, -46) else (49, -40))
            else
            (if n < 3 then (4, -63) else (63, 8)))
          else
          (if n < 6 then
            (if n < 5 then (-44, -51) else (-14, 131))
            else
            (if n < 7 then (54, -40) else (54, -40))))
        else
        (if n < 12 then
          (if n < 10 then
            (if n < 9 then (-129, -24) else (36, 56))
            else
            (if n < 11 then (6, -67) else (-104, 80)))
          else
          (if n < 14 then
            (if n < 13 then (66, 11) else (66, 11))
            else
            (if n < 15 then
              (-72, -110)
              else
              (if n < 16 then (-16, 65) else (-16, 111))))))
      else
      (if n < 25 then
        (if n < 21 then
          (if n < 19 then
            (if n < 18 then (150, -104) else (-109, -24))
            else
            (if n < 20 then (-109, -24) else (92, 157)))
          else
          (if n < 23 then
            (if n < 22 then (32, -107) else (-91, 65))
            else
            (if n < 24 then (179, 37) else (-58, -95))))
        else
        (if n < 29 then
          (if n < 27 then
            (if n < 26 then (-58, -95) else (-50, 176))
            else
            (if n < 28 then (99, -51) else (107, -69)))
          else
          (if n < 31 then
            (if n < 30 then (-195, -50) else (61, 112))
            else
            (if n < 32 then
              (61, 112)
              else
              (if n < 33 then (64, -190) else (-116, 52)))))))
    else
    (if n < 51 then
      (if n < 42 then
        (if n < 38 then
          (if n < 36 then
            (if n < 35 then (124, 30) else (-98, -175))
            else
            (if n < 37 then (-39, 121) else (-39, 121)))
          else
          (if n < 40 then
            (if n < 39 then (182, -85) else (-118, -48))
            else
            (if n < 41 then (-107, -32) else (81, 163))))
        else
        (if n < 46 then
          (if n < 44 then
            (if n < 43 then (39, -105) else (39, -105))
            else
            (if n < 45 then (-169, 69) else (101, 47)))
          else
          (if n < 48 then
            (if n < 47 then (-51, -99) else (-62, 172))
            else
            (if n < 49 then
              (103, -44)
              else
              (if n < 50 then (103, -44) else (-167, -74))))))
      else
      (if n < 59 then
        (if n < 55 then
          (if n < 53 then
            (if n < 52 then (36, 106) else (28, 61))
            else
            (if n < 54 then (51, -121) else (-63, 23)))
          else
          (if n < 57 then
            (if n < 56 then (-63, 23) else (117, 60))
            else
            (if n < 58 then (-18, -64) else (-25, 62))))
        else
        (if n < 63 then
          (if n < 61 then
            (if n < 60 then (123, -47) else (-60, -29))
            else
            (if n < 62 then (-60, -29) else (38, 126)))
          else
          (if n < 65 then
            (if n < 64 then (34, -58) else (-60, 20))
            else
            (if n < 66 then
              (-15, -62)
              else
              (if n < 67 then (-56, -30) else (34, -54))))))))

inductive NuBST
  | empty
  | node (key : ℤ × ℤ × ℤ × ℤ) (val : ℕ) (l r : NuBST)

def nuSub0 : NuBST := (NuBST.node (0, 1, -1, 0) 10 (NuBST.node (0, 0, 1, 1) 15 (NuBST.node (0, 0, 1, -2) 10 (NuBST.node (0, 0, 0, 2) 15 NuBST.empty NuBST.empty) (NuBST.node (0, 0, 1, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (0, 1, -1, -2) 20 (NuBST.node (0, 0, 1, 2) 25 NuBST.empty NuBST.empty) (NuBST.node (0, 1, -1, -1) 10 NuBST.empty NuBST.empty))) (NuBST.node (0, 1, 0, -1) 10 (NuBST.node (0, 1, -1, 2) 15 (NuBST.node (0, 1, -1, 1) 10 NuBST.empty NuBST.empty) (NuBST.node (0, 1, 0, -2) 15 NuBST.empty NuBST.empty)) (NuBST.node (0, 1, 0, 2) 20 (NuBST.node (0, 1, 0, 1) 15 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub1 : NuBST := (NuBST.node (1, -1, -1, 1) 10 (NuBST.node (0, 1, 1, 2) 25 (NuBST.node (0, 1, 1, 0) 10 (NuBST.node (0, 1, 1, -1) 10 NuBST.empty NuBST.empty) (NuBST.node (0, 1, 1, 1) 20 NuBST.empty NuBST.empty)) (NuBST.node (1, -1, -1, -1) 15 (NuBST.node (1, -1, -1, -2) 30 NuBST.empty NuBST.empty) (NuBST.node (1, -1, -1, 0) 10 NuBST.empty NuBST.empty))) (NuBST.node (1, -1, 0, 0) 10 (NuBST.node (1, -1, 0, -2) 20 (NuBST.node (1, -1, -1, 2) 10 NuBST.empty NuBST.empty) (NuBST.node (1, -1, 0, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (1, -1, 0, 2) 15 (NuBST.node (1, -1, 0, 1) 10 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub2 : NuBST := (NuBST.node (1, 0, -1, 1) 10 (NuBST.node (1, -1, 1, 2) 25 (NuBST.node (1, -1, 1, 0) 10 (NuBST.node (1, -1, 1, -1) 10 NuBST.empty NuBST.empty) (NuBST.node (1, -1, 1, 1) 15 NuBST.empty NuBST.empty)) (NuBST.node (1, 0, -1, -1) 10 (NuBST.node (1, 0, -1, -2) 20 NuBST.empty NuBST.empty) (NuBST.node (1, 0, -1, 0) 10 NuBST.empty NuBST.empty))) (NuBST.node (1, 0, 0, 1) 10 (NuBST.node (1, 0, 0, -2) 15 (NuBST.node (1, 0, -1, 2) 15 NuBST.empty NuBST.empty) (NuBST.node (1, 0, 0, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (1, 0, 1, -2) 10 (NuBST.node (1, 0, 0, 2) 25 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub3 : NuBST := (NuBST.node (1, 1, -1, 1) 15 (NuBST.node (1, 1, -1, -2) 15 (NuBST.node (1, 0, 1, 1) 15 (NuBST.node (1, 0, 1, 0) 10 NuBST.empty NuBST.empty) (NuBST.node (1, 0, 1, 2) 20 NuBST.empty NuBST.empty)) (NuBST.node (1, 1, -1, 0) 10 (NuBST.node (1, 1, -1, -1) 10 NuBST.empty NuBST.empty) NuBST.empty)) (NuBST.node (1, 1, 0, 0) 10 (NuBST.node (1, 1, 0, -2) 10 (NuBST.node (1, 1, -1, 2) 15 NuBST.empty NuBST.empty) (NuBST.node (1, 1, 0, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (1, 1, 0, 2) 25 (NuBST.node (1, 1, 0, 1) 15 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub4 : NuBST := (NuBST.node (2, -1, -1, 1) 10 (NuBST.node (1, 1, 1, 2) 30 (NuBST.node (1, 1, 1, 0) 25 (NuBST.node (1, 1, 1, -1) 10 NuBST.empty NuBST.empty) (NuBST.node (1, 1, 1, 1) 20 NuBST.empty NuBST.empty)) (NuBST.node (2, -1, -1, -1) 15 (NuBST.node (2, -1, -1, -2) 15 NuBST.empty NuBST.empty) (NuBST.node (2, -1, -1, 0) 10 NuBST.empty NuBST.empty))) (NuBST.node (2, -1, 0, 0) 10 (NuBST.node (2, -1, 0, -2) 15 (NuBST.node (2, -1, -1, 2) 10 NuBST.empty NuBST.empty) (NuBST.node (2, -1, 0, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (2, -1, 0, 2) 20 (NuBST.node (2, -1, 0, 1) 10 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub5 : NuBST := (NuBST.node (2, 0, -1, 1) 10 (NuBST.node (2, -1, 1, 2) 20 (NuBST.node (2, -1, 1, 0) 10 (NuBST.node (2, -1, 1, -1) 10 NuBST.empty NuBST.empty) (NuBST.node (2, -1, 1, 1) 15 NuBST.empty NuBST.empty)) (NuBST.node (2, 0, -1, -1) 10 (NuBST.node (2, 0, -1, -2) 15 NuBST.empty NuBST.empty) (NuBST.node (2, 0, -1, 0) 10 NuBST.empty NuBST.empty))) (NuBST.node (2, 0, 0, 0) 10 (NuBST.node (2, 0, 0, -2) 10 (NuBST.node (2, 0, -1, 2) 15 NuBST.empty NuBST.empty) (NuBST.node (2, 0, 0, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (2, 0, 0, 2) 20 (NuBST.node (2, 0, 0, 1) 15 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub6 : NuBST := (NuBST.node (2, 1, -1, 1) 10 (NuBST.node (2, 0, 1, 2) 30 (NuBST.node (2, 0, 1, 0) 15 (NuBST.node (2, 0, 1, -1) 10 NuBST.empty NuBST.empty) (NuBST.node (2, 0, 1, 1) 20 NuBST.empty NuBST.empty)) (NuBST.node (2, 1, -1, -1) 10 (NuBST.node (2, 1, -1, -2) 15 NuBST.empty NuBST.empty) (NuBST.node (2, 1, -1, 0) 10 NuBST.empty NuBST.empty))) (NuBST.node (2, 1, 0, 0) 10 (NuBST.node (2, 1, 0, -2) 10 (NuBST.node (2, 1, -1, 2) 20 NuBST.empty NuBST.empty) (NuBST.node (2, 1, 0, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (2, 1, 0, 2) 25 (NuBST.node (2, 1, 0, 1) 20 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub7 : NuBST := (NuBST.node (3, -1, -1, 0) 10 (NuBST.node (2, 1, 1, 2) 80 (NuBST.node (2, 1, 1, 0) 15 (NuBST.node (2, 1, 1, -1) 10 NuBST.empty NuBST.empty) (NuBST.node (2, 1, 1, 1) 25 NuBST.empty NuBST.empty)) (NuBST.node (3, -1, -1, -1) 10 (NuBST.node (3, -1, -1, -2) 25 NuBST.empty NuBST.empty) NuBST.empty)) (NuBST.node (3, -1, 0, -1) 10 (NuBST.node (3, -1, -1, 2) 15 (NuBST.node (3, -1, -1, 1) 10 NuBST.empty NuBST.empty) (NuBST.node (3, -1, 0, -2) 10 NuBST.empty NuBST.empty)) (NuBST.node (3, -1, 0, 1) 10 (NuBST.node (3, -1, 0, 0) 10 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub8 : NuBST := (NuBST.node (3, 0, -1, 0) 10 (NuBST.node (3, -1, 1, 1) 25 (NuBST.node (3, -1, 1, -1) 10 (NuBST.node (3, -1, 1, -2) 10 NuBST.empty NuBST.empty) (NuBST.node (3, -1, 1, 0) 15 NuBST.empty NuBST.empty)) (NuBST.node (3, 0, -1, -2) 15 (NuBST.node (3, -1, 1, 2) 35 NuBST.empty NuBST.empty) (NuBST.node (3, 0, -1, -1) 10 NuBST.empty NuBST.empty))) (NuBST.node (3, 0, 0, -1) 10 (NuBST.node (3, 0, -1, 2) 20 (NuBST.node (3, 0, -1, 1) 15 NuBST.empty NuBST.empty) (NuBST.node (3, 0, 0, -2) 10 NuBST.empty NuBST.empty)) (NuBST.node (3, 0, 0, 1) 20 (NuBST.node (3, 0, 0, 0) 10 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub9 : NuBST := (NuBST.node (3, 1, -1, 0) 10 (NuBST.node (3, 0, 1, 1) 25 (NuBST.node (3, 0, 1, -1) 10 (NuBST.node (3, 0, 1, -2) 10 NuBST.empty NuBST.empty) (NuBST.node (3, 0, 1, 0) 15 NuBST.empty NuBST.empty)) (NuBST.node (3, 1, -1, -2) 10 (NuBST.node (3, 0, 1, 2) 25 NuBST.empty NuBST.empty) (NuBST.node (3, 1, -1, -1) 10 NuBST.empty NuBST.empty))) (NuBST.node (3, 1, 0, -1) 10 (NuBST.node (3, 1, -1, 2) 35 (NuBST.node (3, 1, -1, 1) 15 NuBST.empty NuBST.empty) (NuBST.node (3, 1, 0, -2) 10 NuBST.empty NuBST.empty)) (NuBST.node (3, 1, 0, 1) 20 (NuBST.node (3, 1, 0, 0) 15 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub10 : NuBST := (NuBST.node (4, -1, -1, 0) 10 (NuBST.node (3, 1, 1, 1) 30 (NuBST.node (3, 1, 1, -1) 15 (NuBST.node (3, 1, 1, -2) 10 NuBST.empty NuBST.empty) (NuBST.node (3, 1, 1, 0) 15 NuBST.empty NuBST.empty)) (NuBST.node (4, -1, -1, -2) 15 (NuBST.node (3, 1, 1, 2) 40 NuBST.empty NuBST.empty) (NuBST.node (4, -1, -1, -1) 10 NuBST.empty NuBST.empty))) (NuBST.node (4, -1, 0, -1) 10 (NuBST.node (4, -1, -1, 2) 25 (NuBST.node (4, -1, -1, 1) 10 NuBST.empty NuBST.empty) (NuBST.node (4, -1, 0, -2) 10 NuBST.empty NuBST.empty)) (NuBST.node (4, -1, 0, 1) 15 (NuBST.node (4, -1, 0, 0) 10 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub11 : NuBST := (NuBST.node (4, 0, -1, -1) 10 (NuBST.node (4, -1, 1, 1) 20 (NuBST.node (4, -1, 1, -1) 10 (NuBST.node (4, -1, 1, -2) 10 NuBST.empty NuBST.empty) (NuBST.node (4, -1, 1, 0) 10 NuBST.empty NuBST.empty)) (NuBST.node (4, 0, -1, -2) 10 (NuBST.node (4, -1, 1, 2) 25 NuBST.empty NuBST.empty) NuBST.empty)) (NuBST.node (4, 0, 0, -2) 10 (NuBST.node (4, 0, -1, 1) 20 (NuBST.node (4, 0, -1, 0) 10 NuBST.empty NuBST.empty) (NuBST.node (4, 0, -1, 2) 20 NuBST.empty NuBST.empty)) (NuBST.node (4, 0, 0, 0) 15 (NuBST.node (4, 0, 0, -1) 10 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub12 : NuBST := (NuBST.node (4, 1, -1, -1) 10 (NuBST.node (4, 0, 1, 0) 20 (NuBST.node (4, 0, 1, -2) 10 (NuBST.node (4, 0, 0, 2) 30 NuBST.empty NuBST.empty) (NuBST.node (4, 0, 1, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (4, 0, 1, 2) 40 (NuBST.node (4, 0, 1, 1) 25 NuBST.empty NuBST.empty) (NuBST.node (4, 1, -1, -2) 10 NuBST.empty NuBST.empty))) (NuBST.node (4, 1, 0, -2) 10 (NuBST.node (4, 1, -1, 1) 15 (NuBST.node (4, 1, -1, 0) 10 NuBST.empty NuBST.empty) (NuBST.node (4, 1, -1, 2) 25 NuBST.empty NuBST.empty)) (NuBST.node (4, 1, 0, 0) 15 (NuBST.node (4, 1, 0, -1) 10 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub13 : NuBST := (NuBST.node (5, -1, -1, -1) 10 (NuBST.node (4, 1, 1, 0) 30 (NuBST.node (4, 1, 1, -2) 10 (NuBST.node (4, 1, 0, 2) 30 NuBST.empty NuBST.empty) (NuBST.node (4, 1, 1, -1) 15 NuBST.empty NuBST.empty)) (NuBST.node (4, 1, 1, 2) 35 (NuBST.node (4, 1, 1, 1) 35 NuBST.empty NuBST.empty) NuBST.empty)) (NuBST.node (5, -1, 0, 0) 10 (NuBST.node (5, -1, -1, 1) 15 (NuBST.node (5, -1, -1, 0) 10 NuBST.empty NuBST.empty) (NuBST.node (5, -1, 0, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (5, -1, 1, -1) 10 (NuBST.node (5, -1, 0, 1) 15 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub14 : NuBST := (NuBST.node (5, 0, 1, -1) 15 (NuBST.node (5, 0, -1, 1) 15 (NuBST.node (5, 0, -1, -1) 10 (NuBST.node (5, -1, 1, 1) 20 NuBST.empty NuBST.empty) (NuBST.node (5, 0, -1, 0) 10 NuBST.empty NuBST.empty)) (NuBST.node (5, 0, 0, 0) 15 (NuBST.node (5, 0, 0, -1) 10 NuBST.empty NuBST.empty) (NuBST.node (5, 0, 0, 1) 30 NuBST.empty NuBST.empty))) (NuBST.node (5, 1, -1, 0) 15 (NuBST.node (5, 0, 1, 1) 25 (NuBST.node (5, 0, 1, 0) 20 NuBST.empty NuBST.empty) (NuBST.node (5, 1, -1, -1) 10 NuBST.empty NuBST.empty)) (NuBST.node (5, 1, 0, -1) 10 (NuBST.node (5, 1, -1, 1) 20 NuBST.empty NuBST.empty) NuBST.empty)))
def nuSub15 : NuBST := (NuBST.node (6, -1, 1, 0) 15 (NuBST.node (5, 1, 1, 1) 40 (NuBST.node (5, 1, 1, -1) 20 (NuBST.node (5, 1, 0, 1) 20 NuBST.empty NuBST.empty) (NuBST.node (5, 1, 1, 0) 20 NuBST.empty NuBST.empty)) (NuBST.node (6, -1, 0, 0) 15 (NuBST.node (6, -1, -1, 0) 10 NuBST.empty NuBST.empty) NuBST.empty)) (NuBST.node (6, 1, -1, 0) 25 (NuBST.node (6, 0, 0, 0) 25 (NuBST.node (6, 0, -1, 0) 10 NuBST.empty NuBST.empty) (NuBST.node (6, 0, 1, 0) 20 NuBST.empty NuBST.empty)) (NuBST.node (6, 1, 1, 0) 30 (NuBST.node (6, 1, 0, 0) 20 NuBST.empty NuBST.empty) NuBST.empty)))

def nonUnitBST : NuBST := (NuBST.node (3, -1, 0, 2) 20 (NuBST.node (1, 1, 1, -2) 10 (NuBST.node (1, -1, 1, -2) 10 (NuBST.node (0, 1, 1, -2) 10 nuSub0 nuSub1) (NuBST.node (1, 0, 1, -1) 10 nuSub2 nuSub3)) (NuBST.node (2, 0, 1, -2) 10 (NuBST.node (2, -1, 1, -2) 15 nuSub4 nuSub5) (NuBST.node (2, 1, 1, -2) 10 nuSub6 nuSub7))) (NuBST.node (4, 0, 0, 1) 15 (NuBST.node (3, 1, 0, 2) 30 (NuBST.node (3, 0, 0, 2) 45 nuSub8 nuSub9) (NuBST.node (4, -1, 0, 2) 20 nuSub10 nuSub11)) (NuBST.node (5, -1, 1, 0) 15 (NuBST.node (4, 1, 0, 1) 25 nuSub12 nuSub13) (NuBST.node (5, 1, 0, 0) 25 nuSub14 nuSub15))))

def R0Lit : Ival := ⟨2282550786818, 2282550787123⟩
def zmLit0 : Cval := ⟨⟨605861, 745185⟩, ⟨-4313060, -4173663⟩⟩
def zpLit0 : Cval := ⟨⟨-641098, -501782⟩, ⟨3519823, 3659232⟩⟩
def dzLit0 : Cval := ⟨⟨7822638424606, 7843291614256⟩, ⟨1236671937744, 1257325184556⟩⟩
def z2Lit0 : Cval := ⟨⟨18366123335043, 18368584952638⟩, ⟨-6513206053420, -6510744435848⟩⟩
def zmLit1 : Cval := ⟨⟨2020244, 2301731⟩, ⟨-6362309, -6081041⟩⟩
def zpLit1 : Cval := ⟨⟨-2480213, -2198751⟩, ⟨6595634, 6876882⟩⟩
def dzLit1 : Cval := ⟨⟨12940667606288, 12975245763066⟩, ⟨4483078118290, 4517655654275⟩⟩
def z2Lit1 : Cval := ⟨⟨4447451572372, 4451653571681⟩, ⟨2953623791878, 2957825791192⟩⟩
def zmLit2 : Cval := ⟨⟨-3717156, -3302975⟩, ⟨-6097249, -5682894⟩⟩
def zpLit2 : Cval := ⟨⟨2957884, 3372076⟩, ⟨5103999, 5518354⟩⟩
def dzLit2 : Cval := ⟨⟨11180552550567, 11222065262042⟩, ⟨-6695850971829, -6654337477958⟩⟩
def z2Lit2 : Cval := ⟨⟨3746510145562, 3751578740514⟩, ⟨3524943916087, 3530012511022⟩⟩
def zmLit3 : Cval := ⟨⟨-2069000, -1031922⟩, ⟨-7992703, -6955297⟩⟩
def zpLit3 : Cval := ⟨⟨959738, 1996807⟩, ⟨6602589, 7639992⟩⟩
def dzLit3 : Cval := ⟨⟨14567686879092, 14622661254144⟩, ⟨-3056175867750, -3001198754751⟩⟩
def z2Lit3 : Cval := ⟨⟨16482830143607, 16489579970598⟩, ⟨-9884074937791, -9877325110777⟩⟩

/-! == Lookup table certification, binary-tree combinators, and EM3/dEM3 soundness -/

def lnRad : ℤ := 200
def ivInvSqrt (n : ℕ) : Ival := let a := invSqrtVal n; ⟨a - 1, a + 1⟩
def ivLn (n : ℕ) : Ival := if n == 1 then ⟨0, 0⟩ else let b := lnVal n; ⟨b - lnRad, b + lnRad⟩

def certInvSqrtEntry (n : ℕ) : Bool :=
  let a := invSqrtVal n
  decide (0 < a - 1 ∧ (a - 1) * (a - 1) * (n : ℤ) ≤ Sval * Sval ∧
    Sval * Sval ≤ (a + 1) * (a + 1) * (n : ℤ))

def certLnEntry (n : ℕ) : Bool :=
  if n == 1 then true else
  let b := lnVal n
  let uLo := ivDivNat ⟨b - lnRad, b - lnRad⟩ 8
  strictIval (ivExpSmall uLo) fun e1 => strictIval (ivSq e1) fun e2 =>
  strictIval (ivSq e2) fun e4 => strictIval (ivSq e4) fun e8 =>
  let uHi := ivDivNat ⟨b + lnRad, b + lnRad⟩ 8
  strictIval (ivExpSmall uHi) fun f1 => strictIval (ivSq f1) fun f2 =>
  strictIval (ivSq f2) fun f4 => strictIval (ivSq f4) fun f8 =>
  decide (e8.hi ≤ (n : ℤ) * Sval ∧ (n : ℤ) * Sval ≤ f8.lo ∧
    0 ≤ b - lnRad ∧ b + lnRad ≤ 55000000000000)

def checkRangeBin : ℕ → ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, lo, hi, p => if lo ≤ hi then p lo else true
  | d + 1, lo, hi, p =>
      if hi < lo then true
      else if lo == hi then p lo
      else
        let mid := (lo + hi) / 2
        checkRangeBin d lo mid p && checkRangeBin d (mid + 1) hi p

lemma checkRangeBin_sound {d lo hi : ℕ} {p : ℕ → Bool}
    (hsize : hi - lo < 2 ^ d) (h : checkRangeBin d lo hi p = true) :
    ∀ n, lo ≤ n → n ≤ hi → p n = true := by
  induction d generalizing lo hi with
  | zero =>
    intro n h1 h2
    have heq : n = lo := by omega
    subst heq
    have hle : n ≤ hi := h2
    simpa [checkRangeBin, hle] using h
  | succ d ih =>
    intro n h1 h2
    simp only [checkRangeBin] at h
    split_ifs at h with hlt heq
    · omega
    · have hlo : lo = hi := beq_iff_eq.mp heq
      have hn : n = lo := by omega
      subst hn; exact h
    · rw [Bool.and_eq_true] at h
      set mid := (lo + hi) / 2
      by_cases hnm : n ≤ mid
      · exact ih (by omega) h.1 n h1 hnm
      · exact ih (by omega) h.2 n (by omega) h2

def cvSumRangeBin : ℕ → ℕ → ℕ → (ℕ → Cval) → Cval
  | 0, lo, hi, f => if lo ≤ hi then f lo else ⟨ivConst 0, ivConst 0⟩
  | d + 1, lo, hi, f =>
      if hi < lo then ⟨ivConst 0, ivConst 0⟩
      else if lo == hi then f lo
      else
        let mid := (lo + hi) / 2
        strictCval (cvSumRangeBin d lo mid f) fun l =>
        strictCval (cvSumRangeBin d (mid + 1) hi f) fun r =>
        cvAdd l r

lemma cvSumRangeBin_mem {d lo hi : ℕ} {f : ℕ → Cval} {g : ℕ → ℂ}
    (hsize : hi - lo < 2 ^ d) (hf : ∀ n, lo ≤ n → n ≤ hi → (f n).mem (g n)) :
    (cvSumRangeBin d lo hi f).mem (∑ n ∈ Finset.Icc lo hi, g n) := by
  induction d generalizing lo hi with
  | zero =>
    simp only [cvSumRangeBin]
    split_ifs with hle
    · have heq : hi = lo := by omega
      rw [heq]; simpa using hf lo le_rfl hle
    · have hemp : Finset.Icc lo hi = ∅ := Finset.Icc_eq_empty hle
      rw [hemp, Finset.sum_empty]
      exact ⟨by simpa using ivConst_mem 0, by simpa using ivConst_mem 0⟩
  | succ d ih =>
    simp only [cvSumRangeBin]
    split_ifs with hlt heq
    · have hemp : Finset.Icc lo hi = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]
      exact ⟨by simpa using ivConst_mem 0, by simpa using ivConst_mem 0⟩
    · have hlo : lo = hi := beq_iff_eq.mp heq
      subst hlo; simpa using hf lo le_rfl le_rfl
    · simp only [strictCval_eq]
      set mid := (lo + hi) / 2
      have hsplit : Finset.Icc lo hi = Finset.Icc lo mid ∪ Finset.Icc (mid + 1) hi := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc lo mid) (Finset.Icc (mid + 1) hi) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        simp only [Finset.mem_Icc] at hk1 hk2; omega
      rw [hsplit, Finset.sum_union hdisj]
      exact cvAdd_mem
        (ih (by omega) (fun n h1 h2 => hf n h1 (by omega)))
        (ih (by omega) (fun n h1 h2 => hf n (by omega) h2))

def intSumRangeBin : ℕ → ℕ → ℕ → (ℕ → ℤ) → ℤ
  | 0, lo, hi, f => if lo ≤ hi then f lo else 0
  | d + 1, lo, hi, f =>
      if hi < lo then 0
      else if lo == hi then f lo
      else
        let mid := (lo + hi) / 2
        strictInt (intSumRangeBin d lo mid f) fun l =>
        strictInt (intSumRangeBin d (mid + 1) hi f) fun r =>
        l + r

lemma intSumRangeBin_eq {d lo hi : ℕ} {f : ℕ → ℤ} (hsize : hi - lo < 2 ^ d) :
    intSumRangeBin d lo hi f = ∑ n ∈ Finset.Icc lo hi, f n := by
  induction d generalizing lo hi with
  | zero =>
    simp only [intSumRangeBin]
    split_ifs with hle
    · have heq : hi = lo := by omega
      subst heq; simp
    · rw [Finset.Icc_eq_empty hle, Finset.sum_empty]
  | succ d ih =>
    simp only [intSumRangeBin]
    split_ifs with hlt heq
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    · have hlo : lo = hi := beq_iff_eq.mp heq
      subst hlo; simp
    · simp only [strictInt_eq]
      set mid := (lo + hi) / 2
      have hsplit : Finset.Icc lo hi = Finset.Icc lo mid ∪ Finset.Icc (mid + 1) hi := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc lo mid) (Finset.Icc (mid + 1) hi) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        simp only [Finset.mem_Icc] at hk1 hk2; omega
      rw [hsplit, Finset.sum_union hdisj, ih (by omega), ih (by omega)]

theorem cert_invSqrt_all : checkRangeBin 8 1 160 certInvSqrtEntry = true := by decide
theorem cert_ln_all : checkRangeBin 8 1 160 certLnEntry = true := by decide

lemma ivInvSqrt_mem {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 160) :
    (ivInvSqrt n).mem ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hS := Sval_pos
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hok := checkRangeBin_sound (by norm_num : 160 - 1 < 2 ^ 8) cert_invSqrt_all n h1 h2
  simp only [certInvSqrtEntry, decide_eq_true_eq] at hok
  set a := invSqrtVal n
  have ha1 : (0 : ℝ) < ((a - 1 : ℤ) : ℝ) := by exact_mod_cast hok.1
  have ha2 : (0 : ℝ) < ((a + 1 : ℤ) : ℝ) := by
    have : (0 : ℤ) < a + 1 := by omega
    exact_mod_cast this
  have hsq1 : ((a - 1 : ℤ) : ℝ) * ((a - 1 : ℤ) : ℝ) * (n : ℝ) ≤ (Sval : ℝ) * (Sval : ℝ) := by
    exact_mod_cast hok.2.1
  have hsq2 : (Sval : ℝ) * (Sval : ℝ) ≤ ((a + 1 : ℤ) : ℝ) * ((a + 1 : ℤ) : ℝ) * (n : ℝ) := by
    exact_mod_cast hok.2.2
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  rw [hrpow]
  constructor <;> dsimp only [ivInvSqrt]
  · have hmul : ((a - 1 : ℤ) : ℝ) * Real.sqrt (n : ℝ) ≤ (Sval : ℝ) := by
      have hsq' : (((a - 1 : ℤ) : ℝ) * Real.sqrt (n : ℝ)) ^ 2 ≤ (Sval : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hn0.le]; nlinarith
      nlinarith [mul_pos ha1 hsn]
    rw [div_le_iff₀ hS, inv_mul_eq_div, le_div_iff₀ hsn]; linarith
  · have hmul : (Sval : ℝ) ≤ ((a + 1 : ℤ) : ℝ) * Real.sqrt (n : ℝ) := by
      have hsq' : (Sval : ℝ) ^ 2 ≤ (((a + 1 : ℤ) : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hn0.le]; nlinarith
      nlinarith [mul_pos ha2 hsn]
    rw [le_div_iff₀ hS, inv_mul_eq_div, div_le_iff₀ hsn]; linarith

lemma ivLn_mem {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 160) :
    (ivLn n).mem (Real.log (n : ℝ)) := by
  have hS := Sval_pos
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  by_cases hn1 : n = 1
  · subst hn1
    simp only [ivLn, beq_self_eq_true, ite_true, Nat.cast_one, Real.log_one]
    constructor <;> simp
  · have hok := checkRangeBin_sound (by norm_num : 160 - 1 < 2 ^ 8) cert_ln_all n h1 h2
    have hbeq : (n == 1) = false := beq_false_of_ne hn1
    simp only [certLnEntry, hbeq, Bool.false_eq_true, ite_false, strictIval_eq,
      decide_eq_true_eq] at hok
    set b := lnVal n
    set xLo : ℝ := ((b - lnRad : ℤ) : ℝ) / (Sval : ℝ)
    set xHi : ℝ := ((b + lnRad : ℤ) : ℝ) / (Sval : ℝ)
    have hxLo_abs : |xLo / 8| ≤ 7 / 10 := by
      have h0 : (0 : ℝ) ≤ ((b - lnRad : ℤ) : ℝ) := by exact_mod_cast hok.2.2.1
      have htop : ((b - lnRad : ℤ) : ℝ) ≤ (55000000000000 : ℝ) := by
        have : b - lnRad ≤ 55000000000000 := by dsimp only [lnRad] at hok ⊢; omega
        exact_mod_cast this
      have hnn : 0 ≤ xLo / 8 := by dsimp only [xLo]; positivity
      rw [abs_of_nonneg hnn]
      dsimp only [xLo, Sval] at htop ⊢
      linarith
    have hxHi_abs : |xHi / 8| ≤ 7 / 10 := by
      have h0 : (0 : ℝ) ≤ ((b + lnRad : ℤ) : ℝ) := by
        have : 0 ≤ b + lnRad := by dsimp only [lnRad] at hok ⊢; omega
        exact_mod_cast this
      have htop : ((b + lnRad : ℤ) : ℝ) ≤ (55000000000000 : ℝ) := by exact_mod_cast hok.2.2.2
      have hnn : 0 ≤ xHi / 8 := by dsimp only [xHi]; positivity
      rw [abs_of_nonneg hnn]
      dsimp only [xHi, Sval] at htop ⊢
      linarith
    have huLo : (ivDivNat ⟨b - lnRad, b - lnRad⟩ 8).mem (xLo / 8) :=
      ivDivNat_mem ⟨le_rfl, le_rfl⟩ (by norm_num)
    have huHi : (ivDivNat ⟨b + lnRad, b + lnRad⟩ 8).mem (xHi / 8) :=
      ivDivNat_mem ⟨le_rfl, le_rfl⟩ (by norm_num)
    have he8 := ivSq_mem (ivSq_mem (ivSq_mem (ivExpSmall_mem huLo hxLo_abs)))
    have hf8 := ivSq_mem (ivSq_mem (ivSq_mem (ivExpSmall_mem huHi hxHi_abs)))
    have hexp8 : ∀ y : ℝ,
        ((Real.exp (y / 8) * Real.exp (y / 8)) * (Real.exp (y / 8) * Real.exp (y / 8))) *
        ((Real.exp (y / 8) * Real.exp (y / 8)) * (Real.exp (y / 8) * Real.exp (y / 8))) =
        Real.exp y := fun y => by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hexp8 xLo] at he8
    rw [hexp8 xHi] at hf8
    simp only [ivLn, hbeq, Bool.false_eq_true, ite_false]
    constructor
    · rw [Real.le_log_iff_exp_le hn0]
      have hle : (((ivSq (ivSq (ivSq (ivExpSmall (ivDivNat ⟨b - lnRad, b - lnRad⟩ 8))))).hi : ℤ) : ℝ) ≤
          ((n : ℤ) : ℝ) * (Sval : ℝ) := by exact_mod_cast hok.1
      have hle' : ((ivSq (ivSq (ivSq (ivExpSmall (ivDivNat ⟨b - lnRad, b - lnRad⟩ 8))))).hi : ℝ) /
          (Sval : ℝ) ≤ (n : ℝ) := by
        rw [div_le_iff₀ hS]; simpa using hle
      exact he8.2.trans hle'
    · rw [Real.log_le_iff_le_exp hn0]
      have hge : ((n : ℤ) : ℝ) * (Sval : ℝ) ≤
          (((ivSq (ivSq (ivSq (ivExpSmall (ivDivNat ⟨b + lnRad, b + lnRad⟩ 8))))).lo : ℤ) : ℝ) := by
        exact_mod_cast hok.2.1
      have hge' : (n : ℝ) ≤
          ((ivSq (ivSq (ivSq (ivExpSmall (ivDivNat ⟨b + lnRad, b + lnRad⟩ 8))))).lo : ℝ) / (Sval : ℝ) := by
        rw [le_div_iff₀ hS]; simpa using hge
      exact hge'.trans hf8.1

def cvNpowHalf (tIv : Ival) (n : ℕ) : Cval :=
  cvScale (ivInvSqrt n) (cvExpI (ivNeg (ivMul tIv (ivLn n))))

def cvNpowOne (tIv : Ival) (n : ℕ) : Cval :=
  cvScale (ivRat 1 (n : ℤ)) (cvExpI (ivNeg (ivMul tIv (ivLn n))))

lemma cvNpowHalf_mem {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 160) :
    (cvNpowHalf tIv n).mem ((n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hsplit : (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * I) := by
    rw [show -((1 / 2 : ℂ) + (t : ℂ) * I) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) + (-(t : ℂ) * I) by push_cast; ring,
      Complex.cpow_add _ _ hnne, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hn0.le,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hnne), ← Complex.ofReal_log hn0.le]
    congr 2; push_cast; ring
  rw [hsplit]
  exact cvScale_mem (ivInvSqrt_mem h1 h2) (cvExpI_mem (ivNeg_mem (ivMul_mem ht (ivLn_mem h1 h2))))

lemma cvNpowOne_mem {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 160) :
    (cvNpowOne tIv n).mem ((n : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * I))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hsplit : (n : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * I)) =
      (((1 : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * I) := by
    rw [show -((1 : ℂ) + (t : ℂ) * I) = (-1 : ℂ) + (-(t : ℂ) * I) by ring,
      Complex.cpow_add _ _ hnne, Complex.cpow_neg_one, ← Complex.ofReal_natCast,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hnne), ← Complex.ofReal_log hn0.le]
    congr 1
    · push_cast; rw [one_div]
    · congr 1; push_cast; ring
  rw [hsplit]
  have hrat : (ivRat 1 (n : ℤ)).mem ((1 : ℝ) / (n : ℝ)) := by
    simpa using ivRat_mem 1 (by exact_mod_cast (by omega : 0 < n) : (0 : ℤ) < (n : ℤ))
  exact cvScale_mem hrat (cvExpI_mem (ivNeg_mem (ivMul_mem ht (ivLn_mem h1 h2))))

def cvEm3Half (tIv : Ival) (N : ℕ) : Cval :=
  let s : Cval := ⟨ivRat 1 2, tIv⟩
  let tot := cvSumRangeBin 8 1 (N - 1) (cvNpowHalf tIv)
  let Nms := cvNpowHalf tIv N
  let N1ms := cvScale (ivConst (N : ℤ)) Nms
  let sm1 : Cval := ⟨ivRat (-1) 2, tIv⟩
  let tot := cvAdd tot (cvDiv N1ms sm1)
  let tot := cvAdd tot (cvDivNat Nms 2)
  let invN := ivRat 1 (N : ℤ)
  let invN2 := ivSq invN
  let Nms1 := cvScale invN Nms
  let tot := cvAdd tot (cvDivNat (cvMul s Nms1) 12)
  let s1 : Cval := ⟨ivRat 3 2, tIv⟩
  let s2 : Cval := ⟨ivRat 5 2, tIv⟩
  let p3 := cvMul (cvMul s s1) s2
  let Nms3 := cvScale invN2 Nms1
  let tot := cvSub tot (cvDivNat (cvMul p3 Nms3) 720)
  let s3 : Cval := ⟨ivRat 7 2, tIv⟩
  let s4 : Cval := ⟨ivRat 9 2, tIv⟩
  let p5 := cvMul (cvMul p3 s3) s4
  let Nms5 := cvScale invN2 Nms3
  cvAdd tot (cvDivNat (cvMul p5 Nms5) 30240)

lemma cvEm3Half_mem {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {N : ℕ} (h1 : 1 ≤ N) (h2 : N ≤ 160) :
    (cvEm3Half tIv N).mem (em3 ((1 / 2 : ℂ) + (t : ℂ) * I) N) := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNposZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast (by omega : 0 < N)
  have hsum : (cvSumRangeBin 8 1 (N - 1) (cvNpowHalf tIv)).mem
      (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) := by
    have hIco : Finset.Ico 1 N = Finset.Icc 1 (N - 1) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco]
    exact cvSumRangeBin_mem (by omega) (fun n hn1 hn2 => cvNpowHalf_mem ht hn1 (by omega))
  have hNms := cvNpowHalf_mem ht h1 h2
  have hN1ms : (cvScale (ivConst (N : ℤ)) (cvNpowHalf tIv N)).mem ((N : ℂ) ^ (1 - s)) := by
    have heq : (N : ℂ) ^ (1 - s) = (((N : ℤ) : ℝ) : ℂ) * (N : ℂ) ^ (-s) := by
      rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hNne, Complex.cpow_one]
      push_cast; rfl
    rw [heq]; exact cvScale_mem (ivConst_mem (N : ℤ)) hNms
  have hsm1 : Cval.mem ⟨ivRat (-1) 2, tIv⟩ (s - 1) :=
    ⟨by simpa [s, show (-1 : ℝ) / 2 = 1 / 2 - 1 by norm_num] using ivRat_mem (-1) (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hsm1_pos : 0 < (cvNormSq ⟨ivRat (-1) 2, tIv⟩).lo := by
    have hre : (ivSq (ivRat (-1) 2)).lo = 2500000000000 := by decide
    have him := ivSq_lo_nonneg tIv
    dsimp only [cvNormSq, ivAdd]; omega
  have hdiv1 := (cvDiv_mem hN1ms hsm1 hsm1_pos).2
  have hhalf : (cvDivNat (cvNpowHalf tIv N) 2).mem ((1 / 2 : ℂ) * (N : ℂ) ^ (-s)) := by
    rw [show (1 / 2 : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (-s) / ((2 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem hNms (by norm_num)
  have hinvN : (ivRat 1 (N : ℤ)).mem ((1 : ℝ) / (N : ℝ)) := by simpa using ivRat_mem 1 hNposZ
  have hinvN2 := ivSq_mem hinvN
  have hNms1 : (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N)).mem ((N : ℂ) ^ (-(s + 1))) := by
    have heq : (N : ℂ) ^ (-(s + 1)) = (((1 : ℝ) / (N : ℝ) : ℝ) : ℂ) * (N : ℂ) ^ (-s) := by
      rw [show -(s + 1) = (-1 : ℂ) + (-s) by ring, Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN hNms
  have hNms3 : (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N))).mem
      ((N : ℂ) ^ (-(s + 3))) := by
    have heq : (N : ℂ) ^ (-(s + 3)) = ((((1 : ℝ) / (N : ℝ)) * ((1 : ℝ) / (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 1)) := by
      rw [show -(s + 3) = ((-1 : ℂ) + (-1 : ℂ)) + (-(s + 1)) by ring, Complex.cpow_add _ _ hNne,
        Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN2 hNms1
  have hNms5 : (cvScale (ivSq (ivRat 1 (N : ℤ)))
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N)))).mem
      ((N : ℂ) ^ (-(s + 5))) := by
    have heq : (N : ℂ) ^ (-(s + 5)) = ((((1 : ℝ) / (N : ℝ)) * ((1 : ℝ) / (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 3)) := by
      rw [show -(s + 5) = ((-1 : ℂ) + (-1 : ℂ)) + (-(s + 3)) by ring, Complex.cpow_add _ _ hNne,
        Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN2 hNms3
  have hs0 : Cval.mem ⟨ivRat 1 2, tIv⟩ s :=
    ⟨by simpa [s] using ivRat_mem 1 (by norm_num : (0 : ℤ) < 2), by simpa [s] using ht⟩
  have hs1 : Cval.mem ⟨ivRat 3 2, tIv⟩ (s + 1) :=
    ⟨by simpa [s, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num] using ivRat_mem 3 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs2 : Cval.mem ⟨ivRat 5 2, tIv⟩ (s + 2) :=
    ⟨by simpa [s, show (5 : ℝ) / 2 = 1 / 2 + 2 by norm_num] using ivRat_mem 5 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs3 : Cval.mem ⟨ivRat 7 2, tIv⟩ (s + 3) :=
    ⟨by simpa [s, show (7 : ℝ) / 2 = 1 / 2 + 3 by norm_num] using ivRat_mem 7 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs4 : Cval.mem ⟨ivRat 9 2, tIv⟩ (s + 4) :=
    ⟨by simpa [s, show (9 : ℝ) / 2 = 1 / 2 + 4 by norm_num] using ivRat_mem 9 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hp3 := cvMul_mem (cvMul_mem hs0 hs1) hs2
  have hp5 := cvMul_mem (cvMul_mem hp3 hs3) hs4
  have ht12 : (cvDivNat (cvMul ⟨ivRat 1 2, tIv⟩ (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N))) 12).mem
      ((s / 12) * (N : ℂ) ^ (-(s + 1))) := by
    rw [show (s / 12) * (N : ℂ) ^ (-(s + 1)) = (s * (N : ℂ) ^ (-(s + 1))) / ((12 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hs0 hNms1) (by norm_num)
  have ht720 : (cvDivNat (cvMul (cvMul (cvMul ⟨ivRat 1 2, tIv⟩ ⟨ivRat 3 2, tIv⟩) ⟨ivRat 5 2, tIv⟩)
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N)))) 720).mem
      ((s * (s + 1) * (s + 2) / 720) * (N : ℂ) ^ (-(s + 3))) := by
    rw [show (s * (s + 1) * (s + 2) / 720) * (N : ℂ) ^ (-(s + 3)) =
      (s * (s + 1) * (s + 2) * (N : ℂ) ^ (-(s + 3))) / ((720 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hp3 hNms3) (by norm_num)
  have ht30240 : (cvDivNat (cvMul (cvMul (cvMul (cvMul (cvMul ⟨ivRat 1 2, tIv⟩ ⟨ivRat 3 2, tIv⟩)
      ⟨ivRat 5 2, tIv⟩) ⟨ivRat 7 2, tIv⟩) ⟨ivRat 9 2, tIv⟩)
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivSq (ivRat 1 (N : ℤ)))
        (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N))))) 30240).mem
      ((s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240) * (N : ℂ) ^ (-(s + 5))) := by
    rw [show (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240) * (N : ℂ) ^ (-(s + 5)) =
      (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (N : ℂ) ^ (-(s + 5))) / ((30240 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hp5 hNms5) (by norm_num)
  exact cvAdd_mem (cvSub_mem (cvAdd_mem (cvAdd_mem (cvAdd_mem hsum hdiv1) hhalf) ht12) ht720) ht30240

def cvEm3One (tIv : Ival) (N : ℕ) : Cval :=
  let s : Cval := ⟨ivConst 1, tIv⟩
  let tot := cvSumRangeBin 8 1 (N - 1) (cvNpowOne tIv)
  let Nms := cvNpowOne tIv N
  let N1ms := cvScale (ivConst (N : ℤ)) Nms
  let sm1 : Cval := ⟨ivConst 0, tIv⟩
  let tot := cvAdd tot (cvDiv N1ms sm1)
  let tot := cvAdd tot (cvDivNat Nms 2)
  let invN := ivRat 1 (N : ℤ)
  let invN2 := ivSq invN
  let Nms1 := cvScale invN Nms
  let tot := cvAdd tot (cvDivNat (cvMul s Nms1) 12)
  let s1 : Cval := ⟨ivConst 2, tIv⟩
  let s2 : Cval := ⟨ivConst 3, tIv⟩
  let p3 := cvMul (cvMul s s1) s2
  let Nms3 := cvScale invN2 Nms1
  let tot := cvSub tot (cvDivNat (cvMul p3 Nms3) 720)
  let s3 : Cval := ⟨ivConst 4, tIv⟩
  let s4 : Cval := ⟨ivConst 5, tIv⟩
  let p5 := cvMul (cvMul p3 s3) s4
  let Nms5 := cvScale invN2 Nms3
  cvAdd tot (cvDivNat (cvMul p5 Nms5) 30240)

lemma cvEm3One_mem {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {N : ℕ} (h1 : 1 ≤ N) (h2 : N ≤ 160)
    (htne : 0 < (cvNormSq ⟨ivConst 0, tIv⟩).lo) :
    (cvEm3One tIv N).mem (em3 ((1 : ℂ) + (t : ℂ) * I) N) := by
  set s : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNposZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast (by omega : 0 < N)
  have hsum : (cvSumRangeBin 8 1 (N - 1) (cvNpowOne tIv)).mem
      (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) := by
    have hIco : Finset.Ico 1 N = Finset.Icc 1 (N - 1) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco]
    exact cvSumRangeBin_mem (by omega) (fun n hn1 hn2 => cvNpowOne_mem ht hn1 (by omega))
  have hNms := cvNpowOne_mem ht h1 h2
  have hN1ms : (cvScale (ivConst (N : ℤ)) (cvNpowOne tIv N)).mem ((N : ℂ) ^ (1 - s)) := by
    have heq : (N : ℂ) ^ (1 - s) = (((N : ℤ) : ℝ) : ℂ) * (N : ℂ) ^ (-s) := by
      rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hNne, Complex.cpow_one]
      push_cast; rfl
    rw [heq]; exact cvScale_mem (ivConst_mem (N : ℤ)) hNms
  have hsm1 : Cval.mem ⟨ivConst 0, tIv⟩ (s - 1) :=
    ⟨by simpa [s] using ivConst_mem 0, by simpa [s] using ht⟩
  have hdiv1 := (cvDiv_mem hN1ms hsm1 htne).2
  have hhalf : (cvDivNat (cvNpowOne tIv N) 2).mem ((1 / 2 : ℂ) * (N : ℂ) ^ (-s)) := by
    rw [show (1 / 2 : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (-s) / ((2 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem hNms (by norm_num)
  have hinvN : (ivRat 1 (N : ℤ)).mem ((1 : ℝ) / (N : ℝ)) := by simpa using ivRat_mem 1 hNposZ
  have hinvN2 := ivSq_mem hinvN
  have hNms1 : (cvScale (ivRat 1 (N : ℤ)) (cvNpowOne tIv N)).mem ((N : ℂ) ^ (-(s + 1))) := by
    have heq : (N : ℂ) ^ (-(s + 1)) = (((1 : ℝ) / (N : ℝ) : ℝ) : ℂ) * (N : ℂ) ^ (-s) := by
      rw [show -(s + 1) = (-1 : ℂ) + (-s) by ring, Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN hNms
  have hNms3 : (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowOne tIv N))).mem
      ((N : ℂ) ^ (-(s + 3))) := by
    have heq : (N : ℂ) ^ (-(s + 3)) = ((((1 : ℝ) / (N : ℝ)) * ((1 : ℝ) / (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 1)) := by
      rw [show -(s + 3) = ((-1 : ℂ) + (-1 : ℂ)) + (-(s + 1)) by ring, Complex.cpow_add _ _ hNne,
        Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN2 hNms1
  have hNms5 : (cvScale (ivSq (ivRat 1 (N : ℤ)))
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowOne tIv N)))).mem
      ((N : ℂ) ^ (-(s + 5))) := by
    have heq : (N : ℂ) ^ (-(s + 5)) = ((((1 : ℝ) / (N : ℝ)) * ((1 : ℝ) / (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 3)) := by
      rw [show -(s + 5) = ((-1 : ℂ) + (-1 : ℂ)) + (-(s + 3)) by ring, Complex.cpow_add _ _ hNne,
        Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN2 hNms3
  have hs0 : Cval.mem ⟨ivConst 1, tIv⟩ s := ⟨by simpa [s] using ivConst_mem 1, by simpa [s] using ht⟩
  have hs1 : Cval.mem ⟨ivConst 2, tIv⟩ (s + 1) :=
    ⟨by simpa [s, show (2 : ℝ) = 1 + 1 by norm_num] using ivConst_mem 2, by simpa [s] using ht⟩
  have hs2 : Cval.mem ⟨ivConst 3, tIv⟩ (s + 2) :=
    ⟨by simpa [s, show (3 : ℝ) = 1 + 2 by norm_num] using ivConst_mem 3, by simpa [s] using ht⟩
  have hs3 : Cval.mem ⟨ivConst 4, tIv⟩ (s + 3) :=
    ⟨by simpa [s, show (4 : ℝ) = 1 + 3 by norm_num] using ivConst_mem 4, by simpa [s] using ht⟩
  have hs4 : Cval.mem ⟨ivConst 5, tIv⟩ (s + 4) :=
    ⟨by simpa [s, show (5 : ℝ) = 1 + 4 by norm_num] using ivConst_mem 5, by simpa [s] using ht⟩
  have hp3 := cvMul_mem (cvMul_mem hs0 hs1) hs2
  have hp5 := cvMul_mem (cvMul_mem hp3 hs3) hs4
  have ht12 : (cvDivNat (cvMul ⟨ivConst 1, tIv⟩ (cvScale (ivRat 1 (N : ℤ)) (cvNpowOne tIv N))) 12).mem
      ((s / 12) * (N : ℂ) ^ (-(s + 1))) := by
    rw [show (s / 12) * (N : ℂ) ^ (-(s + 1)) = (s * (N : ℂ) ^ (-(s + 1))) / ((12 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hs0 hNms1) (by norm_num)
  have ht720 : (cvDivNat (cvMul (cvMul (cvMul ⟨ivConst 1, tIv⟩ ⟨ivConst 2, tIv⟩) ⟨ivConst 3, tIv⟩)
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowOne tIv N)))) 720).mem
      ((s * (s + 1) * (s + 2) / 720) * (N : ℂ) ^ (-(s + 3))) := by
    rw [show (s * (s + 1) * (s + 2) / 720) * (N : ℂ) ^ (-(s + 3)) =
      (s * (s + 1) * (s + 2) * (N : ℂ) ^ (-(s + 3))) / ((720 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hp3 hNms3) (by norm_num)
  have ht30240 : (cvDivNat (cvMul (cvMul (cvMul (cvMul (cvMul ⟨ivConst 1, tIv⟩ ⟨ivConst 2, tIv⟩)
      ⟨ivConst 3, tIv⟩) ⟨ivConst 4, tIv⟩) ⟨ivConst 5, tIv⟩)
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivSq (ivRat 1 (N : ℤ)))
        (cvScale (ivRat 1 (N : ℤ)) (cvNpowOne tIv N))))) 30240).mem
      ((s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240) * (N : ℂ) ^ (-(s + 5))) := by
    rw [show (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240) * (N : ℂ) ^ (-(s + 5)) =
      (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (N : ℂ) ^ (-(s + 5))) / ((30240 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hp5 hNms5) (by norm_num)
  exact cvAdd_mem (cvSub_mem (cvAdd_mem (cvAdd_mem (cvAdd_mem hsum hdiv1) hhalf) ht12) ht720) ht30240

def cvDem3Half (tIv : Ival) (N : ℕ) : Cval :=
  let s : Cval := ⟨ivRat 1 2, tIv⟩
  let tot := cvSumRangeBin 8 1 (N - 1) (fun n => cvNeg (cvScale (ivLn n) (cvNpowHalf tIv n)))
  let lnN := ivLn N
  let Nms := cvNpowHalf tIv N
  let N1ms := cvScale (ivConst (N : ℤ)) Nms
  let sm1 : Cval := ⟨ivRat (-1) 2, tIv⟩
  let sm1sq := cvSq sm1
  let num1 := cvSub (cvNeg (cvScale lnN sm1)) ⟨ivConst 1, ivConst 0⟩
  let tot := cvAdd tot (cvDiv (cvMul num1 N1ms) sm1sq)
  let tot := cvSub tot (cvDivNat (cvScale lnN Nms) 2)
  let invN := ivRat 1 (N : ℤ)
  let invN2 := ivSq invN
  let Nms1 := cvScale invN Nms
  let num2 := cvSub ⟨ivConst 1, ivConst 0⟩ (cvScale lnN s)
  let tot := cvAdd tot (cvDivNat (cvMul num2 Nms1) 12)
  let s1 : Cval := ⟨ivRat 3 2, tIv⟩
  let s2 : Cval := ⟨ivRat 5 2, tIv⟩
  let p3 := cvMul (cvMul s s1) s2
  let dp3 := cvAdd (cvAdd (cvMul s1 s2) (cvMul s s2)) (cvMul s s1)
  let Nms3 := cvScale invN2 Nms1
  let tot := cvSub tot (cvDivNat (cvMul (cvSub dp3 (cvScale lnN p3)) Nms3) 720)
  let s3 : Cval := ⟨ivRat 7 2, tIv⟩
  let s4 : Cval := ⟨ivRat 9 2, tIv⟩
  let p5 := cvMul (cvMul p3 s3) s4
  let dp5 := cvAdd (cvMul (cvMul dp3 s3) s4) (cvMul p3 (cvAdd s3 s4))
  let Nms5 := cvScale invN2 Nms3
  cvAdd tot (cvDivNat (cvMul (cvSub dp5 (cvScale lnN p5)) Nms5) 30240)

lemma cvDem3Half_mem {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {N : ℕ} (h1 : 1 ≤ N) (h2 : N ≤ 160)
    (hsq_pos : 0 < (cvNormSq (cvSq ⟨ivRat (-1) 2, tIv⟩)).lo) :
    (cvDem3Half tIv N).mem (dem3 ((1 / 2 : ℂ) + (t : ℂ) * I) N) := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNposZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast (by omega : 0 < N)
  have hsum : (cvSumRangeBin 8 1 (N - 1) (fun n => cvNeg (cvScale (ivLn n) (cvNpowHalf tIv n)))).mem
      (∑ n ∈ Finset.Ico 1 N, -(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) := by
    have hIco : Finset.Ico 1 N = Finset.Icc 1 (N - 1) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco]
    refine cvSumRangeBin_mem (by omega) fun n hn1 hn2 => ?_
    rw [neg_mul]
    exact cvNeg_mem (cvScale_mem (ivLn_mem hn1 (by omega)) (cvNpowHalf_mem ht hn1 (by omega)))
  have hlnN := ivLn_mem h1 h2
  have hNms := cvNpowHalf_mem ht h1 h2
  have hN1ms : (cvScale (ivConst (N : ℤ)) (cvNpowHalf tIv N)).mem ((N : ℂ) ^ (1 - s)) := by
    have heq : (N : ℂ) ^ (1 - s) = (((N : ℤ) : ℝ) : ℂ) * (N : ℂ) ^ (-s) := by
      rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hNne, Complex.cpow_one]
      push_cast; rfl
    rw [heq]; exact cvScale_mem (ivConst_mem (N : ℤ)) hNms
  have h1c : Cval.mem ⟨ivConst 1, ivConst 0⟩ (1 : ℂ) :=
    ⟨by simpa using ivConst_mem 1, by simpa using ivConst_mem 0⟩
  have hsm1 : Cval.mem ⟨ivRat (-1) 2, tIv⟩ (s - 1) :=
    ⟨by simpa [s, show (-1 : ℝ) / 2 = 1 / 2 - 1 by norm_num] using ivRat_mem (-1) (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hsm1sq : (cvSq ⟨ivRat (-1) 2, tIv⟩).mem ((s - 1) ^ 2) := by
    rw [sq]; exact cvSq_mem hsm1
  have hnum1 : (cvSub (cvNeg (cvScale (ivLn N) ⟨ivRat (-1) 2, tIv⟩)) ⟨ivConst 1, ivConst 0⟩).mem
      (-(Real.log (N : ℝ) : ℂ) * (s - 1) - 1) := by
    rw [neg_mul]
    exact cvSub_mem (cvNeg_mem (cvScale_mem hlnN hsm1)) h1c
  have hterm1 := (cvDiv_mem (cvMul_mem hnum1 hN1ms) hsm1sq hsq_pos).2
  have hterm2 : (cvDivNat (cvScale (ivLn N) (cvNpowHalf tIv N)) 2).mem
      ((1 / 2 : ℂ) * (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)) := by
    rw [show (1 / 2 : ℂ) * (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) =
      ((Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)) / ((2 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvScale_mem hlnN hNms) (by norm_num)
  have hinvN : (ivRat 1 (N : ℤ)).mem ((1 : ℝ) / (N : ℝ)) := by simpa using ivRat_mem 1 hNposZ
  have hinvN2 := ivSq_mem hinvN
  have hNms1 : (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N)).mem ((N : ℂ) ^ (-(s + 1))) := by
    have heq : (N : ℂ) ^ (-(s + 1)) = (((1 : ℝ) / (N : ℝ) : ℝ) : ℂ) * (N : ℂ) ^ (-s) := by
      rw [show -(s + 1) = (-1 : ℂ) + (-s) by ring, Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN hNms
  have hNms3 : (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N))).mem
      ((N : ℂ) ^ (-(s + 3))) := by
    have heq : (N : ℂ) ^ (-(s + 3)) = ((((1 : ℝ) / (N : ℝ)) * ((1 : ℝ) / (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 1)) := by
      rw [show -(s + 3) = ((-1 : ℂ) + (-1 : ℂ)) + (-(s + 1)) by ring, Complex.cpow_add _ _ hNne,
        Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN2 hNms1
  have hNms5 : (cvScale (ivSq (ivRat 1 (N : ℤ)))
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N)))).mem
      ((N : ℂ) ^ (-(s + 5))) := by
    have heq : (N : ℂ) ^ (-(s + 5)) = ((((1 : ℝ) / (N : ℝ)) * ((1 : ℝ) / (N : ℝ)) : ℝ) : ℂ) * (N : ℂ) ^ (-(s + 3)) := by
      rw [show -(s + 5) = ((-1 : ℂ) + (-1 : ℂ)) + (-(s + 3)) by ring, Complex.cpow_add _ _ hNne,
        Complex.cpow_add _ _ hNne, Complex.cpow_neg_one]
      push_cast; rw [one_div]
    rw [heq]; exact cvScale_mem hinvN2 hNms3
  have hs0 : Cval.mem ⟨ivRat 1 2, tIv⟩ s :=
    ⟨by simpa [s] using ivRat_mem 1 (by norm_num : (0 : ℤ) < 2), by simpa [s] using ht⟩
  have hs1 : Cval.mem ⟨ivRat 3 2, tIv⟩ (s + 1) :=
    ⟨by simpa [s, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num] using ivRat_mem 3 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs2 : Cval.mem ⟨ivRat 5 2, tIv⟩ (s + 2) :=
    ⟨by simpa [s, show (5 : ℝ) / 2 = 1 / 2 + 2 by norm_num] using ivRat_mem 5 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs3 : Cval.mem ⟨ivRat 7 2, tIv⟩ (s + 3) :=
    ⟨by simpa [s, show (7 : ℝ) / 2 = 1 / 2 + 3 by norm_num] using ivRat_mem 7 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs4 : Cval.mem ⟨ivRat 9 2, tIv⟩ (s + 4) :=
    ⟨by simpa [s, show (9 : ℝ) / 2 = 1 / 2 + 4 by norm_num] using ivRat_mem 9 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hnum2 : (cvSub ⟨ivConst 1, ivConst 0⟩ (cvScale (ivLn N) ⟨ivRat 1 2, tIv⟩)).mem
      (1 - s * (Real.log (N : ℝ) : ℂ)) := by
    rw [mul_comm s]; exact cvSub_mem h1c (cvScale_mem hlnN hs0)
  have hterm3 : (cvDivNat (cvMul (cvSub ⟨ivConst 1, ivConst 0⟩ (cvScale (ivLn N) ⟨ivRat 1 2, tIv⟩))
      (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N))) 12).mem
      ((1 - s * (Real.log (N : ℝ) : ℂ)) / 12 * (N : ℂ) ^ (-(s + 1))) := by
    rw [show (1 - s * (Real.log (N : ℝ) : ℂ)) / 12 * (N : ℂ) ^ (-(s + 1)) =
      ((1 - s * (Real.log (N : ℝ) : ℂ)) * (N : ℂ) ^ (-(s + 1))) / ((12 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hnum2 hNms1) (by norm_num)
  have hp3 := cvMul_mem (cvMul_mem hs0 hs1) hs2
  have hdp3 := cvAdd_mem (cvAdd_mem (cvMul_mem hs1 hs2) (cvMul_mem hs0 hs2)) (cvMul_mem hs0 hs1)
  set p3c := cvMul (cvMul ⟨ivRat 1 2, tIv⟩ ⟨ivRat 3 2, tIv⟩) ⟨ivRat 5 2, tIv⟩
  set dp3c := cvAdd (cvAdd (cvMul ⟨ivRat 3 2, tIv⟩ ⟨ivRat 5 2, tIv⟩)
    (cvMul ⟨ivRat 1 2, tIv⟩ ⟨ivRat 5 2, tIv⟩)) (cvMul ⟨ivRat 1 2, tIv⟩ ⟨ivRat 3 2, tIv⟩)
  set num4c := cvSub dp3c (cvScale (ivLn N) p3c)
  have hnum4 : num4c.mem (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
        s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) := by
    rw [mul_comm (s * (s + 1) * (s + 2))]
    exact cvSub_mem hdp3 (cvScale_mem hlnN hp3)
  have hterm4 : (cvDivNat (cvMul num4c (cvScale (ivSq (ivRat 1 (N : ℤ)))
      (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N)))) 720).mem
      ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
        s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) / 720 * (N : ℂ) ^ (-(s + 3))) := by
    rw [show (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
        s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) / 720 * (N : ℂ) ^ (-(s + 3)) =
      ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) -
        s * (s + 1) * (s + 2) * (Real.log (N : ℝ) : ℂ)) * (N : ℂ) ^ (-(s + 3))) / ((720 : ℕ) : ℂ) by
      push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hnum4 hNms3) (by norm_num)
  set p5c := cvMul (cvMul p3c ⟨ivRat 7 2, tIv⟩) ⟨ivRat 9 2, tIv⟩
  set dp5c := cvAdd (cvMul (cvMul dp3c ⟨ivRat 7 2, tIv⟩) ⟨ivRat 9 2, tIv⟩)
    (cvMul p3c (cvAdd ⟨ivRat 7 2, tIv⟩ ⟨ivRat 9 2, tIv⟩))
  set num5c := cvSub dp5c (cvScale (ivLn N) p5c)
  have hp5 : p5c.mem (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) := cvMul_mem (cvMul_mem hp3 hs3) hs4
  have hdp5 : dp5c.mem (((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
      s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) :=
    cvAdd_mem (cvMul_mem (cvMul_mem hdp3 hs3) hs4) (cvMul_mem hp3 (cvAdd_mem hs3 hs4))
  have hnum5 : num5c.mem
      ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
        s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) := by
    rw [mul_comm (s * (s + 1) * (s + 2) * (s + 3) * (s + 4))]
    exact cvSub_mem hdp5 (cvScale_mem hlnN hp5)
  have hterm5 : (cvDivNat (cvMul num5c (cvScale (ivSq (ivRat 1 (N : ℤ)))
      (cvScale (ivSq (ivRat 1 (N : ℤ))) (cvScale (ivRat 1 (N : ℤ)) (cvNpowHalf tIv N))))) 30240).mem
      (((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
         s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) / 30240 *
        (N : ℂ) ^ (-(s + 5))) := by
    rw [show ((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
         s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) / 30240 *
        (N : ℂ) ^ (-(s + 5)) =
      (((((s + 1) * (s + 2) + s * (s + 2) + s * (s + 1)) * (s + 3) * (s + 4) +
         s * (s + 1) * (s + 2) * ((s + 3) + (s + 4))) -
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (Real.log (N : ℝ) : ℂ)) *
        (N : ℂ) ^ (-(s + 5))) / ((30240 : ℕ) : ℂ) by push_cast; ring]
    exact cvDivNat_mem (cvMul_mem hnum5 hNms5) (by norm_num)
  exact cvAdd_mem (cvSub_mem (cvAdd_mem (cvSub_mem (cvAdd_mem hsum hterm1) hterm2) hterm3) hterm4) hterm5

/-! == Remainder upper bounds (`R6` and `ζ' - dem3`) -/

def ivEm3RemHalfHi (tIv : Ival) (N : ℕ) : ℤ :=
  let p0 : Ival := ⟨0, cvNormL1Hi ⟨ivRat 1 2, tIv⟩⟩
  let p1 := ivMul p0 ⟨0, cvNormL1Hi ⟨ivRat 3 2, tIv⟩⟩
  let p2 := ivMul p1 ⟨0, cvNormL1Hi ⟨ivRat 5 2, tIv⟩⟩
  let p3 := ivMul p2 ⟨0, cvNormL1Hi ⟨ivRat 7 2, tIv⟩⟩
  let p4 := ivMul p3 ⟨0, cvNormL1Hi ⟨ivRat 9 2, tIv⟩⟩
  let p5 := ivMul p4 ⟨0, cvNormL1Hi ⟨ivRat 11 2, tIv⟩⟩
  (ivDivNat (ivMul p5 (ivInvSqrt N)) (166320 * N ^ 5)).hi

def ivEm3RemOneHi (tIv : Ival) (N : ℕ) : ℤ :=
  let p0 : Ival := ⟨0, cvNormL1Hi ⟨ivConst 1, tIv⟩⟩
  let p1 := ivMul p0 ⟨0, cvNormL1Hi ⟨ivConst 2, tIv⟩⟩
  let p2 := ivMul p1 ⟨0, cvNormL1Hi ⟨ivConst 3, tIv⟩⟩
  let p3 := ivMul p2 ⟨0, cvNormL1Hi ⟨ivConst 4, tIv⟩⟩
  let p4 := ivMul p3 ⟨0, cvNormL1Hi ⟨ivConst 5, tIv⟩⟩
  let p5 := ivMul p4 ⟨0, cvNormL1Hi ⟨ivConst 6, tIv⟩⟩
  (ivDivNat p5 (181440 * N ^ 6)).hi

def ivDem3RemHalfHi (tIv : Ival) (N : ℕ) : ℤ :=
  let q := ivRat 1 4
  let p0 := ivAdd ⟨0, cvNormL1Hi ⟨ivRat 1 2, tIv⟩⟩ q
  let p1 := ivMul p0 (ivAdd ⟨0, cvNormL1Hi ⟨ivRat 3 2, tIv⟩⟩ q)
  let p2 := ivMul p1 (ivAdd ⟨0, cvNormL1Hi ⟨ivRat 5 2, tIv⟩⟩ q)
  let p3 := ivMul p2 (ivAdd ⟨0, cvNormL1Hi ⟨ivRat 7 2, tIv⟩⟩ q)
  let p4 := ivMul p3 (ivAdd ⟨0, cvNormL1Hi ⟨ivRat 9 2, tIv⟩⟩ q)
  let p5 := ivMul p4 (ivAdd ⟨0, cvNormL1Hi ⟨ivRat 11 2, tIv⟩⟩ q)
  (ivDivNat p5 (39690 * N ^ 5)).hi

lemma ivEm3RemHalfHi_sound {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {N : ℕ} (h1 : 1 ≤ N) (h2 : N ≤ 160) :
    ‖R6 ((1 / 2 : ℂ) + (t : ℂ) * I) N‖ ≤ (ivEm3RemHalfHi tIv N : ℝ) / (Sval : ℝ) := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hs_re : s.re = 1 / 2 := by simp [s]
  have hR6 := norm_R6_le h1 (s := s) (by rw [hs_re]; norm_num)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpow : (N : ℝ) ^ (s.re + 5) = (N : ℝ) ^ 5 * ((N : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := by
    rw [hs_re, ← Real.rpow_neg hN0.le, neg_neg, show (1 / 2 : ℝ) + 5 = ((5 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Real.rpow_add hN0, Real.rpow_natCast]
  have hR6' : ‖R6 s N‖ ≤
      (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * (N : ℝ) ^ (-(1 / 2 : ℝ))) /
        ((166320 * N ^ 5 : ℕ) : ℝ) := by
    refine hR6.trans_eq ?_
    rw [hpow, hs_re]; push_cast
    have hinv_ne : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    field_simp [hN0.ne', hinv_ne]; ring
  have hs0 : Cval.mem ⟨ivRat 1 2, tIv⟩ s :=
    ⟨by simpa [s] using ivRat_mem 1 (by norm_num : (0 : ℤ) < 2), by simpa [s] using ht⟩
  have hs1 : Cval.mem ⟨ivRat 3 2, tIv⟩ (s + 1) :=
    ⟨by simpa [s, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num] using ivRat_mem 3 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs2 : Cval.mem ⟨ivRat 5 2, tIv⟩ (s + 2) :=
    ⟨by simpa [s, show (5 : ℝ) / 2 = 1 / 2 + 2 by norm_num] using ivRat_mem 5 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs3 : Cval.mem ⟨ivRat 7 2, tIv⟩ (s + 3) :=
    ⟨by simpa [s, show (7 : ℝ) / 2 = 1 / 2 + 3 by norm_num] using ivRat_mem 7 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs4 : Cval.mem ⟨ivRat 9 2, tIv⟩ (s + 4) :=
    ⟨by simpa [s, show (9 : ℝ) / 2 = 1 / 2 + 4 by norm_num] using ivRat_mem 9 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs5 : Cval.mem ⟨ivRat 11 2, tIv⟩ (s + 5) :=
    ⟨by simpa [s, show (11 : ℝ) / 2 = 1 / 2 + 5 by norm_num] using ivRat_mem 11 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hprod := ivMul_mem (ivMul_mem (ivMul_mem (ivMul_mem (ivMul_mem
    (cvNormL1Hi_mem_upper hs0) (cvNormL1Hi_mem_upper hs1))
    (cvNormL1Hi_mem_upper hs2)) (cvNormL1Hi_mem_upper hs3))
    (cvNormL1Hi_mem_upper hs4)) (cvNormL1Hi_mem_upper hs5)
  have hdiv := ivDivNat_mem (ivMul_mem hprod (ivInvSqrt_mem h1 h2))
    (by positivity : 0 < 166320 * N ^ 5)
  exact hR6'.trans hdiv.2

lemma ivEm3RemOneHi_sound {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {N : ℕ} (h1 : 1 ≤ N) :
    ‖R6 ((1 : ℂ) + (t : ℂ) * I) N‖ ≤ (ivEm3RemOneHi tIv N : ℝ) / (Sval : ℝ) := by
  set s : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hs_re : s.re = 1 := by simp [s]
  have hR6 := norm_R6_le h1 (s := s) (by rw [hs_re]; norm_num)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hR6' : ‖R6 s N‖ ≤
      (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖) / ((181440 * N ^ 6 : ℕ) : ℝ) := by
    refine hR6.trans_eq ?_
    rw [hs_re, show (1 : ℝ) + 5 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast; ring
  have hs0 : Cval.mem ⟨ivConst 1, tIv⟩ s := ⟨by simpa [s] using ivConst_mem 1, by simpa [s] using ht⟩
  have hs1 : Cval.mem ⟨ivConst 2, tIv⟩ (s + 1) :=
    ⟨by simpa [s, show (2 : ℝ) = 1 + 1 by norm_num] using ivConst_mem 2, by simpa [s] using ht⟩
  have hs2 : Cval.mem ⟨ivConst 3, tIv⟩ (s + 2) :=
    ⟨by simpa [s, show (3 : ℝ) = 1 + 2 by norm_num] using ivConst_mem 3, by simpa [s] using ht⟩
  have hs3 : Cval.mem ⟨ivConst 4, tIv⟩ (s + 3) :=
    ⟨by simpa [s, show (4 : ℝ) = 1 + 3 by norm_num] using ivConst_mem 4, by simpa [s] using ht⟩
  have hs4 : Cval.mem ⟨ivConst 5, tIv⟩ (s + 4) :=
    ⟨by simpa [s, show (5 : ℝ) = 1 + 4 by norm_num] using ivConst_mem 5, by simpa [s] using ht⟩
  have hs5 : Cval.mem ⟨ivConst 6, tIv⟩ (s + 5) :=
    ⟨by simpa [s, show (6 : ℝ) = 1 + 5 by norm_num] using ivConst_mem 6, by simpa [s] using ht⟩
  have hprod := ivMul_mem (ivMul_mem (ivMul_mem (ivMul_mem (ivMul_mem
    (cvNormL1Hi_mem_upper hs0) (cvNormL1Hi_mem_upper hs1))
    (cvNormL1Hi_mem_upper hs2)) (cvNormL1Hi_mem_upper hs3))
    (cvNormL1Hi_mem_upper hs4)) (cvNormL1Hi_mem_upper hs5)
  have hdiv := ivDivNat_mem hprod (by positivity : 0 < 181440 * N ^ 6)
  exact hR6'.trans hdiv.2

lemma ivDem3RemHalfHi_sound {tIv : Ival} {t : ℝ} (ht : tIv.mem t) {N : ℕ} (h1 : 1 ≤ N) :
    ‖deriv riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) - dem3 ((1 / 2 : ℂ) + (t : ℂ) * I) N‖ ≤
      (ivDem3RemHalfHi tIv N : ℝ) / (Sval : ℝ) := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hd := norm_deriv_riemannZeta_sub_dem3_le h1 t
  have hq : (ivRat 1 4).mem (1 / 4 : ℝ) := by simpa using ivRat_mem 1 (by norm_num : (0 : ℤ) < 4)
  have hs0 : Cval.mem ⟨ivRat 1 2, tIv⟩ s :=
    ⟨by simpa [s] using ivRat_mem 1 (by norm_num : (0 : ℤ) < 2), by simpa [s] using ht⟩
  have hs1 : Cval.mem ⟨ivRat 3 2, tIv⟩ (s + 1) :=
    ⟨by simpa [s, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num] using ivRat_mem 3 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs2 : Cval.mem ⟨ivRat 5 2, tIv⟩ (s + 2) :=
    ⟨by simpa [s, show (5 : ℝ) / 2 = 1 / 2 + 2 by norm_num] using ivRat_mem 5 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs3 : Cval.mem ⟨ivRat 7 2, tIv⟩ (s + 3) :=
    ⟨by simpa [s, show (7 : ℝ) / 2 = 1 / 2 + 3 by norm_num] using ivRat_mem 7 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs4 : Cval.mem ⟨ivRat 9 2, tIv⟩ (s + 4) :=
    ⟨by simpa [s, show (9 : ℝ) / 2 = 1 / 2 + 4 by norm_num] using ivRat_mem 9 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hs5 : Cval.mem ⟨ivRat 11 2, tIv⟩ (s + 5) :=
    ⟨by simpa [s, show (11 : ℝ) / 2 = 1 / 2 + 5 by norm_num] using ivRat_mem 11 (by norm_num : (0 : ℤ) < 2),
     by simpa [s] using ht⟩
  have hprod := ivMul_mem (ivMul_mem (ivMul_mem (ivMul_mem (ivMul_mem
    (ivAdd_mem (cvNormL1Hi_mem_upper hs0) hq) (ivAdd_mem (cvNormL1Hi_mem_upper hs1) hq))
    (ivAdd_mem (cvNormL1Hi_mem_upper hs2) hq)) (ivAdd_mem (cvNormL1Hi_mem_upper hs3) hq))
    (ivAdd_mem (cvNormL1Hi_mem_upper hs4) hq)) (ivAdd_mem (cvNormL1Hi_mem_upper hs5) hq)
  have hdiv := ivDivNat_mem hprod (by positivity : 0 < 39690 * N ^ 5)
  refine hd.trans ?_
  simpa [s, ivDem3RemHalfHi] using hdiv.2

/-! == Lipschitz bounds on vertical lines -/

lemma norm_zeta_half_sub_le {t₀ t T : ℝ} (_hT : 0 ≤ T) (ht₀ : |t₀| ≤ T) (ht : |t| ≤ T) :
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) - riemannZeta ((1 / 2 : ℂ) + (t₀ : ℂ) * I)‖ ≤
      (24 + 16 * ‖(1 / 2 : ℂ) + (T : ℂ) * I‖) * |t - t₀| := by
  let f : ℝ → ℂ := fun u => riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)
  have hdiff : ∀ u ∈ Set.Icc (-T) T, HasDerivAt f (deriv riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) * I) u := by
    intro u _
    have hne : (1 / 2 : ℂ) + (u : ℂ) * I ≠ 1 := by
      intro h; have := congr_arg Complex.re h; simp at this
    have hg : HasDerivAt (fun x : ℝ => (1 / 2 : ℂ) + (x : ℂ) * I) I u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const I |>.const_add (1 / 2 : ℂ)
    exact (differentiableAt_riemannZeta hne).hasDerivAt.comp u hg
  have hbd : ∀ u ∈ Set.Icc (-T) T, ‖deriv f u‖ ≤ 24 + 16 * ‖(1 / 2 : ℂ) + (T : ℂ) * I‖ := by
    intro u hu
    rw [(hdiff u hu).deriv, norm_mul, Complex.norm_I, mul_one]
    have h1 := norm_deriv_riemannZeta_half_le u
    have huT : u ^ 2 ≤ T ^ 2 := by
      have : |u| ≤ T := abs_le.mpr ⟨hu.1, hu.2⟩
      nlinarith [abs_le.mp this]
    have hnorm : ‖(1 / 2 : ℂ) + (u : ℂ) * I‖ ≤ ‖(1 / 2 : ℂ) + (T : ℂ) * I‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      apply Real.sqrt_le_sqrt
      simp [Complex.normSq_apply]
      nlinarith
    linarith
  have hmvt := (convex_Icc (-T) T).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hdiff u hu).differentiableAt) hbd (abs_le.mp ht₀) (abs_le.mp ht)
  simpa [f, Real.norm_eq_abs] using hmvt

lemma norm_deriv_zeta_half_sub_le {t₀ t T : ℝ} (_hT : 0 ≤ T) (ht₀ : |t₀| ≤ T) (ht : |t| ≤ T) :
    ‖deriv riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) -
      deriv riemannZeta ((1 / 2 : ℂ) + (t₀ : ℂ) * I)‖ ≤
      (192 + 128 * ‖(1 / 2 : ℂ) + (T : ℂ) * I‖) * |t - t₀| := by
  let f : ℝ → ℂ := fun u => deriv riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)
  have hdiff : ∀ u ∈ Set.Icc (-T) T,
      HasDerivAt f (iteratedDeriv 2 riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) * I) u := by
    intro u _
    have hopen : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hmem : (1 / 2 : ℂ) + (u : ℂ) * I ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
      intro h; have := congr_arg Complex.re h; simp at this
    have hd_diff : DifferentiableAt ℂ (deriv riemannZeta) ((1 / 2 : ℂ) + (u : ℂ) * I) :=
      (differentiableOn_riemannZeta.deriv hopen).differentiableAt (hopen.mem_nhds hmem)
    have hder2 : deriv (deriv riemannZeta) ((1 / 2 : ℂ) + (u : ℂ) * I) =
        iteratedDeriv 2 riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hg : HasDerivAt (fun x : ℝ => (1 / 2 : ℂ) + (x : ℂ) * I) I u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const I |>.const_add (1 / 2 : ℂ)
    have hc := hd_diff.hasDerivAt.comp u hg
    rw [hder2] at hc
    exact hc
  have hbd : ∀ u ∈ Set.Icc (-T) T, ‖deriv f u‖ ≤ 192 + 128 * ‖(1 / 2 : ℂ) + (T : ℂ) * I‖ := by
    intro u hu
    rw [(hdiff u hu).deriv, norm_mul, Complex.norm_I, mul_one]
    have h1 := norm_deriv2_riemannZeta_half_le u
    have huT : u ^ 2 ≤ T ^ 2 := by
      have : |u| ≤ T := abs_le.mpr ⟨hu.1, hu.2⟩
      nlinarith [abs_le.mp this]
    have hnorm : ‖(1 / 2 : ℂ) + (u : ℂ) * I‖ ≤ ‖(1 / 2 : ℂ) + (T : ℂ) * I‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      apply Real.sqrt_le_sqrt
      simp [Complex.normSq_apply]
      nlinarith
    linarith
  have hmvt := (convex_Icc (-T) T).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hdiff u hu).differentiableAt) hbd (abs_le.mp ht₀) (abs_le.mp ht)
  simpa [f, Real.norm_eq_abs] using hmvt

lemma norm_zeta_one_sub_le {t₀ t T : ℝ} (hlo : 2 ≤ t₀) (hlo2 : 2 ≤ t) (ht₀ : t₀ ≤ T) (ht : t ≤ T) :
    ‖riemannZeta ((1 : ℂ) + (t : ℂ) * I) - riemannZeta ((1 : ℂ) + (t₀ : ℂ) * I)‖ ≤
      (6 + 4 * ‖(1 : ℂ) + (T : ℂ) * I‖) * |t - t₀| := by
  let f : ℝ → ℂ := fun u => riemannZeta ((1 : ℂ) + (u : ℂ) * I)
  have hdiff : ∀ u ∈ Set.Icc (2 : ℝ) T,
      HasDerivAt f (deriv riemannZeta ((1 : ℂ) + (u : ℂ) * I) * I) u := by
    intro u hu
    have hne : (1 : ℂ) + (u : ℂ) * I ≠ 1 := by
      intro h; have := congr_arg Complex.im h; simp at this; linarith [hu.1]
    have hg : HasDerivAt (fun x : ℝ => (1 : ℂ) + (x : ℂ) * I) I u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const I |>.const_add (1 : ℂ)
    exact (differentiableAt_riemannZeta hne).hasDerivAt.comp u hg
  have hbd : ∀ u ∈ Set.Icc (2 : ℝ) T, ‖deriv f u‖ ≤ 6 + 4 * ‖(1 : ℂ) + (T : ℂ) * I‖ := by
    intro u hu
    rw [(hdiff u hu).deriv, norm_mul, Complex.norm_I, mul_one]
    have h1 := norm_deriv_riemannZeta_one_le (t := u) (by rw [abs_of_pos (by linarith [hu.1])]; exact hu.1)
    have hnorm : ‖(1 : ℂ) + (u : ℂ) * I‖ ≤ ‖(1 : ℂ) + (T : ℂ) * I‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      apply Real.sqrt_le_sqrt
      simp [Complex.normSq_apply]
      nlinarith [hu.1, hu.2]
    linarith
  have hmvt := (convex_Icc (2 : ℝ) T).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hdiff u hu).differentiableAt) hbd ⟨hlo, ht₀⟩ ⟨hlo2, ht⟩
  simpa [f, Real.norm_eq_abs] using hmvt

/-! == Certificates 2, 3, 4, 5 and final proof of `S_pos_infinite` -/

def gMid (k : ℕ) : ℤ :=
  match k with
  | 0 => 141347251
  | 1 => 250108576
  | 2 => 304248761
  | _ => 409187190

def deltaNum : ℤ := 5
def deltaIv : Ival := ivRat 5 10000000

def certR0Iv : Ival :=
  let zh := cvEm3Half (ivConst 0) 20
  let ze := ivEm3RemHalfHi (ivConst 0) 20
  let zr : Ival := ⟨zh.re.lo - ze, zh.re.hi + ze⟩
  ivDivNat (ivInvPos (ivNeg zr)) 3

def zmVal (k : ℕ) : Cval :=
  let tm := ivRat (gMid k - deltaNum) 10000000
  cvExpand (cvEm3Half tm 160) (ivEm3RemHalfHi tm 160)

def zpVal (k : ℕ) : Cval :=
  let tp := ivRat (gMid k + deltaNum) 10000000
  cvExpand (cvEm3Half tp 160) (ivEm3RemHalfHi tp 160)

def dzVal (k : ℕ) : Cval :=
  let gm := gMid k
  let tp := ivRat (gm + deltaNum) 10000000
  let t0 := ivRat gm 10000000
  let dzEm := cvDem3Half t0 160
  let dzRem := ivDem3RemHalfHi t0 160
  let d2Hi := 192 * Sval + 128 * cvNormL1Hi ⟨ivRat 1 2, tp⟩
  let dzLip := cdiv (d2Hi * deltaIv.hi) Sval
  cvExpand dzEm (dzRem + dzLip)

def z2Val (k : ℕ) : Cval :=
  let gm := gMid k
  let t20 := ivRat (2 * gm) 10000000
  let t2p := ivRat (2 * (gm + deltaNum)) 10000000
  let z2Em := cvEm3One t20 160
  let z2Rem := ivEm3RemOneHi t20 160
  let dz2Hi := 6 * Sval + 4 * cvNormL1Hi ⟨ivConst 1, t2p⟩
  let z2Lip := cdiv (dz2Hi * (2 * deltaIv.hi)) Sval
  cvExpand z2Em (z2Rem + z2Lip)

def resFromLits (k : ℕ) (dz z2 : Cval) : Cval :=
  let gm := gMid k
  let tm := ivRat (gm - deltaNum) 10000000
  let tp := ivRat (gm + deltaNum) 10000000
  let rhoP1 : Cval := ⟨ivRat 3 2, ⟨tm.lo, tp.hi⟩⟩
  cvDiv (cvSub ⟨ivConst 1, ivConst 0⟩ z2) (cvMul rhoP1 dz)

def checkZeroLits (k : ℕ) (zm zp dz _z2 : Cval) : Bool :=
  let gm := gMid k
  let tm := ivRat (gm - deltaNum) 10000000
  let tp := ivRat (gm + deltaNum) 10000000
  let t0 := ivRat gm 10000000
  let t20 := ivRat (2 * gm) 10000000
  let q := cvDiv zm zp
  let lamHi := q.re.hi + cdiv (cvNormL1Hi q) 100
  let rhoP1 : Cval := ⟨ivRat 3 2, ⟨tm.lo, tp.hi⟩⟩
  decide (0 < (cvNormSq zp).lo ∧ lamHi < 0 ∧ 0 < (cvNormSq dz).lo ∧
    0 < (cvNormSq (cvMul rhoP1 dz)).lo ∧
    0 < (cvNormSq (cvSq ⟨ivRat (-1) 2, t0⟩)).lo ∧
    0 < (cvNormSq ⟨ivConst 0, t20⟩).lo)

-- Certificate 2: R0 upper bound
theorem cert_R0_eq : certR0Iv = R0Lit := by decide
theorem cert_zhalf_neg : (cvEm3Half (ivConst 0) 20).re.hi + ivEm3RemHalfHi (ivConst 0) 20 < 0 := by decide

lemma cert_R0_mem : R0Lit.mem R0 := by
  have hze := ivEm3RemHalfHi_sound (by simpa using ivConst_mem 0) (by norm_num : 1 ≤ 20) (by norm_num : 20 ≤ 160)
  have hzm := cvEm3Half_mem (by simpa using ivConst_mem 0) (by norm_num : 1 ≤ 20) (by norm_num : 20 ≤ 160)
  have hzeta : riemannZeta ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * I) =
      em3 ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * I) 20 + R6 ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * I) 20 :=
    riemannZeta_eq_em3_add_R6 (by norm_num) (by simp) (by intro h; have := congr_arg Complex.re h; simp at this)
  have hz_mem : (cvExpand (cvEm3Half (ivConst 0) 20) (ivEm3RemHalfHi (ivConst 0) 20)).mem
      (riemannZeta ((1 / 2 : ℝ) : ℂ)) := by
    have harg : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg]
    refine cvExpand_mem hzm ?_
    rw [hzeta, add_sub_cancel_left]; exact hze
  have hneg_pos : 0 < (ivNeg ⟨(cvEm3Half (ivConst 0) 20).re.lo - ivEm3RemHalfHi (ivConst 0) 20,
      (cvEm3Half (ivConst 0) 20).re.hi + ivEm3RemHalfHi (ivConst 0) 20⟩).lo := by
    dsimp only [ivNeg]; have := cert_zhalf_neg; omega
  have hinv := (ivInvPos_mem (ivNeg_mem hz_mem.1) hneg_pos).2
  have hdiv := ivDivNat_mem hinv (by norm_num : 0 < 3)
  rw [show (-(riemannZeta ((1 / 2 : ℝ) : ℂ)).re)⁻¹ / ((3 : ℕ) : ℝ) = R0 by
    dsimp only [R0]; push_cast; ring] at hdiv
  rw [← cert_R0_eq]
  exact hdiv

-- Certificate 3: 4 critical-line zeros & residue enclosures (each decide evaluates ONE N=160 sum!)
theorem cert_zm0 : zmVal 0 = zmLit0 := by decide
theorem cert_zp0 : zpVal 0 = zpLit0 := by decide
theorem cert_dz0 : dzVal 0 = dzLit0 := by decide
theorem cert_z20 : z2Val 0 = z2Lit0 := by decide

theorem cert_zm1 : zmVal 1 = zmLit1 := by decide
theorem cert_zp1 : zpVal 1 = zpLit1 := by decide
theorem cert_dz1 : dzVal 1 = dzLit1 := by decide
theorem cert_z21 : z2Val 1 = z2Lit1 := by decide

theorem cert_zm2 : zmVal 2 = zmLit2 := by decide
theorem cert_zp2 : zpVal 2 = zpLit2 := by decide
theorem cert_dz2 : dzVal 2 = dzLit2 := by decide
theorem cert_z22 : z2Val 2 = z2Lit2 := by decide

theorem cert_zm3 : zmVal 3 = zmLit3 := by decide
theorem cert_zp3 : zpVal 3 = zpLit3 := by decide
theorem cert_dz3 : dzVal 3 = dzLit3 := by decide
theorem cert_z23 : z2Val 3 = z2Lit3 := by decide

theorem cert_zeros_ok :
    checkZeroLits 0 zmLit0 zpLit0 dzLit0 z2Lit0 &&
    checkZeroLits 1 zmLit1 zpLit1 dzLit1 z2Lit1 &&
    checkZeroLits 2 zmLit2 zpLit2 dzLit2 z2Lit2 &&
    checkZeroLits 3 zmLit3 zpLit3 dzLit3 z2Lit3 = true := by decide

lemma cert_zero_exists (k : Fin 4)
    (zm zp dz z2 : Cval)
    (hzm : zmVal k.1 = zm) (hzp : zpVal k.1 = zp)
    (hdz : dzVal k.1 = dz) (hz2 : z2Val k.1 = z2)
    (hok : checkZeroLits k.1 zm zp dz z2 = true) :
    ∃ γ : ℝ,
      ((gMid k.1 - deltaNum : ℤ) : ℝ) / 10000000 ≤ γ ∧
      γ ≤ ((gMid k.1 + deltaNum : ℤ) : ℝ) / 10000000 ∧
      0 < γ ∧
      riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 ∧
      deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) ≠ 0 ∧
      (resFromLits k.1 dz z2).mem (resAt γ) := by
  have hS := Sval_pos
  simp only [checkZeroLits, decide_eq_true_eq] at hok
  set gm := gMid k.1
  set t1 : ℝ := ((gm - deltaNum : ℤ) : ℝ) / 10000000
  set t2 : ℝ := ((gm + deltaNum : ℤ) : ℝ) / 10000000
  set t0 : ℝ := (gm : ℝ) / 10000000
  have hgm_range : 140000000 ≤ gm ∧ gm ≤ 410000000 := by
    fin_cases k <;> dsimp only [gm, gMid] <;> decide
  have ht1_mem : (ivRat (gm - deltaNum) 10000000).mem t1 := by
    simpa [t1] using ivRat_mem (gm - deltaNum) (by norm_num : (0 : ℤ) < 10000000)
  have ht2_mem : (ivRat (gm + deltaNum) 10000000).mem t2 := by
    simpa [t2] using ivRat_mem (gm + deltaNum) (by norm_num : (0 : ℤ) < 10000000)
  have ht0_mem : (ivRat gm 10000000).mem t0 := by
    simpa [t0] using ivRat_mem gm (by norm_num : (0 : ℤ) < 10000000)
  have hzm_mem : zm.mem (riemannZeta ((1 / 2 : ℂ) + (t1 : ℂ) * I)) := by
    rw [← hzm]; dsimp only [zmVal]
    refine cvExpand_mem (cvEm3Half_mem ht1_mem (by norm_num) (by norm_num)) ?_
    have hz := riemannZeta_eq_em3_add_R6 (N := 160) (by norm_num) (s := (1 / 2 : ℂ) + (t1 : ℂ) * I)
      (by simp) (by intro h; have := congr_arg Complex.re h; simp at this)
    rw [hz, add_sub_cancel_left]
    exact ivEm3RemHalfHi_sound ht1_mem (by norm_num) (by norm_num)
  have hzp_mem : zp.mem (riemannZeta ((1 / 2 : ℂ) + (t2 : ℂ) * I)) := by
    rw [← hzp]; dsimp only [zpVal]
    refine cvExpand_mem (cvEm3Half_mem ht2_mem (by norm_num) (by norm_num)) ?_
    have hz := riemannZeta_eq_em3_add_R6 (N := 160) (by norm_num) (s := (1 / 2 : ℂ) + (t2 : ℂ) * I)
      (by simp) (by intro h; have := congr_arg Complex.re h; simp at this)
    rw [hz, add_sub_cancel_left]
    exact ivEm3RemHalfHi_sound ht2_mem (by norm_num) (by norm_num)
  obtain ⟨hζ2_ne, hq_mem⟩ := cvDiv_mem hzm_mem hzp_mem hok.1
  have hq_norm := norm_le_cvNormL1Hi hq_mem
  have hlam_neg :
      (riemannZeta ((1 / 2 : ℂ) + (t1 : ℂ) * I) / riemannZeta ((1 / 2 : ℂ) + (t2 : ℂ) * I)).re +
        (1 / 100 : ℝ) * ‖riemannZeta ((1 / 2 : ℂ) + (t1 : ℂ) * I) /
          riemannZeta ((1 / 2 : ℂ) + (t2 : ℂ) * I)‖ < 0 := by
    have hcd := div_le_cdiv (cvNormL1Hi (cvDiv zm zp)) (by norm_num : (0 : ℤ) < 100)
    have h1 : (1 / 100 : ℝ) * ((cvNormL1Hi (cvDiv zm zp) : ℝ) / (Sval : ℝ)) ≤
        (cdiv (cvNormL1Hi (cvDiv zm zp)) 100 : ℝ) / (Sval : ℝ) := by
      rw [show (1 / 100 : ℝ) * ((cvNormL1Hi (cvDiv zm zp) : ℝ) / (Sval : ℝ)) =
        ((cvNormL1Hi (cvDiv zm zp) : ℝ) / (100 : ℤ)) / (Sval : ℝ) by push_cast; ring]
      exact div_le_div_of_nonneg_right hcd hS.le
    have h2 : (((cvDiv zm zp).re.hi + cdiv (cvNormL1Hi (cvDiv zm zp)) 100 : ℤ) : ℝ) / (Sval : ℝ) < 0 := by
      have : ((cvDiv zm zp).re.hi + cdiv (cvNormL1Hi (cvDiv zm zp)) 100 : ℤ) < 0 := hok.2.1
      exact div_neg_of_neg_of_pos (by exact_mod_cast this) hS
    push_cast at h2; rw [add_div] at h2
    linarith [hq_mem.1.2]
  have h12 : t1 ≤ t2 := by dsimp only [t1, t2, deltaNum]; push_cast; linarith
  have ht1_bd : |t1| ≤ 42 := by
    have hgm1 : (140000000 : ℝ) ≤ (gm : ℝ) := by exact_mod_cast hgm_range.1
    have hgm2 : (gm : ℝ) ≤ (410000000 : ℝ) := by exact_mod_cast hgm_range.2
    rw [abs_le]; dsimp only [t1, deltaNum]; push_cast; constructor <;> linarith
  have ht2_bd : |t2| ≤ 42 := by
    have hgm1 : (140000000 : ℝ) ≤ (gm : ℝ) := by exact_mod_cast hgm_range.1
    have hgm2 : (gm : ℝ) ≤ (410000000 : ℝ) := by exact_mod_cast hgm_range.2
    rw [abs_le]; dsimp only [t2, deltaNum]; push_cast; constructor <;> linarith
  have hdiff : t2 - t1 ≤ 1 / 10 ^ 6 := by
    dsimp only [t1, t2, deltaNum]; push_cast; linarith
  obtain ⟨γ, ⟨hγ1, hγ2⟩, hγ_zero⟩ := exists_zero_of_ratio_neg h12 ht1_bd ht2_bd hdiff hζ2_ne hlam_neg
  have hγ_pos : 0 < γ := by
    have hgm1 : (140000000 : ℝ) ≤ (gm : ℝ) := by exact_mod_cast hgm_range.1
    dsimp only [t1, deltaNum] at hγ1; push_cast at hγ1; linarith
  have hγ_t0 : |γ - t0| ≤ 5 / 10000000 := by
    rw [abs_le]; dsimp only [t0, t1, t2, deltaNum] at hγ1 hγ2 ⊢; push_cast at hγ1 hγ2 ⊢
    constructor <;> linarith
  have hδ_mem : deltaIv.mem (5 / 10000000 : ℝ) := by
    simpa [deltaIv] using ivRat_mem 5 (by norm_num : (0 : ℤ) < 10000000)
  have hdz_mem : dz.mem (deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I)) := by
    rw [← hdz]; dsimp only [dzVal]
    refine cvExpand_mem (cvDem3Half_mem ht0_mem (by norm_num) (by norm_num) hok.2.2.2.2.1) ?_
    have hrem := ivDem3RemHalfHi_sound ht0_mem (by norm_num : 1 ≤ 160)
    have hgm1_dz : (140000000 : ℝ) ≤ (gm : ℝ) := by exact_mod_cast hgm_range.1
    have ht0_pos : 0 < t0 := by dsimp only [t0]; linarith
    have hlip := norm_deriv_zeta_half_sub_le (t₀ := t0) (t := γ) (T := t2)
      (by linarith) (by rw [abs_of_pos ht0_pos]; dsimp only [t0, t2, deltaNum]; push_cast; linarith)
      (by rw [abs_of_pos hγ_pos]; exact hγ2)
    have hs_tp : Cval.mem ⟨ivRat 1 2, ivRat (gm + deltaNum) 10000000⟩ ((1 / 2 : ℂ) + (t2 : ℂ) * I) :=
      ⟨by simpa using ivRat_mem 1 (by norm_num : (0 : ℤ) < 2), by simpa using ht2_mem⟩
    have hn_tp := norm_le_cvNormL1Hi hs_tp
    have hd2_le : 192 + 128 * ‖(1 / 2 : ℂ) + (t2 : ℂ) * I‖ ≤
        ((192 * Sval + 128 * cvNormL1Hi ⟨ivRat 1 2, ivRat (gm + deltaNum) 10000000⟩ : ℤ) : ℝ) / (Sval : ℝ) := by
      push_cast; rw [add_div, mul_div_cancel_right₀ _ hS.ne', mul_div_assoc]; linarith
    have hlip_bd : (192 + 128 * ‖(1 / 2 : ℂ) + (t2 : ℂ) * I‖) * |γ - t0| ≤
        (cdiv ((192 * Sval + 128 * cvNormL1Hi ⟨ivRat 1 2, ivRat (gm + deltaNum) 10000000⟩) * deltaIv.hi) Sval : ℝ) /
          (Sval : ℝ) := by
      have hcd := div_le_cdiv ((192 * Sval + 128 * cvNormL1Hi ⟨ivRat 1 2, ivRat (gm + deltaNum) 10000000⟩) * deltaIv.hi) Sval_int_pos
      have hmul := mul_le_mul hd2_le (hγ_t0.trans hδ_mem.2) (abs_nonneg _)
        (by linarith [norm_nonneg ((1 / 2 : ℂ) + (t2 : ℂ) * I)])
      calc _ ≤ (((192 * Sval + 128 * cvNormL1Hi ⟨ivRat 1 2, ivRat (gm + deltaNum) 10000000⟩ : ℤ) : ℝ) / (Sval : ℝ)) *
            ((deltaIv.hi : ℝ) / (Sval : ℝ)) := hmul
        _ = ((((192 * Sval + 128 * cvNormL1Hi ⟨ivRat 1 2, ivRat (gm + deltaNum) 10000000⟩) * deltaIv.hi : ℤ) : ℝ) /
            (Sval : ℝ)) / (Sval : ℝ) := by push_cast; ring
        _ ≤ _ := div_le_div_of_nonneg_right hcd hS.le
    calc ‖deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) - dem3 ((1 / 2 : ℂ) + (t0 : ℂ) * I) 160‖
        = ‖(deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) - deriv riemannZeta ((1 / 2 : ℂ) + (t0 : ℂ) * I)) +
           (deriv riemannZeta ((1 / 2 : ℂ) + (t0 : ℂ) * I) - dem3 ((1 / 2 : ℂ) + (t0 : ℂ) * I) 160)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) - deriv riemannZeta ((1 / 2 : ℂ) + (t0 : ℂ) * I)‖ +
          ‖deriv riemannZeta ((1 / 2 : ℂ) + (t0 : ℂ) * I) - dem3 ((1 / 2 : ℂ) + (t0 : ℂ) * I) 160‖ := norm_add_le _ _
      _ ≤ _ := by push_cast; rw [add_div]; linarith
  have hdz_ne : deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) ≠ 0 := (cvInv_mem hdz_mem hok.2.2.1).1
  have hz2_mem : z2.mem (riemannZeta ((1 : ℂ) + (2 * γ : ℂ) * I)) := by
    rw [← hz2]; dsimp only [z2Val]
    have ht20_mem : (ivRat (2 * gm) 10000000).mem (2 * t0) := by
      have h := ivRat_mem (2 * gm) (by norm_num : (0 : ℤ) < 10000000)
      simpa [t0, mul_div_assoc] using h
    have ht2p_mem : (ivRat (2 * (gm + deltaNum)) 10000000).mem (2 * t2) := by
      have h := ivRat_mem (2 * (gm + deltaNum)) (by norm_num : (0 : ℤ) < 10000000)
      simpa [t2, mul_div_assoc] using h
    refine cvExpand_mem (cvEm3One_mem ht20_mem (by norm_num) (by norm_num) hok.2.2.2.2.2) ?_
    have hrem := ivEm3RemOneHi_sound ht20_mem (by norm_num : 1 ≤ 160)
    have hgm1 : (140000000 : ℝ) ≤ (gm : ℝ) := by exact_mod_cast hgm_range.1
    have h2t0_ge : 2 ≤ 2 * t0 := by dsimp only [t0]; linarith
    have h2γ_ge : 2 ≤ 2 * γ := by dsimp only [t1, deltaNum] at hγ1; push_cast at hγ1; linarith
    have hlip := norm_zeta_one_sub_le (t₀ := 2 * t0) (t := 2 * γ) (T := 2 * t2)
      h2t0_ge h2γ_ge (by dsimp only [t0, t2, deltaNum]; push_cast; linarith) (by linarith)
    have hs_t2p : Cval.mem ⟨ivConst 1, ivRat (2 * (gm + deltaNum)) 10000000⟩ ((1 : ℂ) + ((2 * t2 : ℝ) : ℂ) * I) :=
      ⟨by simpa using ivConst_mem 1, by simpa using ht2p_mem⟩
    have hn_t2p := norm_le_cvNormL1Hi hs_t2p
    have hdz2_le : 6 + 4 * ‖(1 : ℂ) + ((2 * t2 : ℝ) : ℂ) * I‖ ≤
        ((6 * Sval + 4 * cvNormL1Hi ⟨ivConst 1, ivRat (2 * (gm + deltaNum)) 10000000⟩ : ℤ) : ℝ) / (Sval : ℝ) := by
      push_cast at hn_t2p ⊢; rw [add_div, mul_div_cancel_right₀ _ hS.ne', mul_div_assoc]; linarith
    have h2diff : |2 * γ - 2 * t0| ≤ ((2 * deltaIv.hi : ℤ) : ℝ) / (Sval : ℝ) := by
      have : |2 * γ - 2 * t0| = 2 * |γ - t0| := by rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [this]; push_cast; rw [mul_div_assoc]; linarith [hγ_t0, hδ_mem.2]
    have hlip_bd : (6 + 4 * ‖(1 : ℂ) + ((2 * t2 : ℝ) : ℂ) * I‖) * |2 * γ - 2 * t0| ≤
        (cdiv ((6 * Sval + 4 * cvNormL1Hi ⟨ivConst 1, ivRat (2 * (gm + deltaNum)) 10000000⟩) * (2 * deltaIv.hi)) Sval : ℝ) /
          (Sval : ℝ) := by
      have hcd := div_le_cdiv ((6 * Sval + 4 * cvNormL1Hi ⟨ivConst 1, ivRat (2 * (gm + deltaNum)) 10000000⟩) * (2 * deltaIv.hi)) Sval_int_pos
      have hmul := mul_le_mul hdz2_le h2diff (abs_nonneg _)
        (by linarith [norm_nonneg ((1 : ℂ) + ((2 * t2 : ℝ) : ℂ) * I)])
      calc _ ≤ (((6 * Sval + 4 * cvNormL1Hi ⟨ivConst 1, ivRat (2 * (gm + deltaNum)) 10000000⟩ : ℤ) : ℝ) / (Sval : ℝ)) *
            (((2 * deltaIv.hi : ℤ) : ℝ) / (Sval : ℝ)) := hmul
        _ = ((((6 * Sval + 4 * cvNormL1Hi ⟨ivConst 1, ivRat (2 * (gm + deltaNum)) 10000000⟩) * (2 * deltaIv.hi) : ℤ) : ℝ) /
            (Sval : ℝ)) / (Sval : ℝ) := by push_cast; ring
        _ ≤ _ := div_le_div_of_nonneg_right hcd hS.le
    have hz1 := riemannZeta_eq_em3_add_R6 (N := 160) (by norm_num) (s := (1 : ℂ) + ((2 * t0 : ℝ) : ℂ) * I)
      (by simp) (by intro h; have := congr_arg Complex.im h; simp at this; linarith)
    have h2γ_eq : (1 : ℂ) + (2 * γ : ℂ) * I = (1 : ℂ) + ((2 * γ : ℝ) : ℂ) * I := by push_cast; rfl
    rw [h2γ_eq]
    calc ‖riemannZeta ((1 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - em3 ((1 : ℂ) + ((2 * t0 : ℝ) : ℂ) * I) 160‖
        = ‖(riemannZeta ((1 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - riemannZeta ((1 : ℂ) + ((2 * t0 : ℝ) : ℂ) * I)) +
           R6 ((1 : ℂ) + ((2 * t0 : ℝ) : ℂ) * I) 160‖ := by rw [hz1]; ring_nf
      _ ≤ ‖riemannZeta ((1 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - riemannZeta ((1 : ℂ) + ((2 * t0 : ℝ) : ℂ) * I)‖ +
          ‖R6 ((1 : ℂ) + ((2 * t0 : ℝ) : ℂ) * I) 160‖ := norm_add_le _ _
      _ ≤ _ := by rw [Int.cast_add, add_div]; linarith [hlip, hlip_bd, hrem]
  have hrhoP1 : Cval.mem ⟨ivRat 3 2, ⟨(ivRat (gm - deltaNum) 10000000).lo, (ivRat (gm + deltaNum) 10000000).hi⟩⟩
      ((3 / 2 : ℂ) + (γ : ℂ) * I) := by
    refine ⟨by simpa using ivRat_mem 3 (by norm_num : (0 : ℤ) < 2), ?_⟩
    have him : ((3 / 2 : ℂ) + (γ : ℂ) * I).im = γ := by simp
    exact ⟨by rw [him]; exact ht1_mem.1.trans hγ1, by rw [him]; exact hγ2.trans ht2_mem.2⟩
  have hnum_res : (cvSub ⟨ivConst 1, ivConst 0⟩ z2).mem (1 - riemannZeta ((1 : ℂ) + (2 * γ : ℂ) * I)) :=
    cvSub_mem ⟨by simpa using ivConst_mem 1, by simpa using ivConst_mem 0⟩ hz2_mem
  have hden_res := cvMul_mem hrhoP1 hdz_mem
  have hres := (cvDiv_mem hnum_res hden_res hok.2.2.2.1).2
  exact ⟨γ, hγ1, hγ2, hγ_pos, hγ_zero, hdz_ne, hres⟩

-- Certificate 4: Negative quadratic form value (pure integer arithmetic on literals!)
def resLit (k : Fin 4) : Cval :=
  match k with
  | 0 => resFromLits 0 dzLit0 z2Lit0
  | 1 => resFromLits 1 dzLit1 z2Lit1
  | 2 => resFromLits 2 dzLit2 z2Lit2
  | 3 => resFromLits 3 dzLit3 z2Lit3

def certPt (i : Fin 68) : ℤ × ℤ × ℤ × ℤ := certPtVal i.1
def certW (i : Fin 68) : ℂ := ((certWtVal i.1).1 : ℂ) + ((certWtVal i.1).2 : ℂ) * I

def edgeMatch (k : ℕ) (i j : ℕ) : Bool :=
  let pi := certPtVal i
  let pj := certPtVal j
  decide (pi.1 - pj.1 = (if k = 0 then 1 else 0) ∧
          pi.2.1 - pj.2.1 = (if k = 1 then 1 else 0) ∧
          pi.2.2.1 - pj.2.2.1 = (if k = 2 then 1 else 0) ∧
          pi.2.2.2 - pj.2.2.2 = (if k = 3 then 1 else 0))

def edgeReSum (k : ℕ) : ℤ :=
  intSumRangeBin 7 0 67 fun i =>
    intSumRangeBin 7 0 67 fun j =>
      if edgeMatch k i j then
        (certWtVal j).1 * (certWtVal i).1 + (certWtVal j).2 * (certWtVal i).2
      else 0

def edgeImSum (k : ℕ) : ℤ :=
  intSumRangeBin 7 0 67 fun i =>
    intSumRangeBin 7 0 67 fun j =>
      if edgeMatch k i j then
        (certWtVal j).2 * (certWtVal i).1 - (certWtVal j).1 * (certWtVal i).2
      else 0

theorem cert_pts_inj_bool :
    checkRangeBin 7 0 67 (fun i =>
      checkRangeBin 7 0 67 (fun j => decide (certPtVal i = certPtVal j → i = j))) = true := by
  decide

theorem cert_norm_sq_eq :
    intSumRangeBin 7 0 67 (fun i => (certWtVal i).1 * (certWtVal i).1 + (certWtVal i).2 * (certWtVal i).2) =
      999413 := by decide

theorem cert_edges_eq :
    edgeReSum 0 = -588301 ∧ edgeImSum 0 = 680022 ∧
    edgeReSum 1 = 345370 ∧ edgeImSum 1 = -361139 ∧
    edgeReSum 2 = -36887 ∧ edgeImSum 2 = -498338 ∧
    edgeReSum 3 = -457047 ∧ edgeImSum 3 = 492192 := by decide

theorem cert_Q_neg :
    let q0 := ivMulInt 999413 R0Lit
    let r0 := resLit 0; let r1 := resLit 1; let r2 := resLit 2; let r3 := resLit 3
    let t0 := ivSub (ivMulInt (-588301) r0.re) (ivMulInt 680022 r0.im)
    let t1 := ivSub (ivMulInt 345370 r1.re) (ivMulInt (-361139) r1.im)
    let t2 := ivSub (ivMulInt (-36887) r2.re) (ivMulInt (-498338) r2.im)
    let t3 := ivSub (ivMulInt (-457047) r3.re) (ivMulInt 492192 r3.im)
    let q := ivAdd q0 (ivMulInt 2 (ivAdd (ivAdd t0 t1) (ivAdd t2 t3)))
    q.hi < 0 := by decide

lemma certPt_injective : Function.Injective certPt := by
  intro i j hij
  have hi := checkRangeBin_sound (by norm_num : 67 - 0 < 2 ^ 7) cert_pts_inj_bool i.1 (Nat.zero_le _) (Nat.lt_succ_iff.mp i.2)
  have hj := checkRangeBin_sound (by norm_num : 67 - 0 < 2 ^ 7) hi j.1 (Nat.zero_le _) (Nat.lt_succ_iff.mp j.2)
  rw [decide_eq_true_eq] at hj
  exact Fin.ext (hj hij)

lemma sum_norm_sq_certW : ∑ i : Fin 68, ‖certW i‖ ^ 2 = (999413 : ℝ) := by
  have h1 : ∀ i : Fin 68, ‖certW i‖ ^ 2 =
      (((certWtVal i.1).1 * (certWtVal i.1).1 + (certWtVal i.1).2 * (certWtVal i.1).2 : ℤ) : ℝ) := by
    intro i
    rw [certW, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
  simp_rw [h1, ← Int.cast_sum]
  have hfin : (∑ i : Fin 68, ((certWtVal i.1).1 * (certWtVal i.1).1 + (certWtVal i.1).2 * (certWtVal i.1).2)) =
      ∑ n ∈ Finset.Icc 0 67, ((certWtVal n).1 * (certWtVal n).1 + (certWtVal n).2 * (certWtVal n).2) := by
    rw [Fin.sum_univ_eq_sum_range (fun n => (certWtVal n).1 * (certWtVal n).1 + (certWtVal n).2 * (certWtVal n).2)]
    congr 1
  rw [hfin, ← intSumRangeBin_eq (d := 7) (by norm_num), cert_norm_sq_eq]
  norm_cast

lemma edge_sum_certW (k : Fin 4) :
    (∑ i : Fin 68, ∑ j : Fin 68,
      if (certPt i).1 - (certPt j).1 = (if k = 0 then 1 else 0) ∧
         (certPt i).2.1 - (certPt j).2.1 = (if k = 1 then 1 else 0) ∧
         (certPt i).2.2.1 - (certPt j).2.2.1 = (if k = 2 then 1 else 0) ∧
         (certPt i).2.2.2 - (certPt j).2.2.2 = (if k = 3 then 1 else 0)
      then certW j * conj (certW i) else 0) =
    (edgeReSum k.1 : ℂ) + (edgeImSum k.1 : ℂ) * I := by
  have hcond : ∀ i j : Fin 68,
      ((certPt i).1 - (certPt j).1 = (if k = 0 then 1 else 0) ∧
       (certPt i).2.1 - (certPt j).2.1 = (if k = 1 then 1 else 0) ∧
       (certPt i).2.2.1 - (certPt j).2.2.1 = (if k = 2 then 1 else 0) ∧
       (certPt i).2.2.2 - (certPt j).2.2.2 = (if k = 3 then 1 else 0)) ↔
      edgeMatch k.1 i.1 j.1 = true := by
    intro i j
    fin_cases k <;> simp [edgeMatch, certPt]
  have hmul : ∀ i j : Fin 68,
      certW j * conj (certW i) =
        (((certWtVal j.1).1 * (certWtVal i.1).1 + (certWtVal j.1).2 * (certWtVal i.1).2 : ℤ) : ℂ) +
        (((certWtVal j.1).2 * (certWtVal i.1).1 - (certWtVal j.1).1 * (certWtVal i.1).2 : ℤ) : ℂ) * I := by
    intro i j
    apply Complex.ext
    · simp [certW]
    · simp [certW]; ring
  have hre : (∑ i : Fin 68, ∑ j : Fin 68,
      if (certPt i).1 - (certPt j).1 = (if k = 0 then 1 else 0) ∧
         (certPt i).2.1 - (certPt j).2.1 = (if k = 1 then 1 else 0) ∧
         (certPt i).2.2.1 - (certPt j).2.2.1 = (if k = 2 then 1 else 0) ∧
         (certPt i).2.2.2 - (certPt j).2.2.2 = (if k = 3 then 1 else 0)
      then certW j * conj (certW i) else 0).re = (edgeReSum k.1 : ℝ) := by
    simp only [Complex.re_sum]
    have hpt : ∀ i j : Fin 68,
        (if (certPt i).1 - (certPt j).1 = (if k = 0 then 1 else 0) ∧
            (certPt i).2.1 - (certPt j).2.1 = (if k = 1 then 1 else 0) ∧
            (certPt i).2.2.1 - (certPt j).2.2.1 = (if k = 2 then 1 else 0) ∧
            (certPt i).2.2.2 - (certPt j).2.2.2 = (if k = 3 then 1 else 0)
         then certW j * conj (certW i) else 0).re =
        ((if edgeMatch k.1 i.1 j.1 then
            (certWtVal j.1).1 * (certWtVal i.1).1 + (certWtVal j.1).2 * (certWtVal i.1).2
          else 0 : ℤ) : ℝ) := by
      intro i j
      by_cases hc : edgeMatch k.1 i.1 j.1 = true
      · rw [if_pos ((hcond i j).mpr hc), if_pos hc, hmul i j]; simp
      · rw [if_neg (mt (hcond i j).mp hc), if_neg hc]; simp
    simp_rw [hpt, ← Int.cast_sum]
    norm_cast
    rw [edgeReSum, intSumRangeBin_eq (by norm_num)]
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin 68,
      if edgeMatch k.1 i j.1 then
        (certWtVal j.1).1 * (certWtVal i).1 + (certWtVal j.1).2 * (certWtVal i).2
      else 0)]
    rw [show Finset.range 68 = Finset.Icc 0 67 by ext n; simp; omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intSumRangeBin_eq (by norm_num),
      Fin.sum_univ_eq_sum_range (fun j =>
        if edgeMatch k.1 i j then
          (certWtVal j).1 * (certWtVal i).1 + (certWtVal j).2 * (certWtVal i).2
        else 0),
      show Finset.range 68 = Finset.Icc 0 67 by ext n; simp; omega]
  have him : (∑ i : Fin 68, ∑ j : Fin 68,
      if (certPt i).1 - (certPt j).1 = (if k = 0 then 1 else 0) ∧
         (certPt i).2.1 - (certPt j).2.1 = (if k = 1 then 1 else 0) ∧
         (certPt i).2.2.1 - (certPt j).2.2.1 = (if k = 2 then 1 else 0) ∧
         (certPt i).2.2.2 - (certPt j).2.2.2 = (if k = 3 then 1 else 0)
      then certW j * conj (certW i) else 0).im = (edgeImSum k.1 : ℝ) := by
    simp only [Complex.im_sum]
    have hpt : ∀ i j : Fin 68,
        (if (certPt i).1 - (certPt j).1 = (if k = 0 then 1 else 0) ∧
            (certPt i).2.1 - (certPt j).2.1 = (if k = 1 then 1 else 0) ∧
            (certPt i).2.2.1 - (certPt j).2.2.1 = (if k = 2 then 1 else 0) ∧
            (certPt i).2.2.2 - (certPt j).2.2.2 = (if k = 3 then 1 else 0)
         then certW j * conj (certW i) else 0).im =
        ((if edgeMatch k.1 i.1 j.1 then
            (certWtVal j.1).2 * (certWtVal i.1).1 - (certWtVal j.1).1 * (certWtVal i.1).2
          else 0 : ℤ) : ℝ) := by
      intro i j
      by_cases hc : edgeMatch k.1 i.1 j.1 = true
      · rw [if_pos ((hcond i j).mpr hc), if_pos hc, hmul i j]; simp
      · rw [if_neg (mt (hcond i j).mp hc), if_neg hc]; simp
    simp_rw [hpt, ← Int.cast_sum]
    norm_cast
    rw [edgeImSum, intSumRangeBin_eq (by norm_num)]
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin 68,
      if edgeMatch k.1 i j.1 then
        (certWtVal j.1).2 * (certWtVal i).1 - (certWtVal j.1).1 * (certWtVal i).2
      else 0)]
    rw [show Finset.range 68 = Finset.Icc 0 67 by ext n; simp; omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intSumRangeBin_eq (by norm_num),
      Fin.sum_univ_eq_sum_range (fun j =>
        if edgeMatch k.1 i j then
          (certWtVal j).2 * (certWtVal i).1 - (certWtVal j).1 * (certWtVal i).2
        else 0),
      show Finset.range 68 = Finset.Icc 0 67 by ext n; simp; omega]
  apply Complex.ext
  · simpa using hre
  · simpa using him

-- Certificate 5: Non-unit difference nonvanishing via balanced BST (16 parallel decide chunks!)
def NuBST.all (p : (ℤ × ℤ × ℤ × ℤ) × ℕ → Bool) : NuBST → Bool
  | .empty => true
  | .node k v l r => p (k, v) && l.all p && r.all p

def cmpTuple4 (a b : ℤ × ℤ × ℤ × ℤ) : Ordering :=
  match compare a.1 b.1 with
  | .eq => match compare a.2.1 b.2.1 with
    | .eq => match compare a.2.2.1 b.2.2.1 with
      | .eq => compare a.2.2.2 b.2.2.2
      | o => o
    | o => o
  | o => o

lemma cmpTuple4_eq_iff (a b : ℤ × ℤ × ℤ × ℤ) : cmpTuple4 a b = .eq ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [cmpTuple4]
  cases h0 : compare a0 b0 <;> simp
  · rintro rfl; simp at h0
  · cases h1 : compare a1 b1 <;> simp
    · rintro _ rfl; simp at h1
    · cases h2 : compare a2 b2 <;> simp
      · rintro _ _ rfl; simp at h2
      · rw [compare_eq_iff_eq] at h0 h1 h2
        simp [h0, h1, h2]
      · rintro _ _ rfl; simp at h2
    · rintro _ rfl; simp at h1
  · rintro rfl; simp at h0

def NuBST.lookup (d : ℤ × ℤ × ℤ × ℤ) : NuBST → Option ℕ
  | .empty => none
  | .node k v l r =>
      match cmpTuple4 d k with
      | .lt => l.lookup d
      | .eq => some v
      | .gt => r.lookup d

lemma NuBST.lookup_sound {t : NuBST} {p : (ℤ × ℤ × ℤ × ℤ) × ℕ → Bool}
    (hall : t.all p = true) {d : ℤ × ℤ × ℤ × ℤ} {N : ℕ} (hl : t.lookup d = some N) :
    p (d, N) = true := by
  induction t with
  | empty => simp [NuBST.lookup] at hl
  | node k v l r ihl ihr =>
    simp only [NuBST.all, Bool.and_eq_true] at hall
    simp only [NuBST.lookup] at hl
    cases hc : cmpTuple4 d k <;> rw [hc] at hl
    · exact ihl hall.1.2 hl
    · have hdk : d = k := (cmpTuple4_eq_iff d k).mp hc
      have hvN : v = N := Option.some.inj hl
      subst hdk; subst hvN; exact hall.1.1
    · exact ihr hall.2 hl

def checkNonUnitEntry (e : (ℤ × ℤ × ℤ × ℤ) × ℕ) : Bool :=
  let ((d0, d1, d2, d3), N) := e
  let t0Signed := d0 * gMid 0 + d1 * gMid 1 + d2 * gMid 2 + d3 * gMid 3
  let t0Num := if 0 ≤ t0Signed then t0Signed else -t0Signed
  let dtNum := ((d0.natAbs + d1.natAbs + d2.natAbs + d3.natAbs : ℕ) : ℤ) * deltaNum
  let t0Iv := ivRat t0Num 10000000
  let tpIv := ivRat (t0Num + dtNum) 10000000
  let dtIv := ivRat dtNum 10000000
  let lipHi := cdiv ((24 * Sval + 16 * cvNormL1Hi ⟨ivRat 1 2, tpIv⟩) * dtIv.hi) Sval
  let zEm := cvEm3Half t0Iv N
  let rem := ivEm3RemHalfHi t0Iv N
  let err := rem + lipHi
  decide (1 ≤ N ∧ N ≤ 160 ∧ dtNum < t0Num ∧
    (err < zEm.re.lo ∨ zEm.re.hi < -err ∨ err < zEm.im.lo ∨ zEm.im.hi < -err))

theorem cert_nuSub0 : nuSub0.all checkNonUnitEntry = true := by decide
theorem cert_nuSub1 : nuSub1.all checkNonUnitEntry = true := by decide
theorem cert_nuSub2 : nuSub2.all checkNonUnitEntry = true := by decide
theorem cert_nuSub3 : nuSub3.all checkNonUnitEntry = true := by decide
theorem cert_nuSub4 : nuSub4.all checkNonUnitEntry = true := by decide
theorem cert_nuSub5 : nuSub5.all checkNonUnitEntry = true := by decide
theorem cert_nuSub6 : nuSub6.all checkNonUnitEntry = true := by decide
theorem cert_nuSub7 : nuSub7.all checkNonUnitEntry = true := by decide
theorem cert_nuSub8 : nuSub8.all checkNonUnitEntry = true := by decide
theorem cert_nuSub9 : nuSub9.all checkNonUnitEntry = true := by decide
theorem cert_nuSub10 : nuSub10.all checkNonUnitEntry = true := by decide
theorem cert_nuSub11 : nuSub11.all checkNonUnitEntry = true := by decide
theorem cert_nuSub12 : nuSub12.all checkNonUnitEntry = true := by decide
theorem cert_nuSub13 : nuSub13.all checkNonUnitEntry = true := by decide
theorem cert_nuSub14 : nuSub14.all checkNonUnitEntry = true := by decide
theorem cert_nuSub15 : nuSub15.all checkNonUnitEntry = true := by decide

theorem cert_nuBST_all : nonUnitBST.all checkNonUnitEntry = true := by
  simp only [nonUnitBST, NuBST.all,
    cert_nuSub0, cert_nuSub1, cert_nuSub2, cert_nuSub3,
    cert_nuSub4, cert_nuSub5, cert_nuSub6, cert_nuSub7,
    cert_nuSub8, cert_nuSub9, cert_nuSub10, cert_nuSub11,
    cert_nuSub12, cert_nuSub13, cert_nuSub14, cert_nuSub15,
    Bool.and_true]
  decide

def isZeroOrUnit (d : ℤ × ℤ × ℤ × ℤ) : Bool :=
  decide (d = (0, 0, 0, 0) ∨ d = (1, 0, 0, 0) ∨ d = (-1, 0, 0, 0) ∨
          d = (0, 1, 0, 0) ∨ d = (0, -1, 0, 0) ∨ d = (0, 0, 1, 0) ∨
          d = (0, 0, -1, 0) ∨ d = (0, 0, 0, 1) ∨ d = (0, 0, 0, -1))

def negTuple4 (d : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (-d.1, -d.2.1, -d.2.2.1, -d.2.2.2)

def pairRowCovered (i : ℕ) : Bool :=
  checkRangeBin 7 0 67 fun j =>
    let pi := certPtVal i
    let pj := certPtVal j
    let d := (pi.1 - pj.1, pi.2.1 - pj.2.1, pi.2.2.1 - pj.2.2.1, pi.2.2.2 - pj.2.2.2)
    isZeroOrUnit d || (nonUnitBST.lookup d).isSome || (nonUnitBST.lookup (negTuple4 d)).isSome

theorem cert_pairs_covered_0 : checkRangeBin 5 0 16 pairRowCovered = true := by decide
theorem cert_pairs_covered_1 : checkRangeBin 5 17 33 pairRowCovered = true := by decide
theorem cert_pairs_covered_2 : checkRangeBin 5 34 50 pairRowCovered = true := by decide
theorem cert_pairs_covered_3 : checkRangeBin 5 51 67 pairRowCovered = true := by decide

lemma cert_pairs_covered_sound (i : ℕ) (hi : i < 68) : pairRowCovered i = true := by
  by_cases h0 : i ≤ 16
  · exact checkRangeBin_sound (by norm_num : 16 - 0 < 2 ^ 5) cert_pairs_covered_0 i (Nat.zero_le _) h0
  · by_cases h1 : i ≤ 33
    · exact checkRangeBin_sound (by norm_num : 33 - 17 < 2 ^ 5) cert_pairs_covered_1 i (by omega) h1
    · by_cases h2 : i ≤ 50
      · exact checkRangeBin_sound (by norm_num : 50 - 34 < 2 ^ 5) cert_pairs_covered_2 i (by omega) h2
      · exact checkRangeBin_sound (by norm_num : 67 - 51 < 2 ^ 5) cert_pairs_covered_3 i (by omega) (by omega)

lemma checkNonUnitEntry_sound {d : ℤ × ℤ × ℤ × ℤ} {N : ℕ}
    (hok : checkNonUnitEntry (d, N) = true)
    {γ : Fin 4 → ℝ}
    (hγ : ∀ k : Fin 4, ((gMid k.1 - deltaNum : ℤ) : ℝ) / 10000000 ≤ γ k ∧
      γ k ≤ ((gMid k.1 + deltaNum : ℤ) : ℝ) / 10000000) :
    let t := (d.1 : ℝ) * γ 0 + (d.2.1 : ℝ) * γ 1 + (d.2.2.1 : ℝ) * γ 2 + (d.2.2.2 : ℝ) * γ 3
    t ≠ 0 ∧ riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  have hS := Sval_pos
  rcases d with ⟨d0, d1, d2, d3⟩
  simp only [checkNonUnitEntry, decide_eq_true_eq] at hok
  obtain ⟨hN1, hN2, hdt_lt, hbox⟩ := hok
  set t : ℝ := (d0 : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3
  set t0Signed : ℤ := d0 * gMid 0 + d1 * gMid 1 + d2 * gMid 2 + d3 * gMid 3
  set t0Num : ℤ := if 0 ≤ t0Signed then t0Signed else -t0Signed
  set dtNum : ℤ := ((d0.natAbs + d1.natAbs + d2.natAbs + d3.natAbs : ℕ) : ℤ) * deltaNum
  have hγ_err : ∀ k : Fin 4, |γ k - (gMid k.1 : ℝ) / 10000000| ≤ (deltaNum : ℝ) / 10000000 := by
    intro k
    have hk := hγ k
    rw [abs_le]; push_cast at hk; rw [sub_div, add_div] at hk
    constructor <;> linarith
  have ht_dist : |t - (t0Signed : ℝ) / 10000000| ≤ (dtNum : ℝ) / 10000000 := by
    have hsplit : t - (t0Signed : ℝ) / 10000000 =
        (d0 : ℝ) * (γ 0 - (gMid 0 : ℝ) / 10000000) +
        (d1 : ℝ) * (γ 1 - (gMid 1 : ℝ) / 10000000) +
        (d2 : ℝ) * (γ 2 - (gMid 2 : ℝ) / 10000000) +
        (d3 : ℝ) * (γ 3 - (gMid 3 : ℝ) / 10000000) := by
      dsimp only [t, t0Signed]; push_cast; ring
    have hna : ∀ z : ℤ, |(z : ℝ)| = (z.natAbs : ℝ) := fun z => by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    rw [hsplit]
    calc |(d0 : ℝ) * (γ 0 - (gMid 0 : ℝ) / 10000000) +
            (d1 : ℝ) * (γ 1 - (gMid 1 : ℝ) / 10000000) +
            (d2 : ℝ) * (γ 2 - (gMid 2 : ℝ) / 10000000) +
            (d3 : ℝ) * (γ 3 - (gMid 3 : ℝ) / 10000000)|
        ≤ |(d0 : ℝ)| * |γ 0 - (gMid 0 : ℝ) / 10000000| +
          |(d1 : ℝ)| * |γ 1 - (gMid 1 : ℝ) / 10000000| +
          |(d2 : ℝ)| * |γ 2 - (gMid 2 : ℝ) / 10000000| +
          |(d3 : ℝ)| * |γ 3 - (gMid 3 : ℝ) / 10000000| := by
          have := abs_add_le ((d0 : ℝ) * (γ 0 - (gMid 0 : ℝ) / 10000000) +
            (d1 : ℝ) * (γ 1 - (gMid 1 : ℝ) / 10000000) +
            (d2 : ℝ) * (γ 2 - (gMid 2 : ℝ) / 10000000)) ((d3 : ℝ) * (γ 3 - (gMid 3 : ℝ) / 10000000))
          have := abs_add_le ((d0 : ℝ) * (γ 0 - (gMid 0 : ℝ) / 10000000) +
            (d1 : ℝ) * (γ 1 - (gMid 1 : ℝ) / 10000000)) ((d2 : ℝ) * (γ 2 - (gMid 2 : ℝ) / 10000000))
          have := abs_add_le ((d0 : ℝ) * (γ 0 - (gMid 0 : ℝ) / 10000000))
            ((d1 : ℝ) * (γ 1 - (gMid 1 : ℝ) / 10000000))
          simp only [abs_mul] at *; linarith
      _ ≤ (d0.natAbs : ℝ) * ((deltaNum : ℝ) / 10000000) +
          (d1.natAbs : ℝ) * ((deltaNum : ℝ) / 10000000) +
          (d2.natAbs : ℝ) * ((deltaNum : ℝ) / 10000000) +
          (d3.natAbs : ℝ) * ((deltaNum : ℝ) / 10000000) := by
          rw [hna d0, hna d1, hna d2, hna d3]
          have h0 := mul_le_mul_of_nonneg_left (hγ_err 0) (Nat.cast_nonneg d0.natAbs)
          have h1 := mul_le_mul_of_nonneg_left (hγ_err 1) (Nat.cast_nonneg d1.natAbs)
          have h2 := mul_le_mul_of_nonneg_left (hγ_err 2) (Nat.cast_nonneg d2.natAbs)
          have h3 := mul_le_mul_of_nonneg_left (hγ_err 3) (Nat.cast_nonneg d3.natAbs)
          have hfin3 : ((3 : Fin 4) : ℕ) = 3 := rfl
          simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hfin3] at h0 h1 h2 h3
          linarith
      _ = (dtNum : ℝ) / 10000000 := by
          dsimp only [dtNum]
          rw [Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_add, Nat.cast_add]; ring
  have hdt_nonneg : (0 : ℤ) ≤ dtNum := by dsimp only [dtNum, deltaNum]; positivity
  have ht0_pos : (0 : ℤ) < t0Num := by omega
  have ht_pos_abs : 0 < |t| := by
    have ht0_eq : |(t0Signed : ℝ)| = (t0Num : ℝ) := by
      dsimp only [t0Num]; split_ifs with hs
      · exact abs_of_nonneg (by exact_mod_cast hs)
      · rw [Int.cast_neg]; exact abs_of_neg (by exact_mod_cast (lt_of_not_ge hs))
    have hlt : (dtNum : ℝ) / 10000000 < (t0Num : ℝ) / 10000000 := by
      have : (dtNum : ℝ) < (t0Num : ℝ) := by exact_mod_cast hdt_lt
      linarith
    have hrev := abs_sub_abs_le_abs_sub ((t0Signed : ℝ) / 10000000) t
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10000000), ht0_eq, abs_sub_comm] at hrev
    linarith
  have ht_ne : t ≠ 0 := abs_pos.mp ht_pos_abs
  refine ⟨ht_ne, ?_⟩
  -- Let u = |t| (so |u - t0| ≤ dt)
  set u : ℝ := if 0 ≤ t0Signed then t else -t
  have hu_dist : |u - (t0Num : ℝ) / 10000000| ≤ (dtNum : ℝ) / 10000000 := by
    dsimp only [u, t0Num]
    split_ifs with hs
    · exact ht_dist
    · rw [Int.cast_neg, neg_div, sub_neg_eq_add, show -t + (t0Signed : ℝ) / 10000000 = -(t - (t0Signed : ℝ) / 10000000) by ring, abs_neg]
      exact ht_dist
  set t0R : ℝ := (t0Num : ℝ) / 10000000
  set dtR : ℝ := (dtNum : ℝ) / 10000000
  set tpR : ℝ := ((t0Num + dtNum : ℤ) : ℝ) / 10000000
  have ht0Iv : (ivRat t0Num 10000000).mem t0R := by
    simpa [t0R] using ivRat_mem t0Num (by norm_num : (0 : ℤ) < 10000000)
  have htpIv : (ivRat (t0Num + dtNum) 10000000).mem tpR := by
    simpa [tpR] using ivRat_mem (t0Num + dtNum) (by norm_num : (0 : ℤ) < 10000000)
  have hdtIv : (ivRat dtNum 10000000).mem dtR := by
    simpa [dtR] using ivRat_mem dtNum (by norm_num : (0 : ℤ) < 10000000)
  have htp_nonneg : 0 ≤ tpR := by
    have h0 : (0 : ℝ) ≤ ((t0Num + dtNum : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 ≤ t0Num + dtNum)
    dsimp only [tpR]; linarith
  have ht0_le_tp : |t0R| ≤ tpR := by
    have h1 : 0 ≤ t0R := by
      have h1' : (0 : ℝ) ≤ (t0Num : ℝ) := by exact_mod_cast ht0_pos.le
      dsimp only [t0R]; linarith
    have h2 : 0 ≤ dtR := by
      have h2' : (0 : ℝ) ≤ (dtNum : ℝ) := by exact_mod_cast hdt_nonneg
      dsimp only [dtR]; linarith
    rw [abs_of_nonneg h1]; dsimp only [t0R, dtR, tpR] at h1 h2 ⊢; push_cast; linarith
  have hu_le_tp : |u| ≤ tpR := by
    have h1 := abs_le.mp hu_dist
    have h2 : 0 ≤ t0R := by
      have h2' : (0 : ℝ) ≤ (t0Num : ℝ) := by exact_mod_cast ht0_pos.le
      dsimp only [t0R]; linarith
    have h3 : dtR < t0R := by
      have h3' : (dtNum : ℝ) < (t0Num : ℝ) := by exact_mod_cast hdt_lt
      dsimp only [t0R, dtR]; linarith
    rw [abs_le]; dsimp only [t0R, dtR, tpR] at h1 h2 h3 ⊢; push_cast; constructor <;> linarith
  have hlip := norm_zeta_half_sub_le htp_nonneg ht0_le_tp hu_le_tp
  have hrem := ivEm3RemHalfHi_sound ht0Iv hN1 hN2
  have hs_tp : Cval.mem ⟨ivRat 1 2, ivRat (t0Num + dtNum) 10000000⟩ ((1 / 2 : ℂ) + (tpR : ℂ) * I) :=
    ⟨by simpa using ivRat_mem 1 (by norm_num : (0 : ℤ) < 2), by simpa using htpIv⟩
  have hn_tp := norm_le_cvNormL1Hi hs_tp
  have hlip_coef : 24 + 16 * ‖(1 / 2 : ℂ) + (tpR : ℂ) * I‖ ≤
      ((24 * Sval + 16 * cvNormL1Hi ⟨ivRat 1 2, ivRat (t0Num + dtNum) 10000000⟩ : ℤ) : ℝ) / (Sval : ℝ) := by
    push_cast; rw [add_div, mul_div_cancel_right₀ _ hS.ne', mul_div_assoc]; linarith
  set lipHi : ℤ := cdiv ((24 * Sval + 16 * cvNormL1Hi ⟨ivRat 1 2, ivRat (t0Num + dtNum) 10000000⟩) *
      (ivRat dtNum 10000000).hi) Sval
  have hlip_bd : (24 + 16 * ‖(1 / 2 : ℂ) + (tpR : ℂ) * I‖) * |u - t0R| ≤ (lipHi : ℝ) / (Sval : ℝ) := by
    have hcd := div_le_cdiv ((24 * Sval + 16 * cvNormL1Hi ⟨ivRat 1 2, ivRat (t0Num + dtNum) 10000000⟩) *
      (ivRat dtNum 10000000).hi) Sval_int_pos
    have hmul := mul_le_mul hlip_coef (hu_dist.trans hdtIv.2) (abs_nonneg _)
      (by linarith [norm_nonneg ((1 / 2 : ℂ) + (tpR : ℂ) * I)])
    calc _ ≤ (((24 * Sval + 16 * cvNormL1Hi ⟨ivRat 1 2, ivRat (t0Num + dtNum) 10000000⟩ : ℤ) : ℝ) / (Sval : ℝ)) *
          (((ivRat dtNum 10000000).hi : ℝ) / (Sval : ℝ)) := hmul
      _ = ((((24 * Sval + 16 * cvNormL1Hi ⟨ivRat 1 2, ivRat (t0Num + dtNum) 10000000⟩) *
            (ivRat dtNum 10000000).hi : ℤ) : ℝ) / (Sval : ℝ)) / (Sval : ℝ) := by push_cast; ring
      _ ≤ (lipHi : ℝ) / (Sval : ℝ) := div_le_div_of_nonneg_right hcd hS.le
  set err : ℤ := ivEm3RemHalfHi (ivRat t0Num 10000000) N + lipHi
  have hzu_mem : (cvExpand (cvEm3Half (ivRat t0Num 10000000) N) err).mem
      (riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)) := by
    refine cvExpand_mem (cvEm3Half_mem ht0Iv hN1 hN2) ?_
    have hz := riemannZeta_eq_em3_add_R6 hN1 (s := (1 / 2 : ℂ) + (t0R : ℂ) * I)
      (by simp) (by intro h; have := congr_arg Complex.re h; simp at this)
    calc ‖riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) - em3 ((1 / 2 : ℂ) + (t0R : ℂ) * I) N‖
        = ‖(riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) - riemannZeta ((1 / 2 : ℂ) + (t0R : ℂ) * I)) +
           R6 ((1 / 2 : ℂ) + (t0R : ℂ) * I) N‖ := by rw [hz]; ring_nf
      _ ≤ ‖riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) - riemannZeta ((1 / 2 : ℂ) + (t0R : ℂ) * I)‖ +
          ‖R6 ((1 / 2 : ℂ) + (t0R : ℂ) * I) N‖ := norm_add_le _ _
      _ ≤ (err : ℝ) / (Sval : ℝ) := by dsimp only [err]; push_cast; rw [add_div]; linarith
  have hzu_ne : riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) ≠ 0 := by
    intro h0
    have hre0 : (riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)).re = 0 := by rw [h0]; simp
    have him0 : (riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)).im = 0 := by rw [h0]; simp
    have h1 := hzu_mem.1; have h2 := hzu_mem.2
    rw [hre0] at h1; rw [him0] at h2
    dsimp only [cvExpand] at h1 h2
    rcases hbox with hb | hb | hb | hb
    · have : (0 : ℝ) < (((cvEm3Half (ivRat t0Num 10000000) N).re.lo - err : ℤ) : ℝ) / (Sval : ℝ) :=
        div_pos (by exact_mod_cast (by omega : (0 : ℤ) < (cvEm3Half (ivRat t0Num 10000000) N).re.lo - err)) hS
      linarith [h1.1]
    · have : (((cvEm3Half (ivRat t0Num 10000000) N).re.hi + err : ℤ) : ℝ) / (Sval : ℝ) < 0 :=
        div_neg_of_neg_of_pos (by exact_mod_cast (by omega : (cvEm3Half (ivRat t0Num 10000000) N).re.hi + err < 0)) hS
      linarith [h1.2]
    · have : (0 : ℝ) < (((cvEm3Half (ivRat t0Num 10000000) N).im.lo - err : ℤ) : ℝ) / (Sval : ℝ) :=
        div_pos (by exact_mod_cast (by omega : (0 : ℤ) < (cvEm3Half (ivRat t0Num 10000000) N).im.lo - err)) hS
      linarith [h2.1]
    · have : (((cvEm3Half (ivRat t0Num 10000000) N).im.hi + err : ℤ) : ℝ) / (Sval : ℝ) < 0 :=
        div_neg_of_neg_of_pos (by exact_mod_cast (by omega : (cvEm3Half (ivRat t0Num 10000000) N).im.hi + err < 0)) hS
      linarith [h2.2]
  dsimp only [u] at hzu_ne
  split_ifs at hzu_ne with hs
  · exact hzu_ne
  · intro h0
    have hconj : conj ((1 / 2 : ℂ) + (t : ℂ) * I) = (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hzc := riemannZeta_conj ((1 / 2 : ℂ) + (t : ℂ) * I)
    rw [hconj, h0, _root_.map_zero] at hzc
    exact hzu_ne hzc

theorem S_pos_infinite : {n : ℕ | 0 < S n}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, S n ≤ 0 := by
    by_cases hne : {n : ℕ | 0 < S n}.Nonempty
    · refine ⟨hfin.toFinset.max' (hfin.toFinset_nonempty.mpr hne) + 1, fun n hn => ?_⟩
      by_contra hpos
      push Not at hpos
      have hmem : n ∈ hfin.toFinset := hfin.mem_toFinset.mpr hpos
      have hle := Finset.le_max' hfin.toFinset n hmem
      omega
    · refine ⟨0, fun n _ => ?_⟩
      by_contra hpos
      push Not at hpos
      exact hne ⟨n, hpos⟩
  -- Extract the 4 certified critical-line zeros
  have hok_all := cert_zeros_ok
  simp only [Bool.and_eq_true] at hok_all
  obtain ⟨γ0, hγ0_1, hγ0_2, hγ0_pos, hγ0_zero, hγ0_simple, hγ0_res⟩ :=
    cert_zero_exists 0 zmLit0 zpLit0 dzLit0 z2Lit0 cert_zm0 cert_zp0 cert_dz0 cert_z20 hok_all.1.1.1
  obtain ⟨γ1, hγ1_1, hγ1_2, hγ1_pos, hγ1_zero, hγ1_simple, hγ1_res⟩ :=
    cert_zero_exists 1 zmLit1 zpLit1 dzLit1 z2Lit1 cert_zm1 cert_zp1 cert_dz1 cert_z21 hok_all.1.1.2
  obtain ⟨γ2, hγ2_1, hγ2_2, hγ2_pos, hγ2_zero, hγ2_simple, hγ2_res⟩ :=
    cert_zero_exists 2 zmLit2 zpLit2 dzLit2 z2Lit2 cert_zm2 cert_zp2 cert_dz2 cert_z22 hok_all.1.2
  obtain ⟨γ3, hγ3_1, hγ3_2, hγ3_pos, hγ3_zero, hγ3_simple, hγ3_res⟩ :=
    cert_zero_exists 3 zmLit3 zpLit3 dzLit3 z2Lit3 cert_zm3 cert_zp3 cert_dz3 cert_z23 hok_all.2
  let γ : Fin 4 → ℝ := ![γ0, γ1, γ2, γ3]
  have hγ_box : ∀ k : Fin 4,
      ((gMid k.1 - deltaNum : ℤ) : ℝ) / 10000000 ≤ γ k ∧
      γ k ≤ ((gMid k.1 + deltaNum : ℤ) : ℝ) / 10000000 := by
    intro k; fin_cases k
    · exact ⟨hγ0_1, hγ0_2⟩
    · exact ⟨hγ1_1, hγ1_2⟩
    · exact ⟨hγ2_1, hγ2_2⟩
    · exact ⟨hγ3_1, hγ3_2⟩
  have hγ_pos : ∀ k : Fin 4, 0 < γ k := by
    intro k; fin_cases k <;> assumption
  have hγ_zero : ∀ k : Fin 4, riemannZeta ((1 / 2 : ℂ) + (γ k : ℂ) * I) = 0 := by
    intro k; fin_cases k <;> assumption
  have hγ_simple : ∀ k : Fin 4, deriv riemannZeta ((1 / 2 : ℂ) + (γ k : ℂ) * I) ≠ 0 := by
    intro k; fin_cases k <;> assumption
  have hγ_res : ∀ k : Fin 4, (resLit k).mem (resAt (γ k)) := by
    intro k; fin_cases k <;> assumption
  -- Verify h_nonunit for all pairs (i, j) : Fin 68 × Fin 68
  have h_nonunit : ∀ i j : Fin 68,
      let d := (certPt i).1 - (certPt j).1
      let d1 := (certPt i).2.1 - (certPt j).2.1
      let d2 := (certPt i).2.2.1 - (certPt j).2.2.1
      let d3 := (certPt i).2.2.2 - (certPt j).2.2.2
      (d, d1, d2, d3) ≠ (0, 0, 0, 0) →
      (d, d1, d2, d3) ≠ (1, 0, 0, 0) → (d, d1, d2, d3) ≠ (-1, 0, 0, 0) →
      (d, d1, d2, d3) ≠ (0, 1, 0, 0) → (d, d1, d2, d3) ≠ (0, -1, 0, 0) →
      (d, d1, d2, d3) ≠ (0, 0, 1, 0) → (d, d1, d2, d3) ≠ (0, 0, -1, 0) →
      (d, d1, d2, d3) ≠ (0, 0, 0, 1) → (d, d1, d2, d3) ≠ (0, 0, 0, -1) →
      let t := (d : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3
      t ≠ 0 ∧ riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro i j d0 d1 d2 d3 h0 hp0 hm0 hp1 hm1 hp2 hm2 hp3 hm3
    set d : ℤ × ℤ × ℤ × ℤ := (d0, d1, d2, d3)
    have hi := cert_pairs_covered_sound i.1 i.2
    have hj := checkRangeBin_sound (by norm_num : 67 - 0 < 2 ^ 7) hi j.1
      (Nat.zero_le _) (Nat.lt_succ_iff.mp j.2)
    have hnotzu : isZeroOrUnit d = false := by
      simp only [isZeroOrUnit, decide_eq_false_iff_not, not_or]
      exact ⟨h0, hp0, hm0, hp1, hm1, hp2, hm2, hp3, hm3⟩
    change (isZeroOrUnit d || (nonUnitBST.lookup d).isSome || (nonUnitBST.lookup (negTuple4 d)).isSome) = true at hj
    rw [hnotzu, Bool.false_or, Bool.or_eq_true] at hj
    rcases hj with hpos_lk | hneg_lk
    · obtain ⟨N, hN⟩ := Option.isSome_iff_exists.mp hpos_lk
      have hok := NuBST.lookup_sound cert_nuBST_all hN
      exact checkNonUnitEntry_sound hok hγ_box
    · obtain ⟨N, hN⟩ := Option.isSome_iff_exists.mp hneg_lk
      have hok := NuBST.lookup_sound cert_nuBST_all hN
      have hres := checkNonUnitEntry_sound hok hγ_box
      have hneg_t : ((-d0 : ℤ) : ℝ) * γ 0 + ((-d1 : ℤ) : ℝ) * γ 1 + ((-d2 : ℤ) : ℝ) * γ 2 + ((-d3 : ℤ) : ℝ) * γ 3 =
          -((d0 : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3) := by
        push_cast; ring
      dsimp only [negTuple4, d] at hres
      rw [hneg_t] at hres
      refine ⟨fun h => hres.1 (by rw [h, neg_zero]), fun h => ?_⟩
      have hconj : conj ((1 / 2 : ℂ) + (((d0 : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3 : ℝ) : ℂ) * I) =
          (1 / 2 : ℂ) + ((-((d0 : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3) : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      have hzc := riemannZeta_conj ((1 / 2 : ℂ) + (((d0 : ℝ) * γ 0 + (d1 : ℝ) * γ 1 + (d2 : ℝ) * γ 2 + (d3 : ℝ) * γ 3 : ℝ) : ℂ) * I)
      rw [hconj, h, _root_.map_zero] at hzc
      exact hres.2 hzc
  -- Apply the limiting quadratic-form positivity theorem
  have hQ_nonneg := quadratic_form_nonneg_of_S_eventually_nonpos hN₀ γ hγ_pos hγ_zero hγ_simple
    certPt certPt_injective certW h_nonunit
  rw [sum_norm_sq_certW] at hQ_nonneg
  have hQ_rew :
      R0 * (999413 : ℝ) +
        2 * (∑ k : Fin 4,
          (resAt (γ k) *
            ∑ i : Fin 68, ∑ j : Fin 68,
              if (certPt i).1 - (certPt j).1 = (if k = 0 then 1 else 0) ∧
                 (certPt i).2.1 - (certPt j).2.1 = (if k = 1 then 1 else 0) ∧
                 (certPt i).2.2.1 - (certPt j).2.2.1 = (if k = 2 then 1 else 0) ∧
                 (certPt i).2.2.2 - (certPt j).2.2.2 = (if k = 3 then 1 else 0)
              then certW j * conj (certW i) else 0).re) =
      (999413 : ℤ) * R0 +
        2 * (((((-588301 : ℤ) : ℝ) * (resAt (γ 0)).re - ((680022 : ℤ) : ℝ) * (resAt (γ 0)).im) +
              (((345370 : ℤ) : ℝ) * (resAt (γ 1)).re - ((-361139 : ℤ) : ℝ) * (resAt (γ 1)).im)) +
             ((((-36887 : ℤ) : ℝ) * (resAt (γ 2)).re - ((-498338 : ℤ) : ℝ) * (resAt (γ 2)).im) +
              (((-457047 : ℤ) : ℝ) * (resAt (γ 3)).re - ((492192 : ℤ) : ℝ) * (resAt (γ 3)).im))) := by
    have hedge := cert_edges_eq
    have hsum4 : ∀ f : Fin 4 → ℝ, ∑ k : Fin 4, f k = (f 0 + f 1) + (f 2 + f 3) := by
      intro f; rw [Fin.sum_univ_four]; ring
    rw [hsum4, edge_sum_certW 0, edge_sum_certW 1, edge_sum_certW 2, edge_sum_certW 3]
    have hfin3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hfin3,
      hedge.1, hedge.2.1, hedge.2.2.1, hedge.2.2.2.1,
      hedge.2.2.2.2.1, hedge.2.2.2.2.2.1, hedge.2.2.2.2.2.2.1, hedge.2.2.2.2.2.2.2,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    push_cast; ring
  rw [hQ_rew] at hQ_nonneg
  have hQ_mem := ivAdd_mem (ivMulInt_mem 999413 cert_R0_mem)
    (ivMulInt_mem 2 (ivAdd_mem
      (ivAdd_mem (ivSub_mem (ivMulInt_mem (-588301) (hγ_res 0).1) (ivMulInt_mem 680022 (hγ_res 0).2))
        (ivSub_mem (ivMulInt_mem 345370 (hγ_res 1).1) (ivMulInt_mem (-361139) (hγ_res 1).2)))
      (ivAdd_mem (ivSub_mem (ivMulInt_mem (-36887) (hγ_res 2).1) (ivMulInt_mem (-498338) (hγ_res 2).2))
        (ivSub_mem (ivMulInt_mem (-457047) (hγ_res 3).1) (ivMulInt_mem 492192 (hγ_res 3).2)))))
  have hQ_neg_r :
      (((ivAdd (ivMulInt 999413 R0Lit)
          (ivMulInt 2 (ivAdd
            (ivAdd (ivSub (ivMulInt (-588301) (resLit 0).re) (ivMulInt 680022 (resLit 0).im))
              (ivSub (ivMulInt 345370 (resLit 1).re) (ivMulInt (-361139) (resLit 1).im)))
            (ivAdd (ivSub (ivMulInt (-36887) (resLit 2).re) (ivMulInt (-498338) (resLit 2).im))
              (ivSub (ivMulInt (-457047) (resLit 3).re) (ivMulInt 492192 (resLit 3).im)))))).hi : ℤ) : ℝ) /
        (Sval : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast cert_Q_neg) Sval_pos
  have hQ_lt : ((999413 : ℤ) : ℝ) * R0 +
      ((2 : ℤ) : ℝ) * (((((-588301 : ℤ) : ℝ) * (resAt (γ 0)).re - ((680022 : ℤ) : ℝ) * (resAt (γ 0)).im) +
            (((345370 : ℤ) : ℝ) * (resAt (γ 1)).re - ((-361139 : ℤ) : ℝ) * (resAt (γ 1)).im)) +
           ((((-36887 : ℤ) : ℝ) * (resAt (γ 2)).re - ((-498338 : ℤ) : ℝ) * (resAt (γ 2)).im) +
            (((-457047 : ℤ) : ℝ) * (resAt (γ 3)).re - ((492192 : ℤ) : ℝ) * (resAt (γ 3)).im))) < 0 :=
    lt_of_le_of_lt hQ_mem.2 hQ_neg_r
  push_cast at hQ_nonneg hQ_lt
  linarith

end MSE1940934

theorem OMA.solution : type_of% @OMA.S_mse_1940934.main :=
  ⟨MSE1940934.S_pos_infinite, MSE1940934.S_neg_infinite⟩
