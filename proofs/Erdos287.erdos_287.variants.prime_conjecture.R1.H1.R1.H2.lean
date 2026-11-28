import OMAReductions.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1

open Filter
open scoped BigOperators

namespace Erdos287Series

private noncomputable def summand (b : ℕ) : ℝ :=
  let c := b / Nat.gcd b 2
  ((ArithmeticFunction.moebius b : ℝ) ^ 2 * (ArithmeticFunction.moebius c : ℝ)) /
    ((Nat.totient b : ℝ) * (Nat.totient c : ℝ))

private noncomputable def weight (p : ℕ) : ℝ := 1 / ((p - 1 : ℕ) : ℝ) ^ 2

private lemma weight_nonneg (p : ℕ) : 0 ≤ weight p := by
  unfold weight
  positivity

-- For squarefree b, removing the factor 2 leaves the totient unchanged.
private lemma totient_div_gcd_two {b : ℕ} (hb : Squarefree b) :
    Nat.totient (b / Nat.gcd b 2) = Nat.totient b := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right b 2) with h | h
  · simp [h]
  rw [h]
  have hdvd : 2 ∣ b := h ▸ Nat.gcd_dvd_left b 2
  have hmul : 2 * (b / 2) = b := by
    simpa [mul_comm] using Nat.div_mul_cancel hdvd
  have hcop : Nat.Coprime 2 (b / 2) :=
    Nat.coprime_of_squarefree_mul (hmul.symm ▸ hb)
  calc
    Nat.totient (b / 2) = Nat.totient (2 * (b / 2)) := by
      rw [Nat.totient_mul hcop, Nat.totient_prime Nat.prime_two]
      simp
    _ = Nat.totient b := by rw [hmul]

private lemma abs_summand_le {b : ℕ} (hb : Squarefree b) :
    |summand b| ≤ ∏ p ∈ b.primeFactors, weight p := by
  have hmu : (ArithmeticFunction.moebius b : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hb
  have hmu' : |(ArithmeticFunction.moebius (b / Nat.gcd b 2) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b / Nat.gcd b 2)
  have htot : Nat.totient b = ∏ p ∈ b.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hb,
      Nat.div_self (Nat.pos_of_ne_zero hb.ne_zero), one_mul]
  calc
    |summand b| ≤ 1 / (Nat.totient b : ℝ) ^ 2 := by
      simp only [summand, hmu, one_mul, totient_div_gcd_two hb, ← pow_two, abs_div,
        abs_of_nonneg (sq_nonneg (Nat.totient b : ℝ))]
      exact div_le_div_of_nonneg_right hmu' (sq_nonneg _)
    _ = ∏ p ∈ b.primeFactors, weight p := by
      simp only [htot, Nat.cast_prod, weight, one_div, Finset.prod_inv_distrib,
        Finset.prod_pow]

private def smallPrimes : Finset ℕ := {2, 3, 5, 7}

private def largePrimes (M : ℕ) : Finset ℕ := (Finset.Icc 11 M).filter Nat.Prime

private lemma mem_smallPrimes_of_prime {p : ℕ} (hp : p.Prime) (hlt : p < 11) :
    p ∈ smallPrimes := by
  have h : ∀ p : Fin 11, p.val.Prime → p.val ∈ smallPrimes := by decide
  exact h ⟨p, hlt⟩ hp

-- Each squarefree index contributes at most the product of its prime weights.
private lemma summand_mass_le (M : ℕ) :
    ∑ b ∈ Finset.Icc 1 M, |summand b| ≤
      ∏ p ∈ smallPrimes ∪ largePrimes M, (1 + weight p) := by
  classical
  let T := (Finset.Icc 1 M).filter Squarefree
  have hinj : Set.InjOn Nat.primeFactors ↑T := by
    intro b hb c hc heq
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    rw [← Nat.prod_primeFactors_of_squarefree hb', ← Nat.prod_primeFactors_of_squarefree hc', heq]
  have hsubset : T.image Nat.primeFactors ⊆ (smallPrimes ∪ largePrimes M).powerset := by
    intro f hf
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    apply Finset.mem_powerset.mpr
    intro p hp
    obtain ⟨hprime, hdvd, hb0⟩ := Nat.mem_primeFactors.mp hp
    have hbM := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
    have hpM := (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hdvd).trans hbM
    by_cases h : p < 11
    · exact Finset.mem_union_left _ (mem_smallPrimes_of_prime hprime h)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hpM⟩, hprime⟩)
  calc
    ∑ b ∈ Finset.Icc 1 M, |summand b| = ∑ b ∈ T, |summand b| := by
      symm
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : Squarefree b
      · simp [hb]
      · simp [hb, summand, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hb]
    _ ≤ ∑ b ∈ T, ∏ p ∈ b.primeFactors, weight p := by
      exact Finset.sum_le_sum fun b hb => abs_summand_le (Finset.mem_filter.mp hb).2
    _ = ∑ f ∈ T.image Nat.primeFactors, ∏ p ∈ f, weight p := (Finset.sum_image (f := fun f => ∏ p ∈ f, weight p) hinj).symm
    _ ≤ ∑ f ∈ (smallPrimes ∪ largePrimes M).powerset, ∏ p ∈ f, weight p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun f _ _ =>
        Finset.prod_nonneg fun p _ => weight_nonneg p
    _ = _ := (Finset.prod_one_add (f := weight) _).symm

private noncomputable def stepWeight (k : ℕ) : ℝ :=
  1 / (4 * ((k : ℝ) + 4)) - 1 / (4 * ((k : ℝ) + 5))

private lemma stepWeight_nonneg (k : ℕ) : 0 ≤ stepWeight k := by
  apply sub_nonneg.mpr
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

private lemma sum_stepWeight (n : ℕ) :
    ∑ k ∈ Finset.range n, stepWeight k = 1 / 16 - 1 / (4 * ((n : ℝ) + 4)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, stepWeight, Nat.cast_succ]
    rw [show (n : ℝ) + 1 + 4 = (n : ℝ) + 5 by ring]
    ring

private lemma large_prime_index {p : ℕ} (hp : p.Prime) (hlt : 11 ≤ p) :
    p = 2 * (((p - 1) / 2) - 5) + 11 := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  omega

-- An odd prime p ≥ 11 corresponds to the index (p − 11) / 2 in the telescoping sum.
private lemma weight_le_stepWeight {p : ℕ} (hp : p.Prime) (hlt : 11 ≤ p) :
    weight p ≤ stepWeight (((p - 1) / 2) - 5) := by
  let k := ((p - 1) / 2) - 5
  have hp' : p - 1 = 2 * k + 10 := by
    have h := large_prime_index hp hlt
    omega
  have h4 : 0 < (k : ℝ) + 4 := by positivity
  have h5 : 0 < (k : ℝ) + 5 := by positivity
  have hstep : stepWeight k = 1 / (4 * ((k : ℝ) + 4) * ((k : ℝ) + 5)) := by
    unfold stepWeight
    field_simp [ne_of_gt h4, ne_of_gt h5]
    ring
  change weight p ≤ stepWeight k
  rw [weight, hp', Nat.cast_add, Nat.cast_mul, hstep]
  norm_num only [Nat.cast_ofNat]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

private lemma largePrimes_weight_sum_le (M : ℕ) :
    ∑ p ∈ largePrimes M, weight p ≤ 1 / 16 := by
  let f (p : ℕ) := ((p - 1) / 2) - 5
  have hinj : Set.InjOn f ↑(largePrimes M) := by
    intro p hp q hq heq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    rw [large_prime_index hp'.2 (Finset.mem_Icc.mp hp'.1).1,
      large_prime_index hq'.2 (Finset.mem_Icc.mp hq'.1).1]
    change 2 * f p + 11 = 2 * f q + 11
    rw [heq]
  have hsubset : (largePrimes M).image f ⊆ Finset.range (M + 1) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hpM := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    apply Finset.mem_range.mpr
    dsimp [f]
    omega
  calc
    ∑ p ∈ largePrimes M, weight p ≤ ∑ p ∈ largePrimes M, stepWeight (f p) :=
      Finset.sum_le_sum fun p hp => weight_le_stepWeight
        (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    _ = ∑ k ∈ (largePrimes M).image f, stepWeight k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range (M + 1), stepWeight k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun k _ _ => stepWeight_nonneg k
    _ ≤ _ := by
      rw [sum_stepWeight]
      exact sub_le_self _ (by positivity)

-- A nonnegative weight sum below one bounds the product of one plus the weights.
private lemma one_sub_sum_mul_prod_le (S : Finset ℕ) :
    (1 - ∑ p ∈ S, weight p) * (∏ p ∈ S, (1 + weight p)) ≤ 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.sum_insert hp, Finset.prod_insert hp, ← mul_assoc]
    have hw := weight_nonneg p
    have hs : 0 ≤ ∑ q ∈ S, weight q := Finset.sum_nonneg fun q _ => weight_nonneg q
    have hprod : 0 ≤ ∏ q ∈ S, (1 + weight q) :=
      Finset.prod_nonneg fun q _ => by linarith [weight_nonneg q]
    refine (mul_le_mul_of_nonneg_right ?_ hprod).trans ih
    nlinarith [mul_nonneg hw hw, mul_nonneg hw hs]

private lemma prime_product_le (M : ℕ) :
    ∏ p ∈ smallPrimes ∪ largePrimes M, (1 + weight p) ≤ 629 / 216 := by
  have hdisjoint : Disjoint smallPrimes (largePrimes M) := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hp11 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp').1).1
    simp [smallPrimes] at hp
    omega
  have hsmall : ∏ p ∈ smallPrimes, (1 + weight p) = (3145 : ℝ) / 1152 := by
    norm_num [smallPrimes, Finset.prod_insert, weight]
  have hprod : 0 ≤ ∏ p ∈ largePrimes M, (1 + weight p) :=
    Finset.prod_nonneg fun p _ => by linarith [weight_nonneg p]
  have hlarge : ∏ p ∈ largePrimes M, (1 + weight p) ≤ 16 / 15 := by
    have hsum := largePrimes_weight_sum_le M
    have hmul := mul_le_mul_of_nonneg_right (show (15 : ℝ) / 16 ≤
      1 - ∑ p ∈ largePrimes M, weight p by linarith) hprod
    linarith [hmul.trans (one_sub_sum_mul_prod_le (largePrimes M))]
  rw [Finset.prod_union hdisjoint, hsmall]
  linarith

-- The terms at 1 and 2 are both 1. Use the absolute mass to bound the remaining terms.
private lemma series_ge {M : ℕ} (hM : 2 ≤ M) :
    (235 : ℝ) / 216 ≤ ∑ b ∈ Finset.Icc 1 M, summand b := by
  have h1 : summand 1 = 1 := by norm_num [summand]
  have h2 : summand 2 = 1 := by
    norm_num [summand, ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      Nat.totient_prime Nat.prime_two]
  have hsubset : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 M := by
    intro b hb
    simp at hb
    exact Finset.mem_Icc.mpr (by omega)
  have hmass := (summand_mass_le M).trans (prime_product_le M)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun b => summand b + |summand b|)
    hsubset (fun b _ _ => by linarith [neg_abs_le (summand b)])
  have hhead : (∑ b ∈ ({1, 2} : Finset ℕ), (summand b + |summand b|)) = 4 := by
    norm_num [Finset.sum_insert, h1, h2]
  rw [hhead, Finset.sum_add_distrib] at hsum
  linarith

end Erdos287Series

theorem OMA.solution : OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1.H2 := by
  change ∀ᶠ N : ℕ in atTop, (17 : ℝ) / 16 ≤
    ∑ b ∈ Finset.Icc 1 (Nat.floor (Real.log (N : ℝ) ^ 2)), Erdos287Series.summand b
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hlog] with N hN
  change 2 ≤ Real.log (N : ℝ) at hN
  have hcutoff : 2 ≤ Nat.floor (Real.log (N : ℝ) ^ 2) := by
    apply Nat.le_floor
    push_cast
    nlinarith
  exact (by norm_num : (17 : ℝ) / 16 ≤ 235 / 216).trans (Erdos287Series.series_ge hcutoff)
