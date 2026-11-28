import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1_H1_R1

/-!
Proof of `OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1_H1_R1.H2`.
Divisor bound: for every `δ > 0` there is `C` with `d(n) ≤ C * n ^ δ`. Write
`d(n) = ∏ (a_p + 1)` over the prime factorization `n = ∏ p ^ a_p`. If `p ^ δ ≥ 2` then
`a + 1 ≤ 2 ^ a ≤ (p ^ δ) ^ a`; otherwise `p < 2 ^ (1 / δ)` and Bernoulli's inequality gives
`a + 1 ≤ K * (2 ^ δ) ^ a ≤ K * (p ^ δ) ^ a` with `K = max 1 (1 / (2 ^ δ - 1))`. Multiplying,
`d(n) ≤ K ^ N0 * n ^ δ` where `N0 = ⌈2 ^ (1 / δ)⌉`. With `δ = ε / 24`, every `m ≤ N ^ 2`
has `d(m) ≤ C * N ^ (ε / 12)`, and `C ≤ N ^ (ε / 12)` for all large `N`.
-/

namespace OMAProof.DivisorBound

open Finset Filter Topology

theorem lin_le_exp (r : ℝ) (hr : 1 < r) (a : ℕ) :
    (a : ℝ) + 1 ≤ max 1 (1 / (r - 1)) * r ^ a := by
  have h1 : 1 + (a : ℝ) * (r - 1) ≤ r ^ a := by
    have := one_add_mul_le_pow (a := r - 1) (by linarith) a
    simpa using this
  have hM2 : 1 / (r - 1) ≤ max 1 (1 / (r - 1)) := le_max_right _ _
  have hr1 : 0 < r - 1 := by linarith
  have hM3 : 1 ≤ max 1 (1 / (r - 1)) * (r - 1) := by
    rw [div_le_iff₀ hr1] at hM2; linarith
  have hM0 : 0 ≤ max 1 (1 / (r - 1)) := le_trans zero_le_one (le_max_left _ _)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  calc (a : ℝ) + 1 ≤ max 1 (1 / (r - 1)) * (1 + a * (r - 1)) := by
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hM3), le_max_left (1:ℝ) (1 / (r - 1))]
    _ ≤ max 1 (1 / (r - 1)) * r ^ a := mul_le_mul_of_nonneg_left h1 hM0

theorem rpow_pow_comm' (x : ℝ) (hx : 0 ≤ x) (δ : ℝ) (a : ℕ) :
    (x ^ δ) ^ a = (x ^ a) ^ δ := by
  rw [← Real.rpow_mul_natCast hx, ← Real.rpow_natCast_mul hx, mul_comm]

theorem divisor_bound (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
    (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  set r : ℝ := (2 : ℝ) ^ δ with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hδ
  set K : ℝ := max 1 (1 / (r - 1)) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  set N0 : ℕ := ⌈(2 : ℝ) ^ (1 / δ)⌉₊ with hN0
  refine ⟨K ^ N0, by positivity, ?_⟩
  intro n hn
  let c : ℕ → ℝ := fun p => if 2 ≤ (p : ℝ) ^ δ then 1 else K
  have hloc : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1) ≤ c p * ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases h : 2 ≤ (p : ℝ) ^ δ
    · simp only [c, if_pos h, one_mul]
      calc ((n.factorization p : ℕ) : ℝ) + 1 ≤ 2 ^ (n.factorization p) := by
            exact_mod_cast (n.factorization p).lt_two_pow_self
        _ ≤ ((p : ℝ) ^ δ) ^ (n.factorization p) := pow_le_pow_left₀ (by norm_num) h _
    · simp only [c, if_neg h]
      calc ((n.factorization p : ℕ) : ℝ) + 1 ≤ K * r ^ (n.factorization p) :=
            lin_le_exp r hr1 _
        _ ≤ K * ((p : ℝ) ^ δ) ^ (n.factorization p) := by
          gcongr
          exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
  have hcard : (n.divisors.card : ℝ) =
      ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]; push_cast; rfl
  have hprodn : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact_mod_cast h.symm
  have hpow : (n : ℝ) ^ δ =
      ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    rw [hprodn, ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [rpow_pow_comm' _ (Nat.cast_nonneg p)]
  have hc : ∏ p ∈ n.primeFactors, c p ≤ K ^ N0 := by
    have : ∏ p ∈ n.primeFactors, c p =
        K ^ (n.primeFactors.filter (fun p : ℕ => ¬ 2 ≤ (p : ℝ) ^ δ)).card := by
      simp only [c]
      rw [Finset.prod_ite]
      simp
    rw [this]
    apply pow_le_pow_right₀ hK1
    calc (n.primeFactors.filter (fun p : ℕ => ¬ 2 ≤ (p : ℝ) ^ δ)).card
        ≤ (range N0).card := by
          apply card_le_card
          intro p hp
          simp only [mem_filter] at hp
          simp only [mem_range]
          by_contra hge
          push Not at hge
          apply hp.2
          have h1 : (2 : ℝ) ^ (1 / δ) ≤ p :=
            (Nat.le_ceil _).trans (by exact_mod_cast hge)
          calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
                rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne',
                  Real.rpow_one]
            _ ≤ (p : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ.le
      _ = N0 := card_range N0
  rw [hcard, hpow]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (c p * ((p : ℝ) ^ δ) ^ (n.factorization p)) :=
        Finset.prod_le_prod (fun _ _ => by positivity) hloc
    _ = (∏ p ∈ n.primeFactors, c p) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) :=
        Finset.prod_mul_distrib
    _ ≤ K ^ N0 * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
        gcongr

end OMAProof.DivisorBound

open Finset Filter Topology OMAProof.DivisorBound in
theorem OMA.solution :
    OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := divisor_bound (ε / 24) (by positivity)
  have hlarge : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ (ε / 6 - ε / 6 / 2) := by
    have := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < ε / 6 - ε / 6 / 2)).comp
      tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop C
  filter_upwards [hlarge, eventually_ge_atTop 1] with N hN hN1 m hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp only [Nat.divisors_zero, card_empty, Nat.cast_zero]; positivity
  have h1 := hb m hm0.ne'
  have h2 : (m : ℝ) ^ (ε / 24) ≤ (N : ℝ) ^ (ε / 6 / 2) := by
    calc (m : ℝ) ^ (ε / 24) ≤ ((N : ℝ) ^ 2) ^ (ε / 24) :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hm) (by positivity)
      _ = (N : ℝ) ^ (ε / 6 / 2) := by
          rw [← Real.rpow_natCast_mul hNpos.le]; congr 1; push_cast; ring
  calc (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ (ε / 24) := h1
    _ ≤ (N : ℝ) ^ (ε / 6 - ε / 6 / 2) * (N : ℝ) ^ (ε / 6 / 2) := by
        gcongr
    _ = (N : ℝ) ^ (ε / 6) := by rw [← Real.rpow_add hNpos]; ring_nf
