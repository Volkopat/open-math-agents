import OMAReductions.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

/-!
# Recovering the intermediate-prime estimate from large prime factors

The denominator h! of (n+h choose h) removes none of the prime factors above h.
Its logarithm therefore pays for both the intermediate primes and the large ones.
H1 is the large-prime count supplied by Lemma 3 of Erdős, Graham, Ivić and
Pomerance (1996). H2 is the elementary binomial entropy estimate.
-/

namespace OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R1

open Filter Finset Real
open scoped Classical

/-- The large-prime counting lemma of Erdős, Graham, Ivić and Pomerance, at integer starts. -/
def H1 : Prop := ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊
  ρ * (h : ℝ) ≤ (((range h).biUnion (fun i =>
    (n+i+1).primeFactors.filter (fun p : ℕ =>
      (n : ℝ) ^ ((5 : ℝ)/9+1/10000) < (p : ℝ)))).card : ℝ)

/-- The full binomial coefficient has logarithmic mass at most (5/9+o(1)) h log n. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊
  log (((n+h).choose h : ℕ) : ℝ) ≤ (5/9+ε) * (h : ℝ) * log n

/-- Valuations above the window length pass unchanged into its binomial coefficient. -/
lemma window_valuation (n h p : ℕ) (hp : h < p) :
    (∑ i ∈ range h, (n+i+1).factorization p) = ((n+h).choose h).factorization p := by
  have hprod : (∏ i ∈ range h, (n+i+1)) = h.factorial * (n+h).choose h := by
    simpa only [Nat.add_right_comm n 1] using
      (Nat.ascFactorial_eq_prod_range (n+1) h).symm.trans (Nat.ascFactorial_eq_factorial_mul_choose n h)
  rw [← Nat.factorization_prod_apply (fun (i : ℕ) (_ : i ∈ range h) => Nat.succ_ne_zero (n+i)),
      hprod, Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.choose_ne_zero (by omega)),
      Finsupp.add_apply, Nat.factorization_factorial_eq_zero_of_lt hp, zero_add]

lemma mass_budget (n h : ℕ) (A B : ℝ) (hA : (h:ℝ) ≤ A) (hAB : A ≤ B) :
    (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => A < (p:ℝ) ∧ (p:ℝ) ≤ B),
      ((n+i+1).factorization p : ℝ) * log p) +
    (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => B < (p:ℝ)),
      ((n+i+1).factorization p : ℝ) * log p) ≤ log (((n+h).choose h : ℕ) : ℝ) := by
  let T := (range (n+h+1)).filter (fun p => h < p)
  let w := fun (m p : ℕ) => (m.factorization p : ℝ) * log p
  have nonneg (m p : ℕ) : 0 ≤ w m p := by
    by_cases hp : p = 0
    · simp [w, hp]
    · exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp))
  have row (i : ℕ) (hi : i ∈ range h) :
      (∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => A < (p:ℝ) ∧ (p:ℝ) ≤ B), w (n+i+1) p) +
      (∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => B < (p:ℝ)), w (n+i+1) p)
      ≤ ∑ p ∈ T, w (n+i+1) p := by
    let M := (n+i+1).primeFactors.filter (fun p : ℕ => A < (p:ℝ) ∧ (p:ℝ) ≤ B)
    let G := (n+i+1).primeFactors.filter (fun p : ℕ => B < (p:ℝ))
    have dis : Disjoint M G := by
      apply Finset.disjoint_left.mpr
      intro p pm pg
      exact (not_lt_of_ge (mem_filter.mp pm).2.2) (mem_filter.mp pg).2
    have sub : M ∪ G ⊆ T := by
      intro p hp
      have hit : p ∈ (n+i+1).primeFactors ∧ A < (p:ℝ) := by
        rcases mem_union.mp hp with hm | hg
        · exact ⟨(mem_filter.mp hm).1,(mem_filter.mp hm).2.1⟩
        · exact ⟨(mem_filter.mp hg).1,hAB.trans_lt (mem_filter.mp hg).2⟩
      have pd := Nat.le_of_dvd (Nat.succ_pos _) (Nat.dvd_of_mem_primeFactors hit.1)
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hi; omega),
        by exact_mod_cast (hA.trans_lt hit.2)⟩
    rw [← Finset.sum_union dis]
    exact sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => nonneg _ p)
  have total := sum_le_sum row
  rw [sum_add_distrib, sum_comm (s := range h) (t := T)] at total
  have col (p : ℕ) (hp : p ∈ T) :
      (∑ i ∈ range h, w (n+i+1) p) = w ((n+h).choose h) p := by
    dsimp only [w]
    rw [← sum_mul, ← Nat.cast_sum, window_valuation n h p (mem_filter.mp hp).2]
  rw [sum_congr rfl col] at total
  apply total.trans
  let C := (n+h).choose h
  have remove : (∑ p ∈ T.filter (· ∈ C.primeFactors), w C p) = ∑ p ∈ T, w C p := by
    apply sum_subset (filter_subset _ _)
    intro p hp hnot
    have absent : p ∉ C.primeFactors := fun h' => hnot (mem_filter.mpr ⟨hp,h'⟩)
    have zero : C.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using absent
    simp [w, zero]
  change (∑ p ∈ T, w C p) ≤ log (C:ℝ)
  rw [← remove, OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.log_factors C
    (Nat.choose_pos (by omega))]
  exact sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.mp hp).2) (fun p _ _ => nonneg C p)

/-- Every distinct prime in the union contributes at least one logarithm to the window. -/
lemma distinct_prime_mass (n h : ℕ) (B t : ℝ) (ht : 0 ≤ t)
    (hl : ∀ p : ℕ, B < (p:ℝ) → t ≤ log p) :
    let G := fun i : ℕ => (n+i+1).primeFactors.filter (fun p : ℕ => B < (p:ℝ))
    (((range h).biUnion G).card : ℝ)*t ≤ ∑ i ∈ range h, ∑ p ∈ G i,
      ((n+i+1).factorization p : ℝ)*log p := by
  let G := fun i : ℕ => (n+i+1).primeFactors.filter (fun p : ℕ => B < (p:ℝ))
  have hc : (((range h).biUnion G).card : ℝ) ≤ ∑ i ∈ range h, ((G i).card:ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := range h) (t := G))
  calc
    _ ≤ (∑ i ∈ range h, ((G i).card:ℝ))*t := mul_le_mul_of_nonneg_right hc ht
    _ = ∑ i ∈ range h, ∑ _p ∈ G i, t := by simp only [sum_mul, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro p hp
      have hm := (mem_filter.mp hp).1
      have hlog := hl p (mem_filter.mp hp).2
      have hv := (Nat.prime_of_mem_primeFactors hm).factorization_pos_of_dvd
        (Nat.succ_ne_zero (n+i)) (Nat.dvd_of_mem_primeFactors hm)
      have one : (1:ℝ) ≤ ((n+i+1).factorization p : ℝ) := by exact_mod_cast hv
      exact hlog.trans (le_mul_of_one_le_left (ht.trans hlog) one)

/-- A finite form of the entropy bound, sufficient for all window exponents below one. -/
lemma log_window_choose (n h : ℕ) (hh : 0 < h) :
    log (((n+h).choose h : ℕ):ℝ) ≤ h * (log ((n:ℝ)+h) - log h + 1) := by
  have hC : 0 < (n+h).choose h := Nat.choose_pos (by omega)
  have hc := Real.log_le_log (by exact_mod_cast hC : (0:ℝ) < ((n+h).choose h : ℕ))
    (Nat.choose_le_pow_div (α := ℝ) h (n+h))
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at hc
  push_cast at hc
  have hf := Stirling.le_log_factorial_stirling (Nat.ne_of_gt hh)
  have hhlog : 0 ≤ log (h:ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ h from hh))
  have hπ : 0 ≤ log (2 * Real.pi) := log_nonneg (by linarith [Real.pi_gt_three])
  linarith

lemma binomial_entropy : H2 := by
  intro ε hε
  have lp : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have pw : Tendsto (fun n : ℕ => (n:ℝ)^((4:ℝ)/9)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 4/9)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ), pw.eventually_ge_atTop 2,
    lp.eventually_ge_atTop ((2*log 2+1)/ε)] with n hn hpow hlog
  let A := (n:ℝ)^((4:ℝ)/9)
  let h := ⌊A⌋₊
  have hnR : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have ha : 2 ≤ A := hpow
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one _
  have hh : 0 < h := by
    by_contra! hh
    have hz : h = 0 := by omega
    rw [hz, Nat.cast_zero] at hfloor
    linarith
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hA : A ≤ (n:ℝ) := by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (4:ℝ)/9 ≤ 1))
  have hhN := (Nat.floor_le (by dsimp [A]; positivity : 0 ≤ A)).trans hA
  have upper := log_le_log (by positivity : 0 < (n:ℝ)+h)
    (by change (n:ℝ)+⌊A⌋₊ ≤ _; linarith : (n:ℝ)+h ≤ 2*(n:ℝ))
  rw [log_mul (by norm_num) hnR.ne'] at upper
  have lower := log_le_log (by dsimp [A]; positivity : 0 < A)
    (by linarith : A ≤ 2*(h:ℝ))
  rw [log_mul (by norm_num) hhR.ne'] at lower
  dsimp [A] at lower
  rw [Real.log_rpow hnR] at lower
  have err := (div_le_iff₀ hε).mp hlog
  have step : log ((n:ℝ)+h) - log h + 1 ≤ (5/9+ε)*log n := by linarith
  change log (((n+h).choose h : ℕ):ℝ) ≤ (5/9+ε)*(h:ℝ)*log n
  calc
    _ ≤ _ := log_window_choose n h hh
    _ ≤ (h:ℝ)*((5/9+ε)*log n) := mul_le_mul_of_nonneg_left step hhR.le
    _ = _ := by ring

theorem main : H1 → H2 → OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H2 := by
  rintro ⟨ρ, hρ, hlarge⟩ hbin
  refine ⟨ρ/4, by positivity, ?_⟩
  filter_upwards [hlarge, hbin (ρ/4) (by positivity), eventually_ge_atTop (1:ℕ)]
    with n hlarge hbin hn
  let A := (n:ℝ) ^ ((4:ℝ)/9)
  let B := (n:ℝ) ^ ((5:ℝ)/9+1/10000)
  let h := ⌊A⌋₊
  have budget := mass_budget n h A B (Nat.floor_le (by dsimp [A]; positivity))
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num : (4:ℝ)/9 ≤ 5/9+1/10000))
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le hn1
  have hln : 0 ≤ log (n:ℝ) := log_nonneg hn1
  have half : 0 ≤ (1/2:ℝ)*log n := by positivity
  have count := distinct_prime_mass n h B ((1/2:ℝ)*log n) half (by
    intro p hp
    have hlog := log_le_log (by dsimp [B]; positivity : 0 < B) hp.le
    dsimp only [B] at hlog
    rw [log_rpow hn0] at hlog
    linarith)
  have weighted := mul_le_mul_of_nonneg_right hlarge half
  dsimp only at hbin weighted ⊢
  dsimp only [A, B, h] at budget count
  linarith only [budget, weighted, count, hbin]

end OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R1
