import FormalConjectures.Wikipedia.ChebyshevBias

/-!
# Reduction of `ChebyshevBias.knapowski_turan_natural_density_false`

Following Rubinstein–Sarnak (1994, §2.2) and Kaczorowski (1995), assuming GRH for $L(s, \chi_4)$,
we reduce the refutation of the Knapowski–Turán natural-density-$1$ conjecture to three analytic
inputs about the normalized prime race in logarithmic variable:
1. (`H1`) A bounded logarithmic second moment.
2. (`H2`) Uniform Bohr almost-periodicity after convolving with the compactly supported triangle
   kernel $\Lambda_M(u) = (1 - |u| / M) / M$ on $[-M, M]$.
3. (`H3`) Arbitrarily large positive excursions of the triangle-smoothed prime race for some $M > 0$.
-/

-- Reduction ChebyshevBias.knapowski_turan_natural_density_false.R1 of Chebyshev's bias — knapowski turan natural density false
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter Finset MeasureTheory Set
open scoped Topology Classical

namespace OMA.R_ChebyshevBias_knapowski_turan_natural_density_false_R1

/- ### Step 1: Discrete harmonic bound and Abel summation -/

lemma sum_inv_Icc_two_le_log (N : ℕ) :
    ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) ≤ Real.log N := by
  induction N with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have hsub : Finset.Icc 2 (m + 2) = insert (m + 2) (Finset.Icc 2 (m + 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      have hm1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have hm2 : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      have hlog : Real.log (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤
          ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hm1 hm2)
      rw [Real.log_div hm1.ne' hm2.ne'] at hlog
      have hstep : 1 / ((m + 2 : ℕ) : ℝ) ≤
          Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
        have h1 : ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 =
            -(1 / ((m + 2 : ℕ) : ℝ)) := by
          push_cast; field_simp; ring
        linarith
      linarith

lemma sum_by_parts_Icc_two (c : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ) =
      (∑ j ∈ Finset.range (N + 1), c j) / (N : ℝ) -
      (∑ j ∈ Finset.range 2, c j) / 2 +
      ∑ j ∈ Finset.Icc 2 (N - 1),
        (∑ k ∈ Finset.range (j + 1), c k) / ((j : ℝ) * ((j : ℝ) + 1)) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    ring
  | succ n hn ih =>
    have hIcc1 : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hIcc2 : Finset.Icc 2 n = insert n (Finset.Icc 2 (n - 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc1, Finset.sum_insert (by simp), ih]
    simp only [Nat.add_sub_cancel]
    rw [hIcc2, Finset.sum_insert (by simp; omega)]
    rw [Finset.sum_range_succ (n := n + 1)]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma partialDensity_compl_tendsto_zero (S : Set ℕ) (hS : S.HasDensity 1) :
    Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, (if j ∈ S then (0 : ℝ) else 1)) / (n : ℝ))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - S.partialDensity Set.univ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hS
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hIio : (Set.Iio n : Set ℕ) = ↑(Finset.range n) := by
    ext k; simp [Set.mem_Iio]
  have hden : ((Set.univ ∩ Set.Iio n).ncard : ℝ) = (n : ℝ) := by
    rw [Set.univ_inter, hIio, Set.ncard_coe_finset, Finset.card_range]
  have hnum : (((S ∩ Set.univ) ∩ Set.Iio n).ncard : ℝ) =
      (((Finset.range n).filter (fun j => j ∈ S)).card : ℝ) := by
    rw [Set.inter_univ, hIio]
    have hset : S ∩ ↑(Finset.range n) = ↑((Finset.range n).filter (fun j => j ∈ S)) := by
      ext k; simp [and_comm]
    rw [hset, Set.ncard_coe_finset]
  have hcompl : (∑ j ∈ Finset.range n, (if j ∈ S then (0 : ℝ) else 1)) =
      (((Finset.range n).filter (fun j => j ∉ S)).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hpartR : (((Finset.range n).filter (fun j => j ∈ S)).card : ℝ) +
      (((Finset.range n).filter (fun j => j ∉ S)).card : ℝ) = (n : ℝ) := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_add_distrib]
    have hsum1 : ∑ j ∈ Finset.range n, ((if j ∈ S then (1 : ℝ) else 0) +
        (if j ∉ S then (1 : ℝ) else 0)) = ∑ _ ∈ Finset.range n, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ S <;> simp [hj]
    simpa using hsum1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [Set.partialDensity, hden, hnum, hcompl]
  field_simp
  linarith

lemma complement_harmonic_tendsto_zero (S : Set ℕ) (hS : S.HasDensity 1) :
    Tendsto (fun N : ℕ =>
      (∑ j ∈ Finset.Icc 2 N, (if j ∈ S then (0 : ℝ) else 1) / (j : ℝ)) / Real.log N)
      atTop (𝓝 0) := by
  let c : ℕ → ℝ := fun j => if j ∈ S then 0 else 1
  let C : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, c j
  have hc0 : ∀ j, 0 ≤ c j := fun j => by dsimp [c]; split_ifs <;> norm_num
  have hC0 : ∀ m, 0 ≤ C m := fun m => Finset.sum_nonneg fun j _ => hc0 j
  have hCt : Tendsto (fun m : ℕ => C m / (m : ℝ)) atTop (𝓝 0) :=
    partialDensity_compl_tendsto_zero S hS
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp hCt) (ε / 4) (by positivity)
  let M : ℕ := max M₀ 2
  have hM2 : 2 ≤ M := le_max_right _ _
  have hCM : ∀ m ≥ M, C m ≤ (ε / 4) * (m : ℝ) := by
    intro m hm
    have hdist := hM₀ m (le_trans (le_max_left _ _) hm)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hC0 m) (Nat.cast_nonneg m))] at hdist
    have hmpos : (0 : ℝ) < m := by
      have : 0 < m := by omega
      exact_mod_cast this
    exact (div_le_iff₀ hmpos).mp hdist.le
  let K₀ : ℝ := ∑ j ∈ Finset.Icc 2 (M - 1), C (j + 1) / ((j : ℝ) * ((j : ℝ) + 1))
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp hlogTop) (max 1 ((ε / 2 + K₀) / (ε / 2) + 1)))
  refine ⟨max M (max N₀ 3), fun N hN => ?_⟩
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans hM2 hNM
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hlogN : max 1 ((ε / 2 + K₀) / (ε / 2) + 1) ≤ Real.log (N : ℝ) := hN₀ N hN0
  have hlog_pos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hlogN)
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ) :=
    Finset.sum_nonneg fun j _ => div_nonneg (hc0 j) (Nat.cast_nonneg j)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hsum_nonneg hlog_pos.le)]
  have hparts := sum_by_parts_Icc_two c N hN2
  have hlead : C (N + 1) / (N : ℝ) ≤ ε / 2 := by
    have h1 := hCM (N + 1) (by omega)
    have hNpos : (0 : ℝ) < N := by positivity
    rw [div_le_iff₀ hNpos]
    have h2 : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      push_cast
      have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      linarith
    nlinarith
  have hsplit : Finset.Icc 2 (N - 1) = Finset.Icc 2 (M - 1) ∪ Finset.Icc M (N - 1) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 2 (M - 1)) (Finset.Icc M (N - 1)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_Icc] at hj1 hj2
    omega
  have htail : ∑ j ∈ Finset.Icc M (N - 1), C (j + 1) / ((j : ℝ) * ((j : ℝ) + 1)) ≤
      (ε / 4) * Real.log (N : ℝ) := by
    calc
      ∑ j ∈ Finset.Icc M (N - 1), C (j + 1) / ((j : ℝ) * ((j : ℝ) + 1))
          ≤ ∑ j ∈ Finset.Icc M (N - 1), (ε / 4) * (1 / (j : ℝ)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            simp only [Finset.mem_Icc] at hj
            have hjpos : (0 : ℝ) < j := by
              have : 0 < j := by omega
              exact_mod_cast this
            have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
            have hCj : C (j + 1) ≤ (ε / 4) * ((j + 1 : ℕ) : ℝ) := hCM (j + 1) (by omega)
            rw [div_le_iff₀ (mul_pos hjpos hj1pos)]
            have : (ε / 4) * (1 / (j : ℝ)) * ((j : ℝ) * ((j : ℝ) + 1)) =
                (ε / 4) * ((j + 1 : ℕ) : ℝ) := by
              push_cast; field_simp
            linarith
      _ = (ε / 4) * ∑ j ∈ Finset.Icc M (N - 1), (1 / (j : ℝ)) := by rw [← Finset.mul_sum]
      _ ≤ (ε / 4) * ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => by positivity
            intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      _ ≤ (ε / 4) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_left (sum_inv_Icc_two_le_log N) (by positivity)
  have hsum_ub : ∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ) ≤
      ε / 2 + K₀ + (ε / 4) * Real.log (N : ℝ) := by
    rw [hparts, hsplit, Finset.sum_union hdisj]
    have hC2 : 0 ≤ C 2 / 2 := div_nonneg (hC0 2) (by norm_num)
    change C (N + 1) / (N : ℝ) - C 2 / 2 +
      (K₀ + ∑ j ∈ Finset.Icc M (N - 1), C (j + 1) / ((j : ℝ) * ((j : ℝ) + 1))) ≤ _
    linarith
  have hconst : (ε / 2 + K₀) / Real.log (N : ℝ) < ε / 2 := by
    have hK0_nonneg : 0 ≤ K₀ := Finset.sum_nonneg fun j _ =>
      div_nonneg (hC0 (j + 1)) (by positivity)
    have hbound : (ε / 2 + K₀) / (ε / 2) + 1 ≤ Real.log (N : ℝ) :=
      le_trans (le_max_right _ _) hlogN
    have hstrict : (ε / 2 + K₀) / (ε / 2) < Real.log (N : ℝ) := by linarith
    rw [div_lt_iff₀ hlog_pos]
    have := (div_lt_iff₀ (show 0 < ε / 2 by positivity)).mp hstrict
    linarith
  have hdiv : (∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ)) / Real.log (N : ℝ) ≤
      (ε / 2 + K₀) / Real.log (N : ℝ) + ε / 4 := by
    rw [div_le_iff₀ hlog_pos]
    have : ((ε / 2 + K₀) / Real.log (N : ℝ) + ε / 4) * Real.log (N : ℝ) =
        ε / 2 + K₀ + (ε / 4) * Real.log (N : ℝ) := by
      field_simp
    linarith
  linarith

/- ### Step 2: Discrete Cauchy–Schwarz transfer to positive part -/

lemma discrete_pos_part_tendsto_zero
    (hS : ChebyshevBias.chebyshevModFourLeadSet.HasDensity 1)
    (hB : ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
        (((Real.log j / Real.sqrt j) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2) ≤
      B * Real.log N) :
    Tendsto (fun N : ℕ =>
      (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
        max ((Real.log j / Real.sqrt j) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0) / Real.log N)
      atTop (𝓝 0) := by
  let S := ChebyshevBias.chebyshevModFourLeadSet
  let c : ℕ → ℝ := fun j => if j ∈ S then 0 else 1
  let race : ℕ → ℝ := fun j =>
    (Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)
  let p : ℕ → ℝ := fun j => max (race j) 0
  obtain ⟨B, hBpos, hB_ev⟩ := hB
  have hc_tend := complement_harmonic_tendsto_zero S hS
  have hsq_tend : Tendsto (fun N : ℕ =>
      ((∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * p j) / Real.log N) ^ 2) atTop (𝓝 0) := by
    have hprod_tend : Tendsto (fun N : ℕ =>
        ((∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ)) / Real.log N) * B) atTop (𝓝 0) := by
      simpa using hc_tend.mul_const B
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod_tend
      (Eventually.of_forall fun _ => sq_nonneg _) ?_
    filter_upwards [hB_ev, eventually_ge_atTop 2] with N hBN hN2
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hcs : (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * p j) ^ 2 ≤
        (∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ)) *
          (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (race j) ^ 2) := by
      have heq : ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * p j =
          ∑ j ∈ Finset.Icc 2 N, Real.sqrt (c j / (j : ℝ)) * (Real.sqrt (1 / (j : ℝ)) * p j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
        by_cases hjS : j ∈ S
        · have hlt : (j.primeCountingMod 4 1 : ℝ) < j.primeCountingMod 4 3 := by
            exact_mod_cast hjS
          have hscale : 0 ≤ Real.log (j : ℝ) / Real.sqrt (j : ℝ) :=
            div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega)))
              (Real.sqrt_nonneg _)
          have hrace_le : race j ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hscale (by linarith)
          have hp0 : p j = 0 := max_eq_right hrace_le
          simp [c, hp0]
        · have hc1 : c j = 1 := if_neg hjS
          rw [hc1, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
      rw [heq]
      have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 2 N)
        (fun j => Real.sqrt (c j / (j : ℝ))) (fun j => Real.sqrt (1 / (j : ℝ)) * p j)
      refine hsq.trans ?_
      have hleft : ∑ j ∈ Finset.Icc 2 N, (Real.sqrt (c j / (j : ℝ))) ^ 2 =
          ∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => Real.sq_sqrt ?_
        dsimp [c]; split_ifs <;> positivity
      have hright : ∑ j ∈ Finset.Icc 2 N, (Real.sqrt (1 / (j : ℝ)) * p j) ^ 2 ≤
          ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (race j) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        dsimp [p]
        rcases le_total (race j) 0 with hr | hr
        · rw [max_eq_right hr, zero_pow two_ne_zero]; exact sq_nonneg _
        · rw [max_eq_left hr]
      rw [hleft]
      exact mul_le_mul_of_nonneg_left hright
        (Finset.sum_nonneg fun j _ => by dsimp [c]; split_ifs <;> positivity)
    have hsum_c_nonneg : 0 ≤ ∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ) :=
      Finset.sum_nonneg fun j _ => by dsimp [c]; split_ifs <;> positivity
    have h1 : (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * p j) ^ 2 ≤
        (∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ)) * (B * Real.log (N : ℝ)) :=
      hcs.trans (mul_le_mul_of_nonneg_left hBN hsum_c_nonneg)
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hlog_pos)]
    have h2 : (∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ)) / Real.log (N : ℝ) * B *
        Real.log (N : ℝ) ^ 2 =
        (∑ j ∈ Finset.Icc 2 N, c j / (j : ℝ)) * (B * Real.log (N : ℝ)) := by
      field_simp
    linarith
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq_tend
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hnn : 0 ≤ (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * p j) / Real.log (N : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (le_max_right _ _))
      hlog_pos.le
  exact Real.sqrt_sq hnn

/- ### Step 3: Measurability, local boundedness, and discrete-to-continuous transfer -/

lemma measurable_raceE :
    Measurable (fun y : ℝ =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0) := by
  have hexp : Measurable Real.exp := Real.continuous_exp.measurable
  have hfloor : Measurable (fun y : ℝ => Nat.floor (Real.exp y)) :=
    Nat.floor_mono.measurable.comp hexp
  have hdiff : Measurable (fun n : ℕ =>
      (n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3) :=
    measurable_of_countable _
  have hscale : Measurable (fun y : ℝ => y / Real.exp (y / 2)) :=
    measurable_id.div (hexp.comp (measurable_id.div_const 2))
  exact Measurable.ite (measurableSet_Ici.preimage hexp)
    (hscale.mul (hdiff.comp hfloor)) measurable_const

lemma raceE_bounded_on_Icc (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Set.Icc a b,
      |(if 2 ≤ Real.exp y then
          (y / Real.exp (y / 2)) *
            (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
             (Nat.floor (Real.exp y)).primeCountingMod 4 3)
        else 0)| ≤ C := by
  let K : ℕ := Nat.floor (Real.exp b)
  let D : ℝ := ∑ k ∈ Finset.range (K + 1),
    |(k.primeCountingMod 4 1 : ℝ) - k.primeCountingMod 4 3|
  refine ⟨(max |a| |b| / Real.exp (a / 2)) * D, ?_, fun y hy => ?_⟩
  · exact mul_nonneg (div_nonneg (le_trans (abs_nonneg a) (le_max_left _ _))
      (Real.exp_pos _).le) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · split_ifs with h2
    · rw [abs_mul, abs_div, abs_of_pos (Real.exp_pos _)]
      have hy_abs : |y| ≤ max |a| |b| := by
        rw [abs_le]
        constructor
        · linarith [hy.1, neg_abs_le a, le_max_left |a| |b|]
        · linarith [hy.2, le_abs_self b, le_max_right |a| |b|]
      have hexp_le : Real.exp (a / 2) ≤ Real.exp (y / 2) :=
        Real.exp_le_exp.mpr (by linarith [hy.1])
      have hscale : |y| / Real.exp (y / 2) ≤ max |a| |b| / Real.exp (a / 2) :=
        div_le_div₀ (le_trans (abs_nonneg a) (le_max_left _ _)) hy_abs
          (Real.exp_pos _) hexp_le
      have hn_le : Nat.floor (Real.exp y) ≤ K :=
        Nat.floor_mono (Real.exp_le_exp.mpr hy.2)
      have hmem : Nat.floor (Real.exp y) ∈ Finset.range (K + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hn_le)
      have hdiff_le : |((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
          (Nat.floor (Real.exp y)).primeCountingMod 4 3| ≤ D :=
        Finset.single_le_sum
          (f := fun k : ℕ => |(k.primeCountingMod 4 1 : ℝ) - k.primeCountingMod 4 3|)
          (fun k _ => abs_nonneg _) hmem
      exact mul_le_mul hscale hdiff_le (abs_nonneg _)
        (div_nonneg (le_trans (abs_nonneg a) (le_max_left _ _)) (Real.exp_pos _).le)
    · rw [abs_zero]
      exact mul_nonneg (div_nonneg (le_trans (abs_nonneg a) (le_max_left _ _))
        (Real.exp_pos _).le) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma raceE_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0) volume a b := by
  obtain ⟨C, _, hC⟩ := raceE_bounded_on_Icc (min a b) (max a b)
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    measurable_raceE.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  rw [Real.norm_eq_abs]
  exact hC y (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc] using hy))

lemma raceE_pos_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ =>
      max (if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0) 0) volume a b := by
  have heq : (fun y : ℝ => max (if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0) 0) =
      (fun y : ℝ => ((if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0) + ‖if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0‖) / 2) := by
    funext y
    set x := if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0
    rw [Real.norm_eq_abs]
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
  rw [heq]
  have hf := raceE_intervalIntegrable a b
  exact (hf.add hf.norm).div_const 2

lemma continuous_pos_integral_le_discrete (Y : ℝ) (N : ℕ)
    (hY0 : 0 ≤ Y) (hN2 : 2 ≤ N) (hYN : Y ≤ Real.log (N + 1 : ℕ)) :
    let E : ℝ → ℝ := fun y =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0
    ∫ y in (0 : ℝ)..Y, max (E y) 0 ≤
      2 * ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
        max ((Real.log j / Real.sqrt j) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0 := by
  intro E
  have hlog2_pos : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog_mono : Real.log 2 ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ N + 1 by omega))
  have hstep1 : ∫ y in (0 : ℝ)..Y, max (E y) 0 ≤
      ∫ y in (0 : ℝ)..Real.log ((N + 1 : ℕ) : ℝ), max (E y) 0 := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (raceE_pos_intervalIntegrable 0 Y)
      (raceE_pos_intervalIntegrable Y (Real.log ((N + 1 : ℕ) : ℝ)))
    have htail_nn : 0 ≤ ∫ y in Y..Real.log ((N + 1 : ℕ) : ℝ), max (E y) 0 :=
      intervalIntegral.integral_nonneg hYN fun _ _ => le_max_right _ _
    linarith
  have hzero : ∫ y in (0 : ℝ)..Real.log 2, max (E y) 0 = 0 := by
    rw [intervalIntegral.integral_of_le hlog2_pos, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hexp_lt : Real.exp y < 2 := by
      have := Real.exp_lt_exp.mpr hy.2
      rwa [Real.exp_log (by norm_num)] at this
    have hE0 : E y = 0 := if_neg (not_le.mpr hexp_lt)
    simp [hE0]
  have hstep2 : ∫ y in (0 : ℝ)..Real.log ((N + 1 : ℕ) : ℝ), max (E y) 0 =
      ∫ y in Real.log 2..Real.log ((N + 1 : ℕ) : ℝ), max (E y) 0 := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (raceE_pos_intervalIntegrable 0 (Real.log 2))
      (raceE_pos_intervalIntegrable (Real.log 2) (Real.log ((N + 1 : ℕ) : ℝ)))
    linarith
  have hsum_eq_all : ∀ n : ℕ, 2 ≤ n →
      ∫ y in Real.log 2..Real.log ((n + 1 : ℕ) : ℝ), max (E y) 0 =
        ∑ j ∈ Finset.Icc 2 n, ∫ y in Real.log (j : ℝ)..Real.log ((j + 1 : ℕ) : ℝ), max (E y) 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp; norm_num
    | succ m hm ih =>
      have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), ← ih]
      have hadj : (∫ y in Real.log 2..Real.log ((m + 1 : ℕ) : ℝ), max (E y) 0) +
          (∫ y in Real.log ((m + 1 : ℕ) : ℝ)..Real.log ((m + 1 + 1 : ℕ) : ℝ), max (E y) 0) =
          ∫ y in Real.log 2..Real.log ((m + 1 + 1 : ℕ) : ℝ), max (E y) 0 :=
        intervalIntegral.integral_add_adjacent_intervals
          (raceE_pos_intervalIntegrable (Real.log 2) (Real.log ((m + 1 : ℕ) : ℝ)))
          (raceE_pos_intervalIntegrable (Real.log ((m + 1 : ℕ) : ℝ))
            (Real.log ((m + 1 + 1 : ℕ) : ℝ)))
      linarith
  have hsum_eq := hsum_eq_all N hN2
  have hpiece : ∀ j ∈ Finset.Icc 2 N,
      ∫ y in Real.log (j : ℝ)..Real.log ((j + 1 : ℕ) : ℝ), max (E y) 0 ≤
        2 * ((1 / (j : ℝ)) *
          max ((Real.log j / Real.sqrt j) *
            ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0) := by
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hj1pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hle : Real.log (j : ℝ) ≤ Real.log ((j + 1 : ℕ) : ℝ) :=
      Real.log_le_log hjpos (by exact_mod_cast (show j ≤ j + 1 by omega))
    let Mj : ℝ := 2 * max ((Real.log j / Real.sqrt j) *
      ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0
    have hMj_nn : 0 ≤ Mj := mul_nonneg (by norm_num) (le_max_right _ _)
    have hle_int : ∫ y in Real.log (j : ℝ)..Real.log ((j + 1 : ℕ) : ℝ), max (E y) 0 ≤
        ∫ _ in Real.log (j : ℝ)..Real.log ((j + 1 : ℕ) : ℝ), Mj := by
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_mono_on
        ((raceE_pos_intervalIntegrable (Real.log (j : ℝ)) (Real.log ((j + 1 : ℕ) : ℝ))).1.mono_set
          Set.Ioo_subset_Ioc_self)
        (integrableOn_const (hs := measure_Ioo_lt_top.ne)) measurableSet_Ioo fun y hy => ?_
      have hexp_gt : (j : ℝ) < Real.exp y := by
        have := Real.exp_lt_exp.mpr hy.1
        rwa [Real.exp_log hjpos] at this
      have hexp_lt : Real.exp y < ((j + 1 : ℕ) : ℝ) := by
        have := Real.exp_lt_exp.mpr hy.2
        rwa [Real.exp_log hj1pos] at this
      have h2le : 2 ≤ Real.exp y :=
        le_trans (by exact_mod_cast hj2) hexp_gt.le
      have hfl : Nat.floor (Real.exp y) = j := by
        rw [Nat.floor_eq_iff (Real.exp_pos y).le]
        exact ⟨hexp_gt.le, by simpa using hexp_lt⟩
      have hEy : E y = (y / Real.exp (y / 2)) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3) := by
        simp [E, h2le, hfl]
      rw [hEy]
      have hy_pos : 0 < y := lt_of_le_of_lt (Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))) hy.1
      have hy_le : y ≤ 2 * Real.log (j : ℝ) := by
        have hsq : ((j + 1 : ℕ) : ℝ) ≤ (j : ℝ) ^ 2 := by
          have : j + 1 ≤ j * j := by nlinarith
          have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((j * j : ℕ) : ℝ) := by exact_mod_cast this
          simpa [sq] using hcast
        calc
          y ≤ Real.log ((j + 1 : ℕ) : ℝ) := hy.2.le
          _ ≤ Real.log ((j : ℝ) ^ 2) := Real.log_le_log hj1pos hsq
          _ = 2 * Real.log (j : ℝ) := by rw [Real.log_pow]; ring
      have hsqrt_le : Real.sqrt (j : ℝ) ≤ Real.exp (y / 2) := by
        have h1 : Real.sqrt (j : ℝ) = Real.exp (Real.log (j : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hjpos]; ring_nf
        rw [h1]
        exact Real.exp_le_exp.mpr (by linarith [hy.1])
      have hratio : y / Real.exp (y / 2) ≤ 2 * (Real.log (j : ℝ) / Real.sqrt (j : ℝ)) := by
        calc
          y / Real.exp (y / 2) ≤ (2 * Real.log (j : ℝ)) / Real.sqrt (j : ℝ) :=
            div_le_div₀ (by positivity) hy_le (Real.sqrt_pos.mpr hjpos) hsqrt_le
          _ = 2 * (Real.log (j : ℝ) / Real.sqrt (j : ℝ)) := by ring
      set d : ℝ := (j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3
      rcases le_total d 0 with hd | hd
      · have hle0 : (y / Real.exp (y / 2)) * d ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg hy_pos.le (Real.exp_pos _).le) hd
        rw [max_eq_right hle0]
        exact hMj_nn
      · have hpos1 : 0 ≤ (y / Real.exp (y / 2)) * d :=
          mul_nonneg (div_nonneg hy_pos.le (Real.exp_pos _).le) hd
        have hpos2 : 0 ≤ (Real.log (j : ℝ) / Real.sqrt (j : ℝ)) * d :=
          mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega)))
            (Real.sqrt_nonneg _)) hd
        rw [max_eq_left hpos1]
        dsimp [Mj]
        rw [max_eq_left hpos2]
        nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle_int
    have hlen : Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) ≤ 1 / (j : ℝ) := by
      rw [← Real.log_div hj1pos.ne' hjpos.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hj1pos hjpos)
      have h2 : ((j + 1 : ℕ) : ℝ) / (j : ℝ) - 1 = 1 / (j : ℝ) := by
        push_cast; field_simp; ring
      linarith
    have hmul : (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) * Mj ≤ (1 / (j : ℝ)) * Mj :=
      mul_le_mul_of_nonneg_right hlen hMj_nn
    have hfinal : (1 / (j : ℝ)) * Mj =
        2 * ((1 / (j : ℝ)) * max ((Real.log (j : ℝ) / Real.sqrt (j : ℝ)) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0) := by
      dsimp [Mj]; ring
    linarith
  calc
    ∫ y in (0 : ℝ)..Y, max (E y) 0
        ≤ ∫ y in Real.log 2..Real.log ((N + 1 : ℕ) : ℝ), max (E y) 0 := by linarith
    _ = ∑ j ∈ Finset.Icc 2 N, ∫ y in Real.log (j : ℝ)..Real.log ((j + 1 : ℕ) : ℝ), max (E y) 0 :=
          hsum_eq
    _ ≤ ∑ j ∈ Finset.Icc 2 N,
          2 * ((1 / (j : ℝ)) * max ((Real.log j / Real.sqrt j) *
            ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0) :=
          Finset.sum_le_sum hpiece
    _ = 2 * ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
          max ((Real.log j / Real.sqrt j) *
            ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0 := by
          rw [← Finset.mul_sum]

lemma continuous_pos_mean_tendsto_zero
    (hS : ChebyshevBias.chebyshevModFourLeadSet.HasDensity 1)
    (hB : ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
        (((Real.log j / Real.sqrt j) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2) ≤
      B * Real.log N) :
    let E : ℝ → ℝ := fun y =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0
    Tendsto (fun Y : ℝ => (∫ y in (0 : ℝ)..Y, max (E y) 0) / Y) atTop (𝓝 0) := by
  intro E
  let a : ℕ → ℝ := fun N =>
    (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
      max ((Real.log j / Real.sqrt j) *
        ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0) / Real.log N
  have ha_tend : Tendsto a atTop (𝓝 0) := discrete_pos_part_tendsto_zero hS hB
  let Nof : ℝ → ℕ := fun Y => Nat.floor (Real.exp Y) + 1
  have hNof_top : Tendsto Nof atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨Real.log (b + 1 : ℝ), fun Y hY => ?_⟩
    have h1 : (b : ℝ) + 1 ≤ Real.exp Y := by
      have := Real.exp_le_exp.mpr hY
      rwa [Real.exp_log (by positivity)] at this
    have h2 : b ≤ Nat.floor (Real.exp Y) := Nat.le_floor (by linarith)
    dsimp [Nof]; omega
  have hcomp : Tendsto (fun Y : ℝ => 4 * a (Nof Y)) atTop (𝓝 0) := by
    simpa using (ha_tend.comp hNof_top).const_mul (4 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    exact div_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => le_max_right _ _)
      (by linarith)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hYpos : 0 < Y := by linarith
    have hexpY : 2 ≤ Real.exp Y := by
      have h1 : (2 : ℝ) ≤ Y + 1 := by linarith
      exact h1.trans (Real.add_one_le_exp Y)
    have hN2 : 2 ≤ Nof Y := by
      have : 2 ≤ Nat.floor (Real.exp Y) := Nat.le_floor hexpY
      dsimp [Nof]; omega
    have hYN : Y ≤ Real.log ((Nof Y + 1 : ℕ) : ℝ) := by
      have hlt : Real.exp Y < ((Nof Y + 1 : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (Real.exp Y)
        dsimp [Nof]; push_cast; linarith
      calc
        Y = Real.log (Real.exp Y) := (Real.log_exp Y).symm
        _ ≤ Real.log ((Nof Y + 1 : ℕ) : ℝ) := Real.log_le_log (Real.exp_pos Y) hlt.le
    have hlogN_le : Real.log (Nof Y : ℝ) ≤ 2 * Y := by
      have hN_le : (Nof Y : ℝ) ≤ 2 * Real.exp Y := by
        have hfl : (Nat.floor (Real.exp Y) : ℝ) ≤ Real.exp Y :=
          Nat.floor_le (Real.exp_pos Y).le
        dsimp [Nof]; push_cast; linarith
      have hlog2_le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      calc
        Real.log (Nof Y : ℝ) ≤ Real.log (2 * Real.exp Y) :=
          Real.log_le_log (by positivity) hN_le
        _ = Real.log 2 + Y := by rw [Real.log_mul (by norm_num) (Real.exp_pos Y).ne', Real.log_exp]
        _ ≤ 2 * Y := by linarith
    have hint := continuous_pos_integral_le_discrete Y (Nof Y) hYpos.le hN2 hYN
    have hlogN_pos : 0 < Real.log (Nof Y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Nof Y by omega))
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.Icc 2 (Nof Y), (1 / (j : ℝ)) *
        max ((Real.log j / Real.sqrt j) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0 :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (le_max_right _ _)
    rw [div_le_iff₀ hYpos]
    have ha_eq : a (Nof Y) * Real.log (Nof Y : ℝ) =
        ∑ j ∈ Finset.Icc 2 (Nof Y), (1 / (j : ℝ)) *
          max ((Real.log j / Real.sqrt j) *
            ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) 0 :=
      div_mul_cancel₀ _ hlogN_pos.ne'
    have ha_nn : 0 ≤ a (Nof Y) := div_nonneg hsum_nn hlogN_pos.le
    calc
      ∫ y in (0 : ℝ)..Y, max (E y) 0
          ≤ 2 * (a (Nof Y) * Real.log (Nof Y : ℝ)) := by rw [ha_eq]; exact hint
      _ ≤ 2 * (a (Nof Y) * (2 * Y)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogN_le ha_nn) (by norm_num)
      _ = 4 * a (Nof Y) * Y := by ring

/- ### Step 4: Triangle kernel smoothing and Fubini swap -/

lemma triangle_kernel_integral (M : ℝ) (hM : 0 < M) :
    ∫ u in (-M)..M, (1 - |u| / M) / M = 1 := by
  have hcont : Continuous (fun u : ℝ => (1 - |u| / M) / M) :=
    (continuous_const.sub (continuous_abs.div_const M)).div_const M
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := -M) (b := 0) (c := M) (μ := volume)
    (hcont.intervalIntegrable (-M) 0) (hcont.intervalIntegrable 0 M)
  have h1 : ∫ u in (-M)..0, (1 - |u| / M) / M = 1 / 2 := by
    have hcongr : ∫ u in (-M)..0, (1 - |u| / M) / M =
        ∫ u in (-M)..0, ((1 / M) + (1 / (M * M)) * u) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith)] at hu
      rw [abs_of_nonpos hu.2]
      field_simp
      ring
    have hint1 : IntervalIntegrable (fun u : ℝ => (1 / (M * M)) * u) volume (-M) 0 :=
      (continuous_const.mul continuous_id).intervalIntegrable (-M) 0
    rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const hint1,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_id, smul_eq_mul]
    field_simp
    ring
  have h2 : ∫ u in (0 : ℝ)..M, (1 - |u| / M) / M = 1 / 2 := by
    have hcongr : ∫ u in (0 : ℝ)..M, (1 - |u| / M) / M =
        ∫ u in (0 : ℝ)..M, ((1 / M) - (1 / (M * M)) * u) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hM.le] at hu
      rw [abs_of_nonneg hu.1]
      field_simp
    have hint2 : IntervalIntegrable (fun u : ℝ => (1 / (M * M)) * u) volume 0 M :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 M
    rw [hcongr, intervalIntegral.integral_sub intervalIntegrable_const hint2,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_id, smul_eq_mul]
    field_simp
    ring
  linarith

lemma smoothed_race_intervalIntegrable (M A B : ℝ) (hM : 0 < M) :
    let E : ℝ → ℝ := fun y =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0
    IntervalIntegrable (fun y : ℝ =>
      max (∫ u in (-M)..M, ((1 - |u| / M) / M) * E (y - u)) 0) volume A B := by
  intro E
  let K : ℝ → ℝ := fun u => (1 - |u| / M) / M
  have hK_meas : Measurable K :=
    ((measurable_const.sub (continuous_abs.measurable.div_const M)).div_const M)
  have hjoint : Measurable (fun p : ℝ × ℝ => K p.2 * E (p.1 - p.2)) :=
    (hK_meas.comp measurable_snd).mul
      (measurable_raceE.comp (measurable_fst.sub measurable_snd))
  have hS_meas : Measurable (fun y : ℝ => ∫ u in (-M)..M, K u * E (y - u)) := by
    have hrew : (fun y : ℝ => ∫ u in (-M)..M, K u * E (y - u)) =
        (fun y : ℝ => ∫ u, K u * E (y - u) ∂(volume.restrict (Set.Ioc (-M) M))) := by
      ext y
      exact intervalIntegral.integral_of_le (by linarith)
    rw [hrew]
    exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨C, hC0, hC⟩ := raceE_bounded_on_Icc (min A B - M) (max A B + M)
  have hS_int : IntervalIntegrable (fun y : ℝ => ∫ u in (-M)..M, K u * E (y - u)) volume A B := by
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound measure_Ioc_lt_top hS_meas.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hyIcc : y ∈ Set.Icc (min A B) (max A B) :=
      Set.Ioc_subset_Icc_self (by simpa [Set.uIoc] using hy)
    rw [Real.norm_eq_abs, intervalIntegral.integral_of_le (by linarith)]
    calc
      |∫ u in Set.Ioc (-M) M, K u * E (y - u)|
          ≤ ∫ u in Set.Ioc (-M) M, |K u * E (y - u)| := by
            simpa [Real.norm_eq_abs] using
              MeasureTheory.norm_integral_le_integral_norm (fun u => K u * E (y - u))
      _ ≤ ∫ u in Set.Ioc (-M) M, K u * C := by
            refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun u hu => ?_
            · refine IntegrableOn.of_bound measure_Ioc_lt_top
                ((hK_meas.mul (measurable_raceE.comp (measurable_const.sub measurable_id))).abs.aestronglyMeasurable)
                ((1 / M) * C) ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
              have huK : 0 ≤ K u ∧ K u ≤ 1 / M := by
                have habs : |u| ≤ M := abs_le.mpr ⟨hu.1.le, hu.2⟩
                constructor
                · exact div_nonneg (sub_nonneg.mpr ((div_le_one hM).mpr habs)) hM.le
                · exact div_le_div_of_nonneg_right (by linarith [div_nonneg (abs_nonneg u) hM.le]) hM.le
              rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_nonneg huK.1]
              exact mul_le_mul huK.2 (hC (y - u) ⟨by linarith [hyIcc.1, hu.2], by linarith [hyIcc.2, hu.1]⟩)
                (abs_nonneg _) (by positivity)
            · exact (((continuous_const.sub (continuous_abs.div_const M)).div_const M).mul
                continuous_const).integrableOn_Ioc
            · have habs : |u| ≤ M := abs_le.mpr ⟨hu.1.le, hu.2⟩
              have hKnn : 0 ≤ K u := div_nonneg (sub_nonneg.mpr ((div_le_one hM).mpr habs)) hM.le
              rw [abs_mul, abs_of_nonneg hKnn]
              exact mul_le_mul_of_nonneg_left
                (hC (y - u) ⟨by linarith [hyIcc.1, hu.2], by linarith [hyIcc.2, hu.1]⟩) hKnn
      _ = (∫ u in (-M)..M, K u) * C := by
            rw [MeasureTheory.integral_mul_const, ← intervalIntegral.integral_of_le (by linarith)]
      _ = C := by rw [triangle_kernel_integral M hM, one_mul]
  have heq : (fun y : ℝ => max (∫ u in (-M)..M, K u * E (y - u)) 0) =
      (fun y : ℝ => ((∫ u in (-M)..M, K u * E (y - u)) +
        ‖∫ u in (-M)..M, K u * E (y - u)‖) / 2) := by
    funext y
    set x := ∫ u in (-M)..M, K u * E (y - u)
    rw [Real.norm_eq_abs]
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
  rw [heq]
  exact (hS_int.add hS_int.norm).div_const 2

lemma fubini_smoothed_pos_bound (M Y : ℝ) (hM : 0 < M) (hMY : M ≤ Y) :
    let E : ℝ → ℝ := fun y =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0
    ∫ y in M..Y, max (∫ u in (-M)..M, ((1 - |u| / M) / M) * E (y - u)) 0 ≤
      ∫ v in (0 : ℝ)..(Y + M), max (E v) 0 := by
  intro E
  let K : ℝ → ℝ := fun u => (1 - |u| / M) / M
  have hK_nn : ∀ u ∈ Set.Icc (-M) M, 0 ≤ K u := fun u hu =>
    div_nonneg (sub_nonneg.mpr ((div_le_one hM).mpr (abs_le.mpr hu))) hM.le
  have hK_le : ∀ u ∈ Set.Icc (-M) M, K u ≤ 1 / M := fun u hu =>
    div_le_div_of_nonneg_right (by linarith [div_nonneg (abs_nonneg u) hM.le]) hM.le
  have hK_meas : Measurable K :=
    ((measurable_const.sub (continuous_abs.measurable.div_const M)).div_const M)
  obtain ⟨C, hC0, hC⟩ := raceE_bounded_on_Icc 0 (Y + M)
  have hjoint_int : Integrable (fun p : ℝ × ℝ => K p.2 * max (E (p.1 - p.2)) 0)
      ((volume.restrict (Set.Ioc M Y)).prod (volume.restrict (Set.Ioc (-M) M))) := by
    have hmeas : Measurable (fun p : ℝ × ℝ => K p.2 * max (E (p.1 - p.2)) 0) :=
      (hK_meas.comp measurable_snd).mul
        ((measurable_raceE.comp (measurable_fst.sub measurable_snd)).max measurable_const)
    have : IsFiniteMeasure (volume.restrict (Set.Ioc M Y)) :=
      ⟨by simp [Real.volume_Ioc]⟩
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (-M) M)) :=
      ⟨by simp [Real.volume_Ioc]⟩
    refine Integrable.of_bound hmeas.aestronglyMeasurable ((1 / M) * C) ?_
    have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc M Y)).prod
        (volume.restrict (Set.Ioc (-M) M))), p.1 ∈ Set.Ioc M Y ∧ p.2 ∈ Set.Ioc (-M) M := by
      have h1 : ∀ᵐ y ∂(volume.restrict (Set.Ioc M Y)), y ∈ Set.Ioc M Y :=
        ae_restrict_mem measurableSet_Ioc
      have h2 : ∀ᵐ u ∂(volume.restrict (Set.Ioc (-M) M)), u ∈ Set.Ioc (-M) M :=
        ae_restrict_mem measurableSet_Ioc
      exact (Measure.ae_prod_iff_ae_ae
        ((measurableSet_Ioc.prod measurableSet_Ioc))).mpr
        (h1.mono fun y hy => h2.mono fun u hu => ⟨hy, hu⟩)
    refine hmem.mono fun p hp => ?_
    have huIcc : p.2 ∈ Set.Icc (-M) M := Set.Ioc_subset_Icc_self hp.2
    have hsub : p.1 - p.2 ∈ Set.Icc 0 (Y + M) :=
      ⟨by linarith [hp.1.1, hp.2.2], by linarith [hp.1.2, hp.2.1]⟩
    have hEp_le : max (E (p.1 - p.2)) 0 ≤ C :=
      max_le (le_trans (le_abs_self _) (hC _ hsub)) hC0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nn _ huIcc) (le_max_right _ _))]
    exact mul_le_mul (hK_le _ huIcc) hEp_le (le_max_right _ _) (by positivity)
  have hpt : ∀ y ∈ Set.Ioc M Y,
      max (∫ u in (-M)..M, K u * E (y - u)) 0 ≤
        ∫ u in Set.Ioc (-M) M, K u * max (E (y - u)) 0 := by
    intro y hy
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine max_le ?_ (MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun u hu =>
      mul_nonneg (hK_nn u (Set.Ioc_subset_Icc_self hu)) (le_max_right _ _))
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun u hu =>
      mul_le_mul_of_nonneg_left (le_max_left _ _) (hK_nn u (Set.Ioc_subset_Icc_self hu))
    · refine IntegrableOn.of_bound measure_Ioc_lt_top
        ((hK_meas.mul (measurable_raceE.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
        ((1 / M) * C) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have huIcc := Set.Ioc_subset_Icc_self hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn u huIcc)]
      exact mul_le_mul (hK_le u huIcc)
        (hC (y - u) ⟨by linarith [hy.1, hu.2], by linarith [hy.2, hu.1]⟩)
        (abs_nonneg _) (by positivity)
    · refine IntegrableOn.of_bound measure_Ioc_lt_top
        ((hK_meas.mul ((measurable_raceE.comp (measurable_const.sub measurable_id)).max
          measurable_const)).aestronglyMeasurable)
        ((1 / M) * C) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have huIcc := Set.Ioc_subset_Icc_self hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nn u huIcc) (le_max_right _ _))]
      exact mul_le_mul (hK_le u huIcc)
        (max_le (le_trans (le_abs_self _) (hC (y - u) ⟨by linarith [hy.1, hu.2], by linarith [hy.2, hu.1]⟩)) hC0)
        (le_max_right _ _) (by positivity)
  have h1 : ∫ y in M..Y, max (∫ u in (-M)..M, K u * E (y - u)) 0 ≤
      ∫ y in Set.Ioc M Y, ∫ u in Set.Ioc (-M) M, K u * max (E (y - u)) 0 := by
    rw [intervalIntegral.integral_of_le hMY]
    exact MeasureTheory.setIntegral_mono_on
      (smoothed_race_intervalIntegrable M M Y hM).1
      hjoint_int.integral_prod_left measurableSet_Ioc hpt
  have hswap : (∫ y in Set.Ioc M Y, ∫ u in Set.Ioc (-M) M, K u * max (E (y - u)) 0) =
      ∫ u in Set.Ioc (-M) M, ∫ y in Set.Ioc M Y, K u * max (E (y - u)) 0 :=
    MeasureTheory.integral_integral_swap hjoint_int
  have h2 : (∫ u in Set.Ioc (-M) M, ∫ y in Set.Ioc M Y, K u * max (E (y - u)) 0) ≤
      ∫ u in Set.Ioc (-M) M, K u * (∫ v in (0 : ℝ)..(Y + M), max (E v) 0) := by
    refine MeasureTheory.setIntegral_mono_on hjoint_int.integral_prod_right
      ((((continuous_const.sub (continuous_abs.div_const M)).div_const M).mul
        continuous_const).integrableOn_Ioc) measurableSet_Ioc fun u hu => ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hK_nn u (Set.Ioc_subset_Icc_self hu))
    rw [← intervalIntegral.integral_of_le hMY,
      intervalIntegral.integral_comp_sub_right (fun v => max (E v) 0) u]
    have h0le : 0 ≤ M - u := by linarith [hu.2]
    have hle1 : M - u ≤ Y - u := by linarith
    have hle2 : Y - u ≤ Y + M := by linarith [hu.1]
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (raceE_pos_intervalIntegrable 0 (M - u))
      (raceE_pos_intervalIntegrable (M - u) (Y - u))
    have hb := intervalIntegral.integral_add_adjacent_intervals
      (raceE_pos_intervalIntegrable 0 (Y - u))
      (raceE_pos_intervalIntegrable (Y - u) (Y + M))
    have hnn1 : 0 ≤ ∫ v in (0 : ℝ)..(M - u), max (E v) 0 :=
      intervalIntegral.integral_nonneg h0le fun _ _ => le_max_right _ _
    have hnn2 : 0 ≤ ∫ v in (Y - u)..(Y + M), max (E v) 0 :=
      intervalIntegral.integral_nonneg hle2 fun _ _ => le_max_right _ _
    linarith
  have h3 : (∫ u in Set.Ioc (-M) M, K u * (∫ v in (0 : ℝ)..(Y + M), max (E v) 0)) =
      ∫ v in (0 : ℝ)..(Y + M), max (E v) 0 := by
    rw [MeasureTheory.integral_mul_const, ← intervalIntegral.integral_of_le (by linarith),
      triangle_kernel_integral M hM, one_mul]
  linarith

/- ### Step 5: Compactness on the torus and Bohr positive lower density -/

lemma trig_poly_lipschitz {k : ℕ} (c₀ : ℝ) (a b ω : Fin k → ℝ) (y₁ y₂ : ℝ) :
    let P : ℝ → ℝ := fun y =>
      c₀ + ∑ i : Fin k, (a i * Real.cos (ω i * y) + b i * Real.sin (ω i * y))
    |P y₁ - P y₂| ≤ (∑ i : Fin k, (|a i| + |b i|) * |ω i| + 1) * |y₁ - y₂| := by
  intro P
  have hdiff : P y₁ - P y₂ =
      ∑ i : Fin k, (a i * (Real.cos (ω i * y₁) - Real.cos (ω i * y₂)) +
        b i * (Real.sin (ω i * y₁) - Real.sin (ω i * y₂))) := by
    dsimp [P]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hdiff]
  calc
    |∑ i : Fin k, (a i * (Real.cos (ω i * y₁) - Real.cos (ω i * y₂)) +
        b i * (Real.sin (ω i * y₁) - Real.sin (ω i * y₂)))|
        ≤ ∑ i : Fin k, |a i * (Real.cos (ω i * y₁) - Real.cos (ω i * y₂)) +
            b i * (Real.sin (ω i * y₁) - Real.sin (ω i * y₂))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin k, ((|a i| + |b i|) * |ω i|) * |y₁ - y₂| := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hcos : |Real.cos (ω i * y₁) - Real.cos (ω i * y₂)| ≤ |ω i| * |y₁ - y₂| := by
            simpa [← mul_sub, abs_mul] using Real.abs_cos_sub_cos_le (ω i * y₁) (ω i * y₂)
          have hsin : |Real.sin (ω i * y₁) - Real.sin (ω i * y₂)| ≤ |ω i| * |y₁ - y₂| := by
            simpa [← mul_sub, abs_mul] using Real.abs_sin_sub_sin_le (ω i * y₁) (ω i * y₂)
          have htri := abs_add_le
            (a i * (Real.cos (ω i * y₁) - Real.cos (ω i * y₂)))
            (b i * (Real.sin (ω i * y₁) - Real.sin (ω i * y₂)))
          rw [abs_mul, abs_mul] at htri
          nlinarith [abs_nonneg (a i), abs_nonneg (b i)]
    _ = (∑ i : Fin k, (|a i| + |b i|) * |ω i|) * |y₁ - y₂| := by rw [← Finset.sum_mul]
    _ ≤ (∑ i : Fin k, (|a i| + |b i|) * |ω i| + 1) * |y₁ - y₂| := by
          nlinarith [abs_nonneg (y₁ - y₂)]

lemma trig_poly_syndetic_recurrence {k : ℕ} (c₀ : ℝ) (a b ω : Fin k → ℝ)
    (y₀ η : ℝ) (hη : 0 < η) :
    let P : ℝ → ℝ := fun y =>
      c₀ + ∑ i : Fin k, (a i * Real.cos (ω i * y) + b i * Real.sin (ω i * y))
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ t : ℝ,
      ((n - N₀ : ℕ) : ℝ) ≤ t ∧ t ≤ (n : ℝ) ∧ |P (y₀ + t) - P y₀| ≤ η := by
  intro P
  let A : ℝ := ∑ i : Fin k, (|a i| + |b i|) + 1
  have hA : 0 < A := by
    have : 0 ≤ ∑ i : Fin k, (|a i| + |b i|) :=
      Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith
  let q : ℕ := Nat.ceil (2 * Real.pi * A / η) + 1
  have hq_pos : 0 < q := Nat.succ_pos _
  have hqR_pos : (0 : ℝ) < q := by positivity
  have hq_bound : 2 * Real.pi * A / (q : ℝ) ≤ η := by
    have h1 : 2 * Real.pi * A / η ≤ (q : ℝ) := by
      have := Nat.le_ceil (2 * Real.pi * A / η)
      dsimp [q]; push_cast; linarith
    have h2 : 2 * Real.pi * A ≤ (q : ℝ) * η := (div_le_iff₀ hη).mp h1
    rw [div_le_iff₀ hqR_pos]
    linarith
  let α : Fin k → ℝ := fun i => ω i / (2 * Real.pi)
  let box : ℕ → (Fin k → Fin q) := fun n i =>
    ⟨Nat.floor ((q : ℝ) * Int.fract (α i * (n : ℝ))), by
      have hfr := Int.fract_lt_one (α i * (n : ℝ))
      have hmul : (q : ℝ) * Int.fract (α i * (n : ℝ)) < (q : ℝ) := by nlinarith
      exact (Nat.floor_lt (mul_nonneg hqR_pos.le (Int.fract_nonneg _))).mpr hmul⟩
  let w : (Fin k → Fin q) → ℕ := fun b =>
    if h : ∃ m : ℕ, box m = b then h.choose else 0
  let N₀ : ℕ := Finset.univ.sup w
  refine ⟨N₀, fun n hn => ?_⟩
  have hex : ∃ m : ℕ, box m = box n := ⟨n, rfl⟩
  let m : ℕ := w (box n)
  have hm_le : m ≤ N₀ := Finset.le_sup (f := w) (Finset.mem_univ (box n))
  have hm_box : box m = box n := by
    dsimp [m, w]
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨(n : ℝ) - (m : ℝ), ?_, ?_, ?_⟩
  · have : n - N₀ ≤ n - m := Nat.sub_le_sub_left hm_le n
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub (le_trans hm_le hn)
    rw [← hcast]
    exact_mod_cast this
  · linarith [Nat.cast_nonneg (α := ℝ) m]
  · have hdiff : P (y₀ + ((n : ℝ) - (m : ℝ))) - P y₀ =
        ∑ i : Fin k, (a i * (Real.cos (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.cos (ω i * y₀)) +
          b i * (Real.sin (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.sin (ω i * y₀))) := by
      dsimp [P]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hdiff]
    have hcoord : ∀ i : Fin k,
        |Real.cos (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.cos (ω i * y₀)| ≤
          2 * Real.pi / (q : ℝ) ∧
        |Real.sin (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.sin (ω i * y₀)| ≤
          2 * Real.pi / (q : ℝ) := by
      intro i
      have hbi : (box m i).val = (box n i).val := congrArg (fun f => (f i).val) hm_box
      have hfl_eq : Nat.floor ((q : ℝ) * Int.fract (α i * (m : ℝ))) =
          Nat.floor ((q : ℝ) * Int.fract (α i * (n : ℝ))) := hbi
      set fn : ℝ := Int.fract (α i * (n : ℝ))
      set fm : ℝ := Int.fract (α i * (m : ℝ))
      have hfn1 : (Nat.floor ((q : ℝ) * fn) : ℝ) ≤ (q : ℝ) * fn :=
        Nat.floor_le (mul_nonneg hqR_pos.le (Int.fract_nonneg _))
      have hfn2 : (q : ℝ) * fn < (Nat.floor ((q : ℝ) * fn) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hfm1 : (Nat.floor ((q : ℝ) * fm) : ℝ) ≤ (q : ℝ) * fm :=
        Nat.floor_le (mul_nonneg hqR_pos.le (Int.fract_nonneg _))
      have hfm2 : (q : ℝ) * fm < (Nat.floor ((q : ℝ) * fm) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hq_diff : |(q : ℝ) * (fn - fm)| ≤ 1 := by
        rw [hfl_eq] at hfm1 hfm2
        rw [mul_sub, abs_le]
        constructor <;> linarith
      have hfr_diff : |fn - fm| ≤ 1 / (q : ℝ) := by
        rw [abs_mul, abs_of_pos hqR_pos] at hq_diff
        rw [le_div_iff₀ hqR_pos, mul_comm]; linarith
      let z : ℤ := ⌊α i * (n : ℝ)⌋ - ⌊α i * (m : ℝ)⌋
      have hdecomp : ω i * ((n : ℝ) - (m : ℝ)) =
          2 * Real.pi * (fn - fm) + (z : ℝ) * (2 * Real.pi) := by
        have hpi : 2 * Real.pi ≠ 0 := by positivity
        have hαn : α i * (n : ℝ) = (⌊α i * (n : ℝ)⌋ : ℝ) + fn := (Int.floor_add_fract _).symm
        have hαm : α i * (m : ℝ) = (⌊α i * (m : ℝ)⌋ : ℝ) + fm := (Int.floor_add_fract _).symm
        have hsub : α i * ((n : ℝ) - (m : ℝ)) = (fn - fm) + (z : ℝ) := by
          dsimp [z]; push_cast; linarith
        calc
          ω i * ((n : ℝ) - (m : ℝ)) = (2 * Real.pi) * (α i * ((n : ℝ) - (m : ℝ))) := by
            dsimp [α]; field_simp
          _ = 2 * Real.pi * (fn - fm) + (z : ℝ) * (2 * Real.pi) := by
            rw [hsub]; ring
      have harg : ω i * (y₀ + ((n : ℝ) - (m : ℝ))) =
          (ω i * y₀ + 2 * Real.pi * (fn - fm)) + (z : ℝ) * (2 * Real.pi) := by
        linarith
      constructor
      · rw [harg, Real.cos_add_int_mul_two_pi]
        calc
          |Real.cos (ω i * y₀ + 2 * Real.pi * (fn - fm)) - Real.cos (ω i * y₀)|
              ≤ |(ω i * y₀ + 2 * Real.pi * (fn - fm)) - ω i * y₀| :=
                Real.abs_cos_sub_cos_le _ _
          _ = 2 * Real.pi * |fn - fm| := by
                rw [add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]
          _ ≤ 2 * Real.pi * (1 / (q : ℝ)) :=
                mul_le_mul_of_nonneg_left hfr_diff (by positivity)
          _ = 2 * Real.pi / (q : ℝ) := by ring
      · rw [harg, Real.sin_add_int_mul_two_pi]
        calc
          |Real.sin (ω i * y₀ + 2 * Real.pi * (fn - fm)) - Real.sin (ω i * y₀)|
              ≤ |(ω i * y₀ + 2 * Real.pi * (fn - fm)) - ω i * y₀| :=
                Real.abs_sin_sub_sin_le _ _
          _ = 2 * Real.pi * |fn - fm| := by
                rw [add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]
          _ ≤ 2 * Real.pi * (1 / (q : ℝ)) :=
                mul_le_mul_of_nonneg_left hfr_diff (by positivity)
          _ = 2 * Real.pi / (q : ℝ) := by ring
    calc
      |∑ i : Fin k, (a i * (Real.cos (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.cos (ω i * y₀)) +
          b i * (Real.sin (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.sin (ω i * y₀)))|
          ≤ ∑ i : Fin k, |a i * (Real.cos (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.cos (ω i * y₀)) +
              b i * (Real.sin (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.sin (ω i * y₀))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin k, (|a i| + |b i|) * (2 * Real.pi / (q : ℝ)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have ⟨hc, hs⟩ := hcoord i
            have htri := abs_add_le
              (a i * (Real.cos (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.cos (ω i * y₀)))
              (b i * (Real.sin (ω i * (y₀ + ((n : ℝ) - (m : ℝ)))) - Real.sin (ω i * y₀)))
            rw [abs_mul, abs_mul] at htri
            nlinarith [abs_nonneg (a i), abs_nonneg (b i)]
      _ = (∑ i : Fin k, (|a i| + |b i|)) * (2 * Real.pi / (q : ℝ)) := by rw [← Finset.sum_mul]
      _ ≤ A * (2 * Real.pi / (q : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            dsimp [A]; linarith
      _ = 2 * Real.pi * A / (q : ℝ) := by ring
      _ ≤ η := hq_bound

lemma smoothed_lower_density_contradiction
    (M δ : ℝ) (hM : 0 < M) (hδ : 0 < δ)
    (hH2 : let E : ℝ → ℝ := fun y =>
        if 2 ≤ Real.exp y then
          (y / Real.exp (y / 2)) *
            (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
             (Nat.floor (Real.exp y)).primeCountingMod 4 3)
        else 0
      ∃ (k : ℕ) (c₀ : ℝ) (a b ω : Fin k → ℝ), ∀ᶠ y : ℝ in atTop,
        |(∫ u in (-M)..M, ((1 - |u| / M) / M) * E (y - u)) -
          (c₀ + ∑ i : Fin k, (a i * Real.cos (ω i * y) + b i * Real.sin (ω i * y)))| ≤ δ / 4)
    (hH3 : let E : ℝ → ℝ := fun y =>
        if 2 ≤ Real.exp y then
          (y / Real.exp (y / 2)) *
            (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
             (Nat.floor (Real.exp y)).primeCountingMod 4 3)
        else 0
      ∀ Y : ℝ, ∃ y : ℝ, Y ≤ y ∧ δ ≤ ∫ u in (-M)..M, ((1 - |u| / M) / M) * E (y - u))
    (hMean : let E : ℝ → ℝ := fun y =>
        if 2 ≤ Real.exp y then
          (y / Real.exp (y / 2)) *
            (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
             (Nat.floor (Real.exp y)).primeCountingMod 4 3)
        else 0
      Tendsto (fun Y : ℝ => (∫ y in (0 : ℝ)..Y, max (E y) 0) / Y) atTop (𝓝 0)) :
    False := by
  let E : ℝ → ℝ := fun y =>
    if 2 ≤ Real.exp y then
      (y / Real.exp (y / 2)) *
        (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
         (Nat.floor (Real.exp y)).primeCountingMod 4 3)
    else 0
  let S : ℝ → ℝ := fun y => ∫ u in (-M)..M, ((1 - |u| / M) / M) * E (y - u)
  obtain ⟨k, c₀, a, b, ω, happrox⟩ := hH2
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp happrox
  obtain ⟨y₀, hy₀_ge, hy₀_S⟩ := hH3 (max Y₀ M)
  have hy₀_Y₀ : Y₀ ≤ y₀ := le_trans (le_max_left _ _) hy₀_ge
  have hy₀_M : M ≤ y₀ := le_trans (le_max_right _ _) hy₀_ge
  let P : ℝ → ℝ := fun y =>
    c₀ + ∑ i : Fin k, (a i * Real.cos (ω i * y) + b i * Real.sin (ω i * y))
  have hPy₀ : 3 * δ / 4 ≤ P y₀ := by
    have h := (abs_le.mp (hY₀ y₀ hy₀_Y₀)).2
    change S y₀ - P y₀ ≤ δ / 4 at h
    change δ ≤ S y₀ at hy₀_S
    linarith
  obtain ⟨N₀, hN₀⟩ := trig_poly_syndetic_recurrence c₀ a b ω y₀ (δ / 8) (by positivity)
  let L : ℝ := ∑ i : Fin k, (|a i| + |b i|) * |ω i| + 1
  have hL_pos : 0 < L := by
    have : 0 ≤ ∑ i : Fin k, (|a i| + |b i|) * |ω i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
    linarith
  let r : ℝ := min (1 / 2) (δ / (8 * L))
  have hr_pos : 0 < r := lt_min (by norm_num) (by positivity)
  have hr_le1 : r ≤ 1 / 2 := min_le_left _ _
  have hr_le2 : r ≤ δ / (8 * L) := min_le_right _ _
  let R : ℝ := (N₀ : ℝ) + 1
  have hR_pos : 0 < R := by positivity
  have hblock : ∀ j : ℕ,
      (δ / 4) * r ≤ ∫ y in (y₀ + (j : ℝ) * R)..(y₀ + ((j + 1 : ℕ) : ℝ) * R), max (S y) 0 := by
    intro j
    let n : ℕ := N₀ + j * (N₀ + 1)
    obtain ⟨t, ht_lo, ht_hi, ht_P⟩ := hN₀ n (by omega)
    let y₁ : ℝ := y₀ + t
    have hlo : y₀ + (j : ℝ) * R ≤ y₁ := by
      have : n - N₀ = j * (N₀ + 1) := by dsimp [n]; omega
      rw [this] at ht_lo
      push_cast at ht_lo
      dsimp [y₁, R]
      linarith
    have hhi : y₁ + r ≤ y₀ + ((j + 1 : ℕ) : ℝ) * R := by
      have hnR : (n : ℝ) = (N₀ : ℝ) + (j : ℝ) * R := by dsimp [n, R]; push_cast; ring
      have hsucc : ((j + 1 : ℕ) : ℝ) * R = (j : ℝ) * R + R := by push_cast; ring
      dsimp [y₁, R] at *
      linarith
    have hy₁_ge : Y₀ ≤ y₁ := by
      have : (0 : ℝ) ≤ (j : ℝ) * R := by positivity
      linarith
    have hsub_ge : ∀ y ∈ Set.Icc y₁ (y₁ + r), δ / 4 ≤ max (S y) 0 := by
      intro y hy
      have hy_Y₀ : Y₀ ≤ y := le_trans hy₁_ge hy.1
      have hS_P : -(δ / 4) ≤ S y - P y := (abs_le.mp (hY₀ y hy_Y₀)).1
      have hP_lip : |P y - P y₁| ≤ δ / 8 := by
        have hlip := trig_poly_lipschitz c₀ a b ω y y₁
        have habs : |y - y₁| ≤ r := by rw [abs_of_nonneg (by linarith [hy.1])]; linarith [hy.2]
        have hLr : L * r ≤ δ / 8 := by
          have := (le_div_iff₀ (show 0 < 8 * L by positivity)).mp hr_le2
          linarith
        nlinarith [hlip]
      have hP_rec : |P y₁ - P y₀| ≤ δ / 8 := ht_P
      have hPy₁ : 5 * δ / 8 ≤ P y₁ := by linarith [(abs_le.mp hP_rec).1]
      have hPy : δ / 2 ≤ P y := by linarith [(abs_le.mp hP_lip).1]
      have hSy : δ / 4 ≤ S y := by linarith
      exact le_trans hSy (le_max_left _ _)
    have hint_sub : (δ / 4) * r ≤ ∫ y in y₁..(y₁ + r), max (S y) 0 := by
      have hmono := intervalIntegral.integral_mono_on (by linarith : y₁ ≤ y₁ + r)
        intervalIntegrable_const (smoothed_race_intervalIntegrable M y₁ (y₁ + r) hM) hsub_ge
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      linarith
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (smoothed_race_intervalIntegrable M (y₀ + (j : ℝ) * R) y₁ hM)
      (smoothed_race_intervalIntegrable M y₁ (y₁ + r) hM)
    have hb := intervalIntegral.integral_add_adjacent_intervals
      (smoothed_race_intervalIntegrable M (y₀ + (j : ℝ) * R) (y₁ + r) hM)
      (smoothed_race_intervalIntegrable M (y₁ + r) (y₀ + ((j + 1 : ℕ) : ℝ) * R) hM)
    have hnn1 : 0 ≤ ∫ y in (y₀ + (j : ℝ) * R)..y₁, max (S y) 0 :=
      intervalIntegral.integral_nonneg hlo fun _ _ => le_max_right _ _
    have hnn2 : 0 ≤ ∫ y in (y₁ + r)..(y₀ + ((j + 1 : ℕ) : ℝ) * R), max (S y) 0 :=
      intervalIntegral.integral_nonneg hhi fun _ _ => le_max_right _ _
    linarith
  have hsum_blocks : ∀ K : ℕ,
      (K : ℝ) * ((δ / 4) * r) ≤ ∫ y in M..(y₀ + (K : ℝ) * R), max (S y) 0 := by
    intro K
    have hK_int : (K : ℝ) * ((δ / 4) * r) ≤ ∫ y in y₀..(y₀ + (K : ℝ) * R), max (S y) 0 := by
      induction K with
      | zero => simp
      | succ m ih =>
        have hadj : (∫ y in y₀..(y₀ + (m : ℝ) * R), max (S y) 0) +
            (∫ y in (y₀ + (m : ℝ) * R)..(y₀ + ((m + 1 : ℕ) : ℝ) * R), max (S y) 0) =
            ∫ y in y₀..(y₀ + ((m + 1 : ℕ) : ℝ) * R), max (S y) 0 :=
          intervalIntegral.integral_add_adjacent_intervals
            (smoothed_race_intervalIntegrable M y₀ (y₀ + (m : ℝ) * R) hM)
            (smoothed_race_intervalIntegrable M (y₀ + (m : ℝ) * R) (y₀ + ((m + 1 : ℕ) : ℝ) * R) hM)
        have hbm := hblock m
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hadj hbm ⊢
        linarith
    have hadj0 : (∫ y in M..y₀, max (S y) 0) +
        (∫ y in y₀..(y₀ + (K : ℝ) * R), max (S y) 0) =
        ∫ y in M..(y₀ + (K : ℝ) * R), max (S y) 0 :=
      intervalIntegral.integral_add_adjacent_intervals
        (smoothed_race_intervalIntegrable M M y₀ hM)
        (smoothed_race_intervalIntegrable M y₀ (y₀ + (K : ℝ) * R) hM)
    have hnn0 : 0 ≤ ∫ y in M..y₀, max (S y) 0 :=
      intervalIntegral.integral_nonneg hy₀_M fun _ _ => le_max_right _ _
    linarith
  let Yseq : ℕ → ℝ := fun K => y₀ + (K : ℝ) * R
  have hYseq_top : Tendsto Yseq atTop atTop := by
    have h1 : Tendsto (fun K : ℕ => (K : ℝ) * R) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hR_pos tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun K : ℕ => (K : ℝ) * R + y₀) atTop atTop :=
      h1.atTop_add tendsto_const_nhds
    exact h2.congr fun K => add_comm _ _
  have hupper : Tendsto (fun K : ℕ => (∫ y in M..(Yseq K), max (S y) 0) / Yseq K) atTop (𝓝 0) := by
    have hshift : Tendsto (fun K : ℕ =>
        ((∫ v in (0 : ℝ)..(Yseq K + M), max (E v) 0) / (Yseq K + M)) *
          ((Yseq K + M) / Yseq K)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun K : ℕ =>
          (∫ v in (0 : ℝ)..(Yseq K + M), max (E v) 0) / (Yseq K + M)) atTop (𝓝 0) :=
        hMean.comp (hYseq_top.atTop_add tendsto_const_nhds)
      have h2 : Tendsto (fun K : ℕ => (Yseq K + M) / Yseq K) atTop (𝓝 1) := by
        have hinv : Tendsto (fun K : ℕ => M / Yseq K) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hYseq_top
        have hadd : Tendsto (fun K : ℕ => 1 + M / Yseq K) atTop (𝓝 1) := by
          simpa using hinv.const_add 1
        refine hadd.congr' ?_
        filter_upwards [hYseq_top.eventually (eventually_gt_atTop (0 : ℝ))] with K hK
        field_simp [hK.ne']
      simpa using h1.mul h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hshift ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with K _
      have hMY : M ≤ Yseq K := by dsimp [Yseq]; nlinarith
      have hYpos : 0 < Yseq K := lt_of_lt_of_le hM hMY
      exact div_nonneg (intervalIntegral.integral_nonneg hMY fun _ _ => le_max_right _ _) hYpos.le
    · filter_upwards [eventually_ge_atTop 1] with K _
      have hMY : M ≤ Yseq K := by dsimp [Yseq]; nlinarith
      have hYpos : 0 < Yseq K := lt_of_lt_of_le hM hMY
      have hYMpos : 0 < Yseq K + M := by linarith
      have hfub := fubini_smoothed_pos_bound M (Yseq K) hM hMY
      have hrw : (∫ v in (0 : ℝ)..(Yseq K + M), max (E v) 0) / (Yseq K + M) *
          ((Yseq K + M) / Yseq K) =
          (∫ v in (0 : ℝ)..(Yseq K + M), max (E v) 0) / Yseq K := by
        field_simp [hYpos.ne', hYMpos.ne']
      rw [hrw]
      exact div_le_div_of_nonneg_right hfub hYpos.le
  have hlower : Tendsto (fun K : ℕ => ((K : ℝ) * ((δ / 4) * r)) / Yseq K) atTop
      (𝓝 (((δ / 4) * r) / R)) := by
    have hdenom : Tendsto (fun K : ℕ => y₀ / (K : ℝ) + R) atTop (𝓝 R) := by
      simpa using
        ((tendsto_const_nhds (x := y₀)).div_atTop tendsto_natCast_atTop_atTop).add
          (tendsto_const_nhds (x := R))
    have hquot : Tendsto (fun K : ℕ => ((δ / 4) * r) / (y₀ / (K : ℝ) + R)) atTop
        (𝓝 (((δ / 4) * r) / R)) :=
      tendsto_const_nhds.div hdenom hR_pos.ne'
    refine hquot.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : (0 : ℝ) < K := by positivity
    dsimp [Yseq]
    field_simp [hKpos.ne']
  have hle_lim : ((δ / 4) * r) / R ≤ 0 := by
    refine le_of_tendsto_of_tendsto' hlower hupper fun K => ?_
    have hYpos : 0 < Yseq K := lt_of_lt_of_le hM (by dsimp [Yseq]; nlinarith)
    exact div_le_div_of_nonneg_right (hsum_blocks K) hYpos.le
  have hpos_lim : 0 < ((δ / 4) * r) / R := by positivity
  linarith

/- ### Hypotheses and main reduction theorem -/

/-- Under GRH for $L(s, \chi_4)$, the normalized prime race has bounded logarithmic second moment
(Rubinstein–Sarnak 1994, Lemma 2.1). -/
def H1 : Prop :=
  (∀ s : ℂ, 0 < s.re → s.re < 1 →
      DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) s = 0 →
      s.re = 1 / 2) →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
        (((Real.log j / Real.sqrt j) *
          ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2) ≤
      B * Real.log N

/-- Under GRH for $L(s, \chi_4)$, convolving the normalized prime race in logarithmic variable
with the compactly supported triangle kernel yields a uniformly Bohr almost-periodic function. -/
def H2 : Prop :=
  (∀ s : ℂ, 0 < s.re → s.re < 1 →
      DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) s = 0 →
      s.re = 1 / 2) →
    let E : ℝ → ℝ := fun y =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0
    ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε →
      ∃ (k : ℕ) (c₀ : ℝ) (a b ω : Fin k → ℝ), ∀ᶠ y : ℝ in Filter.atTop,
        |(∫ u in (-M)..M, ((1 - |u| / M) / M) * E (y - u)) -
          (c₀ + ∑ i : Fin k, (a i * Real.cos (ω i * y) + b i * Real.sin (ω i * y)))| ≤ ε

/-- Under GRH for $L(s, \chi_4)$, there exist a smoothing width $M > 0$ and threshold $\delta > 0$
such that the triangle-smoothed prime race reaches at least $\delta$ at arbitrarily large $y$. -/
def H3 : Prop :=
  (∀ s : ℂ, 0 < s.re → s.re < 1 →
      DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) s = 0 →
      s.re = 1 / 2) →
    let E : ℝ → ℝ := fun y =>
      if 2 ≤ Real.exp y then
        (y / Real.exp (y / 2)) *
          (((Nat.floor (Real.exp y)).primeCountingMod 4 1 : ℝ) -
           (Nat.floor (Real.exp y)).primeCountingMod 4 3)
      else 0
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℝ, ∃ y : ℝ, Y ≤ y ∧
      δ ≤ ∫ u in (-M)..M, ((1 - |u| / M) / M) * E (y - u)

theorem main : H1 → H2 → H3 → type_of% @ChebyshevBias.knapowski_turan_natural_density_false := by
  intro h1 h2 h3 hGRH hDens
  obtain ⟨M, hM, δ, hδ, hEx⟩ := h3 hGRH
  have hApprox := h2 hGRH M hM (δ / 4) (by positivity)
  have hMean := continuous_pos_mean_tendsto_zero hDens (h1 hGRH)
  exact smoothed_lower_density_contradiction M δ hM hδ hApprox hEx hMean

end OMA.R_ChebyshevBias_knapowski_turan_natural_density_false_R1
