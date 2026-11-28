import FormalConjectures.ErdosProblems.«448»
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
For each continuity point, the natural density equals the residue of the
Dirichlet series of its sublevel set. A dyadic covering transfers lower-tail
bounds for log-divisor interval lengths to those residues.
-/

-- Reduction Erdos448.erdos_448.variants.hall_tenenbaum_upper_bound.R1 of Erdős Problem 448 — hall tenenbaum upper bound
-- Credit: @yuka30240
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos448_erdos_448_variants_hall_tenenbaum_upper_bound_R1

open Erdos448 Filter MeasureTheory Asymptotics
open scoped Topology

/-- The qualitative distribution theorem, restricted to its continuity points. -/
def H1 : Prop :=
  ∃ F : ℝ → ℝ, Monotone F ∧ ∀ z : ℝ, ContinuousAt F z →
    {n : ℕ | (tauPlus n : ℝ) / n.divisors.card ≤ z}.HasDensity (F z)

/-- A lower Dirichlet density estimate for small logarithmic interval unions.
For each fixed threshold, the estimate only needs to hold along some exponents
approaching one from above. The series runs over the positive integers. -/
def H2 : Prop :=
  let L (n : ℕ) := volume.real
    (⋃ d ∈ n.divisors, Set.Icc (Real.log d) (Real.log d + Real.log 2))
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → u < 1 →
    ∃ᶠ s : ℝ in 𝓝[>] 1, (s - 1) *
      (∑' n : ℕ, if L n ≤ u * n.divisors.card then 1 / (n : ℝ) ^ s else 0)
        ≤ C * (u * Real.log (2 / u))

/-- The distribution variant of problem 448 supplies the qualitative step. -/
theorem of_distribution
    (h : type_of% @Erdos448.erdos_448.variants.hall_tenenbaum_distribution) : H1 := by
  obtain ⟨F, hF, _, _, hlim⟩ := h
  exact ⟨F, hF, hlim⟩

/-- Each occupied block covers all its log-divisor intervals by one interval
of length twice log 2. This also handles divisors at a block endpoint. -/
theorem log_union_le (n : ℕ) :
    volume.real (⋃ d ∈ n.divisors, Set.Icc (Real.log d) (Real.log d + Real.log 2))
      ≤ 2 * (tauPlus n : ℝ) := by
  let bins := n.divisors.image (Nat.log 2)
  let cover (k : ℕ) := Set.Icc ((k : ℝ) * Real.log 2) ((k + 2 : ℝ) * Real.log 2)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsub : (⋃ d ∈ n.divisors, Set.Icc (Real.log d) (Real.log d + Real.log 2))
      ⊆ ⋃ k ∈ bins, cover k := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Icc] at hx
    obtain ⟨d, hd, hdx, hxd⟩ := hx
    have hd0 := Nat.pos_of_mem_divisors hd
    let k := Nat.log 2 d
    have hlo : (2 : ℝ) ^ k ≤ (d : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hd0.ne'
    have hhi : (d : ℝ) < 2^(k + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) d
    have hlo' := Real.log_le_log (by positivity) hlo
    have hhi' := Real.log_lt_log (by exact_mod_cast hd0) hhi
    rw [Real.log_pow] at hlo' hhi'
    push_cast at hhi'
    exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_image_of_mem _ hd,
      hlo'.trans hdx, by linarith⟩
  have hfin : volume (⋃ k ∈ bins, cover k) ≠ ⊤ := by
    exact (bins.finite_toSet.isCompact_biUnion fun k _ => isCompact_Icc).measure_lt_top.ne
  calc
    _ ≤ volume.real (⋃ k ∈ bins, cover k) := measureReal_mono hsub hfin
    _ ≤ ∑ k ∈ bins, volume.real (cover k) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ bins, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [Real.volume_real_Icc_of_le (by nlinarith : (k : ℝ) * Real.log 2 ≤ (k + 2 : ℝ) * Real.log 2)]
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
    _ = _ := by simp [bins, tauPlus, mul_comm]

open scoped Classical in
private theorem density_dirichlet (A : Set ℕ) {d : ℝ} (hA : A.HasDensity d) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' n : ℕ,
      if n ∈ A then 1 / (n : ℝ) ^ s else 0) (𝓝[>] 1) (𝓝 d) := by
  classical
  let f (n : ℕ) : ℝ := if n ∈ A then 1 else 0
  have count (N : ℕ) :
      ∑ k ∈ Finset.Icc 1 N, f k = ((A ∩ Set.Iio (N + 1)).ncard : ℝ) - f 0 := by
    have hset : A ∩ Set.Iio (N + 1) = ↑((Finset.range (N + 1)).filter (· ∈ A)) := by
      ext; simp [and_comm]
    have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext i; simp; omega
    rw [hset, Set.ncard_coe_finset, Finset.card_filter, hsplit,
      Finset.sum_insert (by simp)]
    push_cast
    simp [f]
  have hsucc : Tendsto (fun n : ℕ => ((A ∩ Set.Iio (n + 1)).ncard : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 d) := by
    simpa [Set.partialDensity] using
      ((tendsto_add_atTop_iff_nat 1).2 (show Tendsto _ _ _ from hA))
  have hratio := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, f k) / n) atTop (𝓝 d) := by
    have h := (hsucc.mul hratio).sub (tendsto_const_div_atTop_nhds_zero_nat (f 0))
    rw [inv_one, mul_one, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [count]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
  have hres := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg f hlim
    (fun n => by simp [f]; positivity)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hres
  refine hreal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < s := hs
  have heq : LSeries (fun n => (f n : ℂ)) (s : ℂ) =
      ((∑' n : ℕ, if n ∈ A then 1 / (n : ℝ) ^ s else 0 : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term, Real.zero_rpow (by linarith : s ≠ 0)]
    · by_cases ha : n ∈ A <;> simp [LSeries.term, hn, f, ha,
          Complex.ofReal_cpow (Nat.cast_nonneg n)]
  dsimp only [Function.comp_apply]
  rw [heq]
  simp

private theorem upper_bounds (A B : Set ℕ) {d : ℝ} (hsub : A ⊆ B) (hB : B.HasDensity d) :
    0 ≤ A.upperDensity ∧ A.upperDensity ≤ d := by
  have hpos : ∀ n : ℕ, 0 ≤ A.partialDensity Set.univ n := fun _ => by positivity
  have hbound := Filter.isBoundedUnder_of (f := atTop) ⟨(1 : ℝ), Set.partialDensity_le_one A Set.univ⟩
  refine ⟨le_limsup_of_le hbound (fun _ h => ?_), ?_⟩
  · obtain ⟨n, hn⟩ := h.exists
    exact (hpos n).trans hn
  · have hmono : ∀ n : ℕ, A.partialDensity Set.univ n ≤ B.partialDensity Set.univ n := by
      intro n
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _ hsub))
    exact (limsup_le_limsup (Eventually.of_forall hmono)
      (isCoboundedUnder_le_of_eventually_le _ (Eventually.of_forall hpos))
      (show Tendsto _ _ _ from hB).isBoundedUnder_le).trans_eq (show Tendsto _ _ _ from hB).limsup_eq

theorem main : H1 → H2 → type_of% @Erdos448.erdos_448.variants.hall_tenenbaum_upper_bound := by
  classical
  rintro ⟨F, hF, hdist⟩ ⟨C, hC, hmass⟩
  refine isBigO_iff.mpr ⟨4 * C, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  obtain ⟨z, hzcont, hz⟩ := (hF.countable_not_continuousAt.dense_compl ℝ).exists_between
    (show ε < 2 * ε by linarith)
  have hz0 : 0 < z := hε0.trans hz.1
  have hD := hdist z (by simpa using hzcont)
  let A := {n : ℕ | (tauPlus n : ℝ) < ε * n.divisors.card}
  let B := {n : ℕ | (tauPlus n : ℝ) / n.divisors.card ≤ z}
  let L (n : ℕ) := volume.real (⋃ d ∈ n.divisors, Set.Icc (Real.log d) (Real.log d + Real.log 2))
  let U := {n : ℕ | L n ≤ (4 * ε) * n.divisors.card}
  have hAB : A ⊆ B := by
    intro n hn
    change (tauPlus n : ℝ) < ε * n.divisors.card at hn
    by_cases h : n.divisors.card = 0
    · simp [B, h, hz0.le]
    · exact ((div_lt_iff₀ (by positivity : (0 : ℝ) < n.divisors.card)).mpr hn).le.trans hz.1.le
  have hBU : B ⊆ U := by
    intro n hn
    change (tauPlus n : ℝ) / n.divisors.card ≤ z at hn
    by_cases h : n.divisors.card = 0
    · have ht := tauPlus_le_tau n
      rw [h] at ht
      simpa [U, L, h, Nat.eq_zero_of_le_zero ht] using log_union_le n
    · have hτ : 0 < (n.divisors.card : ℝ) := by positivity
      have h1 := (div_le_iff₀ hτ).mp hn
      exact (log_union_le n).trans (by nlinarith [mul_le_mul_of_nonneg_right hz.2.le hτ.le])
  have hdir := density_dirichlet B hD
  have hsmall := hmass (4 * ε) (by linarith) (by linarith)
  have hFbound : F z ≤ C * ((4 * ε) * Real.log (2 / (4 * ε))) := by
    apply le_of_tendsto_of_frequently hdir
    apply (hsmall.and_eventually (self_mem_nhdsWithin : Set.Ioi 1 ∈ 𝓝[>] (1 : ℝ))).mono
    rintro s ⟨hs, hs1⟩
    have hp (S : Set ℕ) : Summable (fun n : ℕ => if n ∈ S then 1 / (n : ℝ) ^ s else 0) := by
      apply (Real.summable_one_div_nat_rpow.mpr hs1).of_nonneg_of_le
      · intro n; split_ifs <;> positivity
      · intro n; split_ifs <;> first | rfl | positivity
    refine le_trans (mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (g := fun n : ℕ =>
      if n ∈ U then 1 / (n : ℝ) ^ s else 0) ?_ (hp B) (hp U)) (sub_nonneg.mpr hs1.le)) hs
    intro n
    by_cases hn : n ∈ B
    · simp [hn, hBU hn]
    · simp only [if_neg hn]; split_ifs <;> positivity
  have hlog : 0 ≤ Real.log (2 / ε) := Real.log_nonneg ((le_div_iff₀ hε0).mpr (by linarith))
  have hlog' : Real.log (2 / (4 * ε)) ≤ Real.log (2 / ε) := by
    apply Real.log_le_log (by positivity)
    gcongr
    linarith
  obtain ⟨hA0, hAF⟩ := upper_bounds A B hAB hD
  change ‖A.upperDensity‖ ≤ 4 * C * ‖ε * Real.log (2 / ε)‖
  rw [Real.norm_of_nonneg hA0, Real.norm_of_nonneg (mul_nonneg hε0.le hlog)]
  calc
    _ ≤ C * ((4 * ε) * Real.log (2 / (4 * ε))) := hAF.trans hFbound
    _ ≤ C * ((4 * ε) * Real.log (2 / ε)) := by gcongr
    _ = _ := by ring

end OMA.R_Erdos448_erdos_448_variants_hall_tenenbaum_upper_bound_R1
