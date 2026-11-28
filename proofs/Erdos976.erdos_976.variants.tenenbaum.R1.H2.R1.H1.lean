import OMAReductions.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1
import Mathlib

/-!
A divisor of a product splits into a divisor of each factor. Holding the second
factor fixed rescales the same multiplicative interval. For the moment bound,
the unit intervals from a maximizing cluster lie in an interval of length two.
Their summed indicators have integral equal to the cluster size. Jensen's
inequality gives the required lower bound for the integral of the power.
-/

namespace OMA.DivisorClusterMoment

open MeasureTheory Filter Real
open scoped ENNReal Classical

private noncomputable def cluster (b : ℕ) (u : ℝ) : Finset ℕ :=
  b.divisors.filter (fun d : ℕ => u < d ∧ (d : ℝ) ≤ exp 1 * u)

private noncomputable def concentration (b : ℕ) : ℕ :=
  sSup (Set.range (fun u : ℝ => (cluster b u).card))

private theorem bounded (b : ℕ) : BddAbove (Set.range fun u : ℝ => (cluster b u).card) :=
  ⟨b.divisors.card, by rintro _ ⟨u, rfl⟩; exact Finset.card_filter_le _ _⟩

private theorem cluster_le (b : ℕ) (u : ℝ) : (cluster b u).card ≤ concentration b :=
  le_csSup (bounded b) (Set.mem_range_self u)

private theorem concentrationProduct (a b : ℕ) :
    concentration (a*b) ≤ concentration a * b.divisors.card := by
  by_cases hab : a*b = 0
  · rw [hab]
    simp [concentration, cluster]
  have ha : a ≠ 0 := by intro h; simp [h] at hab
  have hb : b ≠ 0 := by intro h; simp [h] at hab
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  let G (e : ℕ) := (cluster a (u / e)).image (fun d => d * e)
  have hsub : cluster (a*b) u ⊆ b.divisors.biUnion G := by
    intro d hd
    obtain ⟨hdiv, hleft, hright⟩ := Finset.mem_filter.mp hd
    obtain ⟨c, e, hc, he, rfl⟩ := Nat.dvd_mul.mp (Nat.dvd_of_mem_divisors hdiv)
    have he' : e ∈ b.divisors := Nat.mem_divisors.mpr ⟨he, hb⟩
    have hepos : (0 : ℝ) < e := by exact_mod_cast (Nat.pos_of_mem_divisors he')
    refine Finset.mem_biUnion.mpr ⟨e, he', Finset.mem_image.mpr ⟨c, ?_, rfl⟩⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hc, ha⟩, ?_, ?_⟩
    · exact (div_lt_iff₀ hepos).mpr (by exact_mod_cast hleft)
    · rw [show exp 1 * (u / ↑e) = exp 1 * u / ↑e by ring]
      exact (le_div_iff₀ hepos).mpr (by exact_mod_cast hright)
  calc
    _ ≤ (b.divisors.biUnion G).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ b.divisors, (G e).card := Finset.card_biUnion_le
    _ ≤ b.divisors.card • concentration a := by
      apply Finset.sum_le_card_nsmul
      intro e he
      exact Finset.card_image_le.trans (cluster_le a (u/e))
    _ = _ := by simpa only [nsmul_eq_mul, Nat.cast_id] using mul_comm b.divisors.card (concentration a)

private noncomputable def indicatorAt (d : ℕ) : ℝ → ℝ :=
  (Set.Ico (log d - 1) (log d)).indicator (fun _ => 1)

private noncomputable def mass (D : Finset ℕ) (t : ℝ) : ℝ := ∑ d ∈ D, indicatorAt d t

private theorem indicatorAt_bounds (d : ℕ) (t : ℝ) : 0 ≤ indicatorAt d t ∧ indicatorAt d t ≤ 1 := by
  by_cases h : t ∈ Set.Ico (log (d : ℝ) - 1) (log (d : ℝ)) <;> simp [indicatorAt, h]

private theorem mass_bounds (D : Finset ℕ) (t : ℝ) : 0 ≤ mass D t ∧ mass D t ≤ D.card := by
  constructor
  · exact Finset.sum_nonneg fun d _ => (indicatorAt_bounds d t).1
  · calc
      _ ≤ ∑ _ ∈ D, (1 : ℝ) := Finset.sum_le_sum fun d _ => (indicatorAt_bounds d t).2
      _ = _ := by simp

private theorem mass_measurable (D : Finset ℕ) : Measurable (mass D) := by
  apply Finset.measurable_sum D
  intro d hd
  exact measurable_const.indicator measurableSet_Ico

private theorem mass_integrable (D : Finset ℕ) : Integrable (mass D) := by
  apply integrable_finsetSum D
  intro d hd
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact integrableOn_const (measure_Ico_lt_top.ne)

private theorem mass_pow_integrable (D : Finset ℕ) (q : ℕ) :
    Integrable (fun t => mass D t ^ (q+1)) := by
  refine ((mass_integrable D).mul_const ((D.card : ℝ) ^ q)).mono' ?_ ?_
  · exact ((mass_measurable D).pow_const _).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    obtain ⟨hn, hb⟩ := mass_bounds D t
    rw [Real.norm_of_nonneg (pow_nonneg hn _), pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hb q) hn

private theorem momentBound (b q : ℕ) :
    (concentration b : ℝ) ^ (q+1) ≤ (2 : ℝ)^q * (∫ t : ℝ, mass b.divisors t ^ (q+1)) := by
  obtain ⟨u, hu⟩ := Nat.sSup_mem (Set.range_nonempty (fun u : ℝ => (cluster b u).card)) (bounded b)
  change (cluster b u).card = concentration b at hu
  rw [← hu]
  by_cases hu0 : 0 < u
  swap
  · have hempty : cluster b u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨hdiv, _, hr⟩ := Finset.mem_filter.mp hd
      have hpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_mem_divisors hdiv)
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (exp_pos 1).le (le_of_not_gt hu0)))
        (hpos.trans_le hr)
    simp only [hempty, Finset.card_empty, Nat.cast_zero, zero_pow (Nat.succ_ne_zero q)]
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun t => pow_nonneg (mass_bounds _ t).1 _
  let C := cluster b u
  let J := Set.Icc (log u - 1) (log u + 1)
  have Jvolume : volume J = 2 := by
    change volume (Set.Icc (log u - 1) (log u + 1)) = 2
    rw [Real.volume_Icc, show log u + 1 - (log u - 1) = 2 by ring]
    norm_num
  have Jreal : volume.real J = 2 := by simp [measureReal_def, Jvolume]
  have contains (d : ℕ) (hd : d ∈ C) : Set.Ico (log (d : ℝ) - 1) (log (d : ℝ)) ⊆ J := by
    obtain ⟨hdiv, hl, hr⟩ := Finset.mem_filter.mp hd
    have hpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_mem_divisors hdiv)
    have hlow := Real.log_lt_log hu0 hl
    have hup := Real.log_le_log hpos hr
    rw [Real.log_mul (exp_pos 1).ne' hu0.ne', Real.log_exp] at hup
    intro t ht
    change log u - 1 ≤ t ∧ t ≤ log u + 1
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have harea : (∫ t in J, mass C t) = C.card := by
    change (∫ t in J, ∑ d ∈ C, indicatorAt d t) = _
    rw [integral_finsetSum C]
    · calc
        _ = ∑ _ ∈ C, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [indicatorAt, setIntegral_indicator measurableSet_Ico,
            Set.inter_eq_right.mpr (contains d hd), setIntegral_const, smul_eq_mul, mul_one,
            measureReal_def, Real.volume_Ico, show log (d : ℝ) - (log (d : ℝ) - 1) = 1 by ring]
          norm_num
        _ = _ := by simp
    · intro d hd
      apply Integrable.integrableOn
      apply IntegrableOn.integrable_indicator _ measurableSet_Ico
      exact integrableOn_const (measure_Ico_lt_top.ne)
  have hmean := (convexOn_pow (q+1) : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t^(q+1))).map_set_average_le
    (t := J) (μ := volume) (continuous_pow _).continuousOn isClosed_Ici (by simp [Jvolume]) (by simp [Jvolume])
    (Eventually.of_forall fun t => (mass_bounds C t).1)
    (mass_integrable C).integrableOn (mass_pow_integrable C q).integrableOn
  simp only [setAverage_eq, Jreal, smul_eq_mul, harea] at hmean
  have hcompare : (∫ t in J, mass C t ^ (q+1)) ≤ ∫ t : ℝ, mass b.divisors t ^ (q+1) := by
    calc
      _ ≤ ∫ t in J, mass b.divisors t ^ (q+1) := by
        apply integral_mono (mass_pow_integrable C q).integrableOn (mass_pow_integrable _ q).integrableOn
        intro t
        apply pow_le_pow_left₀ (mass_bounds C t).1
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ =>
          (indicatorAt_bounds d t).1
      _ ≤ _ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun t => pow_nonneg (mass_bounds _ t).1 _) (mass_pow_integrable _ q)
  change (C.card : ℝ) ^ (q+1) ≤ _
  calc
    _ = (2 : ℝ)^(q+1) * ((2 : ℝ)⁻¹ * C.card)^(q+1) := by rw [← mul_pow]; ring_nf
    _ ≤ (2 : ℝ)^(q+1) * ((2 : ℝ)⁻¹ * (∫ t in J, mass C t^(q+1))) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = (2 : ℝ)^q * (∫ t in J, mass C t^(q+1)) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcompare (by positivity)

end OMA.DivisorClusterMoment

open OMA.DivisorClusterMoment

theorem OMA.solution : OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1.H1 :=
  ⟨concentrationProduct, momentBound⟩
