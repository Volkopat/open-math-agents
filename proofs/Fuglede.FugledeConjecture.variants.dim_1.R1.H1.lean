import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.FieldTheory.Finite.Basic

/-!
# Proof of `Fuglede.FugledeConjecture.variants.dim_1.R1.H1`

Self-contained proof of Lagarias-Wang (1996) and Kolountzakis-Lagarias (1996):
every bounded measurable unit-measure translational tile of `ℝ` admits a periodic
rational fiber decomposition over `[0, 1/k)` with fibers tiling `ZMod L` against
a common complement `A`.
-/

namespace FugledeR1H1

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate FourierTransform ENNReal NNReal
open OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1

/- ## Section 1: 1D Tiling Geometry, Autocorrelation, Separation, and Jensen Zero Growth -/

def TilesR (S T : Set ℝ) : Prop :=
  T.Countable ∧
  volume (Set.univ \ ⋃ t ∈ T, {x : ℝ | x - t ∈ S}) = 0 ∧
  ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ →
    volume ({x : ℝ | x - t₁ ∈ S} ∩ {x : ℝ | x - t₂ ∈ S}) = 0

lemma proj1_equiv_eq (Ω : Set (Fin 1 → ℝ)) :
    Ω = {x : Fin 1 → ℝ | x 0 ∈ (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' Ω} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have hx : (fun _ : Fin 1 => x 0) = x := by ext i; fin_cases i; rfl
  rw [hx]

lemma tilesByTranslation_to_tilesR {Ω : Set (Fin 1 → ℝ)}
    (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_meas : MeasurableSet Ω)
    (hΩ_vol : volume Ω = 1) (htile : tilesByTranslation Ω) :
    let S : Set ℝ := (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' Ω
    Bornology.IsBounded S ∧ MeasurableSet S ∧ volume S = 1 ∧ ∃ T : Set ℝ, TilesR S T := by
  intro S
  have hΩ_eq : Ω = {x : Fin 1 → ℝ | x 0 ∈ S} := proj1_equiv_eq Ω
  have hS_bdd : Bornology.IsBounded S := by
    obtain ⟨R, hR⟩ := hΩ_bdd.subset_closedBall (0 : Fin 1 → ℝ)
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)]
    refine ⟨R, fun t ht => ?_⟩
    have h1 := hR ht
    rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
    have hle : ‖t‖ ≤ ‖(fun _ : Fin 1 => t)‖ := by
      simp
    exact le_trans hle h1
  have hS_meas : MeasurableSet S := hΩ_meas.preimage (measurable_pi_lambda _ fun _ => measurable_id)
  have hS_vol : volume S = 1 := by
    rw [← volume_preimage_apply0 S, ← hΩ_eq, hΩ_vol]
  rcases htile with ⟨T0, hT0_cnt, hT0_cov, hT0_disj⟩
  let T : Set ℝ := (fun v : Fin 1 → ℝ => v 0) '' T0
  refine ⟨hS_bdd, hS_meas, hS_vol, T, hT0_cnt.image _, ?_, ?_⟩
  · have hset : Set.univ \ (⋃ t ∈ T, {x : ℝ | x - t ∈ S}) =
        (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' (Set.univ \ ⋃ v ∈ T0, translateSet Ω v) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_iUnion, Set.mem_ofPred_eq,
        Set.mem_preimage, translateSet, S, T]
      constructor
      · intro h ⟨v, hv, hvx⟩
        apply h
        refine ⟨v 0, ⟨v, hv, rfl⟩, ?_⟩
        have heq : (fun _ : Fin 1 => x - v 0) = (fun _ : Fin 1 => x) - v := by
          ext i; fin_cases i; simp
        rwa [heq]
      · intro h ⟨t, ⟨v, hv, hvt⟩, htv⟩
        subst hvt
        apply h
        refine ⟨v, hv, ?_⟩
        have heq : (fun _ : Fin 1 => x) - v = (fun _ : Fin 1 => x - v 0) := by
          ext i; fin_cases i; simp
        rwa [heq]
    have hpre_eq : {x : Fin 1 → ℝ | x 0 ∈ Set.univ \ ⋃ t ∈ T, {y : ℝ | y - t ∈ S}} =
        Set.univ \ ⋃ v ∈ T0, translateSet Ω v := by
      rw [hset]
      exact (proj1_equiv_eq _).symm
    rw [← volume_preimage_apply0, hpre_eq, hT0_cov]
  · intro t₁ ht₁ t₂ ht₂ hne
    rcases ht₁ with ⟨v₁, hv₁, rfl⟩
    rcases ht₂ with ⟨v₂, hv₂, rfl⟩
    have hvne : v₁ ≠ v₂ := fun h => hne (congrArg (fun v : Fin 1 → ℝ => v 0) h)
    have hpre_eq : {x : Fin 1 → ℝ | x 0 ∈ ({y : ℝ | y - v₁ 0 ∈ S} ∩ {y : ℝ | y - v₂ 0 ∈ S})} =
        translateSet Ω v₁ ∩ translateSet Ω v₂ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, translateSet, S]
      have h1 : (fun _ : Fin 1 => x 0 - v₁ 0) = x - v₁ := by ext i; fin_cases i; simp
      have h2 : (fun _ : Fin 1 => x 0 - v₂ 0) = x - v₂ := by ext i; fin_cases i; simp
      rw [h1, h2]
    rw [← volume_preimage_apply0, hpre_eq]
    exact hT0_disj hv₁ hv₂ hvne

noncomputable def indS (S : Set ℝ) (x : ℝ) : ℝ :=
  S.indicator (fun _ => (1 : ℝ)) x

lemma integrable_indS {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    Integrable (indS S) volume := by
  unfold indS
  rw [integrable_indicator_iff hS_meas]
  exact integrableOn_const (by rw [hS_vol]; exact ENNReal.one_ne_top)

noncomputable def hAuto (S : Set ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, indS S x * indS S (x - y)

lemma hAuto_eq_volume_inter {S : Set ℝ} (hS_meas : MeasurableSet S) (y : ℝ) :
    hAuto S y = (volume (S ∩ {x : ℝ | x - y ∈ S})).toReal := by
  unfold hAuto indS
  have hpt : (fun x : ℝ => S.indicator (fun _ => (1 : ℝ)) x *
      S.indicator (fun _ => (1 : ℝ)) (x - y)) =
      (S ∩ {x : ℝ | x - y ∈ S}).indicator (1 : ℝ → ℝ) := by
    funext x
    by_cases hx1 : x ∈ S <;> by_cases hx2 : x - y ∈ S <;> simp [hx1, hx2]
  rw [hpt, integral_indicator_one]
  · simp [Measure.real]
  · exact hS_meas.inter (hS_meas.preimage (measurable_id.sub measurable_const))

lemma hAuto_zero {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    hAuto S 0 = 1 := by
  rw [hAuto_eq_volume_inter hS_meas]
  have : S ∩ {x : ℝ | x - 0 ∈ S} = S := by ext x; simp
  rw [this, hS_vol]
  simp

lemma continuous_hAuto {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    Continuous (hAuto S) := by
  have hf : Integrable (indS S) volume := integrable_indS hS_meas hS_vol
  rw [Metric.continuous_iff]
  intro y₀ ε hε
  obtain ⟨φ, hφ_cs, hφ_approx, hφ_cont, hφ_int⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le (show 0 < ε / 3 by linarith)
  obtain ⟨R, hR⟩ := hφ_cs.isBounded.subset_closedBall (0 : ℝ)
  set M : ℝ := max R 0
  have hφ_supp : ∀ x : ℝ, M < |x| → φ x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hne)
    have hdist : dist x 0 ≤ R := hR hmem
    rw [Real.dist_eq, sub_zero] at hdist
    linarith [le_max_left R 0]
  obtain ⟨C, hC⟩ := hφ_cs.exists_bound_of_continuous hφ_cont
  have htrans : Tendsto (fun t : ℝ => ∫ x : ℝ, ‖φ (x - t) - φ x‖) (𝓝 0) (𝓝 0) := by
    have hlim : (0 : ℝ) = ∫ _x : ℝ, (0 : ℝ) := by simp
    conv_rhs => rw [hlim]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (Set.Icc (-(M + 1)) (M + 1)).indicator (fun _ => 2 * C) x) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t =>
        (hφ_cont.comp (continuous_id.sub continuous_const) |>.sub hφ_cont).norm.aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      filter_upwards with x
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      by_cases hx : x ∈ Set.Icc (-(M + 1)) (M + 1)
      · rw [Set.indicator_of_mem hx]
        calc ‖φ (x - t) - φ x‖ ≤ ‖φ (x - t)‖ + ‖φ x‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring
      · rw [Set.indicator_of_notMem hx]
        have hx_gt : M + 1 < |x| := by
          by_contra hle; push Not at hle; exact hx (abs_le.mp hle)
        have h1 : M < |x| := by linarith
        have h2 : M < |x - t| := by
          have := abs_sub_abs_le_abs_sub x t; linarith
        rw [hφ_supp x h1, hφ_supp (x - t) h2, sub_self, norm_zero]
    · rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (by simp [Real.volume_Icc])
    · filter_upwards with x
      have h1 : Tendsto (fun t : ℝ => φ (x - t) - φ x) (𝓝 0) (𝓝 (φ (x - 0) - φ x)) :=
        ((hφ_cont.tendsto (x - 0)).comp (tendsto_const_nhds.sub tendsto_id)).sub tendsto_const_nhds
      rw [sub_zero, sub_self] at h1
      simpa using h1.norm
  rw [Metric.tendsto_nhds] at htrans
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (htrans (ε / 3) (by linarith))
  refine ⟨δ, hδ_pos, fun y hy => ?_⟩
  rw [dist_eq_norm]
  have hint_sub : ∀ z : ℝ, Integrable (fun x => indS S x * indS S (x - z)) volume := fun z => by
    refine hf.norm.mono' (hf.aestronglyMeasurable.mul (hf.comp_sub_right z).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul]
    have h1 : ‖indS S (x - z)‖ ≤ 1 := by
      unfold indS; by_cases h : x - z ∈ S <;> simp [h]
    simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg (indS S x))
  have hstep1 : ‖hAuto S y - hAuto S y₀‖ ≤ ∫ x, ‖indS S (x - y) - indS S (x - y₀)‖ := by
    unfold hAuto
    rw [← integral_sub (hint_sub y) (hint_sub y₀)]
    calc
      ‖∫ x, (indS S x * indS S (x - y) - indS S x * indS S (x - y₀))‖
          ≤ ∫ x, ‖indS S x * (indS S (x - y) - indS S (x - y₀))‖ := by
            simpa [mul_sub] using norm_integral_le_integral_norm (μ := volume)
              (fun x => indS S x * indS S (x - y) - indS S x * indS S (x - y₀))
      _ ≤ ∫ x, ‖indS S (x - y) - indS S (x - y₀)‖ := by
            apply integral_mono
            · exact ((hint_sub y).sub (hint_sub y₀)).norm.congr
                (Eventually.of_forall fun x => by simp [mul_sub])
            · exact ((hf.comp_sub_right y).sub (hf.comp_sub_right y₀)).norm
            · intro x; dsimp only; rw [norm_mul]
              have h1 : ‖indS S x‖ ≤ 1 := by unfold indS; by_cases h : x ∈ S <;> simp [h]
              simpa using mul_le_mul_of_nonneg_right h1 (norm_nonneg (indS S (x - y) - indS S (x - y₀)))
  have hshift : ∫ x, ‖indS S (x - y) - indS S (x - y₀)‖ =
      ∫ u, ‖indS S (u - (y - y₀)) - indS S u‖ := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun u => ‖indS S (u - (y - y₀)) - indS S u‖) y₀
    rw [← h]; congr 1; funext x; ring_nf
  have htri : ∫ u, ‖indS S (u - (y - y₀)) - indS S u‖ ≤
      (∫ u, ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖) +
      (∫ u, ‖φ (u - (y - y₀)) - φ u‖) +
      (∫ u, ‖φ u - indS S u‖) := by
    have ha : Integrable (fun u => ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖) volume :=
      ((hf.comp_sub_right (y - y₀)).sub (hφ_int.comp_sub_right (y - y₀))).norm
    have hb : Integrable (fun u => ‖φ (u - (y - y₀)) - φ u‖) volume :=
      ((hφ_int.comp_sub_right (y - y₀)).sub hφ_int).norm
    have hc : Integrable (fun u => ‖φ u - indS S u‖) volume := (hφ_int.sub hf).norm
    have hab : Integrable (fun u => ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖ +
        ‖φ (u - (y - y₀)) - φ u‖) volume := ha.add hb
    rw [← integral_add ha hb, ← integral_add hab hc]
    refine integral_mono (((hf.comp_sub_right (y - y₀)).sub hf).norm) (hab.add hc) fun u => ?_
    dsimp only
    calc
      ‖indS S (u - (y - y₀)) - indS S u‖
          = ‖(indS S (u - (y - y₀)) - φ (u - (y - y₀))) +
              ((φ (u - (y - y₀)) - φ u) + (φ u - indS S u))‖ := by ring_nf
      _ ≤ ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖ +
            ‖(φ (u - (y - y₀)) - φ u) + (φ u - indS S u)‖ := norm_add_le _ _
      _ ≤ ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖ +
            (‖φ (u - (y - y₀)) - φ u‖ + ‖φ u - indS S u‖) := by
            gcongr; exact norm_add_le _ _
      _ = _ := by ring
  have h1 : ∫ u, ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖ ≤ ε / 3 := by
    rw [integral_sub_right_eq_self (fun u => ‖indS S u - φ u‖) (y - y₀)]
    simpa [Pi.sub_apply] using hφ_approx
  have h3 : ∫ u, ‖φ u - indS S u‖ ≤ ε / 3 := by
    have : (fun u => ‖φ u - indS S u‖) = (fun u => ‖indS S u - φ u‖) := by
      funext u; exact norm_sub_rev _ _
    rw [this]; simpa [Pi.sub_apply] using hφ_approx
  have h2 : ∫ u, ‖φ (u - (y - y₀)) - φ u‖ < ε / 3 := by
    have hdist0 : dist (y - y₀) 0 < δ := by simpa [Real.dist_eq] using hy
    have hspec := hδ hdist0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at hspec
    exact hspec
  linarith [hstep1, hshift, htri]

lemma tilesR_uniform_sep {S T : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1)
    (htile : TilesR S T) :
    ∃ δ > 0, ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → δ ≤ |t₁ - t₂| := by
  have hcont := continuous_hAuto hS_meas hS_vol
  have h0 : hAuto S 0 = 1 := hAuto_zero hS_meas hS_vol
  have hnhds : {y : ℝ | (1 / 2 : ℝ) < hAuto S y} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt continuous_const hcont).mem_nhds (by show (1 / 2 : ℝ) < hAuto S 0; linarith)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ_pos, fun t₁ ht₁ t₂ ht₂ hne => ?_⟩
  by_contra hlt
  push Not at hlt
  have hmem : t₂ - t₁ ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_sub_comm]; exact hlt
  have hpos : (1 / 2 : ℝ) < hAuto S (t₂ - t₁) := hδ hmem
  have hdisj := htile.2.2 t₁ ht₁ t₂ ht₂ hne
  have hshift_eq : volume (S ∩ {x : ℝ | x - (t₂ - t₁) ∈ S}) =
      volume ({x : ℝ | x - t₁ ∈ S} ∩ {x : ℝ | x - t₂ ∈ S}) := by
    have hpre : (fun x : ℝ => x + t₁) ⁻¹' ({x : ℝ | x - t₁ ∈ S} ∩ {x : ℝ | x - t₂ ∈ S}) =
        S ∩ {x : ℝ | x - (t₂ - t₁) ∈ S} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
      have h1 : x + t₁ - t₁ = x := by ring
      have h2 : x + t₁ - t₂ = x - (t₂ - t₁) := by ring
      rw [h1, h2]
    rw [← hpre, measure_preimage_add_right]
  rw [hAuto_eq_volume_inter hS_meas, hshift_eq, hdisj] at hpos
  norm_num at hpos

lemma separated_inter_Icc_finite_and_card_le {Λ : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y|) (a b : ℝ) :
    (Λ ∩ Set.Icc a b).Finite ∧
      (Λ ∩ Set.Icc a b).ncard ≤ Nat.floor (max 0 (b - a) / δ) + 1 := by
  set N : ℕ := Nat.floor (max 0 (b - a) / δ) + 1
  let f : (Λ ∩ Set.Icc a b : Set ℝ) → Fin N := fun x =>
    ⟨Nat.floor ((x.1 - a) / δ), by
      have hxa : 0 ≤ x.1 - a := sub_nonneg.mpr x.2.2.1
      have hxb : x.1 - a ≤ max 0 (b - a) := le_trans (sub_le_sub_right x.2.2.2 a) (le_max_right _ _)
      have hdiv : (x.1 - a) / δ ≤ max 0 (b - a) / δ := div_le_div_of_nonneg_right hxb hδ.le
      exact Nat.lt_succ_of_le (Nat.floor_mono hdiv)⟩
  have hfinj : Function.Injective f := by
    rintro ⟨x, hxΛ, hxa, _⟩ ⟨y, hyΛ, hya, _⟩ heq
    apply Subtype.ext
    by_contra hne
    have hfloor : Nat.floor ((x - a) / δ) = Nat.floor ((y - a) / δ) := congrArg Fin.val heq
    have hx0 : 0 ≤ (x - a) / δ := div_nonneg (sub_nonneg.mpr hxa) hδ.le
    have hy0 : 0 ≤ (y - a) / δ := div_nonneg (sub_nonneg.mpr hya) hδ.le
    have hx_lo : (Nat.floor ((x - a) / δ) : ℝ) ≤ (x - a) / δ := Nat.floor_le hx0
    have hx_hi : (x - a) / δ < (Nat.floor ((x - a) / δ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hy_lo : (Nat.floor ((x - a) / δ) : ℝ) ≤ (y - a) / δ := hfloor ▸ Nat.floor_le hy0
    have hy_hi : (y - a) / δ < (Nat.floor ((x - a) / δ) : ℝ) + 1 := hfloor ▸ Nat.lt_floor_add_one _
    have hdiff : |(x - a) / δ - (y - a) / δ| < 1 := by rw [abs_lt]; constructor <;> linarith
    have heq1 : (x - a) / δ - (y - a) / δ = (x - y) / δ := by ring
    rw [heq1, abs_div, abs_of_pos hδ] at hdiff
    have hlt : |x - y| < δ := (div_lt_one hδ).mp hdiff
    linarith [hsep x hxΛ y hyΛ hne]
  have : Finite (Λ ∩ Set.Icc a b : Set ℝ) := Finite.of_injective f hfinj
  refine ⟨Set.toFinite _, ?_⟩
  have hle := Nat.card_le_card_of_injective f hfinj
  simpa [Set.ncard_def, Nat.card_fin] using hle

lemma tilesR_ae_unique {S T : Set ℝ} (htile : TilesR S T) :
    ∀ᵐ x ∂volume, ∃! t : ℝ, t ∈ T ∧ x - t ∈ S := by
  rcases htile with ⟨hT_cnt, hcov, hdisj⟩
  have : Countable T := hT_cnt.to_subtype
  let badOverlap : Set ℝ :=
    ⋃ p : {p : T × T // p.1.1 ≠ p.2.1}, ({x : ℝ | x - p.1.1.1 ∈ S} ∩ {x : ℝ | x - p.1.2.1 ∈ S})
  have hbad_null : volume badOverlap = 0 := by
    refine measure_iUnion_null fun p => hdisj p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2
  have hunion_null : volume ((Set.univ \ ⋃ t ∈ T, {x : ℝ | x - t ∈ S}) ∪ badOverlap) = 0 :=
    measure_union_null hcov hbad_null
  filter_upwards [compl_mem_ae_iff.mpr hunion_null] with x hx
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_sdiff, Set.mem_univ, true_and,
    not_not, Set.mem_iUnion, Set.mem_ofPred_eq] at hx
  rcases hx with ⟨⟨t, ht, hxt⟩, hno⟩
  refine ⟨t, ⟨ht, hxt⟩, fun t' ⟨ht', hxt'⟩ => ?_⟩
  by_contra hne
  apply hno
  exact Set.mem_iUnion.mpr ⟨⟨(⟨t', ht'⟩, ⟨t, ht⟩), hne⟩, ⟨hxt', hxt⟩⟩

/- ### Entire Fourier Transform `F` and Jensen Linear Zero-Set Growth -/

noncomputable def F (S : Set ℝ) (z : ℂ) : ℂ :=
  ∫ t in S, Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))

lemma F_zero {S : Set ℝ} (hS_vol : volume S = 1) : F S 0 = 1 := by
  unfold F; simp [hS_vol, Measure.real]

lemma norm_F_le_exp {S : Set ℝ} {R : ℝ} (_hR : 0 ≤ R) (hS_sub : S ⊆ Set.Icc (-R) R)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (z : ℂ) :
    ‖F S z‖ ≤ Real.exp (2 * Real.pi * R * ‖z‖) := by
  unfold F
  have hbound : ∀ t ∈ S, ‖Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))‖ ≤
      Real.exp (2 * Real.pi * R * ‖z‖) := by
    intro t ht
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-2 * Real.pi * Complex.I * z * (t : ℂ)).re = 2 * Real.pi * z.im * t := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have htR : |t| ≤ R := abs_le.mpr (hS_sub ht)
    have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    calc 2 * Real.pi * z.im * t ≤ |2 * Real.pi * z.im * t| := le_abs_self _
      _ = 2 * Real.pi * |z.im| * |t| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ 2 * Real.pi * ‖z‖ * R := by
        have h1 : 2 * Real.pi * |z.im| ≤ 2 * Real.pi * ‖z‖ := by
          gcongr
        calc 2 * Real.pi * |z.im| * |t| ≤ 2 * Real.pi * ‖z‖ * |t| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
          _ ≤ 2 * Real.pi * ‖z‖ * R :=
              mul_le_mul_of_nonneg_left htR (by positivity)
      _ = 2 * Real.pi * R * ‖z‖ := by ring
  have hint_const : IntegrableOn (fun _ : ℝ => Real.exp (2 * Real.pi * R * ‖z‖)) S volume :=
    integrableOn_const (by rw [hS_vol]; exact ENNReal.one_ne_top)
  calc
    ‖∫ t in S, Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))‖
        ≤ ∫ t in S, ‖Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))‖ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ _t in S, Real.exp (2 * Real.pi * R * ‖z‖) := by
          refine setIntegral_mono_on ?_ hint_const hS_meas hbound
          exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set hS_sub
    _ = Real.exp (2 * Real.pi * R * ‖z‖) := by simp [hS_vol, Measure.real]

lemma differentiable_F {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) : Differentiable ℂ (F S) := by
  intro z₀
  obtain ⟨R, hR⟩ := hS_bdd.subset_closedBall (0 : ℝ)
  set M : ℝ := max R 0
  have hS_bound : ∀ t ∈ S, |t| ≤ M := fun t ht => by
    have h1 : dist t 0 ≤ R := hR ht
    rw [Real.dist_eq, sub_zero] at h1
    exact le_trans h1 (le_max_left R 0)
  have hS_fin : volume S ≠ ⊤ := by
    have hsub : S ⊆ Set.Icc (-M) M := fun t ht => abs_le.mp (hS_bound t ht)
    exact ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono hsub)
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simp [hS_fin.lt_top]⟩
  let f : ℂ → ℝ → ℂ := fun z t => Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))
  let f' : ℂ → ℝ → ℂ := fun z t =>
    (-2 * Real.pi * Complex.I * (t : ℂ)) * Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))
  let C : ℝ := 2 * Real.pi * M * Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M)
  have hdiff : ∀ t : ℝ, ∀ z : ℂ, HasDerivAt (fun w => f w t) (f' z t) z := by
    intro t z
    have hlin : HasDerivAt (fun w : ℂ => -2 * Real.pi * Complex.I * w * (t : ℂ))
        (-2 * Real.pi * Complex.I * (t : ℂ)) z := by
      have := ((hasDerivAt_id z).const_mul (-2 * Real.pi * Complex.I)).mul_const (t : ℂ)
      simpa using this
    simpa [f, f', mul_comm] using hlin.cexp
  have hF_int : ∀ᶠ z in 𝓝 z₀, Integrable (f z) (volume.restrict S) := by
    refine Eventually.of_forall fun z => ?_
    have hsub : S ⊆ Set.Icc (-M) M := fun t ht => abs_le.mp (hS_bound t ht)
    exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set hsub
  have hbound : ∀ᵐ t ∂(volume.restrict S), ∀ z ∈ Metric.ball z₀ 1, ‖f' z t‖ ≤ C := by
    filter_upwards [ae_restrict_mem hS_meas] with t ht z hz
    have htM : |t| ≤ M := hS_bound t ht
    have hzM : ‖z‖ ≤ ‖z₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have := norm_sub_norm_le z z₀; linarith
    have hnorm_fac : ‖(-2 * Real.pi * Complex.I * (t : ℂ))‖ = 2 * Real.pi * |t| := by
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hnorm_exp : ‖Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))‖ ≤
        Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (-2 * Real.pi * Complex.I * z * (t : ℂ)).re = 2 * Real.pi * z.im * t := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre]
      have hzim : |z.im| ≤ ‖z₀‖ + 1 := le_trans (Complex.abs_im_le_norm z) hzM
      calc 2 * Real.pi * z.im * t ≤ |2 * Real.pi * z.im * t| := le_abs_self _
        _ = 2 * Real.pi * |z.im| * |t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ 2 * Real.pi * (‖z₀‖ + 1) * M := by
          have h1 : 2 * Real.pi * |z.im| ≤ 2 * Real.pi * (‖z₀‖ + 1) := by gcongr
          calc 2 * Real.pi * |z.im| * |t| ≤ 2 * Real.pi * (‖z₀‖ + 1) * |t| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
            _ ≤ 2 * Real.pi * (‖z₀‖ + 1) * M :=
                mul_le_mul_of_nonneg_left htM (by positivity)
    dsimp only [f']
    rw [norm_mul, hnorm_fac]
    have h1 : 2 * Real.pi * |t| ≤ 2 * Real.pi * M := by gcongr
    exact mul_le_mul h1 hnorm_exp (norm_nonneg _) (by positivity)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Eventually.of_forall fun z => Continuous.aestronglyMeasurable (by fun_prop))
    (hF_int.self_of_nhds)
    (Continuous.aestronglyMeasurable (by fun_prop))
    hbound
    (integrable_const C)
    (Eventually.of_forall fun t z _ => hdiff t z)
  exact hres.2.differentiableAt

lemma zero_set_linear_growth {S : Set ℝ} {R : ℝ} (hR : 0 ≤ R) (hS_sub : S ⊆ Set.Icc (-R) R)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    ∀ r : ℝ, 0 < r →
      ({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r).Finite ∧
      (({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r).ncard : ℝ) ≤
        (4 * Real.pi * R / Real.log 2) * r := by
  have hS_bdd : Bornology.IsBounded S :=
    Metric.isBounded_Icc (-R) R |>.subset hS_sub
  have han : AnalyticOnNhd ℂ (F S) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_F hS_bdd hS_meas)
  have hF0 : F S 0 ≠ 0 := by rw [F_zero hS_vol]; exact one_ne_zero
  intro r hr
  have hr_abs : 0 < |r| := abs_pos.mpr hr.ne'
  have hr2 : |r| < |2 * r| := by
    rw [abs_of_pos hr, abs_of_pos (by linarith)]; linarith
  have hM : (1 : ℝ) ≤ Real.exp (2 * Real.pi * R * (2 * r)) :=
    Real.one_le_exp (by positivity)
  have hfb : ∀ z ∈ Metric.sphere (0 : ℂ) |2 * r|,
      ‖F S z‖ ≤ Real.exp (2 * Real.pi * R * (2 * r)) := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos (by linarith)] at hz
    simpa [hz] using norm_F_le_exp hR hS_sub hS_meas hS_vol z
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (2 * Real.pi * R * (2 * r))) hr_abs hr2 hM
    (han.mono (Set.subset_univ _)) hF0 hfb
  have hdiv_fin : (MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|)).support.Finite :=
    (MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|)).finiteSupport
      (isCompact_closedBall _ _)
  have hsub_supp : Complex.ofReal '' ({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r) ⊆
      (MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|)).support := by
    rintro z ⟨ξ, ⟨hξ0, hξIcc⟩, rfl⟩
    have hmem : (ξ : ℂ) ∈ Metric.closedBall (0 : ℂ) |r| := by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      exact abs_le.mpr hξIcc
    have han_ball : AnalyticOnNhd ℂ (F S) (Metric.closedBall (0 : ℂ) |r|) :=
      han.mono (Set.subset_univ _)
    rw [Function.mem_support, MeromorphicOn.AnalyticOnNhd.divisor_apply han_ball hmem]
    have hne_top : analyticOrderAt (F S) (ξ : ℂ) ≠ ⊤ := by
      intro htop
      have heq0 : Set.EqOn (F S) 0 Set.univ :=
        han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (Set.mem_univ _) (analyticOrderAt_eq_top.mp htop)
      exact hF0 (heq0 (Set.mem_univ 0))
    have hpos_ord : 0 < analyticOrderAt (F S) (ξ : ℂ) := by
      by_contra hle
      have h0 : analyticOrderAt (F S) (ξ : ℂ) = 0 := le_antisymm (not_lt.mp hle) zero_le
      exact ((han (ξ : ℂ) (Set.mem_univ _)).analyticOrderAt_eq_zero.mp h0) hξ0
    lift analyticOrderAt (F S) (ξ : ℂ) to ℕ using hne_top with n
    have hn_pos : 0 < n := by exact_mod_cast hpos_ord
    simpa [WithTop.untop₀] using Int.natCast_ne_zero.mpr hn_pos.ne'
  have hfin : ({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r).Finite :=
    (hdiv_fin.subset hsub_supp).of_finite_image (Complex.ofReal_injective.injOn)
  refine ⟨hfin, ?_⟩
  have hdiv_nonneg : ∀ u, 0 ≤ MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|) u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han.mono (Set.subset_univ _))
  have hdiv_ge_one : ∀ u ∈ Complex.ofReal '' ({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r),
      (1 : ℤ) ≤ MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|) u := by
    intro u hu
    have hne0 : MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|) u ≠ 0 :=
      Function.mem_support.mp (hsub_supp hu)
    have hge0 := hdiv_nonneg u
    omega
  have hcard_le_sum : (({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r).ncard : ℤ) ≤
      ∑ᶠ u, MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|) u := by
    rw [finsum_eq_sum_of_support_subset _ hdiv_fin.coe_toFinset.ge]
    have himg_card : (hfin.toFinset.image Complex.ofReal).card = hfin.toFinset.card :=
      Finset.card_image_of_injective _ Complex.ofReal_injective
    have hsub_fin : hfin.toFinset.image Complex.ofReal ⊆ hdiv_fin.toFinset := by
      intro u hu
      rw [Set.Finite.mem_toFinset]
      apply hsub_supp
      rcases Finset.mem_image.mp hu with ⟨ξ, hξ, rfl⟩
      exact ⟨ξ, hfin.mem_toFinset.mp hξ, rfl⟩
    calc (({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r).ncard : ℤ)
        = (hfin.toFinset.card : ℤ) := by rw [Set.ncard_eq_toFinset_card _ hfin]
      _ = ((hfin.toFinset.image Complex.ofReal).card : ℤ) := by rw [himg_card]
      _ = ∑ _u ∈ hfin.toFinset.image Complex.ofReal, (1 : ℤ) := by simp
      _ ≤ ∑ u ∈ hfin.toFinset.image Complex.ofReal,
            MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|) u := by
          refine Finset.sum_le_sum fun u hu => hdiv_ge_one u ?_
          rcases Finset.mem_image.mp hu with ⟨ξ, hξ, rfl⟩
          exact ⟨ξ, hfin.mem_toFinset.mp hξ, rfl⟩
      _ ≤ ∑ u ∈ hdiv_fin.toFinset,
            MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|) u :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_fin fun u _ _ => hdiv_nonneg u
  have hrhs : Real.log (Real.exp (2 * Real.pi * R * (2 * r)) / ‖F S 0‖) / Real.log (2 * r / r) =
      (4 * Real.pi * R / Real.log 2) * r := by
    rw [F_zero hS_vol, norm_one, div_one, Real.log_exp, mul_div_cancel_right₀ _ hr.ne']
    ring
  calc (({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r).ncard : ℝ)
      = ((({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-r) r).ncard : ℤ) : ℝ) := by norm_cast
    _ ≤ ((∑ᶠ u, MeromorphicOn.divisor (F S) (Metric.closedBall (0 : ℂ) |r|) u : ℤ) : ℝ) := by
        exact_mod_cast hcard_le_sum
    _ ≤ Real.log (Real.exp (2 * Real.pi * R * (2 * r)) / ‖F S 0‖) / Real.log (2 * r / r) := hjensen
    _ = (4 * Real.pi * R / Real.log 2) * r := hrhs

/- ## Section 2: Atomic Fourier Representation of the Smoothed Dirac Comb -/

lemma fourier_deriv_eq_mul_fourier {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ 1 ψ)
    (hψ_cs : HasCompactSupport ψ) (t : ℝ) :
    𝓕 (deriv ψ) t = (2 * Real.pi * Complex.I * (t : ℂ)) * 𝓕 ψ t := by
  obtain ⟨R, hR⟩ := hψ_cs.isBounded.subset_closedBall (0 : ℝ)
  set M : ℝ := max R 0 + 1
  have hM_pos : 0 < M := by positivity
  have hψ_zero : ∀ x : ℝ, M ≤ |x| → ψ x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
    have hd : |x| ≤ R := by simpa [Real.dist_eq] using hR hmem
    linarith [le_max_left R 0]
  have hψ'_zero : ∀ x : ℝ, M ≤ |x| → deriv ψ x = 0 := by
    intro x hx
    have hts : tsupport (deriv ψ) ⊆ tsupport ψ := tsupport_deriv_subset
    by_contra hne
    have hmem : x ∈ tsupport ψ := hts (subset_tsupport _ (Function.mem_support.mpr hne))
    have hd : |x| ≤ R := by simpa [Real.dist_eq] using hR hmem
    linarith [le_max_left R 0]
  have hsupp1 : Function.support (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * deriv ψ x)
      ⊆ Set.Ioc (-M) M := by
    intro x hx
    rw [Function.mem_support] at hx
    have hne : deriv ψ x ≠ 0 := right_ne_zero_of_mul hx
    have hlt : |x| < M := by
      by_contra hge; push Not at hge; exact hne (hψ'_zero x hge)
    exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
  have hsupp2 : Function.support (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * ψ x)
      ⊆ Set.Ioc (-M) M := by
    intro x hx
    rw [Function.mem_support] at hx
    have hne : ψ x ≠ 0 := right_ne_zero_of_mul hx
    have hlt : |x| < M := by
      by_contra hge; push Not at hge; exact hne (hψ_zero x hge)
    exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp1,
      ← intervalIntegral.integral_eq_integral_of_support_subset hsupp2]
  let u : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I)
  let u' : ℝ → ℂ := fun x => (-2 * Real.pi * Complex.I * (t : ℂ)) * u x
  have hu : ∀ x ∈ Set.uIcc (-M) M, HasDerivAt u (u' x) x := by
    intro x _
    have hlin : HasDerivAt (fun y : ℝ => ((↑(-2 * Real.pi * y * t) : ℂ) * Complex.I))
        (-2 * Real.pi * Complex.I * (t : ℂ)) x := by
      have h1 : HasDerivAt (fun y : ℝ => (-2 * Real.pi * y * t : ℝ)) (-2 * Real.pi * t) x := by
        simpa [mul_comm, mul_assoc] using ((hasDerivAt_id x).const_mul (-2 * Real.pi)).mul_const t
      have h2 : HasDerivAt (fun y : ℝ => (↑(-2 * Real.pi * y * t) : ℂ) * Complex.I)
          ((↑(-2 * Real.pi * t) : ℂ) * Complex.I) x :=
        h1.ofReal_comp.mul_const Complex.I
      convert h2 using 1
      push_cast; ring
    simpa [u, u', mul_comm] using hlin.cexp
  have hv : ∀ x ∈ Set.uIcc (-M) M, HasDerivAt ψ (deriv ψ x) x := fun x _ =>
    (hψ_diff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hu'_int : IntervalIntegrable u' volume (-M) M := by
    have hc : Continuous u' := by unfold u' u; fun_prop
    exact hc.intervalIntegrable _ _
  have hv'_int : IntervalIntegrable (deriv ψ) volume (-M) M :=
    (hψ_diff.continuous_deriv le_rfl).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'_int hv'_int
  have hψM : ψ M = 0 := hψ_zero M (by rw [abs_of_pos hM_pos])
  have hψmM : ψ (-M) = 0 := hψ_zero (-M) (by rw [abs_neg, abs_of_pos hM_pos])
  rw [hψM, hψmM, mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  calc ∫ x in (-M)..M, u x * deriv ψ x
      = - ∫ x in (-M)..M, ((-2 * Real.pi * Complex.I * (t : ℂ)) * u x) * ψ x := hibp
    _ = - ∫ x in (-M)..M, (-2 * Real.pi * Complex.I * (t : ℂ)) * (u x * ψ x) := by
          congr 1; refine intervalIntegral.integral_congr fun x _ => by ring
    _ = - ((-2 * Real.pi * Complex.I * (t : ℂ)) * ∫ x in (-M)..M, u x * ψ x) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (2 * Real.pi * Complex.I * (t : ℂ)) * ∫ x in (-M)..M, u x * ψ x := by ring

lemma fourier_iteratedDeriv_eq {ψ : ℝ → ℂ} (k : ℕ) (hψ_diff : ContDiff ℝ (k : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ) (t : ℝ) :
    𝓕 (iteratedDeriv k ψ) t = (2 * Real.pi * Complex.I * (t : ℂ)) ^ k * 𝓕 ψ t := by
  induction k generalizing ψ with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    have h1 : ContDiff ℝ 1 ψ := hψ_diff.of_le (by exact_mod_cast Nat.succ_pos k)
    have hdk : ContDiff ℝ (k : ℕ∞) (deriv ψ) := by
      have h' : ContDiff ℝ ((k : ℕ∞) + 1) ψ := by simpa [Nat.cast_succ] using hψ_diff
      exact (contDiff_succ_iff_deriv.mp h').2.2
    have hcs_d : HasCompactSupport (deriv ψ) := hψ_cs.deriv
    rw [iteratedDeriv_succ', ih hdk hcs_d, fourier_deriv_eq_mul_fourier h1 hψ_cs]
    ring

lemma norm_fourier_le_of_iteratedDeriv {ψ : ℝ → ℂ} (k : ℕ) (hψ_diff : ContDiff ℝ (k : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ) (t : ℝ) :
    (2 * Real.pi * |t|) ^ k * ‖𝓕 ψ t‖ ≤ ∫ x : ℝ, ‖iteratedDeriv k ψ x‖ := by
  have heq := fourier_iteratedDeriv_eq k hψ_diff hψ_cs t
  have hnorm_lhs : ‖(2 * Real.pi * Complex.I * (t : ℂ)) ^ k * 𝓕 ψ t‖ =
      (2 * Real.pi * |t|) ^ k * ‖𝓕 ψ t‖ := by
    rw [norm_mul, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← hnorm_lhs, ← heq, Real.fourier_real_eq_integral_exp_smul]
  calc ‖∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) • iteratedDeriv k ψ v‖
      ≤ ∫ v : ℝ, ‖Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) • iteratedDeriv k ψ v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v : ℝ, ‖iteratedDeriv k ψ v‖ := by
        congr 1; funext v
        rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma norm_fourier_decay_sq {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ 2 ψ) (hψ_cs : HasCompactSupport ψ) :
    ∀ t : ℝ, ‖𝓕 ψ t‖ ≤
      ((∫ x : ℝ, ‖ψ x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 ψ x‖) / (4 * Real.pi ^ 2)) / (1 + t ^ 2) := by
  intro t
  have h0 := norm_fourier_le_of_iteratedDeriv 0 (hψ_diff.of_le (by norm_num)) hψ_cs t
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h0
  have h2 := norm_fourier_le_of_iteratedDeriv 2 hψ_diff hψ_cs t
  have hpi2 : 0 < 4 * Real.pi ^ 2 := by positivity
  have h2' : t ^ 2 * ‖𝓕 ψ t‖ ≤ (∫ x : ℝ, ‖iteratedDeriv 2 ψ x‖) / (4 * Real.pi ^ 2) := by
    rw [le_div_iff₀ hpi2]
    have hlhs : (2 * Real.pi * |t|) ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    linarith [hlhs ▸ h2]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)]
  nlinarith [h0, h2']

lemma norm_fourier_decay_four {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ 4 ψ) (hψ_cs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖𝓕 ψ t‖ ≤ C / (1 + t ^ 4) := by
  set C0 := ∫ x : ℝ, ‖ψ x‖
  set C4 := ∫ x : ℝ, ‖iteratedDeriv 4 ψ x‖
  refine ⟨C0 + C4 / (16 * Real.pi ^ 4), by positivity, fun t => ?_⟩
  have h0 := norm_fourier_le_of_iteratedDeriv 0 (hψ_diff.of_le (by norm_num)) hψ_cs t
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h0
  have h4 := norm_fourier_le_of_iteratedDeriv 4 hψ_diff hψ_cs t
  have hpi4 : 0 < 16 * Real.pi ^ 4 := by positivity
  have h4' : t ^ 4 * ‖𝓕 ψ t‖ ≤ C4 / (16 * Real.pi ^ 4) := by
    rw [le_div_iff₀ hpi4]
    have hlhs : (2 * Real.pi * |t|) ^ 4 = 16 * Real.pi ^ 4 * t ^ 4 := by
      rw [mul_pow, mul_pow]
      have habs4 : |t| ^ 4 = t ^ 4 := by
        have : |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
        rw [this, sq_abs]; ring
      rw [habs4]; ring
    linarith [hlhs ▸ h4]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 4)]
  nlinarith [h0, h4']

lemma integrable_fourier_of_smooth_cs {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ 2 ψ)
    (hψ_cs : HasCompactSupport ψ) : Integrable (𝓕 ψ) volume := by
  set C := (∫ x : ℝ, ‖ψ x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 ψ x‖) / (4 * Real.pi ^ 2)
  have hint_dom : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul C
  have hcont : Continuous (𝓕 ψ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (hψ_diff.continuous.integrable_of_hasCompactSupport hψ_cs)
  refine hint_dom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [← div_eq_mul_inv]
  exact norm_fourier_decay_sq hψ_diff hψ_cs t

/- Summability and uniform scaled-sum bounds over sets with linear counting growth -/

lemma summable_and_bound_linear_count {Z : Set ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hcount : ∀ r : ℝ, 1 ≤ r → (Z ∩ Set.Icc (-r) r).Finite ∧ ((Z ∩ Set.Icc (-r) r).ncard : ℝ) ≤ A * r) :
    ∀ M : ℝ, 1 ≤ M →
      Summable (fun γ : Z => (1 : ℝ) / (M * (1 + (γ.1 / M) ^ 2))) ∧
      ∑' γ : Z, (1 : ℝ) / (M * (1 + (γ.1 / M) ^ 2)) ≤ 5 * A := by
  intro M hM
  let f : Z → ℝ := fun γ => (1 : ℝ) / (M * (1 + (γ.1 / M) ^ 2))
  have hf_nn : ∀ γ : Z, 0 ≤ f γ := fun γ => by positivity
  have hsum_union_le : ∀ a b : Finset Z, ∑ γ ∈ a ∪ b, f γ ≤ (∑ γ ∈ a, f γ) + ∑ γ ∈ b, f γ := fun a b => by
    have h := Finset.sum_union_inter (s₁ := a) (s₂ := b) (f := f)
    have hnn : 0 ≤ ∑ γ ∈ a ∩ b, f γ := Finset.sum_nonneg fun γ _ => hf_nn γ
    linarith
  have hfin_bound : ∀ s : Finset Z, ∑ γ ∈ s, f γ ≤ 5 * A := by
    intro s
    have hmax_ex : ∃ N : ℕ, ∀ γ ∈ s, |γ.1| ≤ (2 : ℝ) ^ N * M := by
      by_cases hs : s.Nonempty
      · set B := (s.image fun γ : Z => |γ.1|).max' (hs.image _)
        obtain ⟨N, hN⟩ := exists_nat_gt (B / M)
        refine ⟨N, fun γ hγ => ?_⟩
        have htB : |γ.1| ≤ B :=
          Finset.le_max' (s.image fun γ : Z => |γ.1|) |γ.1|
            (Finset.mem_image_of_mem (fun γ : Z => |γ.1|) hγ)
        have h2N : (N : ℝ) ≤ (2 : ℝ) ^ N := by
          exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
        have hBM : B ≤ (2 : ℝ) ^ N * M := by
          have : B < (N : ℝ) * M := (div_lt_iff₀ (by linarith)).mp hN
          nlinarith
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hs; subst hs; exact ⟨0, by simp⟩
    rcases hmax_ex with ⟨N, hN⟩
    let s0 : Finset Z := s.filter fun γ => |γ.1| ≤ M
    let sk : ℕ → Finset Z := fun k =>
      s.filter fun γ => (2 : ℝ) ^ k * M < |γ.1| ∧ |γ.1| ≤ (2 : ℝ) ^ (k + 1) * M
    have hsum_biUnion_le : ∀ I : Finset ℕ, ∑ γ ∈ I.biUnion sk, f γ ≤ ∑ k ∈ I, ∑ γ ∈ sk k, f γ := by
      intro I
      induction I using Finset.induction_on with
      | empty => simp
      | @insert a I ha ih =>
        rw [Finset.biUnion_insert, Finset.sum_insert ha]
        exact (hsum_union_le _ _).trans (by linarith)
    have hsub : s ⊆ s0 ∪ (Finset.range N).biUnion sk := by
      intro γ hγ
      by_cases hle : |γ.1| ≤ M
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hle⟩)
      · push Not at hle
        apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        have hex : ∃ k < N, (2 : ℝ) ^ k * M < |γ.1| ∧ |γ.1| ≤ (2 : ℝ) ^ (k + 1) * M := by
          have hset : ∃ k : ℕ, k ≤ N ∧ |γ.1| ≤ (2 : ℝ) ^ k * M := ⟨N, le_rfl, hN γ hγ⟩
          classical
          let m := Nat.find hset
          have hm : m ≤ N ∧ |γ.1| ≤ (2 : ℝ) ^ m * M := Nat.find_spec hset
          have hm_pos : 0 < m := by
            by_contra h0
            have hm0 : m = 0 := Nat.eq_zero_of_not_pos h0
            rw [hm0, pow_zero, one_mul] at hm
            linarith
          refine ⟨m - 1, by omega, ?_, ?_⟩
          · by_contra hle'
            push Not at hle'
            exact Nat.find_min hset (by omega) ⟨by omega, hle'⟩
          · rw [Nat.sub_add_cancel hm_pos]; exact hm.2
        rcases hex with ⟨k, hkN, hk1, hk2⟩
        exact ⟨k, Finset.mem_range.mpr hkN, Finset.mem_filter.mpr ⟨hγ, hk1, hk2⟩⟩
    have hcard_s0 : (s0.card : ℝ) ≤ A * M := by
      have hfin := (hcount M hM).1
      have hinj : s0.image Subtype.val ⊆ hfin.toFinset := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨γ, hγ, rfl⟩
        rw [Set.Finite.mem_toFinset]
        exact ⟨γ.2, abs_le.mp (Finset.mem_filter.mp hγ).2⟩
      have h1 : s0.card ≤ hfin.toFinset.card := by
        rw [← Finset.card_image_of_injective s0 Subtype.val_injective]
        exact Finset.card_le_card hinj
      calc (s0.card : ℝ) ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast h1
        _ = ((Z ∩ Set.Icc (-M) M).ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card _ hfin]
        _ ≤ A * M := (hcount M hM).2
    have hcard_sk : ∀ k : ℕ, ((sk k).card : ℝ) ≤ A * ((2 : ℝ) ^ (k + 1) * M) := by
      intro k
      have hr : 1 ≤ (2 : ℝ) ^ (k + 1) * M := by
        have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
        nlinarith
      have hfin := (hcount _ hr).1
      have hinj : (sk k).image Subtype.val ⊆ hfin.toFinset := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨γ, hγ, rfl⟩
        rw [Set.Finite.mem_toFinset]
        exact ⟨γ.2, abs_le.mp (Finset.mem_filter.mp hγ).2.2⟩
      have h1 : (sk k).card ≤ hfin.toFinset.card := by
        rw [← Finset.card_image_of_injective (sk k) Subtype.val_injective]
        exact Finset.card_le_card hinj
      calc ((sk k).card : ℝ) ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast h1
        _ = ((Z ∩ Set.Icc (-((2 : ℝ) ^ (k + 1) * M)) ((2 : ℝ) ^ (k + 1) * M)).ncard : ℝ) := by
          rw [Set.ncard_eq_toFinset_card _ hfin]
        _ ≤ A * ((2 : ℝ) ^ (k + 1) * M) := (hcount _ hr).2
    have hsum_s0 : ∑ γ ∈ s0, f γ ≤ A := by
      calc ∑ γ ∈ s0, f γ ≤ ∑ _γ ∈ s0, (1 / M) := by
            refine Finset.sum_le_sum fun γ _ => ?_
            dsimp only [f]; rw [one_div, one_div]
            apply inv_anti₀ (by linarith)
            nlinarith [sq_nonneg (γ.1 / M)]
        _ = (s0.card : ℝ) * (1 / M) := by simp
        _ ≤ (A * M) * (1 / M) := mul_le_mul_of_nonneg_right hcard_s0 (by positivity)
        _ = A := by field_simp
    have hsum_sk : ∀ k : ℕ, ∑ γ ∈ sk k, f γ ≤ 2 * A * ((1 / 2 : ℝ) ^ k) := by
      intro k
      calc ∑ γ ∈ sk k, f γ ≤ ∑ _γ ∈ sk k, (1 / (M * ((2 : ℝ) ^ k) ^ 2)) := by
            refine Finset.sum_le_sum fun γ hγ => ?_
            have htgt : (2 : ℝ) ^ k * M < |γ.1| := (Finset.mem_filter.mp hγ).2.1
            have hMpos : 0 < M := by linarith
            have hdiv : (2 : ℝ) ^ k < |γ.1 / M| := by
              rw [abs_div, abs_of_pos hMpos, lt_div_iff₀ hMpos]
              exact htgt
            have hsq : ((2 : ℝ) ^ k) ^ 2 ≤ (γ.1 / M) ^ 2 := by
              rw [← sq_abs (γ.1 / M)]
              exact pow_le_pow_left₀ (by positivity) hdiv.le 2
            dsimp only [f]; rw [one_div, one_div]
            apply inv_anti₀ (by positivity)
            nlinarith
        _ = ((sk k).card : ℝ) * (1 / (M * ((2 : ℝ) ^ k) ^ 2)) := by simp
        _ ≤ (A * ((2 : ℝ) ^ (k + 1) * M)) * (1 / (M * ((2 : ℝ) ^ k) ^ 2)) :=
            mul_le_mul_of_nonneg_right (hcard_sk k) (by positivity)
        _ = 2 * A * ((1 / 2 : ℝ) ^ k) := by
            have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
            have hM0 : M ≠ 0 := by linarith
            rw [pow_succ, one_div_pow]
            field_simp
    have hgeo : ∑ k ∈ Finset.range N, (2 * A * ((1 / 2 : ℝ) ^ k)) ≤ 4 * A := by
      rw [← Finset.mul_sum]
      have h1 : ∑ k ∈ Finset.range N, ((1 / 2 : ℝ) ^ k) ≤ 2 := by
        rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
        have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
        have h2 : ((1 / 2 : ℝ) ^ N - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ N) := by ring
        linarith
      nlinarith
    calc ∑ γ ∈ s, f γ
        ≤ ∑ γ ∈ s0 ∪ (Finset.range N).biUnion sk, f γ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun γ _ _ => hf_nn γ
      _ ≤ (∑ γ ∈ s0, f γ) + ∑ γ ∈ (Finset.range N).biUnion sk, f γ :=
          hsum_union_le _ _
      _ ≤ (∑ γ ∈ s0, f γ) + ∑ k ∈ Finset.range N, ∑ γ ∈ sk k, f γ := by
          gcongr; exact hsum_biUnion_le _
      _ ≤ A + ∑ k ∈ Finset.range N, (2 * A * ((1 / 2 : ℝ) ^ k)) := by
          gcongr; exact hsum_sk _
      _ ≤ A + 4 * A := by linarith
      _ = 5 * A := by ring
  have hsum : Summable f := summable_of_sum_le hf_nn hfin_bound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin_bound⟩

lemma summable_and_bound_scaled_inv_sq {T : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → δ ≤ |t₁ - t₂|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ), 1 ≤ M →
      Summable (fun t : T => (1 : ℝ) / (M * (1 + (t.1 / M) ^ 2))) ∧
      ∑' t : T, (1 : ℝ) / (M * (1 + (t.1 / M) ^ 2)) ≤ C := by
  have hcount : ∀ r : ℝ, 1 ≤ r →
      (T ∩ Set.Icc (-r) r).Finite ∧
      ((T ∩ Set.Icc (-r) r).ncard : ℝ) ≤ (2 / δ + 2) * r := by
    intro r hr
    have h := separated_inter_Icc_finite_and_card_le hδ hsep (-r) r
    refine ⟨h.1, ?_⟩
    have hmax : max 0 (r - -r) = 2 * r := by
      rw [show r - -r = 2 * r by ring, max_eq_right (by linarith)]
    rw [hmax] at h
    have hfl : (Nat.floor (2 * r / δ) : ℝ) ≤ 2 * r / δ := Nat.floor_le (by positivity)
    have hle : ((T ∩ Set.Icc (-r) r).ncard : ℝ) ≤ (Nat.floor (2 * r / δ) : ℝ) + 1 := by
      exact_mod_cast h.2
    calc ((T ∩ Set.Icc (-r) r).ncard : ℝ) ≤ 2 * r / δ + 1 := by linarith
      _ ≤ 2 * r / δ + 2 * r := by linarith
      _ = (2 / δ + 2) * r := by ring
  exact ⟨5 * (2 / δ + 2), by positivity,
    summable_and_bound_linear_count (by positivity) hcount⟩

lemma summable_fourier_over_sep {T : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → δ ≤ |t₁ - t₂|)
    {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ 2 ψ) (hψ_cs : HasCompactSupport ψ) :
    Summable (fun t : T => 𝓕 ψ t.1) := by
  obtain ⟨C0, _, hC0⟩ := summable_and_bound_scaled_inv_sq hδ hsep
  have hsum1 := (hC0 1 le_rfl).1
  set K := (∫ x : ℝ, ‖ψ x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 ψ x‖) / (4 * Real.pi ^ 2)
  refine Summable.of_norm_bounded (g := fun t : T => K * ((1 : ℝ) / (1 * (1 + (t.1 / 1) ^ 2))))
    (hsum1.mul_left K) fun t => ?_
  simp only [one_mul, div_one, mul_one_div]
  exact norm_fourier_decay_sq hψ_diff hψ_cs t.1

lemma smooth_to_c1 {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ 1 f :=
  hf.of_le (show ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)

lemma smooth_to_c2 {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ 2 f :=
  hf.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)

lemma smooth_to_c4 {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ 4 f :=
  hf.of_le (show ((4 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)

/- Annihilation away from `Z = {ξ | F S ξ = 0}` -/

lemma sum_fourier_eq_eval_zero_of_disjoint_Z {S T : Set ℝ}
    (hS_bdd : Bornology.IsBounded S) (hS_meas : MeasurableSet S)
    (hS_vol : volume S = 1) (htile : TilesR S T)
    {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hdisj : ∀ ξ ∈ tsupport ψ, F S (ξ : ℂ) ≠ 0) :
    ∑' t : T, 𝓕 ψ t.1 = ψ 0 := by
  classical
  let q : ℝ → ℂ := fun ξ => ψ ξ / F S (ξ : ℂ)
  have hFC : ContDiff ℂ ⊤ (F S) := (differentiable_F hS_bdd hS_meas).contDiff
  have hq_smooth : ContDiff ℝ (⊤ : ℕ∞) q := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hmem : ξ ∈ tsupport ψ
    · have hinvC : ContDiffAt ℂ ⊤ (fun z => (F S z)⁻¹) (ξ : ℂ) :=
        hFC.contDiffAt.inv (hdisj ξ hmem)
      have hinvR : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (F S (x : ℂ))⁻¹) ξ :=
        ((hinvC.restrict_scalars ℝ).of_le le_top).comp ξ
          (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).contDiffAt
      simpa only [q, div_eq_mul_inv] using hψ_diff.contDiffAt.mul hinvR
    · have hzero : q =ᶠ[𝓝 ξ] 0 := by
        have hopen : (tsupport ψ)ᶜ ∈ 𝓝 ξ := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hmem
        filter_upwards [hopen] with x hx
        have hψ0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [q, hψ0]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hq_cs : HasCompactSupport q := by
    refine hψ_cs.mono fun x hx => ?_
    rw [Function.mem_support] at hx ⊢
    intro h0; exact hx (by simp [q, h0])
  let η : ℝ → ℂ := 𝓕⁻ q
  have hq_int : Integrable q volume := hq_smooth.continuous.integrable_of_hasCompactSupport hq_cs
  have hη_int : Integrable η volume := by
    have h1 := integrable_fourier_of_smooth_cs (smooth_to_c2 hq_smooth) hq_cs
    have heq : η = fun x => 𝓕 q (-x) := funext fun x => Real.fourierInv_eq_fourier_neg q x
    rw [heq]
    exact h1.comp_neg
  have hη_cont : Continuous η :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hq_int
  have hconv : ∀ t : ℝ, 𝓕 ψ t = ∫ y in S, η (-t - y) := by
    intro t
    have hFub : Integrable (Function.uncurry fun y ξ : ℝ =>
        Complex.exp (↑(2 * Real.pi * ξ * (-t - y)) * Complex.I) * q ξ)
        ((volume.restrict S).prod volume) := by
      have hmeas : AEStronglyMeasurable (Function.uncurry fun y ξ : ℝ =>
          Complex.exp (↑(2 * Real.pi * ξ * (-t - y)) * Complex.I) * q ξ)
          ((volume.restrict S).prod volume) := by
        have hc : Continuous (Function.uncurry fun y ξ : ℝ =>
            Complex.exp (↑(2 * Real.pi * ξ * (-t - y)) * Complex.I) * q ξ) := by
          unfold Function.uncurry; fun_prop
        exact hc.aestronglyMeasurable
      have hdom : Integrable (Function.uncurry fun (_y : ℝ) (ξ : ℝ) => ‖q ξ‖)
          ((volume.restrict S).prod volume) := by
        have : IsFiniteMeasure (volume.restrict S) := ⟨by simp [hS_vol]⟩
        exact (integrable_const (1 : ℝ)).mul_prod hq_int.norm |>.congr
          (Eventually.of_forall fun p => by simp [Function.uncurry])
      refine hdom.mono' hmeas (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
    have hη_eq : ∀ y : ℝ, η (-t - y) = ∫ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * ξ * (-t - y)) * Complex.I) * q ξ := by
      intro y
      change 𝓕⁻ q (-t - y) = _
      rw [Real.fourierInv_eq']
      congr 1; funext ξ
      simp only [Real.inner_apply, smul_eq_mul]
      congr 2; push_cast; ring
    simp_rw [hη_eq]
    rw [integral_integral_swap hFub]
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1; funext ξ
    have hsplit : ∀ y : ℝ, Complex.exp (↑(2 * Real.pi * ξ * (-t - y)) * Complex.I) * q ξ =
        (Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * q ξ) *
          Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (y : ℂ)) := by
      intro y
      calc Complex.exp (↑(2 * Real.pi * ξ * (-t - y)) * Complex.I) * q ξ
          = (Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) *
              Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (y : ℂ))) * q ξ := by
            rw [← Complex.exp_add]; congr 2; push_cast; ring
        _ = (Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * q ξ) *
              Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (y : ℂ)) := by ring
    simp_rw [hsplit]
    rw [integral_const_mul, smul_eq_mul]
    have hF_def : (∫ y in S, Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (y : ℂ))) = F S (ξ : ℂ) := rfl
    have hqF : q ξ * F S (ξ : ℂ) = ψ ξ := by
      by_cases hξ : ξ ∈ tsupport ψ
      · exact div_mul_cancel₀ (ψ ξ) (hdisj ξ hξ)
      · have hψ0 : ψ ξ = 0 := image_eq_zero_of_notMem_tsupport hξ
        simp [q, hψ0]
    rw [hF_def, mul_assoc (Complex.exp _), hqF]
  have hshift : ∀ t : ℝ, ∫ y in S, η (-t - y) = ∫ u : ℝ, (if u - t ∈ S then η (-u) else 0) := by
    intro t
    rw [← integral_indicator hS_meas]
    have h := integral_sub_right_eq_self (μ := volume)
      (fun u : ℝ => if u - t ∈ S then η (-u) else 0) (-t)
    rw [← h]
    congr 1; funext y
    have h1 : y - -t - t = y := by ring
    have h2 : -(y - -t) = -t - y := by ring
    rw [h1, h2]
    by_cases hy : y ∈ S <;> simp [hy]
  have : Countable T := htile.1.to_subtype
  let g : T → ℝ → ℂ := fun t u => if u - t.1 ∈ S then η (-u) else 0
  have hg_meas : ∀ t : T, AEStronglyMeasurable (g t) volume := fun t => by
    have hSet : MeasurableSet {u : ℝ | u - t.1 ∈ S} :=
      hS_meas.preimage (measurable_id.sub measurable_const)
    have h_eq : g t = {u : ℝ | u - t.1 ∈ S}.indicator (fun u => η (-u)) := by
      funext u; by_cases h : u - t.1 ∈ S <;> simp [g, h]
    rw [h_eq]
    exact (hη_cont.comp continuous_neg).aestronglyMeasurable.indicator hSet
  have hae_uniq := tilesR_ae_unique htile
  have htsum_pt : ∀ᵐ u ∂volume, ∑' t : T, g t u = η (-u) := by
    filter_upwards [hae_uniq] with u hu
    rcases hu with ⟨t₀, ⟨ht₀T, ht₀S⟩, huniq⟩
    rw [tsum_eq_single (⟨t₀, ht₀T⟩ : T)]
    · simp [g, ht₀S]
    · rintro ⟨t, htT⟩ hne
      have hnotS : u - t ∉ S := fun hS => hne (Subtype.ext (huniq t ⟨htT, hS⟩))
      simp [g, hnotS]
  have htsum_enorm : ∑' t : T, ∫⁻ u : ℝ, ‖g t u‖ₑ ≠ ∞ := by
    rw [← lintegral_tsum fun t => (hg_meas t).enorm]
    have hae_norm : (fun u => ∑' t : T, ‖g t u‖ₑ) =ᵐ[volume] (fun u => ‖η (-u)‖ₑ) := by
      filter_upwards [hae_uniq] with u hu
      rcases hu with ⟨t₀, ⟨ht₀T, ht₀S⟩, huniq⟩
      rw [tsum_eq_single (⟨t₀, ht₀T⟩ : T)]
      · simp [g, ht₀S]
      · rintro ⟨t, htT⟩ hne
        have hnotS : u - t ∉ S := fun hS => hne (Subtype.ext (huniq t ⟨htT, hS⟩))
        simp [g, hnotS]
    rw [lintegral_congr_ae hae_norm]
    exact hη_int.comp_neg.hasFiniteIntegral.ne
  calc ∑' t : T, 𝓕 ψ t.1
      = ∑' t : T, ∫ u : ℝ, g t u := by
        congr 1; funext t; rw [hconv t.1, hshift t.1]
    _ = ∫ u : ℝ, ∑' t : T, g t u := (integral_tsum hg_meas htsum_enorm).symm
    _ = ∫ u : ℝ, η (-u) := integral_congr_ae htsum_pt
    _ = ∫ v : ℝ, η v := integral_neg_eq_self η volume
    _ = 𝓕 (𝓕⁻ q) 0 := by
        rw [Real.fourier_real_eq_integral_exp_smul]; simp [η]
    _ = q 0 := by
        rw [hq_smooth.continuous.fourier_fourierInv_eq hq_int
          (integrable_fourier_of_smooth_cs (smooth_to_c2 hq_smooth) hq_cs)]
    _ = ψ 0 := by simp [q, F_zero hS_vol]

/- Local evaluation at an isolated zero `γ ∈ Z` via scaled bump + twice-IBP -/

noncomputable def stdBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

lemma stdBump_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (stdBump u : ℂ)) :=
  (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp stdBump.contDiff

lemma fourier_scaled_shift (f : ℝ → ℂ) (γ M t : ℝ) (hM : 0 < M) :
    𝓕 (fun ξ : ℝ => f (M * (ξ - γ))) t =
      (Complex.exp (↑(-2 * Real.pi * γ * t) * Complex.I) / (M : ℂ)) * 𝓕 f (t / M) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  rw [← integral_const_mul]
  have h1 := integral_add_right_eq_self (μ := volume)
    (fun ξ : ℝ => Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * f (M * (ξ - γ))) γ
  rw [← h1]
  simp_rw [add_sub_cancel_right]
  have h2 := Measure.integral_comp_mul_left (g := fun u : ℝ =>
    Complex.exp (↑(-2 * Real.pi * (u / M + γ) * t) * Complex.I) * f u) M
  have hsub : (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * (x + γ) * t) * Complex.I) * f (M * x)) =
      (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * ((M * x) / M + γ) * t) * Complex.I) * f (M * x)) := by
    funext x; rw [mul_div_cancel_left₀ x hM.ne']
  rw [hsub, h2, abs_inv, abs_of_pos hM, Complex.real_smul, ← integral_const_mul]
  congr 1; funext u
  rw [show (-2 * Real.pi * (u / M + γ) * t : ℝ) = -2 * Real.pi * γ * t + (-2 * Real.pi * u * (t / M)) by
    field_simp; ring]
  push_cast
  rw [add_mul, Complex.exp_add, div_eq_mul_inv]
  ring

lemma sum_fourier_eq_zero_of_isolated_vanish {S T : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → δ ≤ |t₁ - t₂|)
    (hS_bdd : Bornology.IsBounded S) (hS_meas : MeasurableSet S)
    (hS_vol : volume S = 1) (htile : TilesR S T)
    {γ : ℝ} (_hγ0 : γ ≠ 0)
    {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_zero : ψ γ = 0)
    (hsupp_Z : ∀ ξ ∈ tsupport ψ, F S (ξ : ℂ) = 0 → ξ = γ)
    (h0_not : (0 : ℝ) ∉ tsupport ψ) :
    ∑' t : T, 𝓕 ψ t.1 = 0 := by
  obtain ⟨Cδ, hCδ_nn, hCδ⟩ := summable_and_bound_scaled_inv_sq hδ hsep
  -- Bound derivatives of stdBump and ψ on compact intervals
  have hχ_cs : HasCompactSupport (fun u : ℝ => (stdBump u : ℂ)) :=
    stdBump.hasCompactSupport.comp_left Complex.ofReal_zero
  obtain ⟨B0, hB0⟩ := (stdBump_smooth.continuous).bounded_above_of_compact_support hχ_cs
  obtain ⟨B1, hB1⟩ := ((smooth_to_c1 stdBump_smooth).continuous_deriv le_rfl).bounded_above_of_compact_support hχ_cs.deriv
  obtain ⟨B2, hB2⟩ := ((smooth_to_c2 stdBump_smooth).continuous_iteratedDeriv 2 le_rfl).bounded_above_of_compact_support
    (by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact hχ_cs.deriv.deriv)
  obtain ⟨K1, hK1⟩ := ((smooth_to_c1 hψ_diff).continuous_deriv le_rfl).bounded_above_of_compact_support hψ_cs.deriv
  obtain ⟨K2, hK2⟩ := ((smooth_to_c2 hψ_diff).continuous_iteratedDeriv 2 le_rfl).bounded_above_of_compact_support
    (by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact hψ_cs.deriv.deriv)
  have hB0_nn : 0 ≤ B0 := le_trans (norm_nonneg _) (hB0 0)
  have hB1_nn : 0 ≤ B1 := le_trans (norm_nonneg _) (hB1 0)
  have hB2_nn : 0 ≤ B2 := le_trans (norm_nonneg _) (hB2 0)
  have hK1_nn : 0 ≤ K1 := le_trans (norm_nonneg _) (hK1 0)
  have hK2_nn : 0 ≤ K2 := le_trans (norm_nonneg _) (hK2 0)
  -- For any M ≥ 1, split ψ = (1 - χ_M) ψ + χ_M ψ
  have hbound_M : ∀ M : ℝ, 1 ≤ M →
      ‖∑' t : T, 𝓕 ψ t.1‖ ≤
        (2 * (B0 * K1 + (B2 * K1 + 2 * B1 * K1 + B0 * K2) / (4 * Real.pi ^ 2)) * Cδ) / M := by
    intro M hM
    have hM_pos : 0 < M := by linarith
    let χM : ℝ → ℂ := fun ξ => (stdBump (M * (ξ - γ)) : ℂ)
    have hχM_smooth : ContDiff ℝ (⊤ : ℕ∞) χM :=
      stdBump_smooth.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
    let ψ1 : ℝ → ℂ := fun ξ => (1 - χM ξ) * ψ ξ
    let ψ2 : ℝ → ℂ := fun ξ => χM ξ * ψ ξ
    have hψ1_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ1 := (contDiff_const.sub hχM_smooth).mul hψ_diff
    have hψ2_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ2 := hχM_smooth.mul hψ_diff
    have hψ1_cs : HasCompactSupport ψ1 := hψ_cs.mul_left
    have hψ2_cs : HasCompactSupport ψ2 := hψ_cs.mul_left
    have hψ1_disj : ∀ ξ ∈ tsupport ψ1, F S (ξ : ℂ) ≠ 0 := by
      intro ξ hξ hF0
      have hts : tsupport ψ1 ⊆ tsupport ψ := tsupport_mul_subset_right
      have hξγ : ξ = γ := hsupp_Z ξ (hts hξ) hF0
      subst ξ
      -- χM = 1 in a neighborhood of γ, so ψ1 = 0 in a neighborhood of γ
      have hnbhd : Metric.ball γ (1 / (2 * M)) ∈ 𝓝 γ :=
        Metric.ball_mem_nhds γ (by positivity)
      have hzero_nbhd : ψ1 =ᶠ[𝓝 γ] 0 := by
        filter_upwards [hnbhd] with x hx
        rw [Metric.mem_ball, Real.dist_eq] at hx
        have hmem : M * (x - γ) ∈ Metric.closedBall (0 : ℝ) stdBump.rIn := by
          rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_of_pos hM_pos]
          change M * |x - γ| ≤ 1 / 2
          have : |x - γ| < 1 / (2 * M) := hx
          have h1 : M * |x - γ| < M * (1 / (2 * M)) := mul_lt_mul_of_pos_left this hM_pos
          have h2 : M * (1 / (2 * M)) = 1 / 2 := by field_simp
          linarith
        simp [ψ1, χM, stdBump.one_of_mem_closedBall hmem]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hzero_nbhd) hξ
    have hψ1_0 : ψ1 0 = 0 := by
      have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport h0_not
      simp [ψ1, hψ0]
    have hsum1 : ∑' t : T, 𝓕 ψ1 t.1 = 0 := by
      rw [sum_fourier_eq_eval_zero_of_disjoint_Z hS_bdd hS_meas hS_vol htile hψ1_smooth hψ1_cs hψ1_disj,
        hψ1_0]
    have hsplit_F : ∀ t : ℝ, 𝓕 ψ t = 𝓕 ψ1 t + 𝓕 ψ2 t := by
      intro t
      have hadd : ψ = ψ1 + ψ2 := by funext ξ; simp [ψ1, ψ2]; ring
      rw [hadd]
      have hint1 : Integrable ψ1 volume := hψ1_smooth.continuous.integrable_of_hasCompactSupport hψ1_cs
      have hint2 : Integrable ψ2 volume := hψ2_smooth.continuous.integrable_of_hasCompactSupport hψ2_cs
      rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
        Real.fourier_real_eq_integral_exp_smul]
      simp_rw [Pi.add_apply, smul_add, smul_eq_mul]
      have hI1 : Integrable (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) * ψ1 v) volume :=
        hint1.norm.mono'
          ((by fun_prop : Continuous fun v : ℝ =>
            Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) * ψ1 v).aestronglyMeasurable)
          (Eventually.of_forall fun v => by
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul])
      have hI2 : Integrable (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) * ψ2 v) volume :=
        hint2.norm.mono'
          ((by fun_prop : Continuous fun v : ℝ =>
            Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) * ψ2 v).aestronglyMeasurable)
          (Eventually.of_forall fun v => by
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul])
      exact integral_add hI1 hI2
    have hsum_eq : ∑' t : T, 𝓕 ψ t.1 = ∑' t : T, 𝓕 ψ2 t.1 := by
      have hs1 := summable_fourier_over_sep hδ hsep (smooth_to_c2 hψ1_smooth) hψ1_cs
      have hs2 := summable_fourier_over_sep hδ hsep (smooth_to_c2 hψ2_smooth) hψ2_cs
      calc ∑' t : T, 𝓕 ψ t.1 = ∑' t : T, (𝓕 ψ1 t.1 + 𝓕 ψ2 t.1) := by
            congr 1; funext t; exact hsplit_F t.1
        _ = (∑' t : T, 𝓕 ψ1 t.1) + ∑' t : T, 𝓕 ψ2 t.1 := hs1.tsum_add hs2
        _ = ∑' t : T, 𝓕 ψ2 t.1 := by rw [hsum1, zero_add]
    rw [hsum_eq]
    -- Rewrite ψ2(ξ) = HM(M * (ξ - γ)) where HM(u) = stdBump(u) * ψ(γ + u / M)
    let HM : ℝ → ℂ := fun u => (stdBump u : ℂ) * ψ (γ + u / M)
    have hψ2_eq : ψ2 = fun ξ => HM (M * (ξ - γ)) := by
      funext ξ
      simp only [ψ2, χM, HM]
      rw [show γ + M * (ξ - γ) / M = ξ by field_simp; ring]
    have hHM_smooth : ContDiff ℝ (⊤ : ℕ∞) HM :=
      stdBump_smooth.mul (hψ_diff.comp (contDiff_const.add (contDiff_id.div_const M)))
    have hHM_cs : HasCompactSupport HM := hχ_cs.mul_right
    have hHM_supp : ∀ u : ℝ, 1 ≤ |u| → HM u = 0 := by
      intro u hu
      have h0 : stdBump u = 0 := stdBump.zero_of_le_dist (by simpa [Real.dist_eq, stdBump] using hu)
      simp [HM, h0]
    have hHM_d2_supp : ∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 HM u = 0 := by
      intro u hu
      have hts : tsupport (iteratedDeriv 2 HM) ⊆ tsupport (fun x => (stdBump x : ℂ)) := by
        calc tsupport (iteratedDeriv 2 HM) ⊆ tsupport HM := by
              rw [iteratedDeriv_succ, iteratedDeriv_one]
              exact tsupport_deriv_subset.trans tsupport_deriv_subset
          _ ⊆ tsupport (fun x => (stdBump x : ℂ)) := tsupport_mul_subset_left
      have hts_std : tsupport (fun x : ℝ => (stdBump x : ℂ)) ⊆ Metric.closedBall (0 : ℝ) 1 := by
        change tsupport (fun x : ℝ => (stdBump x : ℂ)) ⊆ Metric.closedBall (0 : ℝ) stdBump.rOut
        rw [← stdBump.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _
      by_cases hgt : 1 < |u|
      · apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have hle := hts_std (hts hmem)
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hle
        linarith
      · -- At |u| = 1, continuity of iteratedDeriv 2 HM from outside gives 0
        have heq1 : |u| = 1 := le_antisymm (not_lt.mp hgt) hu
        have hcont2 : Continuous (iteratedDeriv 2 HM) :=
          (smooth_to_c2 hHM_smooth).continuous_iteratedDeriv 2 le_rfl
        have hlim : Tendsto (fun n : ℕ => iteratedDeriv 2 HM (u + (if 0 ≤ u then (1 : ℝ) else -1) / ((n : ℝ) + 1)))
            atTop (𝓝 (iteratedDeriv 2 HM u)) := by
          have ht : Tendsto (fun n : ℕ => u + (if 0 ≤ u then (1 : ℝ) else -1) / ((n : ℝ) + 1))
              atTop (𝓝 (u + 0)) :=
            tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
              (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
          rw [add_zero] at ht
          exact (hcont2.tendsto u).comp ht
        have h0seq : ∀ n : ℕ, iteratedDeriv 2 HM (u + (if 0 ≤ u then (1 : ℝ) else -1) / ((n : ℝ) + 1)) = 0 := by
          intro n
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          have hle := hts_std (hts hmem)
          rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hle
          have hpos_n : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          split_ifs at hle with hnn
          · rw [abs_of_nonneg hnn] at heq1
            rw [abs_of_nonneg (by linarith)] at hle; linarith
          · push Not at hnn
            rw [abs_of_neg hnn] at heq1
            have hneg_div : (-1 : ℝ) / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) := by ring
            rw [hneg_div] at hle
            rw [abs_of_neg (by linarith)] at hle; linarith
        have h0lim : Tendsto (fun n : ℕ => iteratedDeriv 2 HM (u + (if 0 ≤ u then (1 : ℝ) else -1) / ((n : ℝ) + 1)))
            atTop (𝓝 0) := by
          simp_rw [h0seq]; exact tendsto_const_nhds
        exact tendsto_nhds_unique hlim h0lim
    -- Mean value bound on ‖ψ (γ + u / M)‖ for |u| ≤ 1
    have hψ_mvt : ∀ u : ℝ, |u| ≤ 1 → ‖ψ (γ + u / M)‖ ≤ K1 / M := by
      intro u hu
      have hlip : ∀ x : ℝ, ‖deriv ψ x‖ ≤ K1 := hK1
      have hdiff_ψ : Differentiable ℝ ψ := (smooth_to_c1 hψ_diff).differentiable one_ne_zero
      have hdist := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdiff_ψ x)
        (fun x _ => hlip x) convex_univ (Set.mem_univ γ) (Set.mem_univ (γ + u / M))
      rw [hψ_zero, sub_zero, add_sub_cancel_left, Real.norm_eq_abs, abs_div, abs_of_pos hM_pos] at hdist
      calc ‖ψ (γ + u / M)‖ ≤ K1 * (|u| / M) := hdist
        _ ≤ K1 * (1 / M) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hu hM_pos.le) hK1_nn
        _ = K1 / M := by ring
    have hHM_bound0 : ∀ u : ℝ, |u| ≤ 1 → ‖HM u‖ ≤ B0 * K1 / M := by
      intro u hu
      dsimp only [HM]
      rw [norm_mul]
      calc ‖(stdBump u : ℂ)‖ * ‖ψ (γ + u / M)‖ ≤ B0 * (K1 / M) :=
            mul_le_mul (hB0 u) (hψ_mvt u hu) (norm_nonneg _) hB0_nn
        _ = B0 * K1 / M := by ring
    -- Compute deriv and second deriv of HM explicitly
    have hHM_d1 : ∀ u : ℝ, deriv HM u =
        deriv (fun x : ℝ => (stdBump x : ℂ)) u * ψ (γ + u / M) +
        (stdBump u : ℂ) * ((1 / M : ℝ) • deriv ψ (γ + u / M)) := by
      intro u
      have h1 : HasDerivAt (fun x : ℝ => (stdBump x : ℂ))
          (deriv (fun x : ℝ => (stdBump x : ℂ)) u) u :=
        ((smooth_to_c1 stdBump_smooth).differentiable one_ne_zero).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun x : ℝ => γ + x / M) (1 / M) u := by
        simpa using (hasDerivAt_id u |>.div_const M).const_add γ
      have h3 : HasDerivAt (fun x : ℝ => ψ (γ + x / M)) ((1 / M : ℝ) • deriv ψ (γ + u / M)) u :=
        (((smooth_to_c1 hψ_diff).differentiable one_ne_zero).differentiableAt.hasDerivAt).scomp u h2
      exact (h1.mul h3).deriv
    have hHM_d2 : ∀ u : ℝ, iteratedDeriv 2 HM u =
        iteratedDeriv 2 (fun x : ℝ => (stdBump x : ℂ)) u * ψ (γ + u / M) +
        2 * (deriv (fun x : ℝ => (stdBump x : ℂ)) u * ((1 / M : ℝ) • deriv ψ (γ + u / M))) +
        (stdBump u : ℂ) * (((1 / M : ℝ) * (1 / M : ℝ)) • iteratedDeriv 2 ψ (γ + u / M)) := by
      intro u
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      have heq_fn : deriv HM = fun x =>
          deriv (fun y : ℝ => (stdBump y : ℂ)) x * ψ (γ + x / M) +
          (stdBump x : ℂ) * ((1 / M : ℝ) • deriv ψ (γ + x / M)) := funext hHM_d1
      rw [heq_fn]
      have hd_g : HasDerivAt (fun x : ℝ => deriv (fun y : ℝ => (stdBump y : ℂ)) x)
          (iteratedDeriv 2 (fun y : ℝ => (stdBump y : ℂ)) u) u := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
        exact ((contDiff_succ_iff_deriv.mp (smooth_to_c2 stdBump_smooth)).2.2.differentiable
          one_ne_zero).differentiableAt.hasDerivAt
      have hlin : HasDerivAt (fun x : ℝ => γ + x / M) (1 / M) u := by
        simpa using (hasDerivAt_id u |>.div_const M).const_add γ
      have hd_ψ : HasDerivAt (fun x : ℝ => ψ (γ + x / M)) ((1 / M : ℝ) • deriv ψ (γ + u / M)) u :=
        (((smooth_to_c1 hψ_diff).differentiable one_ne_zero).differentiableAt.hasDerivAt).scomp u hlin
      have hd_ψ' : HasDerivAt (fun x : ℝ => deriv ψ (γ + x / M))
          ((1 / M : ℝ) • iteratedDeriv 2 ψ (γ + u / M)) u := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
        have hd2 := (contDiff_succ_iff_deriv.mp (smooth_to_c2 hψ_diff)).2.2.differentiable one_ne_zero
        exact (hd2.differentiableAt.hasDerivAt).scomp u hlin
      have hd_b : HasDerivAt (fun x : ℝ => (stdBump x : ℂ))
          (deriv (fun y : ℝ => (stdBump y : ℂ)) u) u :=
        ((smooth_to_c1 stdBump_smooth).differentiable one_ne_zero).differentiableAt.hasDerivAt
      have ht1 := hd_g.mul hd_ψ
      have ht2 := hd_b.mul (hd_ψ'.const_smul (1 / M : ℝ))
      calc deriv (fun x : ℝ => deriv (fun y : ℝ => (stdBump y : ℂ)) x * ψ (γ + x / M) +
              (stdBump x : ℂ) * ((1 / M : ℝ) • deriv ψ (γ + x / M))) u
          = (iteratedDeriv 2 (fun y : ℝ => (stdBump y : ℂ)) u * ψ (γ + u / M) +
              deriv (fun y : ℝ => (stdBump y : ℂ)) u * ((1 / M : ℝ) • deriv ψ (γ + u / M))) +
            (deriv (fun y : ℝ => (stdBump y : ℂ)) u * ((1 / M : ℝ) • deriv ψ (γ + u / M)) +
              (stdBump u : ℂ) * ((1 / M : ℝ) • ((1 / M : ℝ) • iteratedDeriv 2 ψ (γ + u / M)))) :=
            (ht1.add ht2).deriv
        _ = _ := by rw [smul_smul]; ring
    have hHM_bound2 : ∀ u : ℝ, |u| ≤ 1 →
        ‖iteratedDeriv 2 HM u‖ ≤ (B2 * K1 + 2 * B1 * K1 + B0 * K2) / M := by
      intro u hu
      rw [hHM_d2 u]
      have h1 : ‖iteratedDeriv 2 (fun x : ℝ => (stdBump x : ℂ)) u * ψ (γ + u / M)‖ ≤ B2 * K1 / M := by
        rw [norm_mul]
        calc _ ≤ B2 * (K1 / M) := mul_le_mul (hB2 u) (hψ_mvt u hu) (norm_nonneg _) hB2_nn
          _ = B2 * K1 / M := by ring
      have h2 : ‖2 * (deriv (fun x : ℝ => (stdBump x : ℂ)) u *
          ((1 / M : ℝ) • deriv ψ (γ + u / M)))‖ ≤ 2 * B1 * K1 / M := by
        rw [norm_mul, Complex.norm_ofNat, norm_mul, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / M)]
        calc 2 * (‖deriv (fun x : ℝ => (stdBump x : ℂ)) u‖ * (1 / M * ‖deriv ψ (γ + u / M)‖))
            ≤ 2 * (B1 * (1 / M * K1)) := by gcongr; exact hB1 u; exact hK1 _
          _ = 2 * B1 * K1 / M := by ring
      have h3 : ‖(stdBump u : ℂ) * (((1 / M : ℝ) * (1 / M : ℝ)) • iteratedDeriv 2 ψ (γ + u / M))‖ ≤
          B0 * K2 / M := by
        rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (1 / M) * (1 / M))]
        have hM2 : (1 / M) * (1 / M) ≤ 1 / M := by
          have : 1 / M ≤ 1 := (div_le_one hM_pos).mpr hM
          nlinarith [show (0 : ℝ) < 1 / M by positivity]
        calc ‖(stdBump u : ℂ)‖ * ((1 / M * (1 / M)) * ‖iteratedDeriv 2 ψ (γ + u / M)‖)
            ≤ B0 * ((1 / M) * K2) := by
              gcongr; exact hB0 u; exact hK2 _
          _ = B0 * K2 / M := by ring
      calc ‖_ + _ + _‖ ≤ ‖_ + _‖ + ‖_‖ := norm_add_le _ _
        _ ≤ ‖_‖ + ‖_‖ + ‖_‖ := by gcongr; exact norm_add_le _ _
        _ ≤ B2 * K1 / M + 2 * B1 * K1 / M + B0 * K2 / M := by linarith
        _ = (B2 * K1 + 2 * B1 * K1 + B0 * K2) / M := by ring
    -- Integrate ‖HM‖ and ‖iteratedDeriv 2 HM‖ over [-1, 1]
    have hint_HM0 : ∫ u : ℝ, ‖HM u‖ ≤ 2 * (B0 * K1 / M) := by
      have hsupp : Function.support (fun u : ℝ => ‖HM u‖) ⊆ Set.Icc (-1) 1 := by
        intro u hu
        rw [Function.mem_support, norm_ne_zero_iff] at hu
        exact abs_le.mp (by by_contra hgt; push Not at hgt; exact hu (hHM_supp u hgt.le))
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-1) 1)
        (fun u hu => by
          by_contra hne; exact hu (hsupp (Function.mem_support.mpr hne)))]
      calc ∫ u in Set.Icc (-1 : ℝ) 1, ‖HM u‖
          ≤ ∫ _u in Set.Icc (-1 : ℝ) 1, (B0 * K1 / M) := by
            refine setIntegral_mono_on (hHM_smooth.continuous.norm.integrableOn_Icc)
              (integrableOn_const (by simp [Real.volume_Icc])) measurableSet_Icc
              fun u hu => hHM_bound0 u (abs_le.mpr hu)
        _ = 2 * (B0 * K1 / M) := by simp [Real.volume_Icc, Measure.real]; norm_num
    have hint_HM2 : ∫ u : ℝ, ‖iteratedDeriv 2 HM u‖ ≤
        2 * ((B2 * K1 + 2 * B1 * K1 + B0 * K2) / M) := by
      have hsupp : Function.support (fun u : ℝ => ‖iteratedDeriv 2 HM u‖) ⊆ Set.Icc (-1) 1 := by
        intro u hu
        rw [Function.mem_support, norm_ne_zero_iff] at hu
        exact abs_le.mp (by by_contra hgt; push Not at hgt; exact hu (hHM_d2_supp u hgt.le))
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-1) 1)
        (fun u hu => by
          by_contra hne; exact hu (hsupp (Function.mem_support.mpr hne)))]
      calc ∫ u in Set.Icc (-1 : ℝ) 1, ‖iteratedDeriv 2 HM u‖
          ≤ ∫ _u in Set.Icc (-1 : ℝ) 1, ((B2 * K1 + 2 * B1 * K1 + B0 * K2) / M) := by
            refine setIntegral_mono_on
              (((smooth_to_c2 hHM_smooth).continuous_iteratedDeriv 2 le_rfl).norm.integrableOn_Icc)
              (integrableOn_const (by simp [Real.volume_Icc])) measurableSet_Icc
              fun u hu => hHM_bound2 u (abs_le.mpr hu)
        _ = 2 * ((B2 * K1 + 2 * B1 * K1 + B0 * K2) / M) := by
            simp [Real.volume_Icc, Measure.real]; norm_num
    -- Apply norm_fourier_decay_sq to HM and sum over t ∈ T
    set D : ℝ := 2 * (B0 * K1 + (B2 * K1 + 2 * B1 * K1 + B0 * K2) / (4 * Real.pi ^ 2))
    have hD_nn : 0 ≤ D := by positivity
    have hterm : ∀ t : T, ‖𝓕 ψ2 t.1‖ ≤ (D / M) * ((1 : ℝ) / (M * (1 + (t.1 / M) ^ 2))) := by
      intro t
      rw [hψ2_eq, fourier_scaled_shift HM γ M t.1 hM_pos, norm_mul, norm_div,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos]
      have hdec := norm_fourier_decay_sq (smooth_to_c2 hHM_smooth) hHM_cs (t.1 / M)
      have hnum : (∫ x : ℝ, ‖HM x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 HM x‖) / (4 * Real.pi ^ 2) ≤ D / M := by
        have h1 : (∫ x : ℝ, ‖iteratedDeriv 2 HM x‖) / (4 * Real.pi ^ 2) ≤
            (2 * ((B2 * K1 + 2 * B1 * K1 + B0 * K2) / M)) / (4 * Real.pi ^ 2) :=
          div_le_div_of_nonneg_right hint_HM2 (by positivity)
        have heq : 2 * (B0 * K1 / M) + (2 * ((B2 * K1 + 2 * B1 * K1 + B0 * K2) / M)) / (4 * Real.pi ^ 2) =
            D / M := by dsimp only [D]; ring
        linarith
      calc (1 / M) * ‖𝓕 HM (t.1 / M)‖
          ≤ (1 / M) * ((D / M) / (1 + (t.1 / M) ^ 2)) := by
            gcongr
            exact le_trans hdec (div_le_div_of_nonneg_right hnum (by positivity))
        _ = (D / M) * (1 / (M * (1 + (t.1 / M) ^ 2))) := by field_simp
    have hsum_scaled := hCδ M hM
    have hsum_ψ2 := summable_fourier_over_sep hδ hsep (smooth_to_c2 hψ2_smooth) hψ2_cs
    calc ‖∑' t : T, 𝓕 ψ2 t.1‖
        ≤ ∑' t : T, ‖𝓕 ψ2 t.1‖ := norm_tsum_le_tsum_norm hsum_ψ2.norm
      _ ≤ ∑' t : T, (D / M) * (1 / (M * (1 + (t.1 / M) ^ 2))) :=
          hsum_ψ2.norm.tsum_le_tsum hterm (hsum_scaled.1.mul_left _)
      _ = (D / M) * ∑' t : T, (1 / (M * (1 + (t.1 / M) ^ 2))) := tsum_mul_left
      _ ≤ (D / M) * Cδ := mul_le_mul_of_nonneg_left hsum_scaled.2 (by positivity)
      _ = (D * Cδ) / M := by ring
  -- Let M → ∞ to conclude ‖∑' t : T, 𝓕 ψ t.1‖ = 0
  set E := 2 * (B0 * K1 + (B2 * K1 + 2 * B1 * K1 + B0 * K2) / (4 * Real.pi ^ 2)) * Cδ
  have hnorm0 : ‖∑' t : T, 𝓕 ψ t.1‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hpos
    push Not at hpos
    set M := max 1 (E / ‖∑' t : T, 𝓕 ψ t.1‖ + 1)
    have h1 := hbound_M M (le_max_left _ _)
    have hM_gt : E / ‖∑' t : T, 𝓕 ψ t.1‖ < M := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have h2 : E / M < ‖∑' t : T, 𝓕 ψ t.1‖ := by
      rw [div_lt_iff₀ hM_pos]
      have := (div_lt_iff₀ hpos).mp hM_gt
      linarith
    linarith
  exact norm_eq_zero.mp hnorm0

/- Patching over all `ψ ∈ C_c^∞(ℝ)` and DCT to the smoothed comb `g_n` -/

lemma fourier_integrable_of_integrable {f : ℝ → ℂ} (hf : Integrable f volume) (t : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) * f v) volume :=
  hf.norm.mono'
    (((by fun_prop : Continuous fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable)
    (Eventually.of_forall fun v => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul])

lemma fourierInv_smooth_of_hasCompactSupport {u : ℝ → ℂ}
    (hu_cont : Continuous u) (hu_cs : HasCompactSupport u) :
    ContDiff ℝ (⊤ : ℕ∞) (𝓕⁻ u) := by
  let G : ℂ → ℂ := fun z => ∫ y : ℝ, Complex.exp (2 * Real.pi * Complex.I * z * (y : ℂ)) * u y
  have hG_diff : Differentiable ℂ G := by
    intro z₀
    obtain ⟨B, hB⟩ := hu_cs.isBounded.subset_closedBall (0 : ℝ)
    set M0 : ℝ := max B 0 + 1
    obtain ⟨Ku, hKu⟩ := hu_cont.bounded_above_of_compact_support hu_cs
    let Cg : ℝ := 2 * Real.pi * M0 * Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M0) * Ku
    let bound : ℝ → ℝ := (Set.Icc (-M0) M0).indicator (fun _ => Cg)
    let f : ℂ → ℝ → ℂ := fun z y => Complex.exp (2 * Real.pi * Complex.I * z * (y : ℂ)) * u y
    let f' : ℂ → ℝ → ℂ := fun z y =>
      (2 * Real.pi * Complex.I * (y : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * z * (y : ℂ)) * u y
    have hu_zero : ∀ y : ℝ, M0 < |y| → u y = 0 := fun y hy => by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hd : |y| ≤ B := by simpa [Real.dist_eq] using hB hmem
      linarith [le_max_left B 0]
    have hf_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (f z) volume :=
      Eventually.of_forall fun z => (by fun_prop : Continuous (f z)).aestronglyMeasurable
    have hf_int : Integrable (f z₀) volume := by
      have hcs : HasCompactSupport (f z₀) := hu_cs.mul_left
      exact (by fun_prop : Continuous (f z₀)).integrable_of_hasCompactSupport hcs
    have hf'_meas : AEStronglyMeasurable (f' z₀) volume :=
      (by fun_prop : Continuous (f' z₀)).aestronglyMeasurable
    have hbound : ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball z₀ 1, ‖f' z y‖ ≤ bound y := by
      refine Eventually.of_forall fun y z hz => ?_
      dsimp only [f']
      by_cases hy : y ∈ Set.Icc (-M0) M0
      · rw [show bound y = Cg from Set.indicator_of_mem hy _]
        have hyM : |y| ≤ M0 := abs_le.mpr hy
        have hzM : ‖z‖ ≤ ‖z₀‖ + 1 := by
          rw [Metric.mem_ball, dist_eq_norm] at hz
          linarith [norm_sub_norm_le z z₀]
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs]
        have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * z * (y : ℂ))‖ ≤
            Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M0) := by
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have hre : (2 * Real.pi * Complex.I * z * (y : ℂ)).re = -(2 * Real.pi * z.im * y) := by
            simp [Complex.mul_re, Complex.mul_im]
          rw [hre]
          have hzim : |z.im| ≤ ‖z₀‖ + 1 := le_trans (Complex.abs_im_le_norm z) hzM
          calc -(2 * Real.pi * z.im * y) ≤ |2 * Real.pi * z.im * y| := neg_le_abs _
            _ = 2 * Real.pi * |z.im| * |y| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
            _ ≤ 2 * Real.pi * (‖z₀‖ + 1) * M0 := by
              have h1 : 2 * Real.pi * |z.im| ≤ 2 * Real.pi * (‖z₀‖ + 1) := by gcongr
              calc 2 * Real.pi * |z.im| * |y| ≤ 2 * Real.pi * (‖z₀‖ + 1) * |y| :=
                    mul_le_mul_of_nonneg_right h1 (abs_nonneg y)
                _ ≤ 2 * Real.pi * (‖z₀‖ + 1) * M0 :=
                    mul_le_mul_of_nonneg_left hyM (by positivity)
        have hKu_nn : 0 ≤ Ku := le_trans (norm_nonneg _) (hKu 0)
        calc 2 * Real.pi * |y| * ‖Complex.exp (2 * Real.pi * Complex.I * z * (y : ℂ))‖ * ‖u y‖
            ≤ (2 * Real.pi * M0 * Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M0)) * Ku := by
              gcongr
              exact hKu y
          _ = Cg := rfl
      · rw [show bound y = 0 from Set.indicator_of_notMem hy _]
        have hgt : M0 < |y| := by
          by_contra hle; push Not at hle; exact hy (abs_le.mp hle)
        simp [hu_zero y hgt]
    have hbound_int : Integrable bound volume := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (by simp [Real.volume_Icc])
    have hdiff : ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball z₀ 1, HasDerivAt (fun w => f w y) (f' z y) z :=
      Eventually.of_forall fun y z _ => by
        have hlin : HasDerivAt (fun w : ℂ => 2 * Real.pi * Complex.I * w * (y : ℂ))
            (2 * Real.pi * Complex.I * (y : ℂ)) z := by
          simpa using ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)).mul_const (y : ℂ)
        simpa [f, f', mul_comm, mul_assoc] using (hlin.cexp.mul_const (u y))
    have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds z₀ zero_lt_one) hf_meas hf_int hf'_meas hbound hbound_int hdiff
    exact hres.2.differentiableAt
  have hG_eq : 𝓕⁻ u = fun ξ : ℝ => G (ξ : ℂ) := by
    funext ξ
    rw [Real.fourierInv_eq']
    congr 1; funext y
    simp only [Real.inner_apply, smul_eq_mul]
    congr 2; push_cast; ring
  rw [hG_eq]
  exact ((hG_diff.contDiff.restrict_scalars ℝ).of_le le_top).comp
    (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞)))

lemma exists_finset_min_sep (s : Finset ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → d ≤ |a - b| := by
  classical
  let P : Finset (ℝ × ℝ) := (s ×ˢ s).filter fun p => p.1 ≠ p.2
  by_cases hP : P.Nonempty
  · let D : Finset ℝ := P.image fun p => |p.1 - p.2|
    have hD : D.Nonempty := hP.image _
    refine ⟨D.min' hD, ?_, ?_⟩
    · rcases Finset.mem_image.mp (Finset.min'_mem D hD) with ⟨p, hp, heq⟩
      rw [← heq]
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
    · intro a ha b hb hne
      have hp : (a, b) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hne⟩
      exact Finset.min'_le D |a - b| (Finset.mem_image.mpr ⟨(a, b), hp, rfl⟩)
  · refine ⟨1, zero_lt_one, fun a ha b hb hne => ?_⟩
    exact absurd ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hne⟩⟩ hP

lemma sum_fourier_eq_tsum_atomic_of_local {S T Z0 : Set ℝ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hsep : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → δ ≤ |t₁ - t₂|)
    (hS_bdd : Bornology.IsBounded S) (hS_meas : MeasurableSet S)
    (hS_vol : volume S = 1) (htile : TilesR S T)
    (h0_mem : (0 : ℝ) ∈ Z0) (hZ_sub : ∀ ξ : ℝ, F S (ξ : ℂ) = 0 → ξ ∈ Z0)
    (hZ0_fin : ∀ r : ℝ, 1 ≤ r → (Z0 ∩ Set.Icc (-r) r).Finite)
    {rOf : ℝ → ℝ} (hrOf_pos : ∀ γ ∈ Z0, 0 < rOf γ)
    {c : ℝ → ℂ}
    (hlocal : ∀ γ ∈ Z0, ∀ ψ : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.closedBall γ (rOf γ) →
      ∑' t : T, 𝓕 ψ t.1 = c γ * ψ γ)
    {ψ : ℝ → ℂ} (hψ_diff : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ) :
    ∑' t : T, 𝓕 ψ t.1 = ∑' γ : Z0, c γ.1 * ψ γ.1 := by
  classical
  obtain ⟨B, hB⟩ := hψ_cs.isBounded.subset_closedBall (0 : ℝ)
  set R1 : ℝ := max B 1
  have hK_fin : (Z0 ∩ Set.Icc (-R1) R1).Finite := hZ0_fin R1 (le_max_right _ _)
  let Kfin : Finset ℝ := hK_fin.toFinset
  have hsupp_sub : ∀ γ : Z0, γ.1 ∉ Kfin → ψ γ.1 = 0 := by
    intro γ hnot
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hnot
    rw [Set.Finite.mem_toFinset]
    have hd : |γ.1| ≤ B := by simpa [Real.dist_eq] using hB hmem
    exact ⟨γ.2, abs_le.mp (le_trans hd (le_max_left _ _))⟩
  obtain ⟨sepR, hsepR_pos, hsepR_le⟩ := exists_finset_min_sep Kfin
  let rad : ℝ → ℝ := fun γ => min (rOf γ) (sepR / 3)
  have hrad_pos : ∀ γ ∈ Kfin, 0 < rad γ := fun γ hγ =>
    lt_min (hrOf_pos γ (hK_fin.mem_toFinset.mp hγ).1) (div_pos hsepR_pos (by norm_num))
  let βOf : ∀ γ : ℝ, γ ∈ Kfin → ContDiffBump γ := fun γ hγ =>
    ⟨rad γ / 2, rad γ, half_pos (hrad_pos γ hγ), half_lt_self (hrad_pos γ hγ)⟩
  let piece : ℝ → ℝ → ℂ := fun γ ξ =>
    if hγ : γ ∈ Kfin then ((βOf γ hγ ξ : ℝ) : ℂ) * ψ ξ else 0
  have hpiece_smooth : ∀ γ ∈ Kfin, ContDiff ℝ (⊤ : ℕ∞) (piece γ) := fun γ hγ => by
    simp only [piece, dif_pos hγ]
    exact ((Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp (βOf γ hγ).contDiff).mul hψ_diff
  have hpiece_cs : ∀ γ ∈ Kfin, HasCompactSupport (piece γ) := fun γ hγ => by
    simp only [piece, dif_pos hγ]
    exact hψ_cs.mul_left
  have hpiece_eval : ∀ γ ∈ Kfin, ∑' t : T, 𝓕 (piece γ) t.1 = c γ * ψ γ := fun γ hγ => by
    have hγZ0 : γ ∈ Z0 := (hK_fin.mem_toFinset.mp hγ).1
    have hts : tsupport (piece γ) ⊆ Metric.closedBall γ (rOf γ) := by
      simp only [piece, dif_pos hγ]
      calc tsupport (fun ξ => ((βOf γ hγ ξ : ℝ) : ℂ) * ψ ξ)
          ⊆ tsupport (fun ξ => ((βOf γ hγ ξ : ℝ) : ℂ)) := tsupport_mul_subset_left
        _ ⊆ tsupport (βOf γ hγ) := tsupport_comp_subset Complex.ofReal_zero _
        _ = Metric.closedBall γ (rad γ) := (βOf γ hγ).tsupport_eq
        _ ⊆ Metric.closedBall γ (rOf γ) := Metric.closedBall_subset_closedBall (min_le_left _ _)
    have hval : piece γ γ = ψ γ := by
      simp only [piece, dif_pos hγ]
      have h1 := (βOf γ hγ).one_of_mem_closedBall (Metric.mem_closedBall_self (βOf γ hγ).rIn_pos.le)
      simp [h1]
    rw [hlocal γ hγZ0 (piece γ) (hpiece_smooth γ hγ) (hpiece_cs γ hγ) hts, hval]
  let rem : ℝ → ℂ := fun ξ => ψ ξ - ∑ γ ∈ Kfin, piece γ ξ
  have hrem_smooth : ContDiff ℝ (⊤ : ℕ∞) rem :=
    hψ_diff.sub (ContDiff.sum fun γ hγ => hpiece_smooth γ hγ)
  have hsum_pc_zero : ∀ ξ, ξ ∉ tsupport ψ → ∑ γ ∈ Kfin, piece γ ξ = 0 := fun ξ hξ =>
    Finset.sum_eq_zero fun γ hγ => by
      simp only [piece, dif_pos hγ, image_eq_zero_of_notMem_tsupport hξ, mul_zero]
  have hrem_ts : tsupport rem ⊆ tsupport ψ := by
    refine closure_minimal (fun ξ hξ => ?_) (isClosed_tsupport ψ)
    by_contra hnot
    exact hξ (by simp [rem, image_eq_zero_of_notMem_tsupport hnot, hsum_pc_zero ξ hnot])
  have hrem_cs : HasCompactSupport rem :=
    HasCompactSupport.of_support_subset_isCompact hψ_cs ((subset_tsupport rem).trans hrem_ts)
  have hrem_disj : ∀ ξ ∈ tsupport rem, F S (ξ : ℂ) ≠ 0 := by
    intro ξ hξ hF0
    by_cases hξK : ξ ∈ Kfin
    · have hnbhd : Metric.ball ξ (rad ξ / 2) ∈ 𝓝 ξ :=
        Metric.ball_mem_nhds ξ (half_pos (hrad_pos ξ hξK))
      have hrem0 : rem =ᶠ[𝓝 ξ] 0 := by
        filter_upwards [hnbhd] with x hx
        rw [Metric.mem_ball, Real.dist_eq] at hx
        have hsum_eq : ∑ γ ∈ Kfin, piece γ x = piece ξ x := by
          refine Finset.sum_eq_single ξ (fun γ hγ hne => ?_) (fun hnot => absurd hξK hnot)
          simp only [piece, dif_pos hγ]
          have hdist : sepR ≤ |γ - ξ| := hsepR_le γ hγ ξ hξK hne
          have hxγ : rad γ ≤ |x - γ| := by
            have hradγ : rad γ ≤ sepR / 3 := min_le_right _ _
            have hradξ : rad ξ / 2 ≤ sepR / 6 := by linarith [min_le_right (rOf ξ) (sepR / 3)]
            have htri : |γ - ξ| ≤ |x - γ| + |x - ξ| := by
              have := abs_add_le (γ - x) (x - ξ)
              rw [show (γ - x) + (x - ξ) = γ - ξ by ring, abs_sub_comm γ x] at this
              exact this
            linarith
          have h0 : βOf γ hγ x = 0 :=
            (βOf γ hγ).zero_of_le_dist (by rw [Real.dist_eq]; exact hxγ)
          simp [h0]
        have h1 : βOf ξ hξK x = 1 :=
          (βOf ξ hξK).one_of_mem_closedBall (by
            rw [Metric.mem_closedBall, Real.dist_eq]; exact hx.le)
        simp [rem, hsum_eq, piece, dif_pos hξK, h1]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hrem0) hξ
    · have hξ_gt : R1 < |ξ| := by
        by_contra hle; push Not at hle
        exact hξK (hK_fin.mem_toFinset.mpr ⟨hZ_sub ξ hF0, abs_le.mp hle⟩)
      have hξ_not_ψ : ξ ∉ tsupport ψ := by
        intro hmem
        have hd : |ξ| ≤ B := by simpa [Real.dist_eq] using hB hmem
        linarith [le_max_left B 1]
      exact hξ_not_ψ (hrem_ts hξ)
  have hrem_0 : rem 0 = 0 := by
    have h0K : (0 : ℝ) ∈ Kfin := hK_fin.mem_toFinset.mpr ⟨h0_mem, by
      constructor <;> linarith [le_max_right B 1]⟩
    have hsum_eq : ∑ γ ∈ Kfin, piece γ 0 = piece 0 0 := by
      refine Finset.sum_eq_single 0 (fun γ hγ hne => ?_) (fun hnot => absurd h0K hnot)
      simp only [piece, dif_pos hγ]
      have hdist : sepR ≤ |γ - 0| := hsepR_le γ hγ 0 h0K hne
      have hge : rad γ ≤ |0 - γ| := by
        rw [abs_sub_comm]; linarith [min_le_right (rOf γ) (sepR / 3), hsepR_pos]
      have h0 : βOf γ hγ 0 = 0 :=
        (βOf γ hγ).zero_of_le_dist (by rw [Real.dist_eq]; exact hge)
      simp [h0]
    have h1 : βOf 0 h0K 0 = 1 :=
      (βOf 0 h0K).one_of_mem_closedBall (Metric.mem_closedBall_self (βOf 0 h0K).rIn_pos.le)
    simp [rem, hsum_eq, piece, dif_pos h0K, h1]
  have hsum_rem : ∑' t : T, 𝓕 rem t.1 = 0 := by
    rw [sum_fourier_eq_eval_zero_of_disjoint_Z hS_bdd hS_meas hS_vol htile hrem_smooth hrem_cs hrem_disj,
      hrem_0]
  have hF_split : ∀ t : ℝ, 𝓕 ψ t = 𝓕 rem t + ∑ γ ∈ Kfin, 𝓕 (piece γ) t := by
    intro t
    have hψ_eq : ψ = fun ξ => rem ξ + ∑ γ ∈ Kfin, piece γ ξ := by funext ξ; simp [rem]
    rw [hψ_eq]
    have hint_rem : Integrable rem volume := hrem_smooth.continuous.integrable_of_hasCompactSupport hrem_cs
    have hint_pc : ∀ γ ∈ Kfin, Integrable (piece γ) volume := fun γ hγ =>
      (hpiece_smooth γ hγ).continuous.integrable_of_hasCompactSupport (hpiece_cs γ hγ)
    have hsum_int : Integrable (fun ξ => ∑ γ ∈ Kfin, piece γ ξ) volume :=
      integrable_finsetSum Kfin hint_pc
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_add, smul_eq_mul]
    rw [integral_add (fourier_integrable_of_integrable hint_rem t)
      (fourier_integrable_of_integrable hsum_int t)]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum Kfin fun γ hγ => fourier_integrable_of_integrable (hint_pc γ hγ) t]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_eq_mul]
  have hs_rem := summable_fourier_over_sep hδ_pos hsep (smooth_to_c2 hrem_smooth) hrem_cs
  have hs_pc : ∀ γ ∈ Kfin, Summable (fun t : T => 𝓕 (piece γ) t.1) := fun γ hγ =>
    summable_fourier_over_sep hδ_pos hsep (smooth_to_c2 (hpiece_smooth γ hγ)) (hpiece_cs γ hγ)
  have hs_sum : Summable (fun t : T => ∑ γ ∈ Kfin, 𝓕 (piece γ) t.1) := by
    have hgen : ∀ s : Finset ℝ, (∀ γ ∈ s, Summable (fun t : T => 𝓕 (piece γ) t.1)) →
        Summable (fun t : T => ∑ γ ∈ s, 𝓕 (piece γ) t.1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | @insert a s ha ih =>
        intro hs
        simp_rw [Finset.sum_insert ha]
        exact (hs a (Finset.mem_insert_self _ _)).add
          (ih fun γ hγ => hs γ (Finset.mem_insert_of_mem hγ))
    exact hgen Kfin hs_pc
  have htsum_lhs : ∑' t : T, 𝓕 ψ t.1 = ∑ γ ∈ Kfin, c γ * ψ γ := by
    calc ∑' t : T, 𝓕 ψ t.1
        = ∑' t : T, (𝓕 rem t.1 + ∑ γ ∈ Kfin, 𝓕 (piece γ) t.1) := by
          congr 1; funext t; exact hF_split t.1
      _ = (∑' t : T, 𝓕 rem t.1) + ∑' t : T, ∑ γ ∈ Kfin, 𝓕 (piece γ) t.1 :=
          hs_rem.tsum_add hs_sum
      _ = ∑ γ ∈ Kfin, ∑' t : T, 𝓕 (piece γ) t.1 := by
          rw [hsum_rem, zero_add, Summable.tsum_finsetSum hs_pc]
      _ = ∑ γ ∈ Kfin, c γ * ψ γ := Finset.sum_congr rfl hpiece_eval
  rw [htsum_lhs]
  let fEmb : {x // x ∈ Kfin} ↪ Z0 :=
    ⟨fun p => ⟨p.1, (hK_fin.mem_toFinset.mp p.2).1⟩,
      fun a b h => Subtype.ext (congrArg (Subtype.val : Z0 → ℝ) h)⟩
  let Ksub : Finset Z0 := Kfin.attach.map fEmb
  rw [tsum_eq_sum (s := Ksub)]
  · rw [Finset.sum_map]
    exact (Finset.sum_attach Kfin fun γ => c γ * ψ γ).symm
  · intro γ hnot
    have hnotK : γ.1 ∉ Kfin := by
      intro hmem
      apply hnot
      exact Finset.mem_map.mpr ⟨⟨γ.1, hmem⟩, Finset.mem_attach _ _, rfl⟩
    rw [hsupp_sub γ hnotK, mul_zero]

lemma exists_atomic_coeffs_of_tilesR {S T : Set ℝ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hsep : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → δ ≤ |t₁ - t₂|)
    (hS_bdd : Bornology.IsBounded S) (hS_meas : MeasurableSet S)
    (hS_vol : volume S = 1) (htile : TilesR S T) :
    ∃ (Z0 : Set ℝ) (A_Z0 C_atom : ℝ) (c : ℝ → ℂ),
      0 ≤ A_Z0 ∧ 0 ≤ C_atom ∧ Z0.Countable ∧
      (∀ r : ℝ, 1 ≤ r → (Z0 ∩ Set.Icc (-r) r).Finite ∧ ((Z0 ∩ Set.Icc (-r) r).ncard : ℝ) ≤ A_Z0 * r) ∧
      (∀ γ : ℝ, ‖c γ‖ ≤ C_atom) ∧
      (∀ ψ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∑' t : T, 𝓕 ψ t.1 = ∑' γ : Z0, c γ.1 * ψ γ.1) := by
  classical
  obtain ⟨Cδ, hCδ_nn, hCδ⟩ := summable_and_bound_scaled_inv_sq hδ_pos hsep
  obtain ⟨R0, hR0⟩ := hS_bdd.subset_closedBall (0 : ℝ)
  set R : ℝ := max R0 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hS_sub : S ⊆ Set.Icc (-R) R := fun t ht => by
    have h1 : |t| ≤ R0 := by simpa [Real.dist_eq] using hR0 ht
    exact abs_le.mp (le_trans h1 (le_max_left _ _))
  let Z : Set ℝ := {ξ : ℝ | F S (ξ : ℂ) = 0}
  let Z0 : Set ℝ := insert (0 : ℝ) Z
  have hZ_growth := zero_set_linear_growth hR_pos.le hS_sub hS_meas hS_vol
  have h0_not_Z : (0 : ℝ) ∉ Z := by
    change F S (0 : ℂ) ≠ 0; rw [F_zero hS_vol]; exact one_ne_zero
  set A_Z0 : ℝ := 4 * Real.pi * R / Real.log 2 + 1
  have hZ0_count : ∀ r : ℝ, 1 ≤ r →
      (Z0 ∩ Set.Icc (-r) r).Finite ∧ ((Z0 ∩ Set.Icc (-r) r).ncard : ℝ) ≤ A_Z0 * r := by
    intro r hr
    have hZr := hZ_growth r (by linarith)
    have hsub : Z0 ∩ Set.Icc (-r) r ⊆ insert 0 (Z ∩ Set.Icc (-r) r) := by
      intro x hx
      rcases hx.1 with rfl | hxZ
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨hxZ, hx.2⟩
    have hfin : (Z0 ∩ Set.Icc (-r) r).Finite := (hZr.1.insert 0).subset hsub
    refine ⟨hfin, ?_⟩
    have hnc : (Z0 ∩ Set.Icc (-r) r).ncard ≤ (Z ∩ Set.Icc (-r) r).ncard + 1 :=
      le_trans (Set.ncard_le_ncard hsub (hZr.1.insert 0)) (Set.ncard_insert_le _ _)
    have hncR : ((Z0 ∩ Set.Icc (-r) r).ncard : ℝ) ≤ ((Z ∩ Set.Icc (-r) r).ncard : ℝ) + 1 := by
      exact_mod_cast hnc
    dsimp only [A_Z0]
    linarith [hZr.2]
  have hZ0_countable : Z0.Countable := by
    have hunion : Z0 = ⋃ n : ℕ, (Z0 ∩ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        refine ⟨n, hx, abs_le.mp (by linarith)⟩
      · rintro ⟨n, hx, _⟩; exact hx
    rw [hunion]
    exact Set.countable_iUnion fun n => (hZ0_count ((n : ℝ) + 1) (by linarith)).1.countable
  have hisol : ∀ γ ∈ Z0, ∃ r > 0, ∀ ξ ∈ Z0, ξ ∈ Metric.closedBall γ r → ξ = γ := by
    intro γ hγ
    have hfin := (hZ0_count (|γ| + 2) (by linarith [abs_nonneg γ])).1
    let Sfin : Finset ℝ := hfin.toFinset.erase γ
    by_cases hne : Sfin.Nonempty
    · set d := (Sfin.image fun ξ => |ξ - γ|).min' (hne.image _)
      have hd_pos : 0 < d := by
        have hm := Finset.min'_mem (Sfin.image fun ξ => |ξ - γ|) (hne.image _)
        rcases Finset.mem_image.mp hm with ⟨ξ, hξ, hd_eq⟩
        rw [show d = |ξ - γ| from hd_eq.symm]
        exact abs_pos.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hξ))
      refine ⟨min (1 / 2) (d / 2), lt_min (by norm_num) (by linarith), fun ξ hξ hball => ?_⟩
      by_contra hneγ
      rw [Metric.mem_closedBall, Real.dist_eq] at hball
      have hξ_bound : |ξ| ≤ |γ| + 2 := by
        have h1 : |ξ - γ| ≤ 1 / 2 := le_trans hball (min_le_left _ _)
        have h2 := abs_sub_abs_le_abs_sub ξ γ
        linarith
      have hξ_mem : ξ ∈ Sfin := Finset.mem_erase.mpr
        ⟨hneγ, hfin.mem_toFinset.mpr ⟨hξ, abs_le.mp hξ_bound⟩⟩
      have hge : d ≤ |ξ - γ| := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hξ_mem)
      have hle : |ξ - γ| ≤ d / 2 := le_trans hball (min_le_right _ _)
      linarith
    · refine ⟨1 / 2, by norm_num, fun ξ hξ hball => ?_⟩
      by_contra hneγ
      rw [Metric.mem_closedBall, Real.dist_eq] at hball
      have hξ_bound : |ξ| ≤ |γ| + 2 := by
        have := abs_sub_abs_le_abs_sub ξ γ; linarith
      exact hne ⟨ξ, Finset.mem_erase.mpr ⟨hneγ, hfin.mem_toFinset.mpr ⟨hξ, abs_le.mp hξ_bound⟩⟩⟩
  let rOf : ℝ → ℝ := fun γ => if h : γ ∈ Z0 then (hisol γ h).choose else 1
  have hrOf_pos : ∀ γ ∈ Z0, 0 < rOf γ := fun γ h => by
    simp only [rOf, dif_pos h]; exact (hisol γ h).choose_spec.1
  have hrOf_isol : ∀ γ ∈ Z0, ∀ ξ ∈ Z0, ξ ∈ Metric.closedBall γ (rOf γ) → ξ = γ := fun γ h => by
    simp only [rOf, dif_pos h]; exact (hisol γ h).choose_spec.2
  let bumpAt : ∀ γ : ℝ, γ ∈ Z0 → ContDiffBump γ := fun γ h =>
    ⟨rOf γ / 2, rOf γ, half_pos (hrOf_pos γ h), half_lt_self (hrOf_pos γ h)⟩
  let c : ℝ → ℂ := fun γ =>
    if h : γ ∈ Z0 then ∑' t : T, 𝓕 (fun ξ => ((bumpAt γ h ξ : ℝ) : ℂ)) t.1 else 0
  have hc_zero : c 0 = 1 := by
    have h0Z0 : (0 : ℝ) ∈ Z0 := Set.mem_insert 0 Z
    simp only [c, dif_pos h0Z0]
    let β : ContDiffBump (0 : ℝ) := bumpAt 0 h0Z0
    have hβ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => (β ξ : ℂ)) :=
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp β.contDiff
    have hβ_cs : HasCompactSupport (fun ξ => (β ξ : ℂ)) :=
      β.hasCompactSupport.comp_left Complex.ofReal_zero
    have hβ_disj : ∀ ξ ∈ tsupport (fun ξ => (β ξ : ℂ)), F S (ξ : ℂ) ≠ 0 := by
      intro ξ hξ hF0
      have hmem : ξ ∈ Metric.closedBall (0 : ℝ) (rOf 0) := by
        have hsub : tsupport (fun x => (β x : ℂ)) ⊆ tsupport β :=
          tsupport_comp_subset Complex.ofReal_zero _
        have := hsub hξ
        rwa [β.tsupport_eq] at this
      have hξ0 : ξ = 0 := hrOf_isol 0 h0Z0 ξ (Set.mem_insert_of_mem 0 hF0) hmem
      subst hξ0
      exact h0_not_Z hF0
    rw [sum_fourier_eq_eval_zero_of_disjoint_Z hS_bdd hS_meas hS_vol htile hβ_smooth hβ_cs hβ_disj]
    have h1 : β 0 = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
    simp [h1]
  have hlocal : ∀ γ (hγ : γ ∈ Z0) (ψ : ℝ → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.closedBall γ (rOf γ) →
      ∑' t : T, 𝓕 ψ t.1 = c γ * ψ γ := by
    intro γ hγ ψ hψ_diff hψ_cs hψ_ball
    let β : ContDiffBump γ := bumpAt γ hγ
    have hβ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => (β ξ : ℂ)) :=
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp β.contDiff
    have hβ_cs : HasCompactSupport (fun ξ => (β ξ : ℂ)) :=
      β.hasCompactSupport.comp_left Complex.ofReal_zero
    have hβγ : β γ = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
    by_cases hγ0 : γ = 0
    · subst hγ0
      rw [hc_zero, one_mul]
      refine sum_fourier_eq_eval_zero_of_disjoint_Z hS_bdd hS_meas hS_vol htile hψ_diff hψ_cs ?_
      intro ξ hξ hF0
      have hξ0 : ξ = 0 := hrOf_isol 0 hγ ξ (Set.mem_insert_of_mem 0 hF0) (hψ_ball hξ)
      subst hξ0; exact h0_not_Z hF0
    · let ψ0 : ℝ → ℂ := fun ξ => ψ ξ - ψ γ * (β ξ : ℂ)
      have hψ0_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ0 := hψ_diff.sub (contDiff_const.mul hβ_smooth)
      have hψ0_cs : HasCompactSupport ψ0 := hψ_cs.sub (hβ_cs.mul_left)
      have hψ0_van : ψ0 γ = 0 := by simp [ψ0, hβγ]
      have hψ0_ts : tsupport ψ0 ⊆ Metric.closedBall γ (rOf γ) := by
        have hβ_ts : tsupport (fun ξ => ψ γ * (β ξ : ℂ)) ⊆ Metric.closedBall γ (rOf γ) := by
          calc tsupport (fun ξ => ψ γ * (β ξ : ℂ)) ⊆ tsupport (fun ξ => (β ξ : ℂ)) :=
                tsupport_mul_subset_right
            _ ⊆ tsupport β := tsupport_comp_subset Complex.ofReal_zero _
            _ = Metric.closedBall γ (rOf γ) := β.tsupport_eq
        exact (tsupport_sub _ _).trans (Set.union_subset hψ_ball hβ_ts)
      have h0_not : (0 : ℝ) ∉ tsupport ψ0 := fun h0m =>
        hγ0 (hrOf_isol γ hγ 0 (Set.mem_insert 0 Z) (hψ0_ts h0m)).symm
      have hsupp_Z : ∀ ξ ∈ tsupport ψ0, F S (ξ : ℂ) = 0 → ξ = γ := fun ξ hξ hF0 =>
        hrOf_isol γ hγ ξ (Set.mem_insert_of_mem 0 hF0) (hψ0_ts hξ)
      have hsum0 : ∑' t : T, 𝓕 ψ0 t.1 = 0 :=
        sum_fourier_eq_zero_of_isolated_vanish hδ_pos hsep hS_bdd hS_meas hS_vol htile
          hγ0 hψ0_smooth hψ0_cs hψ0_van hsupp_Z h0_not
      have hF_lin : ∀ t : ℝ, 𝓕 ψ0 t = 𝓕 ψ t - ψ γ * 𝓕 (fun ξ => (β ξ : ℂ)) t := by
        intro t
        have hintψ : Integrable ψ volume := hψ_diff.continuous.integrable_of_hasCompactSupport hψ_cs
        have hintβ : Integrable (fun ξ => (β ξ : ℂ)) volume :=
          hβ_smooth.continuous.integrable_of_hasCompactSupport hβ_cs
        rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
          Real.fourier_real_eq_integral_exp_smul]
        simp_rw [ψ0, smul_sub, smul_eq_mul]
        rw [integral_sub (fourier_integrable_of_integrable hintψ t)
          (fourier_integrable_of_integrable (hintβ.const_mul (ψ γ)) t)]
        congr 1
        rw [← integral_const_mul]
        congr 1; funext ξ; ring
      have hsψ := summable_fourier_over_sep hδ_pos hsep (smooth_to_c2 hψ_diff) hψ_cs
      have hsβ := summable_fourier_over_sep hδ_pos hsep (smooth_to_c2 hβ_smooth) hβ_cs
      have hsub_sum : ∑' t : T, 𝓕 ψ0 t.1 =
          (∑' t : T, 𝓕 ψ t.1) - ψ γ * ∑' t : T, 𝓕 (fun ξ => (β ξ : ℂ)) t.1 := by
        calc ∑' t : T, 𝓕 ψ0 t.1
            = ∑' t : T, (𝓕 ψ t.1 - ψ γ * 𝓕 (fun ξ => (β ξ : ℂ)) t.1) := by
              congr 1; funext t; exact hF_lin t.1
          _ = (∑' t : T, 𝓕 ψ t.1) - ∑' t : T, (ψ γ * 𝓕 (fun ξ => (β ξ : ℂ)) t.1) :=
              hsψ.tsum_sub (hsβ.mul_left _)
          _ = (∑' t : T, 𝓕 ψ t.1) - ψ γ * ∑' t : T, 𝓕 (fun ξ => (β ξ : ℂ)) t.1 := by
              rw [tsum_mul_left]
      rw [hsum0] at hsub_sum
      have heq : ∑' t : T, 𝓕 ψ t.1 = ψ γ * ∑' t : T, 𝓕 (fun ξ => (β ξ : ℂ)) t.1 :=
        sub_eq_zero.mp hsub_sum.symm
      rw [heq, mul_comm]
      simp [c, dif_pos hγ, β]
  set K_std : ℝ := (∫ x : ℝ, ‖(stdBump x : ℂ)‖) +
    (∫ x : ℝ, ‖iteratedDeriv 2 (fun x : ℝ => (stdBump x : ℂ)) x‖) / (4 * Real.pi ^ 2)
  have hK_std_nn : 0 ≤ K_std := by positivity
  have hc_bound : ∀ γ : ℝ, ‖c γ‖ ≤ K_std * Cδ := by
    intro γ
    by_cases hγ : γ ∈ Z0
    · set M : ℝ := max 1 (2 / rOf γ)
      have hM1 : 1 ≤ M := le_max_left _ _
      have hM_pos : 0 < M := by linarith
      let ψ : ℝ → ℂ := fun ξ => (stdBump (M * (ξ - γ)) : ℂ)
      have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
        stdBump_smooth.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
      have hψ_ball : tsupport ψ ⊆ Metric.closedBall γ (rOf γ) := by
        refine closure_minimal (fun ξ hξ => ?_) Metric.isClosed_closedBall
        by_contra hnot
        rw [Metric.mem_closedBall, Real.dist_eq, not_le] at hnot
        have hge1 : 1 ≤ |M * (ξ - γ)| := by
          rw [abs_mul, abs_of_pos hM_pos]
          have hM2 : 2 / rOf γ ≤ M := le_max_right _ _
          have hrpos := hrOf_pos γ hγ
          have h1 : (2 / rOf γ) * rOf γ = 2 := by field_simp
          nlinarith
        have h0 : stdBump (M * (ξ - γ)) = 0 :=
          stdBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hge1)
        exact hξ (by simp [ψ, h0])
      have hψ_cs : HasCompactSupport ψ :=
        HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall γ (rOf γ))
          ((subset_tsupport ψ).trans hψ_ball)
      have hψγ : ψ γ = 1 := by
        simp only [ψ, sub_self, mul_zero]
        have h1 : stdBump 0 = 1 := stdBump.one_of_mem_closedBall (Metric.mem_closedBall_self stdBump.rIn_pos.le)
        simp [h1]
      have hev := hlocal γ hγ ψ hψ_smooth hψ_cs hψ_ball
      rw [hψγ, mul_one] at hev
      rw [← hev]
      have hχ_cs : HasCompactSupport (fun x : ℝ => (stdBump x : ℂ)) :=
        stdBump.hasCompactSupport.comp_left Complex.ofReal_zero
      have hsψ := summable_fourier_over_sep hδ_pos hsep (smooth_to_c2 hψ_smooth) hψ_cs
      have hscaled := hCδ M hM1
      calc ‖∑' t : T, 𝓕 ψ t.1‖ ≤ ∑' t : T, ‖𝓕 ψ t.1‖ := norm_tsum_le_tsum_norm hsψ.norm
        _ ≤ ∑' t : T, K_std * (1 / (M * (1 + (t.1 / M) ^ 2))) := by
            refine hsψ.norm.tsum_le_tsum (fun t => ?_) (hscaled.1.mul_left _)
            rw [show ψ = fun ξ => (stdBump (M * (ξ - γ)) : ℂ) from rfl,
              fourier_scaled_shift (fun x => (stdBump x : ℂ)) γ M t.1 hM_pos,
              norm_mul, norm_div, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hM_pos]
            have hdec := norm_fourier_decay_sq (smooth_to_c2 stdBump_smooth) hχ_cs (t.1 / M)
            calc (1 / M) * ‖𝓕 (fun x => (stdBump x : ℂ)) (t.1 / M)‖
                ≤ (1 / M) * (K_std / (1 + (t.1 / M) ^ 2)) := mul_le_mul_of_nonneg_left hdec (by positivity)
              _ = K_std * (1 / (M * (1 + (t.1 / M) ^ 2))) := by field_simp
        _ = K_std * ∑' t : T, (1 / (M * (1 + (t.1 / M) ^ 2))) := tsum_mul_left
        _ ≤ K_std * Cδ := mul_le_mul_of_nonneg_left hscaled.2 hK_std_nn
    · simp [c, dif_neg hγ]; positivity
  refine ⟨Z0, A_Z0, K_std * Cδ, c, by positivity, by positivity, hZ0_countable, hZ0_count, hc_bound,
    fun ψ hψ_diff hψ_cs => sum_fourier_eq_tsum_atomic_of_local hδ_pos hsep hS_bdd hS_meas hS_vol htile
      (Set.mem_insert 0 Z) (fun ξ hF0 => Set.mem_insert_of_mem 0 hF0) (fun r hr => (hZ0_count r hr).1)
      hrOf_pos hlocal hψ_diff hψ_cs⟩

lemma comb_eq_tsum_atomic {T Z0 : Set ℝ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hsep : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → δ ≤ |t₁ - t₂|)
    {c : ℝ → ℂ}
    (hglobal : ∀ ψ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∑' t : T, 𝓕 ψ t.1 = ∑' γ : Z0, c γ.1 * ψ γ.1)
    (φ0 : ContDiffBump (0 : ℝ)) (hφ0_rOut : φ0.rOut ≤ 1 / 2)
    (n : ℕ) (x : ℝ)
    (hw_sum : Summable (fun γ : Z0 =>
      ‖c γ.1 * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) *
        𝓕 (fun u : ℝ => (φ0 u : ℂ)) (-(γ.1 / ((n : ℝ) + 1)))‖)) :
    ∑' γ : Z0,
      (c γ.1 * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) *
        𝓕 (fun u : ℝ => (φ0 u : ℂ)) (-(γ.1 / ((n : ℝ) + 1)))) *
        Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ)) =
      ∑' t : T, (φ0 (((n : ℝ) + 1) * (t.1 - x)) : ℂ) := by
  set N : ℝ := (n : ℝ) + 1
  have hN_pos : 0 < N := by positivity
  have hφ0_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (φ0 u : ℂ)) :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp φ0.contDiff
  let u : ℝ → ℂ := fun y => (φ0 (N * (y - x)) : ℂ)
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    hφ0_smooth.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hu_cs : HasCompactSupport u := by
    refine HasCompactSupport.intro (isCompact_closedBall x (1 / N)) fun y hy => ?_
    have hgt : 1 / N < |y - x| := by
      by_contra hle; push Not at hle; exact hy (by rwa [Metric.mem_closedBall, Real.dist_eq])
    have hge : φ0.rOut ≤ |N * (y - x)| := by
      rw [abs_mul, abs_of_pos hN_pos]
      have h1 : N * (1 / N) = 1 := by field_simp
      nlinarith
    have h0 : φ0 (N * (y - x)) = 0 := φ0.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hge)
    simp [u, h0]
  have hFu : ∀ ξ : ℝ, 𝓕⁻ u ξ =
      ((1 / N : ℝ) : ℂ) * 𝓕 (fun v : ℝ => (φ0 v : ℂ)) (-(ξ / N)) *
        Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) := by
    intro ξ
    rw [Real.fourierInv_eq_fourier_neg]
    have hsc := fourier_scaled_shift (fun v : ℝ => (φ0 v : ℂ)) x N (-ξ) hN_pos
    simpa [u, neg_div, div_eq_mul_inv] using hsc.trans (by
      have hexp : Complex.exp (↑(-2 * Real.pi * x * -ξ) * Complex.I) =
          Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) := by
        congr 1; push_cast; ring
      rw [hexp]; ring)
  let ψm : ℕ → ℝ → ℂ := fun m ξ => (stdBump (ξ / ((m : ℝ) + 1)) : ℂ) * 𝓕⁻ u ξ
  have hFu_smooth : ContDiff ℝ (⊤ : ℕ∞) (𝓕⁻ u) :=
    fourierInv_smooth_of_hasCompactSupport hu_smooth.continuous hu_cs
  have hψm_eq_glob : ∀ m : ℕ,
      ∑' t : T, 𝓕 (ψm m) t.1 =
        ∑' γ : Z0, (stdBump (γ.1 / ((m : ℝ) + 1)) : ℂ) *
          ((c γ.1 * ((1 / N : ℝ) : ℂ) * 𝓕 (fun v : ℝ => (φ0 v : ℂ)) (-(γ.1 / N))) *
            Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ))) := by
    intro m
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (ψm m) :=
      (stdBump_smooth.comp (contDiff_id.div_const _)).mul hFu_smooth
    have hcs : HasCompactSupport (ψm m) := by
      refine (HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((m : ℝ) + 1)) fun ξ hξ => ?_).mul_right
      have hgt : (m : ℝ) + 1 < |ξ| := by
        by_contra hle; push Not at hle
        exact hξ (by rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero])
      have hge : 1 ≤ |ξ / ((m : ℝ) + 1)| := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1), one_le_div (by positivity)]
        exact hgt.le
      have h0 : stdBump (ξ / ((m : ℝ) + 1)) = 0 :=
        stdBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hge)
      simp [h0]
    rw [hglobal (ψm m) hsm hcs]
    congr 1; funext γ
    simp only [ψm, hFu γ.1]
    ring
  have hRHS_lim : Tendsto
      (fun m : ℕ => ∑' γ : Z0, (stdBump (γ.1 / ((m : ℝ) + 1)) : ℂ) *
        ((c γ.1 * ((1 / N : ℝ) : ℂ) * 𝓕 (fun v : ℝ => (φ0 v : ℂ)) (-(γ.1 / N))) *
          Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ))))
      atTop (𝓝 (∑' γ : Z0,
        (c γ.1 * ((1 / N : ℝ) : ℂ) * 𝓕 (fun v : ℝ => (φ0 v : ℂ)) (-(γ.1 / N))) *
          Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ)))) := by
    refine tendsto_tsum_of_dominated_convergence hw_sum ?_ ?_
    · intro γ
      have hlim0 : Tendsto (fun m : ℕ => γ.1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have hstd : Tendsto (fun m : ℕ => (stdBump (γ.1 / ((m : ℝ) + 1)) : ℂ)) atTop (𝓝 1) := by
        have h0 : (stdBump 0 : ℂ) = 1 := by
          have := stdBump.one_of_mem_closedBall (Metric.mem_closedBall_self stdBump.rIn_pos.le)
          simp [this]
        rw [← h0]
        exact (stdBump_smooth.continuous.tendsto 0).comp hlim0
      simpa using hstd.mul tendsto_const_nhds
    · refine Eventually.of_forall fun m γ => ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg stdBump.nonneg]
      have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ))‖ = 1 := by
        have : 2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ) =
            ((2 * Real.pi * γ.1 * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [hexp, mul_one]
      exact mul_le_of_le_one_left (norm_nonneg _) stdBump.le_one
  have hFψm_conv : ∀ (m : ℕ) (t : ℝ),
      𝓕 (ψm m) t = ∫ v : ℝ, u (t - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v := by
    intro m t
    set Rm : ℝ := (m : ℝ) + 1
    have hRm_pos : 0 < Rm := by positivity
    have hχm_int : Integrable (fun ξ : ℝ => (stdBump (ξ / Rm) : ℂ)) volume := by
      have hcs : HasCompactSupport (fun ξ : ℝ => (stdBump (ξ / Rm) : ℂ)) :=
        HasCompactSupport.intro (isCompact_closedBall 0 Rm) fun ξ hξ => by
          have hgt : Rm < |ξ| := by
            by_contra hle; push Not at hle
            exact hξ (by rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero])
          have hge : 1 ≤ |ξ / Rm| := by
            rw [abs_div, abs_of_pos hRm_pos, one_le_div hRm_pos]; exact hgt.le
          have h0 : stdBump (ξ / Rm) = 0 :=
            stdBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hge)
          simp [h0]
      exact (stdBump_smooth.continuous.comp (continuous_id.div_const Rm)).integrable_of_hasCompactSupport hcs
    have hu_int : Integrable u volume := hu_smooth.continuous.integrable_of_hasCompactSupport hu_cs
    have hFub : Integrable (Function.uncurry fun ξ y : ℝ =>
        Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * ((stdBump (ξ / Rm) : ℂ) *
          (Complex.exp (↑(2 * Real.pi * (y * ξ)) * Complex.I) * u y)))
        (volume.prod volume) := by
      have hdom : Integrable (Function.uncurry fun ξ y : ℝ =>
          ‖(stdBump (ξ / Rm) : ℂ)‖ * ‖u y‖) (volume.prod volume) :=
        hχm_int.norm.mul_prod hu_int.norm
      have hcont_f : Continuous (Function.uncurry fun ξ y : ℝ =>
          Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * ((stdBump (ξ / Rm) : ℂ) *
            (Complex.exp (↑(2 * Real.pi * (y * ξ)) * Complex.I) * u y))) := by
        unfold Function.uncurry
        have h1 : Continuous (fun p : ℝ × ℝ => Complex.exp (↑(-2 * Real.pi * p.1 * t) * Complex.I)) := by fun_prop
        have h2 : Continuous (fun p : ℝ × ℝ => (stdBump (p.1 / Rm) : ℂ)) :=
          stdBump_smooth.continuous.comp (continuous_fst.div_const Rm)
        have h3 : Continuous (fun p : ℝ × ℝ => Complex.exp (↑(2 * Real.pi * (p.2 * p.1)) * Complex.I)) := by fun_prop
        have h4 : Continuous (fun p : ℝ × ℝ => u p.2) := hu_smooth.continuous.comp continuous_snd
        exact h1.mul (h2.mul (h3.mul h4))
      refine hdom.mono' hcont_f.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
    have hstep1 : 𝓕 (ψm m) t = ∫ y : ℝ, u y * (Rm * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) (Rm * (t - y))) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp_rw [ψm, Real.fourierInv_eq', Real.inner_apply, smul_eq_mul, ← integral_const_mul]
      change ∫ ξ : ℝ, ∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) *
          ((stdBump (ξ / Rm) : ℂ) * (Complex.exp (↑(2 * Real.pi * (y * ξ)) * Complex.I) * u y)) = _
      rw [integral_integral_swap hFub]
      congr 1; funext y
      have hinner : ∀ ξ : ℝ,
          Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * ((stdBump (ξ / Rm) : ℂ) *
            (Complex.exp (↑(2 * Real.pi * (y * ξ)) * Complex.I) * u y)) =
          u y * (Complex.exp (↑(-2 * Real.pi * ξ * (t - y)) * Complex.I) * (stdBump (ξ / Rm) : ℂ)) := by
        intro ξ
        have hexp : Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) *
            Complex.exp (↑(2 * Real.pi * (y * ξ)) * Complex.I) =
            Complex.exp (↑(-2 * Real.pi * ξ * (t - y)) * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        calc _ = u y * (Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) *
              Complex.exp (↑(2 * Real.pi * (y * ξ)) * Complex.I) * (stdBump (ξ / Rm) : ℂ)) := by ring
          _ = _ := by rw [hexp]
      simp_rw [hinner]
      rw [integral_const_mul]
      congr 1
      have hsc := fourier_scaled_shift (fun ξ : ℝ => (stdBump ξ : ℂ)) 0 (1 / Rm) (t - y) (by positivity)
      have hsimp : (fun ξ : ℝ => (stdBump (1 / Rm * (ξ - 0)) : ℂ)) =
          (fun ξ : ℝ => (stdBump (ξ / Rm) : ℂ)) := by funext ξ; congr 2; ring
      rw [hsimp] at hsc
      rw [Real.fourier_real_eq_integral_exp_smul] at hsc
      simp_rw [smul_eq_mul] at hsc
      rw [hsc]
      have h0e : Complex.exp (↑(-2 * Real.pi * 0 * (t - y)) * Complex.I) = 1 := by simp
      have hRmC : (Rm : ℂ) ≠ 0 := by exact_mod_cast hRm_pos.ne'
      rw [h0e, show (t - y) / (1 / Rm) = Rm * (t - y) by field_simp]
      push_cast; field_simp
    rw [hstep1]
    have hch1 := integral_sub_left_eq_self (μ := volume)
      (fun y : ℝ => u y * (Rm * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) (Rm * (t - y)))) t
    rw [← hch1]
    simp_rw [sub_sub_cancel]
    have hch2 := Measure.integral_comp_mul_left (g := fun v : ℝ =>
      u (t - v / Rm) * (Rm * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v)) Rm
    have hsub : (fun y : ℝ => u (t - y) * (Rm * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) (Rm * y))) =
        (fun y : ℝ => u (t - (Rm * y) / Rm) * (Rm * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) (Rm * y))) := by
      funext y; rw [mul_div_cancel_left₀ y hRm_pos.ne']
    rw [hsub, hch2, abs_inv, abs_of_pos hRm_pos, Complex.real_smul, ← integral_const_mul]
    congr 1; funext v
    have hRmC : (Rm : ℂ) ≠ 0 := by exact_mod_cast hRm_pos.ne'
    push_cast; field_simp
  have hχ_cs : HasCompactSupport (fun ξ : ℝ => (stdBump ξ : ℂ)) :=
    stdBump.hasCompactSupport.comp_left Complex.ofReal_zero
  obtain ⟨C4, hC4_nn, hC4⟩ := norm_fourier_decay_four (smooth_to_c4 stdBump_smooth) hχ_cs
  have hFχ_int : Integrable (𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ))) volume :=
    integrable_fourier_of_smooth_cs (smooth_to_c2 stdBump_smooth) hχ_cs
  have hFχ_tot : ∫ v : ℝ, 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v = 1 := by
    have hinv := (stdBump_smooth.continuous).fourierInv_fourier_eq
      (stdBump_smooth.continuous.integrable_of_hasCompactSupport hχ_cs) hFχ_int
    have h0 := congrFun hinv 0
    rw [Real.fourierInv_eq'] at h0
    simp only [Real.inner_apply, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul] at h0
    rw [h0]
    have hb0 : stdBump 0 = 1 :=
      stdBump.one_of_mem_closedBall (Metric.mem_closedBall_self stdBump.rIn_pos.le)
    simp [hb0]
  have hdom_T : ∃ gT : T → ℝ, Summable gT ∧ ∀ m : ℕ, ∀ t : T, ‖𝓕 (ψm m) t.1‖ ≤ gT t := by
    set B_int := ∫ v : ℝ, ‖𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖
    set I_sq := ∫ v : ℝ, (1 + v ^ 2)⁻¹
    have hIsq_nn : 0 ≤ I_sq := integral_nonneg fun v => by positivity
    set C_big := max B_int (2 * C4 * I_sq)
    let gT : T → ℝ := fun t =>
      if |t.1 - x| ≤ 2 then C_big else C_big / (|t.1 - x| - 1) ^ 2
    have hgT_sum : Summable gT := by
      have hsep_shift : ∀ t₁ ∈ (fun y => y - x) '' T, ∀ t₂ ∈ (fun y => y - x) '' T,
          t₁ ≠ t₂ → δ ≤ |t₁ - t₂| := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
        rw [show a - x - (b - x) = a - b by ring]
        exact hsep a ha b hb fun h => hne (by rw [h])
      obtain ⟨Cs, _, hCs⟩ := summable_and_bound_scaled_inv_sq hδ_pos hsep_shift
      have hsum_sh := (hCs 1 le_rfl).1
      let e : T ≃ (fun y => y - x) '' T :=
        { toFun := fun t => ⟨t.1 - x, ⟨t.1, t.2, rfl⟩⟩
          invFun := fun s => ⟨s.1 + x, by
            rcases s.2 with ⟨a, ha, hax⟩; rw [← hax, sub_add_cancel]; exact ha⟩
          left_inv := fun t => Subtype.ext (by simp)
          right_inv := fun s => Subtype.ext (by simp) }
      have hsum_inv : Summable (fun t : T => (1 : ℝ) / (1 + (t.1 - x) ^ 2)) :=
        (hsum_sh.comp_injective e.injective).congr fun t => by simp [e]
      have hCb_nn : 0 ≤ C_big := le_trans (integral_nonneg fun _ => norm_nonneg _) (le_max_left _ _)
      refine Summable.of_nonneg_of_le (fun t => by
        dsimp only [gT]; split_ifs <;> positivity) (fun t => ?_) (hsum_inv.mul_left (5 * C_big))
      dsimp only [gT]
      split_ifs with hle
      · have h1 : 1 + (t.1 - x) ^ 2 ≤ 5 := by
          have hsq : (t.1 - x) ^ 2 ≤ 4 := by
            rw [← sq_abs]; nlinarith [abs_nonneg (t.1 - x)]
          linarith
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        nlinarith
      · push Not at hle
        have hpos1 : 0 < |t.1 - x| - 1 := by linarith
        have hrel : 1 + (t.1 - x) ^ 2 ≤ 5 * (|t.1 - x| - 1) ^ 2 := by
          rw [← sq_abs (t.1 - x)]
          nlinarith
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (|t.1 - x| - 1) ^ 2),
          mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
    refine ⟨gT, hgT_sum, fun m t => ?_⟩
    rw [hFψm_conv m t.1]
    have hu_le1 : ∀ y : ℝ, ‖u y‖ ≤ 1 := fun y => by
      simp only [u, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg φ0.nonneg]
      exact φ0.le_one
    have hint_prod : Integrable (fun v : ℝ =>
        ‖u (t.1 - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖) volume := by
      refine hFχ_int.norm.mono'
        (((hu_smooth.continuous.comp (continuous_const.sub (continuous_id.div_const _))).mul
          (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
            (innerSL ℝ).continuous₂ (stdBump_smooth.continuous.integrable_of_hasCompactSupport hχ_cs))).norm.aestronglyMeasurable)
        (Eventually.of_forall fun v => by
          rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hu_le1 _))
    dsimp only [gT]
    split_ifs with hle
    · calc ‖∫ v : ℝ, u (t.1 - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖
          ≤ ∫ v : ℝ, ‖u (t.1 - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ v : ℝ, ‖𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖ :=
            integral_mono hint_prod hFχ_int.norm fun v => by
              rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hu_le1 _)
        _ ≤ C_big := le_max_left _ _
    · push Not at hle
      set a := |t.1 - x| - 1
      have ha_pos : 0 < a := by linarith
      have ha_gt1 : 1 < a := by linarith
      have hRm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      have hvan : ∀ v : ℝ, |v| < a → u (t.1 - v / ((m : ℝ) + 1)) = 0 := by
        intro v hv
        have hvRm : |v / ((m : ℝ) + 1)| ≤ |v| := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
          exact div_le_self (abs_nonneg v) hRm1
        have hdist : 1 < |t.1 - v / ((m : ℝ) + 1) - x| := by
          have htri := abs_sub_abs_le_abs_sub (t.1 - x) (v / ((m : ℝ) + 1))
          rw [show (t.1 - x) - v / ((m : ℝ) + 1) = t.1 - v / ((m : ℝ) + 1) - x by ring] at htri
          linarith
        have hge : φ0.rOut ≤ |N * (t.1 - v / ((m : ℝ) + 1) - x)| := by
          rw [abs_mul, abs_of_pos hN_pos]
          have hN1 : (1 : ℝ) ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) n]
          nlinarith
        have h0 : φ0 (N * (t.1 - v / ((m : ℝ) + 1) - x)) = 0 :=
          φ0.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hge)
        simp [u, h0]
      have hbd : ∀ v : ℝ, ‖u (t.1 - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖ ≤
          (2 * C4 / a ^ 2) * (1 + v ^ 2)⁻¹ := by
        intro v
        by_cases hv : |v| < a
        · rw [hvan v hv, zero_mul, norm_zero]; positivity
        · push Not at hv
          rw [norm_mul]
          have h1 := mul_le_of_le_one_left (norm_nonneg (𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v))
            (hu_le1 (t.1 - v / ((m : ℝ) + 1)))
          have h2 := hC4 v
          have hv2 : a ^ 2 ≤ v ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ ha_pos.le hv 2
          have ha2v2 : a ^ 2 * (1 + v ^ 2) ≤ 2 * (1 + v ^ 4) := by
            have h1v : 1 ≤ v ^ 2 := by nlinarith
            nlinarith [sq_nonneg v, show v ^ 4 = v ^ 2 * v ^ 2 by ring]
          have hfrac : C4 / (1 + v ^ 4) ≤ (2 * C4 / a ^ 2) * (1 + v ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hC4_nn]
          exact le_trans h1 (le_trans h2 hfrac)
      calc ‖∫ v : ℝ, u (t.1 - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖
          ≤ ∫ v : ℝ, ‖u (t.1 - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ v : ℝ, (2 * C4 / a ^ 2) * (1 + v ^ 2)⁻¹ :=
            integral_mono hint_prod (integrable_inv_one_add_sq.const_mul _) hbd
        _ = (2 * C4 / a ^ 2) * I_sq := integral_const_mul _ _
        _ = (2 * C4 * I_sq) / a ^ 2 := by ring
        _ ≤ C_big / a ^ 2 := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  rcases hdom_T with ⟨gT, hgT_sum, hgT_bd⟩
  have hLHS_lim : Tendsto (fun m : ℕ => ∑' t : T, 𝓕 (ψm m) t.1)
      atTop (𝓝 (∑' t : T, u t.1)) := by
    refine tendsto_tsum_of_dominated_convergence hgT_sum ?_ (Eventually.of_forall hgT_bd)
    intro t
    have hconv_eq : (fun m : ℕ => 𝓕 (ψm m) t.1) =
        fun m : ℕ => ∫ v : ℝ, u (t.1 - v / ((m : ℝ) + 1)) * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v :=
      funext fun m => hFψm_conv m t.1
    rw [hconv_eq]
    have htarget : u t.1 = ∫ v : ℝ, u t.1 * 𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v := by
      rw [integral_const_mul, hFχ_tot, mul_one]
    rw [htarget]
    refine tendsto_integral_of_dominated_convergence (fun v => ‖𝓕 (fun ξ : ℝ => (stdBump ξ : ℂ)) v‖)
      ?_ hFχ_int.norm ?_ ?_
    · intro m
      exact ((hu_smooth.continuous.comp (continuous_const.sub (continuous_id.div_const _))).mul
        (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
          (innerSL ℝ).continuous₂ (stdBump_smooth.continuous.integrable_of_hasCompactSupport hχ_cs))).aestronglyMeasurable
    · intro m
      filter_upwards with v
      rw [norm_mul]
      have hu1 : ‖u (t.1 - v / ((m : ℝ) + 1))‖ ≤ 1 := by
        simp only [u, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg φ0.nonneg]
        exact φ0.le_one
      exact mul_le_of_le_one_left (norm_nonneg _) hu1
    · filter_upwards with v
      have harg : Tendsto (fun m : ℕ => t.1 - v / ((m : ℝ) + 1)) atTop (𝓝 (t.1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
      rw [sub_zero] at harg
      exact ((hu_smooth.continuous.tendsto t.1).comp harg).mul tendsto_const_nhds
  have hLHS_lim' : Tendsto
      (fun m : ℕ => ∑' γ : Z0, (stdBump (γ.1 / ((m : ℝ) + 1)) : ℂ) *
        ((c γ.1 * ((1 / N : ℝ) : ℂ) * 𝓕 (fun v : ℝ => (φ0 v : ℂ)) (-(γ.1 / N))) *
          Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ))))
      atTop (𝓝 (∑' t : T, u t.1)) := by
    simpa only [← hψm_eq_glob] using hLHS_lim
  exact tendsto_nhds_unique hRHS_lim hLHS_lim'

lemma exists_atomic_approx_of_tilesR {S T : Set ℝ}
    (hS_bdd : Bornology.IsBounded S) (hS_meas : MeasurableSet S)
    (hS_vol : volume S = 1) (htile : TilesR S T) :
    ∃ (Z0 : Set ℝ) (M : ℝ) (w : ℕ → ℝ → ℂ),
      Z0.Countable ∧ 0 ≤ M ∧
      (∀ n : ℕ, Summable (fun γ : Z0 => ‖w n γ.1‖)) ∧
      (∀ n : ℕ, ∑' γ : Z0, ‖w n γ.1‖ ≤ M) ∧
      (∀ x : ℝ, Tendsto
        (fun n : ℕ => ∑' γ : Z0, w n γ.1 * Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ)))
        atTop (𝓝 (Set.indicator T (fun _ => (1 : ℂ)) x))) := by
  classical
  obtain ⟨δ, hδ_pos, hsep⟩ := tilesR_uniform_sep hS_meas hS_vol htile
  obtain ⟨Z0, A_Z0, C_atom, c, hAZ0_nn, hCatom_nn, hZ0_cnt, hZ0_count, hc_bound, hglobal⟩ :=
    exists_atomic_coeffs_of_tilesR hδ_pos hsep hS_bdd hS_meas hS_vol htile
  let φ0 : ContDiffBump (0 : ℝ) :=
    ⟨min (δ / 4) (1 / 4), min (δ / 2) (1 / 2),
      lt_min (by linarith) (by norm_num),
      by
        rcases le_total (δ / 4) (1 / 4) with h | h
        · rw [min_eq_left h, min_eq_left (by linarith)]; linarith
        · rw [min_eq_right h, min_eq_right (by linarith)]; norm_num⟩
  have hφ0_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (φ0 u : ℂ)) :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp φ0.contDiff
  have hφ0_cs : HasCompactSupport (fun u : ℝ => (φ0 u : ℂ)) :=
    φ0.hasCompactSupport.comp_left Complex.ofReal_zero
  let w : ℕ → ℝ → ℂ := fun n γ =>
    c γ * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * 𝓕 (fun u : ℝ => (φ0 u : ℂ)) (-(γ / ((n : ℝ) + 1)))
  set K_φ0 : ℝ := (∫ x : ℝ, ‖(φ0 x : ℂ)‖) +
    (∫ x : ℝ, ‖iteratedDeriv 2 (fun x : ℝ => (φ0 x : ℂ)) x‖) / (4 * Real.pi ^ 2)
  set M_unif : ℝ := C_atom * K_φ0 * (5 * A_Z0)
  have hw_bound : ∀ n : ℕ, Summable (fun γ : Z0 => ‖w n γ.1‖) ∧
      ∑' γ : Z0, ‖w n γ.1‖ ≤ M_unif := by
    intro n
    set N : ℝ := (n : ℝ) + 1
    have hN1 : 1 ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hsumZ := summable_and_bound_linear_count hAZ0_nn hZ0_count N hN1
    have hpt : ∀ γ : Z0, ‖w n γ.1‖ ≤
        (C_atom * K_φ0) * (1 / (N * (1 + (γ.1 / N) ^ 2))) := by
      intro γ
      dsimp only [w]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
      have hdec := norm_fourier_decay_sq (smooth_to_c2 hφ0_smooth) hφ0_cs (-(γ.1 / N))
      rw [neg_sq] at hdec
      calc ‖c γ.1‖ * (1 / N) * ‖𝓕 (fun u : ℝ => (φ0 u : ℂ)) (-(γ.1 / N))‖
          ≤ C_atom * (1 / N) * (K_φ0 / (1 + (γ.1 / N) ^ 2)) := by
            gcongr
            exact hc_bound γ.1
        _ = (C_atom * K_φ0) * (1 / (N * (1 + (γ.1 / N) ^ 2))) := by field_simp
    have hsum_w : Summable (fun γ : Z0 => ‖w n γ.1‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsumZ.1.mul_left _)
    refine ⟨hsum_w, ?_⟩
    calc ∑' γ : Z0, ‖w n γ.1‖
        ≤ ∑' γ : Z0, (C_atom * K_φ0) * (1 / (N * (1 + (γ.1 / N) ^ 2))) :=
          hsum_w.tsum_le_tsum hpt (hsumZ.1.mul_left _)
      _ = (C_atom * K_φ0) * ∑' γ : Z0, (1 / (N * (1 + (γ.1 / N) ^ 2))) := tsum_mul_left
      _ ≤ (C_atom * K_φ0) * (5 * A_Z0) :=
          mul_le_mul_of_nonneg_left hsumZ.2 (by positivity)
      _ = M_unif := rfl
  refine ⟨Z0, M_unif, w, hZ0_cnt, by positivity, fun n => (hw_bound n).1,
    fun n => (hw_bound n).2, fun x => ?_⟩
  have hfn_eq : (fun n : ℕ => ∑' γ : Z0, w n γ.1 *
      Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ))) =
      (fun n : ℕ => ∑' t : T, (φ0 (((n : ℝ) + 1) * (t.1 - x)) : ℂ)) :=
    funext fun n => comb_eq_tsum_atomic hδ_pos hsep hglobal φ0 (min_le_right _ _) n x (hw_bound n).1
  rw [hfn_eq]
  by_cases hxT : x ∈ T
  · rw [Set.indicator_of_mem hxT]
    have hconst : ∀ n : ℕ, ∑' t : T, (φ0 (((n : ℝ) + 1) * (t.1 - x)) : ℂ) = 1 := by
      intro n
      rw [tsum_eq_single (⟨x, hxT⟩ : T)]
      · simp only [sub_self, mul_zero]
        have h1 : φ0 0 = 1 := φ0.one_of_mem_closedBall (Metric.mem_closedBall_self φ0.rIn_pos.le)
        simp [h1]
      · rintro ⟨t, htT⟩ hne
        have hsep' : δ ≤ |t - x| := hsep t htT x hxT (fun h => hne (Subtype.ext h))
        have hge : φ0.rOut ≤ |((n : ℝ) + 1) * (t - x)| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
          have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
          have hro : φ0.rOut ≤ δ / 2 := min_le_left _ _
          nlinarith
        have h0 : φ0 (((n : ℝ) + 1) * (t - x)) = 0 :=
          φ0.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hge)
        simp [h0]
    simp_rw [hconst]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem hxT]
    have hfin := (separated_inter_Icc_finite_and_card_le hδ_pos hsep (x - 1) (x + 1)).1
    let Sx : Finset ℝ := hfin.toFinset
    have hex_d : ∃ d > 0, ∀ t ∈ T, d ≤ |t - x| := by
      by_cases hne : Sx.Nonempty
      · set d := (Sx.image fun t => |t - x|).min' (hne.image _)
        have hd_pos : 0 < d := by
          have hm := Finset.min'_mem (Sx.image fun t => |t - x|) (hne.image _)
          rcases Finset.mem_image.mp hm with ⟨t, ht, hteq⟩
          rw [show d = |t - x| from hteq.symm]
          have htT : t ∈ T := (hfin.mem_toFinset.mp ht).1
          exact abs_pos.mpr (sub_ne_zero.mpr fun h => hxT (h ▸ htT))
        refine ⟨min 1 d, lt_min zero_lt_one hd_pos, fun t htT => ?_⟩
        by_cases hle : |t - x| ≤ 1
        · have hmem : t ∈ Sx := hfin.mem_toFinset.mpr ⟨htT, by
            have := abs_le.mp hle; constructor <;> linarith⟩
          exact le_trans (min_le_right 1 d) (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hmem))
        · exact le_trans (min_le_left 1 d) (le_of_not_ge hle)
      · refine ⟨1, zero_lt_one, fun t htT => ?_⟩
        by_contra hlt; push Not at hlt
        exact hne ⟨t, hfin.mem_toFinset.mpr ⟨htT, by
          have := abs_le.mp hlt.le; constructor <;> linarith⟩⟩
    rcases hex_d with ⟨d, hd_pos, hd⟩
    obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / d)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N0] with n hn
    symm
    have hzero : ∀ t : T, (φ0 (((n : ℝ) + 1) * (t.1 - x)) : ℂ) = 0 := by
      intro t
      have hge : φ0.rOut ≤ |((n : ℝ) + 1) * (t.1 - x)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        have hro : φ0.rOut ≤ 1 / 2 := min_le_right _ _
        have hn' : 1 / d < (n : ℝ) + 1 := by
          have : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        have h1 : 1 < ((n : ℝ) + 1) * d := (div_lt_iff₀ hd_pos).mp hn'
        nlinarith [hd t.1 t.2]
      have h0 : φ0 (((n : ℝ) + 1) * (t.1 - x)) = 0 :=
        φ0.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hge)
      simp [h0]
    simp [hzero]

/- ## Section 3: Bohr Compactification, Complex RMK, and Amemiya-Ito (1964) -/

/- Part 3A: The Bohr compactification `BohrR` and Stone-Weierstrass density -/

abbrev BohrR : Type := {χ : ℝ → Circle // ∀ x y : ℝ, χ (x + y) = χ x * χ y}

instance : TopologicalSpace BohrR := inferInstanceAs (TopologicalSpace (Subtype _))
instance : T2Space BohrR := inferInstanceAs (T2Space (Subtype _))
instance : MeasurableSpace BohrR := borel BohrR
instance : BorelSpace BohrR := ⟨rfl⟩

lemma bohrR_isClosed_carrier :
    IsClosed {χ : ℝ → Circle | ∀ x y : ℝ, χ (x + y) = χ x * χ y} := by
  have heq : {χ : ℝ → Circle | ∀ x y : ℝ, χ (x + y) = χ x * χ y} =
      ⋂ x : ℝ, ⋂ y : ℝ, {χ : ℝ → Circle | χ (x + y) = χ x * χ y} := by
    ext χ; simp
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).mul (continuous_apply y))

instance : CompactSpace BohrR :=
  isCompact_iff_compactSpace.mp bohrR_isClosed_carrier.isCompact

lemma bohrR_map_zero (χ : BohrR) : χ.1 0 = 1 := by
  have h := χ.2 0 0
  rw [add_zero] at h
  exact mul_left_cancel (by simpa using h.symm : χ.1 0 * χ.1 0 = χ.1 0 * 1)

lemma bohrR_map_neg (χ : BohrR) (x : ℝ) : χ.1 (-x) = (χ.1 x)⁻¹ := by
  have h := χ.2 x (-x)
  rw [add_neg_cancel, bohrR_map_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

noncomputable instance : CommGroup BohrR where
  one := ⟨fun _ => 1, fun _ _ => by simp⟩
  mul χ ψ := ⟨fun x => χ.1 x * ψ.1 x, fun x y => by dsimp only; rw [χ.2, ψ.2]; ac_rfl⟩
  inv χ := ⟨fun x => (χ.1 x)⁻¹, fun x y => by dsimp only; rw [χ.2, mul_inv]⟩
  mul_assoc a b c := Subtype.ext (funext fun x => mul_assoc _ _ _)
  one_mul a := Subtype.ext (funext fun x => one_mul _)
  mul_one a := Subtype.ext (funext fun x => mul_one _)
  mul_comm a b := Subtype.ext (funext fun x => mul_comm _ _)
  inv_mul_cancel a := Subtype.ext (funext fun x => inv_mul_cancel _)

instance : IsTopologicalGroup BohrR where
  continuous_mul := by
    refine Continuous.subtype_mk (continuous_pi fun x => ?_) _
    exact ((continuous_apply x).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply x).comp (continuous_subtype_val.comp continuous_snd))
  continuous_inv := by
    refine Continuous.subtype_mk (continuous_pi fun x => ?_) _
    exact ((continuous_apply x).comp continuous_subtype_val).inv

def eChar (x : ℝ) : C(BohrR, ℂ) :=
  ⟨fun χ => (χ.1 x : ℂ),
    continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)⟩

@[simp] lemma eChar_apply (x : ℝ) (χ : BohrR) : eChar x χ = (χ.1 x : ℂ) := rfl

lemma eChar_zero : eChar 0 = 1 := by
  ext χ; simp [bohrR_map_zero]

lemma eChar_add (x y : ℝ) : eChar (x + y) = eChar x * eChar y := by
  ext χ; simp [χ.2]

lemma eChar_neg (x : ℝ) : eChar (-x) = star (eChar x) := by
  ext χ
  simp only [eChar_apply, ContinuousMap.star_apply, RCLike.star_def, bohrR_map_neg]
  exact Circle.coe_inv_eq_conj (χ.1 x)

lemma norm_eChar_apply (x : ℝ) (χ : BohrR) : ‖eChar x χ‖ = 1 := by
  rw [eChar_apply, Circle.norm_coe]

lemma norm_eChar (x : ℝ) : ‖eChar x‖ = 1 := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le (eChar x) zero_le_one]
    intro χ; rw [norm_eChar_apply]
  · rw [← norm_eChar_apply x (1 : BohrR)]
    exact ContinuousMap.norm_coe_le_norm (eChar x) (1 : BohrR)

noncomputable def eCharStarSubalgebra : StarSubalgebra ℂ C(BohrR, ℂ) where
  carrier := (Submodule.span ℂ (Set.range eChar) : Set C(BohrR, ℂ))
  mul_mem' {f g} hf hg := by
    refine Submodule.span_induction (p := fun u _ => u * g ∈ Submodule.span ℂ (Set.range eChar))
      ?_ (by simp) (fun u v _ _ hu hv => by rw [add_mul]; exact Submodule.add_mem _ hu hv)
      (fun c u _ hu => by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu) hf
    rintro _ ⟨x, rfl⟩
    refine Submodule.span_induction (p := fun v _ => eChar x * v ∈ Submodule.span ℂ (Set.range eChar))
      ?_ (by simp) (fun u v _ _ hu hv => by rw [mul_add]; exact Submodule.add_mem _ hu hv)
      (fun c u _ hu => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu) hg
    rintro _ ⟨y, rfl⟩
    rw [← eChar_add]
    exact Submodule.subset_span ⟨x + y, rfl⟩
  one_mem' := by rw [← eChar_zero]; exact Submodule.subset_span ⟨0, rfl⟩
  add_mem' hf hg := Submodule.add_mem _ hf hg
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' c := by
    have h1 : algebraMap ℂ C(BohrR, ℂ) c = c • eChar 0 := by
      ext χ; simp [bohrR_map_zero]
    rw [h1]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' {f} hf := by
    refine Submodule.span_induction (p := fun u _ => star u ∈ Submodule.span ℂ (Set.range eChar))
      ?_ (by simp) (fun u v _ _ hu hv => by rw [star_add]; exact Submodule.add_mem _ hu hv)
      (fun c u _ hu => by rw [star_smul]; exact Submodule.smul_mem _ (star c) hu) hf
    rintro _ ⟨x, rfl⟩
    rw [← eChar_neg]
    exact Submodule.subset_span ⟨-x, rfl⟩

lemma eCharStarSubalgebra_dense : eCharStarSubalgebra.topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro χ₁ χ₂ hne
  have hne' : χ₁.1 ≠ χ₂.1 := fun h => hne (Subtype.ext h)
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne'
  refine ⟨eChar x, ⟨eChar x, Submodule.subset_span ⟨x, rfl⟩, rfl⟩, ?_⟩
  intro hval
  exact hx (Subtype.ext hval)

lemma exists_finset_eChar_approx (f : C(BohrR, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℝ) (a : ℝ → ℂ), ‖f - ∑ x ∈ s, a x • eChar x‖ < ε := by
  have hmem : f ∈ eCharStarSubalgebra.topologicalClosure := by
    rw [eCharStarSubalgebra_dense]; trivial
  change f ∈ closure (eCharStarSubalgebra : Set C(BohrR, ℂ)) at hmem
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨g, hg, hdist⟩ := hmem ε hε
  change g ∈ Submodule.span ℂ (Set.range eChar) at hg
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hg
  rcases hg with ⟨c, rfl⟩
  refine ⟨c.support, fun x => c x, ?_⟩
  rw [Finsupp.sum] at hdist
  rwa [dist_eq_norm] at hdist

lemma eq_of_eq_on_eChar {Λ₁ Λ₂ : StrongDual ℂ C(BohrR, ℂ)}
    (h : ∀ x : ℝ, Λ₁ (eChar x) = Λ₂ (eChar x)) : Λ₁ = Λ₂ := by
  ext f
  have hzero : ∀ ε > 0, ‖Λ₁ f - Λ₂ f‖ ≤ (‖Λ₁‖ + ‖Λ₂‖) * ε := by
    intro ε hε
    obtain ⟨s, a, happrox⟩ := exists_finset_eChar_approx f hε
    set g := ∑ x ∈ s, a x • eChar x
    have hLg : Λ₁ g = Λ₂ g := by
      simp only [g, map_sum, map_smul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [h x]
    have hdiff : Λ₁ f - Λ₂ f = Λ₁ (f - g) - Λ₂ (f - g) := by
      rw [map_sub, map_sub, hLg]; ring
    rw [hdiff]
    calc ‖Λ₁ (f - g) - Λ₂ (f - g)‖ ≤ ‖Λ₁ (f - g)‖ + ‖Λ₂ (f - g)‖ := norm_sub_le _ _
      _ ≤ ‖Λ₁‖ * ‖f - g‖ + ‖Λ₂‖ * ‖f - g‖ :=
          add_le_add (Λ₁.le_opNorm _) (Λ₂.le_opNorm _)
      _ = (‖Λ₁‖ + ‖Λ₂‖) * ‖f - g‖ := by ring
      _ ≤ (‖Λ₁‖ + ‖Λ₂‖) * ε := mul_le_mul_of_nonneg_left happrox.le (by positivity)
  have hnorm0 : ‖Λ₁ f - Λ₂ f‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hpos
    push Not at hpos
    have hM : 0 < ‖Λ₁‖ + ‖Λ₂‖ + 1 := by positivity
    have h1 := hzero (‖Λ₁ f - Λ₂ f‖ / (2 * (‖Λ₁‖ + ‖Λ₂‖ + 1))) (by positivity)
    have h2 : (‖Λ₁‖ + ‖Λ₂‖) * (‖Λ₁ f - Λ₂ f‖ / (2 * (‖Λ₁‖ + ‖Λ₂‖ + 1))) < ‖Λ₁ f - Λ₂ f‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg Λ₁, norm_nonneg Λ₂]
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

/- Part 3B: Extracting a weak-* limit functional `Λ : StrongDual ℂ C(BohrR, ℂ)` -/

noncomputable def bohrOfReal (γ : ℝ) : BohrR :=
  ⟨fun x => Circle.exp (2 * Real.pi * γ * x), fun x y => by dsimp only; rw [mul_add, Circle.exp_add]⟩

lemma eChar_bohrOfReal (x γ : ℝ) :
    eChar x (bohrOfReal γ) = Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ) * (x : ℂ)) := by
  change ((Circle.exp (2 * Real.pi * γ * x) : Circle) : ℂ) = _
  rw [Circle.coe_exp]
  congr 1; push_cast; ring

lemma exists_bohr_dual_of_atomic_approx {T Z0 : Set ℝ} {M : ℝ} {w : ℕ → ℝ → ℂ}
    (hM : 0 ≤ M)
    (hsum : ∀ n : ℕ, Summable (fun γ : Z0 => ‖w n γ.1‖))
    (hbd : ∀ n : ℕ, ∑' γ : Z0, ‖w n γ.1‖ ≤ M)
    (hlim : ∀ x : ℝ, Tendsto
      (fun n : ℕ => ∑' γ : Z0, w n γ.1 * Complex.exp (2 * Real.pi * Complex.I * (γ.1 : ℂ) * (x : ℂ)))
      atTop (𝓝 (Set.indicator T (fun _ => (1 : ℂ)) x))) :
    ∃ Λ : StrongDual ℂ C(BohrR, ℂ),
      ‖Λ‖ ≤ M ∧ ∀ x : ℝ, Λ (eChar x) = Set.indicator T (fun _ => (1 : ℂ)) x := by
  have hsumm_eval : ∀ (n : ℕ) (f : C(BohrR, ℂ)),
      Summable (fun γ : Z0 => w n γ.1 * f (bohrOfReal γ.1)) := fun n f => by
    refine Summable.of_norm_bounded (g := fun γ : Z0 => ‖w n γ.1‖ * ‖f‖)
      ((hsum n).mul_right ‖f‖) fun γ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _)
  let Λn : ℕ → StrongDual ℂ C(BohrR, ℂ) := fun n =>
    LinearMap.mkContinuous
      { toFun := fun f => ∑' γ : Z0, w n γ.1 * f (bohrOfReal γ.1)
        map_add' := fun f g => by
          simp_rw [ContinuousMap.add_apply, mul_add]
          exact (hsumm_eval n f).tsum_add (hsumm_eval n g)
        map_smul' := fun c f => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
          have heq : (fun γ : Z0 => w n γ.1 * (c * f (bohrOfReal γ.1))) =
              fun γ : Z0 => c * (w n γ.1 * f (bohrOfReal γ.1)) := funext fun γ => by ring
          rw [heq, tsum_mul_left] }
      M (fun f => by
        calc ‖∑' γ : Z0, w n γ.1 * f (bohrOfReal γ.1)‖
            ≤ ∑' γ : Z0, ‖w n γ.1 * f (bohrOfReal γ.1)‖ := norm_tsum_le_tsum_norm (hsumm_eval n f).norm
          _ ≤ ∑' γ : Z0, ‖w n γ.1‖ * ‖f‖ :=
              (hsumm_eval n f).norm.tsum_le_tsum (fun γ => by
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _))
                ((hsum n).mul_right _)
          _ = (∑' γ : Z0, ‖w n γ.1‖) * ‖f‖ := tsum_mul_right
          _ ≤ M * ‖f‖ := mul_le_mul_of_nonneg_right (hbd n) (norm_nonneg _))
  have hΛn_norm : ∀ n : ℕ, ‖Λn n‖ ≤ M := fun n =>
    LinearMap.mkContinuous_norm_le _ hM _
  let K : Set (WeakDual ℂ C(BohrR, ℂ)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ C(BohrR, ℂ)) M
  have hK_comp : IsCompact K := WeakDual.isCompact_closedBall 0 M
  let u : ℕ → WeakDual ℂ C(BohrR, ℂ) := fun n => StrongDual.toWeakDual (Λn n)
  have hu_mem : ∀ n : ℕ, u n ∈ K := fun n => by
    simp only [K, u, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    exact hΛn_norm n
  have hle_prin : Filter.map u atTop ≤ 𝓟 K := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Eventually.of_forall hu_mem
  obtain ⟨Λw, hΛw_K, hclust⟩ := hK_comp hle_prin
  let Λ : StrongDual ℂ C(BohrR, ℂ) := WeakDual.toStrongDual Λw
  refine ⟨Λ, by simpa [K, Λ] using hΛw_K, fun x => ?_⟩
  have heval_cont : Continuous (fun μ : WeakDual ℂ C(BohrR, ℂ) => WeakDual.toStrongDual μ (eChar x)) :=
    WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) (eChar x)
  have hcl_x : ClusterPt (Λ (eChar x)) (Filter.map (fun n => Λn n (eChar x)) atTop) := by
    have h1 := hclust.map heval_cont.continuousAt (tendsto_map' le_rfl)
    simpa [u, Λ, Filter.map_map, Function.comp_def] using h1
  have hlim_x : Tendsto (fun n => Λn n (eChar x)) atTop (𝓝 (Set.indicator T (fun _ => (1 : ℂ)) x)) := by
    convert hlim x using 1
    funext n
    simp only [Λn, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, eChar_bohrOfReal]
  exact eq_of_nhds_neBot (NeBot.mono hcl_x (inf_le_inf_left _ hlim_x))

/- Part 3C: Jordan decomposition and Complex Riesz-Markov-Kakutani polar representation -/

lemma outerRegular_add_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [Measure.OuterRegular μ] [Measure.OuterRegular ν] :
    Measure.OuterRegular (μ + ν) := by
  refine ⟨fun A _ r hr => ?_⟩
  by_cases hr_top : r = ∞
  · refine ⟨Set.univ, Set.subset_univ A, isOpen_univ, ?_⟩
    rw [hr_top, Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, measure_lt_top ν _⟩
  · rw [Measure.add_apply] at hr
    set δ : ℝ≥0∞ := (r - (μ A + ν A)) / 2
    have hδ_pos : 0 < δ := ENNReal.div_pos (tsub_pos_iff_lt.mpr hr).ne' ENNReal.ofNat_ne_top
    obtain ⟨U₁, hAU₁, hU₁o, hU₁lt⟩ := Set.exists_isOpen_lt_of_lt A (μ A + δ)
      (ENNReal.lt_add_right (measure_ne_top μ A) hδ_pos.ne')
    obtain ⟨U₂, hAU₂, hU₂o, hU₂lt⟩ := Set.exists_isOpen_lt_of_lt A (ν A + δ)
      (ENNReal.lt_add_right (measure_ne_top ν A) hδ_pos.ne')
    refine ⟨U₁ ∩ U₂, Set.subset_inter hAU₁ hAU₂, hU₁o.inter hU₂o, ?_⟩
    rw [Measure.add_apply]
    have h1 : μ (U₁ ∩ U₂) < μ A + δ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hU₁lt
    have h2 : ν (U₁ ∩ U₂) < ν A + δ := lt_of_le_of_lt (measure_mono Set.inter_subset_right) hU₂lt
    have hsum : μ (U₁ ∩ U₂) + ν (U₁ ∩ U₂) < (μ A + δ) + (ν A + δ) := ENNReal.add_lt_add h1 h2
    have h2δ : δ + δ = r - (μ A + ν A) := by
      dsimp only [δ]; rw [← two_mul, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    have heq : (μ A + δ) + (ν A + δ) = r := by
      calc (μ A + δ) + (ν A + δ) = (μ A + ν A) + (δ + δ) := by ac_rfl
        _ = (μ A + ν A) + (r - (μ A + ν A)) := by rw [h2δ]
        _ = r := add_tsub_cancel_of_le hr.le
    rwa [heq] at hsum

lemma regular_add_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular] :
    (μ + ν).Regular := by
  have : Measure.OuterRegular (μ + ν) := outerRegular_add_measure
  refine ⟨?_⟩
  · -- InnerRegularWRT (μ + ν) IsCompact IsOpen
    intro U hU r hr
    rw [Measure.add_apply] at hr
    by_cases hμ0 : μ U = 0
    · rw [hμ0, zero_add] at hr
      obtain ⟨K, hKU, hKc, hKr⟩ := Measure.Regular.innerRegular hU r hr
      exact ⟨K, hKU, hKc, by rw [Measure.add_apply]; exact lt_of_lt_of_le hKr le_add_self⟩
    · by_cases hν0 : ν U = 0
      · rw [hν0, add_zero] at hr
        obtain ⟨K, hKU, hKc, hKr⟩ := Measure.Regular.innerRegular hU r hr
        exact ⟨K, hKU, hKc, by rw [Measure.add_apply]; exact lt_of_lt_of_le hKr le_self_add⟩
      · have hfin : μ U + ν U ≠ ∞ := ENNReal.add_ne_top.mpr ⟨measure_ne_top μ U, measure_ne_top ν U⟩
        set δ : ℝ≥0∞ := (μ U + ν U - r) / 2
        have hδ_pos : 0 < δ := ENNReal.div_pos (tsub_pos_iff_lt.mpr hr).ne' ENNReal.ofNat_ne_top
        have hμ_lt : μ U - δ < μ U := ENNReal.sub_lt_self (measure_ne_top μ U) hμ0 hδ_pos.ne'
        have hν_lt : ν U - δ < ν U := ENNReal.sub_lt_self (measure_ne_top ν U) hν0 hδ_pos.ne'
        obtain ⟨K₁, hK₁U, hK₁c, hK₁r⟩ := Measure.Regular.innerRegular hU (μ U - δ) hμ_lt
        obtain ⟨K₂, hK₂U, hK₂c, hK₂r⟩ := Measure.Regular.innerRegular hU (ν U - δ) hν_lt
        refine ⟨K₁ ∪ K₂, Set.union_subset hK₁U hK₂U, hK₁c.union hK₂c, ?_⟩
        rw [Measure.add_apply]
        have h1 : μ U - δ < μ (K₁ ∪ K₂) := lt_of_lt_of_le hK₁r (measure_mono Set.subset_union_left)
        have h2 : ν U - δ < ν (K₁ ∪ K₂) := lt_of_lt_of_le hK₂r (measure_mono Set.subset_union_right)
        have hsum : (μ U - δ) + (ν U - δ) < μ (K₁ ∪ K₂) + ν (K₁ ∪ K₂) := ENNReal.add_lt_add h1 h2
        have hge : r ≤ (μ U - δ) + (ν U - δ) := by
          have h2δ : δ + δ = μ U + ν U - r := by
            dsimp only [δ]; rw [← two_mul, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
          have hadd : r + (δ + δ) = μ U + ν U := by rw [h2δ, add_tsub_cancel_of_le hr.le]
          have htot : r + (δ + δ) ≤ ((μ U - δ) + (ν U - δ)) + (δ + δ) := by
            calc r + (δ + δ) = μ U + ν U := hadd
              _ ≤ ((μ U - δ) + δ) + ((ν U - δ) + δ) := add_le_add le_tsub_add le_tsub_add
              _ = ((μ U - δ) + (ν U - δ)) + (δ + δ) := by ac_rfl
          have hδ2_ne : δ + δ ≠ ∞ := by rw [h2δ]; exact ENNReal.sub_ne_top hfin
          exact (ENNReal.add_le_add_iff_right hδ2_ne).mp htot
        exact lt_of_le_of_lt hge hsum

noncomputable def toCc (f : C(BohrR, ℝ)) : CompactlySupportedContinuousMap BohrR ℝ :=
  ⟨f, HasCompactSupport.of_compactSpace f⟩

lemma continuousMap_norm_le_of_nonneg_le {f g : C(BohrR, ℝ)} (h0 : 0 ≤ g) (hgf : g ≤ f) :
    ‖g‖ ≤ ‖f‖ := by
  rw [ContinuousMap.norm_le g (norm_nonneg f)]
  intro x
  rw [Real.norm_of_nonneg (show 0 ≤ g x from h0 x)]
  exact (hgf x).trans (le_trans (le_abs_self (f x)) (ContinuousMap.norm_coe_le_norm f x))

lemma jordan_decomp (L : StrongDual ℝ C(BohrR, ℝ)) :
    ∃ μ₁ μ₂ : Measure BohrR,
      IsFiniteMeasure μ₁ ∧ IsFiniteMeasure μ₂ ∧ μ₁.Regular ∧ μ₂.Regular ∧
      ∀ f : C(BohrR, ℝ), L f = ∫ g, f g ∂μ₁ - ∫ g, f g ∂μ₂ := by
  let S : C(BohrR, ℝ) → Set ℝ := fun f => {r : ℝ | ∃ g : C(BohrR, ℝ), 0 ≤ g ∧ g ≤ f ∧ L g = r}
  let φ : C(BohrR, ℝ) → ℝ := fun f => sSup (S f)
  have hS_ne : ∀ {f : C(BohrR, ℝ)}, 0 ≤ f → (S f).Nonempty := fun {f} hf =>
    ⟨0, ⟨0, le_rfl, hf, map_zero L⟩⟩
  have hS_bdd : ∀ {f : C(BohrR, ℝ)}, 0 ≤ f → BddAbove (S f) := fun {f} hf => by
    refine ⟨‖L‖ * ‖f‖, ?_⟩
    rintro _ ⟨g, hg0, hgf, rfl⟩
    calc L g ≤ |L g| := le_abs_self _
      _ = ‖L g‖ := rfl
      _ ≤ ‖L‖ * ‖g‖ := L.le_opNorm g
      _ ≤ ‖L‖ * ‖f‖ := mul_le_mul_of_nonneg_left (continuousMap_norm_le_of_nonneg_le hg0 hgf) (norm_nonneg L)
  have hφ_nonneg : ∀ {f : C(BohrR, ℝ)}, 0 ≤ f → 0 ≤ φ f := fun {f} hf =>
    le_csSup (hS_bdd hf) ⟨0, le_rfl, hf, map_zero L⟩
  have hL_le_φ : ∀ {f : C(BohrR, ℝ)}, 0 ≤ f → L f ≤ φ f := fun {f} hf =>
    le_csSup (hS_bdd hf) ⟨f, hf, le_rfl, rfl⟩
  have hφ_add : ∀ {f₁ f₂ : C(BohrR, ℝ)}, 0 ≤ f₁ → 0 ≤ f₂ → φ (f₁ + f₂) = φ f₁ + φ f₂ := by
    intro f₁ f₂ hf₁ hf₂
    have hf12 : 0 ≤ f₁ + f₂ := add_nonneg hf₁ hf₂
    apply le_antisymm
    · refine csSup_le (hS_ne hf12) ?_
      rintro _ ⟨g, hg0, hgle, rfl⟩
      let g₁ : C(BohrR, ℝ) := ⟨fun x => min (g x) (f₁ x), g.continuous.min f₁.continuous⟩
      let g₂ : C(BohrR, ℝ) := g - g₁
      have hg₁0 : 0 ≤ g₁ := fun x => le_min (hg0 x) (hf₁ x)
      have hg₁le : g₁ ≤ f₁ := fun x => min_le_right _ _
      have hg₂0 : 0 ≤ g₂ := fun x => sub_nonneg.mpr (min_le_left _ _)
      have hg₂le : g₂ ≤ f₂ := fun x => by
        change g x - min (g x) (f₁ x) ≤ f₂ x
        rcases le_total (g x) (f₁ x) with h | h
        · rw [min_eq_left h, sub_self]; exact hf₂ x
        · rw [min_eq_right h]
          have hx := hgle x
          change g x ≤ f₁ x + f₂ x at hx
          linarith
      have hgeq : g = g₁ + g₂ := by ext x; change g x = g₁ x + (g x - g₁ x); ring
      rw [hgeq, map_add]
      exact add_le_add (le_csSup (hS_bdd hf₁) ⟨g₁, hg₁0, hg₁le, rfl⟩)
        (le_csSup (hS_bdd hf₂) ⟨g₂, hg₂0, hg₂le, rfl⟩)
    · have h1 : ∀ r₁ ∈ S f₁, ∀ r₂ ∈ S f₂, r₁ + r₂ ≤ φ (f₁ + f₂) := by
        rintro _ ⟨g₁, hg₁0, hg₁le, rfl⟩ _ ⟨g₂, hg₂0, hg₂le, rfl⟩
        rw [← map_add]
        exact le_csSup (hS_bdd hf12) ⟨g₁ + g₂, add_nonneg hg₁0 hg₂0, add_le_add hg₁le hg₂le, rfl⟩
      have h2 : ∀ r₁ ∈ S f₁, r₁ + φ f₂ ≤ φ (f₁ + f₂) := fun r₁ hr₁ => by
        rw [← le_sub_iff_add_le']
        exact csSup_le (hS_ne hf₂) fun r₂ hr₂ => le_sub_iff_add_le'.mpr (h1 r₁ hr₁ r₂ hr₂)
      rw [← le_sub_iff_add_le]
      exact csSup_le (hS_ne hf₁) fun r₁ hr₁ => le_sub_iff_add_le.mpr (h2 r₁ hr₁)
  have hφ_smul : ∀ {c : ℝ} {f : C(BohrR, ℝ)}, 0 ≤ c → 0 ≤ f → φ (c • f) = c * φ f := by
    intro c f hc hf
    rcases hc.eq_or_lt with rfl | hcpos
    · simp only [zero_smul, zero_mul]
      apply le_antisymm
      · refine csSup_le (hS_ne le_rfl) ?_
        rintro _ ⟨g, hg0, hg0', rfl⟩
        have : g = 0 := le_antisymm hg0' hg0
        rw [this, map_zero]
      · exact hφ_nonneg le_rfl
    · have hcf : 0 ≤ c • f := fun x => mul_nonneg hcpos.le (hf x)
      apply le_antisymm
      · refine csSup_le (hS_ne hcf) ?_
        rintro _ ⟨g, hg0, hgle, rfl⟩
        have h1 : 0 ≤ c⁻¹ • g := fun x => mul_nonneg (inv_nonneg.mpr hcpos.le) (hg0 x)
        have h2 : c⁻¹ • g ≤ f := fun x => by
          change c⁻¹ * g x ≤ f x
          rw [inv_mul_le_iff₀ hcpos]
          exact hgle x
        have h3 : L (c⁻¹ • g) ≤ φ f := le_csSup (hS_bdd hf) ⟨c⁻¹ • g, h1, h2, rfl⟩
        rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hcpos] at h3
        exact h3
      · rw [← le_div_iff₀' hcpos]
        refine csSup_le (hS_ne hf) ?_
        rintro _ ⟨g, hg0, hgle, rfl⟩
        rw [le_div_iff₀' hcpos, ← smul_eq_mul, ← map_smul]
        exact le_csSup (hS_bdd hcf) ⟨c • g, fun x => mul_nonneg hcpos.le (hg0 x),
          fun x => mul_le_mul_of_nonneg_left (hgle x) hcpos.le, rfl⟩
  let posPart : C(BohrR, ℝ) → C(BohrR, ℝ) := fun f => ⟨fun x => max (f x) 0, f.continuous.max continuous_const⟩
  let negPart : C(BohrR, ℝ) → C(BohrR, ℝ) := fun f => ⟨fun x => max (-f x) 0, f.continuous.neg.max continuous_const⟩
  have hpos_nonneg : ∀ f, 0 ≤ posPart f := fun f x => le_max_right _ _
  have hneg_nonneg : ∀ f, 0 ≤ negPart f := fun f x => le_max_right _ _
  have hdecomp : ∀ f, f = posPart f - negPart f := fun f => by
    ext x
    change f x = max (f x) 0 - max (-f x) 0
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  have hpos_of_nonneg : ∀ {f}, 0 ≤ f → posPart f = f := fun hf => by
    ext x; exact max_eq_left (hf x)
  have hneg_of_nonneg : ∀ {f}, 0 ≤ f → negPart f = 0 := fun hf => by
    ext x; exact max_eq_right (neg_nonpos.mpr (hf x))
  let ψ : C(BohrR, ℝ) → ℝ := fun f => φ (posPart f) - φ (negPart f)
  have hψ_of_nonneg : ∀ {f}, 0 ≤ f → ψ f = φ f := fun hf => by
    dsimp only [ψ]
    rw [hpos_of_nonneg hf, hneg_of_nonneg hf]
    have h0 : φ 0 = 0 := by simpa using hφ_smul (c := 0) (f := 0) le_rfl le_rfl
    rw [h0, sub_zero]
  have hψ_add : ∀ f g, ψ (f + g) = ψ f + ψ g := fun f g => by
    have heq : posPart (f + g) + negPart f + negPart g = negPart (f + g) + posPart f + posPart g := by
      have h1 := hdecomp (f + g)
      have h2 := hdecomp f
      have h3 := hdecomp g
      ext x
      have hx1 := congrFun (congrArg DFunLike.coe h1) x
      have hx2 := congrFun (congrArg DFunLike.coe h2) x
      have hx3 := congrFun (congrArg DFunLike.coe h3) x
      simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply] at hx1 hx2 hx3 ⊢
      linarith
    have hφeq := congrArg φ heq
    rw [hφ_add (add_nonneg (hpos_nonneg _) (hneg_nonneg _)) (hneg_nonneg _),
      hφ_add (hpos_nonneg _) (hneg_nonneg _),
      hφ_add (add_nonneg (hneg_nonneg _) (hpos_nonneg _)) (hpos_nonneg _),
      hφ_add (hneg_nonneg _) (hpos_nonneg _)] at hφeq
    dsimp only [ψ]
    linarith
  have hψ_smul : ∀ (c : ℝ) (f : C(BohrR, ℝ)), ψ (c • f) = c * ψ f := fun c f => by
    rcases le_total 0 c with hc | hc
    · have hp : posPart (c • f) = c • posPart f := by
        ext x; change max (c * f x) 0 = c * max (f x) 0
        rw [mul_max_of_nonneg _ _ hc, mul_zero]
      have hn : negPart (c • f) = c • negPart f := by
        ext x; change max (-(c * f x)) 0 = c * max (-f x) 0
        rw [← mul_neg, mul_max_of_nonneg _ _ hc, mul_zero]
      dsimp only [ψ]
      rw [hp, hn, hφ_smul hc (hpos_nonneg f), hφ_smul hc (hneg_nonneg f)]
      ring
    · have hnc : 0 ≤ -c := neg_nonneg.mpr hc
      have hp : posPart (c • f) = (-c) • negPart f := by
        ext x; change max (c * f x) 0 = (-c) * max (-f x) 0
        rw [mul_max_of_nonneg _ _ hnc, mul_zero, neg_mul_neg]
      have hn : negPart (c • f) = (-c) • posPart f := by
        ext x; change max (-(c * f x)) 0 = (-c) * max (f x) 0
        rw [mul_max_of_nonneg _ _ hnc, mul_zero, neg_mul]
      dsimp only [ψ]
      rw [hp, hn, hφ_smul hnc (hneg_nonneg f), hφ_smul hnc (hpos_nonneg f)]
      ring
  have hψ_sub : ∀ f g, ψ (f - g) = ψ f - ψ g := fun f g => by
    rw [sub_eq_add_neg, hψ_add, show -g = (-1 : ℝ) • g by simp, hψ_smul]; ring
  let Lpos : CompactlySupportedContinuousMap BohrR ℝ →ₚ[ℝ] ℝ :=
    { toFun := fun f => ψ f.toContinuousMap
      map_add' := fun f g => hψ_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact hψ_smul c f.toContinuousMap
      monotone' := fun f g hfg => by
        have h0 : (0 : C(BohrR, ℝ)) ≤ g.toContinuousMap - f.toContinuousMap := fun x => sub_nonneg.mpr (hfg x)
        have h1 : 0 ≤ ψ (g.toContinuousMap - f.toContinuousMap) := by
          rw [hψ_of_nonneg h0]; exact hφ_nonneg h0
        rw [hψ_sub] at h1
        linarith }
  let Lneg : CompactlySupportedContinuousMap BohrR ℝ →ₚ[ℝ] ℝ :=
    { toFun := fun f => ψ f.toContinuousMap - L f.toContinuousMap
      map_add' := fun f g => by
        change ψ (f.toContinuousMap + g.toContinuousMap) - L (f.toContinuousMap + g.toContinuousMap) = _
        rw [hψ_add, map_add]; ring
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        change ψ (c • f.toContinuousMap) - L (c • f.toContinuousMap) = _
        rw [hψ_smul, map_smul, smul_eq_mul]; ring
      monotone' := fun f g hfg => by
        have h0 : (0 : C(BohrR, ℝ)) ≤ g.toContinuousMap - f.toContinuousMap := fun x => sub_nonneg.mpr (hfg x)
        have h1 : L (g.toContinuousMap - f.toContinuousMap) ≤ ψ (g.toContinuousMap - f.toContinuousMap) := by
          rw [hψ_of_nonneg h0]; exact hL_le_φ h0
        rw [hψ_sub, map_sub] at h1
        linarith }
  let μ₁ := RealRMK.rieszMeasure Lpos
  let μ₂ := RealRMK.rieszMeasure Lneg
  refine ⟨μ₁, μ₂, inferInstance, inferInstance, inferInstance, inferInstance, fun f => ?_⟩
  have h1 : ∫ g, f g ∂μ₁ = Lpos (toCc f) := RealRMK.integral_rieszMeasure Lpos (toCc f)
  have h2 : ∫ g, f g ∂μ₂ = Lneg (toCc f) := RealRMK.integral_rieszMeasure Lneg (toCc f)
  rw [h1, h2]
  change L f = ψ f - (ψ f - L f)
  ring

structure PolarRep (Λ : StrongDual ℂ C(BohrR, ℂ)) where
  ν : Measure BohrR
  ρ : Measure BohrR
  u : BohrR → ℂ
  hν_fin : IsFiniteMeasure ν
  hρ_fin : IsFiniteMeasure ρ
  hρ_reg : ρ.Regular
  hν_le : ν ≤ (2 : ℝ≥0∞) • ρ
  hu_meas : Measurable u
  hu_norm : ∀ g : BohrR, ‖u g‖ = 1
  hrep : ∀ f : C(BohrR, ℂ), Λ f = ∫ g, f g * u g ∂ν
  hnorm : (ν Set.univ).toReal = ‖Λ‖

noncomputable def projUnit (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then z else z / (‖z‖ : ℂ)

lemma continuous_projUnit : Continuous projUnit := by
  have heq : projUnit = fun z : ℂ => z / ((max (1 : ℝ) ‖z‖ : ℝ) : ℂ) := by
    funext z
    dsimp only [projUnit]
    split_ifs with h
    · rw [max_eq_left h]; simp
    · push Not at h; rw [max_eq_right h.le]
  rw [heq]
  refine continuous_id.div (Complex.continuous_ofReal.comp (continuous_const.max continuous_norm)) fun z => ?_
  have hpos : (0 : ℝ) < max 1 ‖z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

lemma norm_projUnit_le_one (z : ℂ) : ‖projUnit z‖ ≤ 1 := by
  dsimp only [projUnit]
  split_ifs with h
  · exact h
  · push Not at h
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
      div_self (lt_trans zero_lt_one h).ne']

lemma norm_projUnit_sub_le {z w : ℂ} (hw : ‖w‖ = 1) :
    ‖projUnit z - w‖ ≤ 2 * ‖z - w‖ := by
  dsimp only [projUnit]
  split_ifs with h
  · linarith [norm_nonneg (z - w)]
  · push Not at h
    have hz_pos : 0 < ‖z‖ := lt_trans zero_lt_one h
    have h1 : ‖z / (‖z‖ : ℂ) - z‖ = ‖z‖ - 1 := by
      have heq : z / (‖z‖ : ℂ) - z = z * ((1 / ‖z‖ - 1 : ℝ) : ℂ) := by
        push_cast; field_simp [Complex.ofReal_ne_zero.mpr hz_pos.ne']
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by rw [sub_nonpos, div_le_one hz_pos]; exact h.le)]
      field_simp [hz_pos.ne']
      ring
    have h2 : ‖z‖ - 1 ≤ ‖z - w‖ := by
      rw [← hw]
      exact norm_sub_norm_le z w
    calc ‖z / (‖z‖ : ℂ) - w‖ = ‖(z / (‖z‖ : ℂ) - z) + (z - w)‖ := by ring_nf
      _ ≤ ‖z / (‖z‖ : ℂ) - z‖ + ‖z - w‖ := norm_add_le _ _
      _ = (‖z‖ - 1) + ‖z - w‖ := by rw [h1]
      _ ≤ 2 * ‖z - w‖ := by linarith

lemma exists_polar_rep (Λ : StrongDual ℂ C(BohrR, ℂ)) : Nonempty (PolarRep Λ) := by
  let embed : C(BohrR, ℝ) →L[ℝ] C(BohrR, ℂ) :=
    LinearMap.mkContinuous
      { toFun := fun f => ⟨fun g => (f g : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
        map_add' := fun f₁ f₂ => by ext g; simp
        map_smul' := fun c f => by ext g; simp }
      1 (fun f => by
        rw [one_mul]
        change ‖(⟨fun g => (f g : ℂ), _⟩ : C(BohrR, ℂ))‖ ≤ ‖f‖
        rw [ContinuousMap.norm_le _ (norm_nonneg f)]
        intro g
        change ‖(f g : ℂ)‖ ≤ ‖f‖
        rw [Complex.norm_real]
        exact ContinuousMap.norm_coe_le_norm f g)
  let Lre : StrongDual ℝ C(BohrR, ℝ) := Complex.reCLM.comp ((Λ.restrictScalars ℝ).comp embed)
  let Lim : StrongDual ℝ C(BohrR, ℝ) := Complex.imCLM.comp ((Λ.restrictScalars ℝ).comp embed)
  obtain ⟨μ₁, μ₂, hμ₁f, hμ₂f, hμ₁r, hμ₂r, hLre⟩ := jordan_decomp Lre
  obtain ⟨μ₃, μ₄, hμ₃f, hμ₄f, hμ₃r, hμ₄r, hLim⟩ := jordan_decomp Lim
  have : IsFiniteMeasure μ₁ := hμ₁f
  have : IsFiniteMeasure μ₂ := hμ₂f
  have : IsFiniteMeasure μ₃ := hμ₃f
  have : IsFiniteMeasure μ₄ := hμ₄f
  have : μ₁.Regular := hμ₁r
  have : μ₂.Regular := hμ₂r
  have : μ₃.Regular := hμ₃r
  have : μ₄.Regular := hμ₄r
  let ρ : Measure BohrR := (μ₁ + μ₂) + (μ₃ + μ₄)
  have : IsFiniteMeasure ρ := inferInstance
  have : (μ₁ + μ₂).Regular := regular_add_measure
  have : (μ₃ + μ₄).Regular := regular_add_measure
  have hρ_reg : ρ.Regular := regular_add_measure
  have hle1 : μ₁ ≤ ρ := le_trans (Measure.le_add_right le_rfl) (Measure.le_add_right le_rfl)
  have hle2 : μ₂ ≤ ρ := le_trans (Measure.le_add_left le_rfl) (Measure.le_add_right le_rfl)
  have hle3 : μ₃ ≤ ρ := le_trans (Measure.le_add_right le_rfl) (Measure.le_add_left le_rfl)
  have hle4 : μ₄ ≤ ρ := le_trans (Measure.le_add_left le_rfl) (Measure.le_add_left le_rfl)
  let d₁ := μ₁.rnDeriv ρ
  let d₂ := μ₂.rnDeriv ρ
  let d₃ := μ₃.rnDeriv ρ
  let d₄ := μ₄.rnDeriv ρ
  have hd_le_one : ∀ {μ : Measure BohrR} (_ : μ ≤ ρ), ∀ᵐ g ∂ρ, μ.rnDeriv ρ g ≤ 1 := fun hμ =>
    Measure.rnDeriv_le_one_of_le hμ
  have hd1_le : ∀ᵐ g ∂ρ, d₁ g ≤ 1 := hd_le_one hle1
  have hd2_le : ∀ᵐ g ∂ρ, d₂ g ≤ 1 := hd_le_one hle2
  have hd3_le : ∀ᵐ g ∂ρ, d₃ g ≤ 1 := hd_le_one hle3
  have hd4_le : ∀ᵐ g ∂ρ, d₄ g ≤ 1 := hd_le_one hle4
  let h : BohrR → ℂ := fun g =>
    (((d₁ g).toReal - (d₂ g).toReal : ℝ) : ℂ) + (((d₃ g).toReal - (d₄ g).toReal : ℝ) : ℂ) * Complex.I
  let h' : BohrR → ℂ := fun g => if ‖h g‖ ≤ 2 then h g else 0
  have hh_meas : Measurable h := by
    refine (Complex.continuous_ofReal.measurable.comp
      (((Measure.measurable_rnDeriv μ₁ ρ).ennreal_toReal).sub
       ((Measure.measurable_rnDeriv μ₂ ρ).ennreal_toReal))).add ?_
    exact (Complex.continuous_ofReal.measurable.comp
      (((Measure.measurable_rnDeriv μ₃ ρ).ennreal_toReal).sub
       ((Measure.measurable_rnDeriv μ₄ ρ).ennreal_toReal))).mul measurable_const
  have hh'_meas : Measurable h' :=
    hh_meas.ite (measurableSet_le hh_meas.norm measurable_const) measurable_const
  have hh'_bd : ∀ g, ‖h' g‖ ≤ 2 := fun g => by
    dsimp only [h']
    split_ifs with hg
    · exact hg
    · simp
  have hh'_ae : h' =ᵐ[ρ] h := by
    filter_upwards [hd1_le, hd2_le, hd3_le, hd4_le] with g h1 h2 h3 h4
    have h1r : (d₁ g).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)
    have h2r : (d₂ g).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h2)
    have h3r : (d₃ g).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h3)
    have h4r : (d₄ g).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h4)
    have ha : |(d₁ g).toReal - (d₂ g).toReal| ≤ 1 := abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := d₁ g)],
      by linarith [ENNReal.toReal_nonneg (a := d₂ g)]⟩
    have hb : |(d₃ g).toReal - (d₄ g).toReal| ≤ 1 := abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := d₃ g)],
      by linarith [ENNReal.toReal_nonneg (a := d₄ g)]⟩
    have hnorm : ‖h g‖ ≤ 2 := by
      calc ‖h g‖ ≤ ‖(((d₁ g).toReal - (d₂ g).toReal : ℝ) : ℂ)‖ +
            ‖(((d₃ g).toReal - (d₄ g).toReal : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |(d₁ g).toReal - (d₂ g).toReal| + |(d₃ g).toReal - (d₄ g).toReal| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 + 1 := add_le_add ha hb
        _ = 2 := by norm_num
    simp only [h', if_pos hnorm]
  have hΛ_real : ∀ f : C(BohrR, ℝ), Λ (embed f) = ∫ g, (f g : ℂ) * h' g ∂ρ := by
    intro f
    have hint_real : ∀ {μ : Measure BohrR} (_ : μ ≤ ρ),
        ∫ g, f g ∂μ = ∫ g, f g * (μ.rnDeriv ρ g).toReal ∂ρ := by
      intro μ hμ
      have : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
      have hac := Measure.absolutelyContinuous_of_le hμ
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ρ hac]
      rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv μ ρ)
        (Measure.rnDeriv_lt_top μ ρ)]
      refine integral_congr_ae (Eventually.of_forall fun g => by simp [smul_eq_mul, mul_comm])
    have hint_f_d : ∀ {μ : Measure BohrR} (_ : μ ≤ ρ),
        Integrable (fun g => f g * (μ.rnDeriv ρ g).toReal) ρ := by
      intro μ hμ
      refine Integrable.mono' (integrable_const (‖f‖ * 1))
        ((f.continuous.measurable.mul (Measure.measurable_rnDeriv μ ρ).ennreal_toReal).aestronglyMeasurable) ?_
      filter_upwards [hd_le_one hμ] with g hg
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul (ContinuousMap.norm_coe_le_norm f g)
        (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hg)) ENNReal.toReal_nonneg (norm_nonneg f)
    have hre : (Λ (embed f)).re = ∫ g, f g * ((d₁ g).toReal - (d₂ g).toReal) ∂ρ := by
      change Lre f = _
      rw [hLre f, hint_real hle1, hint_real hle2, ← integral_sub (hint_f_d hle1) (hint_f_d hle2)]
      refine integral_congr_ae (Eventually.of_forall fun g => by ring)
    have him : (Λ (embed f)).im = ∫ g, f g * ((d₃ g).toReal - (d₄ g).toReal) ∂ρ := by
      change Lim f = _
      rw [hLim f, hint_real hle3, hint_real hle4, ← integral_sub (hint_f_d hle3) (hint_f_d hle4)]
      refine integral_congr_ae (Eventually.of_forall fun g => by ring)
    have h1 : Λ (embed f) = ((Λ (embed f)).re : ℂ) + ((Λ (embed f)).im : ℂ) * Complex.I :=
      (Complex.re_add_im _).symm
    rw [h1, hre, him]
    have hI1 : (((∫ g, f g * ((d₁ g).toReal - (d₂ g).toReal) ∂ρ) : ℝ) : ℂ) =
        ∫ g, (((f g * ((d₁ g).toReal - (d₂ g).toReal) : ℝ) : ℂ)) ∂ρ :=
      (integral_ofReal).symm
    have hI2 : (((∫ g, f g * ((d₃ g).toReal - (d₄ g).toReal) ∂ρ) : ℝ) : ℂ) * Complex.I =
        ∫ g, (((f g * ((d₃ g).toReal - (d₄ g).toReal) : ℝ) : ℂ) * Complex.I) ∂ρ := by
      have hI2a : (((∫ g, f g * ((d₃ g).toReal - (d₄ g).toReal) ∂ρ) : ℝ) : ℂ) =
          ∫ g, (((f g * ((d₃ g).toReal - (d₄ g).toReal) : ℝ) : ℂ)) ∂ρ :=
        (integral_ofReal).symm
      rw [hI2a, ← integral_mul_const]
    rw [hI1, hI2]
    have hintR1 : Integrable (fun g => f g * ((d₁ g).toReal - (d₂ g).toReal)) ρ :=
      ((hint_f_d hle1).sub (hint_f_d hle2)).congr (Eventually.of_forall fun g => by dsimp only [Pi.sub_apply]; ring)
    have hintR2 : Integrable (fun g => f g * ((d₃ g).toReal - (d₄ g).toReal)) ρ :=
      ((hint_f_d hle3).sub (hint_f_d hle4)).congr (Eventually.of_forall fun g => by dsimp only [Pi.sub_apply]; ring)
    have hintC1 : Integrable (fun g => ((f g * ((d₁ g).toReal - (d₂ g).toReal) : ℝ) : ℂ)) ρ :=
      hintR1.ofReal
    have hintC2 : Integrable (fun g => ((f g * ((d₃ g).toReal - (d₄ g).toReal) : ℝ) : ℂ) * Complex.I) ρ :=
      hintR2.ofReal.mul_const Complex.I
    rw [← integral_add hintC1 hintC2]
    refine integral_congr_ae ?_
    filter_upwards [hh'_ae] with g hg
    rw [hg]
    dsimp only [h]
    push_cast; ring
  have hΛ_all : ∀ f : C(BohrR, ℂ), Λ f = ∫ g, f g * h' g ∂ρ := by
    intro f
    let fre : C(BohrR, ℝ) := ⟨fun g => (f g).re, Complex.continuous_re.comp f.continuous⟩
    let fim : C(BohrR, ℝ) := ⟨fun g => (f g).im, Complex.continuous_im.comp f.continuous⟩
    have hf_eq : f = embed fre + Complex.I • embed fim := by
      ext g
      change f g = ((f g).re : ℂ) + Complex.I * ((f g).im : ℂ)
      rw [mul_comm]; exact (Complex.re_add_im (f g)).symm
    rw [hf_eq, map_add, map_smul, hΛ_real fre, hΛ_real fim, smul_eq_mul, ← integral_const_mul]
    have hint_em : ∀ u : C(BohrR, ℝ), Integrable (fun g => (u g : ℂ) * h' g) ρ := fun u =>
      Integrable.mono' (integrable_const (‖u‖ * 2))
        (((Complex.continuous_ofReal.measurable.comp u.continuous.measurable).mul hh'_meas).aestronglyMeasurable)
        (Eventually.of_forall fun g => by
          rw [norm_mul, Complex.norm_real]
          exact mul_le_mul (ContinuousMap.norm_coe_le_norm u g) (hh'_bd g) (norm_nonneg _) (norm_nonneg u))
    rw [← integral_add (hint_em fre) ((hint_em fim).const_mul Complex.I)]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change (fre g : ℂ) * h' g + Complex.I * ((fim g : ℂ) * h' g) =
      ((fre g : ℂ) + Complex.I * (fim g : ℂ)) * h' g
    ring
  let ν : Measure BohrR := ρ.withDensity (fun g => ENNReal.ofReal ‖h' g‖)
  have hν_le : ν ≤ (2 : ℝ≥0∞) • ρ := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ g in s, ENNReal.ofReal ‖h' g‖ ∂ρ
        ≤ ∫⁻ _ in s, (2 : ℝ≥0∞) ∂ρ := lintegral_mono fun g => by
          simpa using ENNReal.ofReal_le_ofReal (hh'_bd g)
      _ = 2 * ρ s := by rw [setLIntegral_const]
  have h2ρ_fin : IsFiniteMeasure ((2 : ℝ≥0∞) • ρ) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top (measure_lt_top ρ Set.univ)
  have hν_fin : IsFiniteMeasure ν := isFiniteMeasure_of_le ((2 : ℝ≥0∞) • ρ) hν_le
  let u : BohrR → ℂ := fun g => if h' g = 0 then 1 else h' g / (‖h' g‖ : ℂ)
  have hu_meas : Measurable u :=
    measurable_const.ite (measurableSet_eq_fun hh'_meas measurable_const)
      (hh'_meas.div (Complex.continuous_ofReal.measurable.comp hh'_meas.norm))
  have hu_norm : ∀ g, ‖u g‖ = 1 := fun g => by
    dsimp only [u]
    split_ifs with hg
    · simp
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hg)]
  have hmul_u : ∀ g, ((‖h' g‖ : ℝ) : ℂ) * u g = h' g := fun g => by
    dsimp only [u]
    split_ifs with hg
    · simp [hg]
    · have hne : (‖h' g‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
      exact mul_div_cancel₀ _ hne
  have hrep : ∀ f : C(BohrR, ℂ), Λ f = ∫ g, f g * u g ∂ν := fun f => by
    rw [hΛ_all f]
    dsimp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun g => ENNReal.ofReal ‖h' g‖)
      (ENNReal.continuous_ofReal.measurable.comp hh'_meas.norm)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (norm_nonneg _), Complex.real_smul]
    calc f g * h' g = f g * (((‖h' g‖ : ℝ) : ℂ) * u g) := by rw [hmul_u g]
      _ = ((‖h' g‖ : ℝ) : ℂ) * (f g * u g) := by ring
  have hnorm_le : ‖Λ‖ ≤ (ν Set.univ).toReal := by
    refine ContinuousLinearMap.opNorm_le_bound Λ ENNReal.toReal_nonneg fun f => ?_
    rw [hrep f]
    calc ‖∫ g, f g * u g ∂ν‖ ≤ ∫ g, ‖f g * u g‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ _, ‖f‖ ∂ν := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _) (Eventually.of_forall fun g => ?_)
          dsimp only
          rw [norm_mul, hu_norm g, mul_one]
          exact ContinuousMap.norm_coe_le_norm f g
      _ = (ν Set.univ).toReal * ‖f‖ := by
          rw [integral_const, smul_eq_mul, Measure.real_def]
  have hnorm_ge : (ν Set.univ).toReal ≤ ‖Λ‖ := by
    by_contra hlt
    push Not at hlt
    set ε := ((ν Set.univ).toReal - ‖Λ‖) / 4
    have hε : 0 < ε := by dsimp only [ε]; linarith
    have hint_cu : Integrable (fun g => star (u g)) ρ :=
      Integrable.mono' (integrable_const (1 : ℝ))
        (Complex.continuous_conj.measurable.comp hu_meas).aestronglyMeasurable
        (Eventually.of_forall fun g => by simp [hu_norm g])
    obtain ⟨φ, _, hφ_L1, hφ_cont, _⟩ :=
      hint_cu.exists_hasCompactSupport_integral_sub_le (ε := ε / 2) (by positivity)
    let ψ : C(BohrR, ℂ) := ⟨fun g => projUnit (φ g), continuous_projUnit.comp hφ_cont⟩
    have hψ_norm : ‖ψ‖ ≤ 1 := by
      rw [ContinuousMap.norm_le ψ zero_le_one]
      intro g; exact norm_projUnit_le_one (φ g)
    have hψ_bound : ‖Λ ψ‖ ≤ ‖Λ‖ := by
      calc ‖Λ ψ‖ ≤ ‖Λ‖ * ‖ψ‖ := Λ.le_opNorm ψ
        _ ≤ ‖Λ‖ * 1 := mul_le_mul_of_nonneg_left hψ_norm (norm_nonneg Λ)
        _ = ‖Λ‖ := mul_one _
    have hdiff_int : ‖∫ g, (1 - ψ g * u g) ∂ν‖ ≤ 2 * ε := by
      calc ‖∫ g, (1 - ψ g * u g) ∂ν‖
          ≤ ∫ g, ‖1 - ψ g * u g‖ ∂ν := norm_integral_le_integral_norm _
        _ = ∫ g, ‖h' g‖ * ‖1 - ψ g * u g‖ ∂ρ := by
            dsimp only [ν]
            rw [integral_withDensity_eq_integral_toReal_smul (f := fun g => ENNReal.ofReal ‖h' g‖)
              (ENNReal.continuous_ofReal.measurable.comp hh'_meas.norm)
              (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
            refine integral_congr_ae (Eventually.of_forall fun g => ?_)
            dsimp only
            rw [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
        _ ≤ ∫ g, 2 * (2 * ‖star (u g) - φ g‖) ∂ρ := by
            refine integral_mono_of_nonneg
              (Eventually.of_forall fun g => mul_nonneg (norm_nonneg _) (norm_nonneg _))
              ((hint_cu.sub (Integrable.mono' (integrable_const (‖ContinuousMap.mk φ hφ_cont‖))
                hφ_cont.aestronglyMeasurable
                (Eventually.of_forall fun g => ContinuousMap.norm_coe_le_norm ⟨φ, hφ_cont⟩ g))).norm.const_mul 2 |>.const_mul 2)
              (Eventually.of_forall fun g => ?_)
            dsimp only
            have h1 : ‖1 - ψ g * u g‖ = ‖ψ g - star (u g)‖ := by
              have hsu : star (u g) * u g = 1 := by
                rw [RCLike.star_def, Complex.conj_mul', hu_norm g]; norm_num
              have heq : 1 - ψ g * u g = -(ψ g - star (u g)) * u g := by
                rw [neg_mul, sub_mul, hsu]; ring
              rw [heq, norm_mul, norm_neg, hu_norm g, mul_one]
            have h2 : ‖ψ g - star (u g)‖ ≤ 2 * ‖φ g - star (u g)‖ :=
              norm_projUnit_sub_le (by simp [hu_norm g])
            rw [h1, norm_sub_rev (star (u g)) (φ g)]
            exact mul_le_mul (hh'_bd g) h2 (norm_nonneg _) zero_le_two
        _ = 4 * ∫ g, ‖star (u g) - φ g‖ ∂ρ := by
            simp_rw [← mul_assoc]; rw [integral_const_mul]; norm_num
        _ ≤ 4 * (ε / 2) := mul_le_mul_of_nonneg_left hφ_L1 (by norm_num)
        _ = 2 * ε := by ring
    have hint1 : Integrable (fun _ : BohrR => (1 : ℂ)) ν := integrable_const _
    have hint2 : Integrable (fun g : BohrR => ψ g * u g) ν :=
      Integrable.mono' (integrable_const (1 : ℝ))
        ((ψ.continuous.measurable.mul hu_meas).aestronglyMeasurable)
        (Eventually.of_forall fun g => by
          rw [norm_mul, hu_norm g, mul_one]; exact norm_projUnit_le_one _)
    have hsub_eq : ∫ g, (1 - ψ g * u g) ∂ν = ((ν Set.univ).toReal : ℂ) - Λ ψ := by
      rw [integral_sub hint1 hint2, integral_const, Measure.real_def, Complex.real_smul, mul_one, ← hrep ψ]
    rw [hsub_eq] at hdiff_int
    have htri : (ν Set.univ).toReal - ‖Λ ψ‖ ≤ ‖((ν Set.univ).toReal : ℂ) - Λ ψ‖ := by
      have h1 := norm_sub_norm_le ((ν Set.univ).toReal : ℂ) (Λ ψ)
      rwa [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg] at h1
    have h2ε : 2 * ε = ((ν Set.univ).toReal - ‖Λ‖) / 2 := by dsimp only [ε]; ring
    linarith
  exact ⟨⟨ν, ρ, u, hν_fin, inferInstance, hρ_reg, hν_le, hu_meas, hu_norm, hrep,
    le_antisymm hnorm_ge hnorm_le⟩⟩

/- Part 3D: Circle divisibility, Zorn character extension, AnnSubgroup, and Haar measure `mH` -/

lemma circle_divisible (z : Circle) {n : ℕ} (hn : 0 < n) : ∃ w : Circle, w ^ n = z := by
  refine ⟨Circle.exp (Complex.arg (z : ℂ) / n), ?_⟩
  rw [← Circle.exp_natCast_mul]
  have hmul : (n : ℝ) * (Complex.arg (z : ℂ) / n) = Complex.arg (z : ℂ) :=
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')
  rw [hmul]
  apply Subtype.ext
  rw [Circle.coe_exp]
  have h1 := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at h1
  exact h1

structure PartialChar where
  H : AddSubgroup ℝ
  f : ℝ → Circle
  map_add : ∀ x ∈ H, ∀ y ∈ H, f (x + y) = f x * f y
  outside : ∀ x, x ∉ H → f x = 1

lemma partialChar_map_zero (p : PartialChar) : p.f 0 = 1 := by
  have h := p.map_add 0 p.H.zero_mem 0 p.H.zero_mem
  rw [add_zero] at h
  exact mul_left_cancel (by simpa using h.symm : p.f 0 * p.f 0 = p.f 0 * 1)

lemma partialChar_map_neg (p : PartialChar) {x : ℝ} (hx : x ∈ p.H) : p.f (-x) = (p.f x)⁻¹ := by
  have h := p.map_add x hx (-x) (p.H.neg_mem hx)
  rw [add_neg_cancel, partialChar_map_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma partialChar_map_zsmul (p : PartialChar) (k : ℤ) {x : ℝ} (hx : x ∈ p.H) :
    p.f (k • x) = (p.f x) ^ k := by
  induction k using Int.induction_on with
  | zero => simp [partialChar_map_zero]
  | succ n ih =>
    have h1 : ((n : ℤ) + 1) • x = (n : ℤ) • x + x := by rw [add_zsmul, one_zsmul]
    rw [h1, p.map_add _ (p.H.zsmul_mem hx _) _ hx, ih, zpow_add_one]
  | pred n ih =>
    have h1 : (-(n : ℤ) - 1) • x = (-(n : ℤ)) • x + (-x) := by
      rw [sub_eq_add_neg, add_zsmul, neg_one_zsmul]
    rw [h1, p.map_add _ (p.H.zsmul_mem hx _) _ (p.H.neg_mem hx), ih, partialChar_map_neg p hx,
      zpow_sub_one]

instance : PartialOrder PartialChar where
  le p q := p.H ≤ q.H ∧ ∀ x ∈ p.H, p.f x = q.f x
  le_refl p := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1, fun x hx => (hpq.2 x hx).trans (hqr.2 x (hpq.1 hx))⟩
  le_antisymm p q hpq hqp := by
    have hH : p.H = q.H := le_antisymm hpq.1 hqp.1
    have hf : p.f = q.f := by
      funext x
      by_cases hx : x ∈ p.H
      · exact hpq.2 x hx
      · have hx' : x ∉ q.H := hH ▸ hx
        rw [p.outside x hx, q.outside x hx']
    cases p; cases q; simp only [PartialChar.mk.injEq]; exact ⟨hH, hf⟩

lemma partialChar_extend_one_step (p : PartialChar) (x : ℝ) (_hx : x ∉ p.H)
    (w : Circle) (hw : ∀ k : ℤ, k • x ∈ p.H → w ^ k = p.f (k • x)) :
    ∃ q : PartialChar, p ≤ q ∧ x ∈ q.H ∧ q.f x = w := by
  let K : AddSubgroup ℝ := p.H ⊔ AddSubgroup.zmultiples x
  have hmemK : ∀ y, y ∈ K ↔ ∃ h ∈ p.H, ∃ k : ℤ, y = h + k • x := fun y => by
    rw [AddSubgroup.mem_sup]
    constructor
    · rintro ⟨h, hh, z, hz, rfl⟩
      rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨k, rfl⟩
      exact ⟨h, hh, k, rfl⟩
    · rintro ⟨h, hh, k, rfl⟩
      exact ⟨h, hh, k • x, AddSubgroup.mem_zmultiples_iff.mpr ⟨k, rfl⟩, rfl⟩
  have hwelldef : ∀ h₁ ∈ p.H, ∀ h₂ ∈ p.H, ∀ k₁ k₂ : ℤ,
      h₁ + k₁ • x = h₂ + k₂ • x → p.f h₁ * w ^ k₁ = p.f h₂ * w ^ k₂ := by
    intro h₁ hh₁ h₂ hh₂ k₁ k₂ heq
    have hdiff : (k₁ - k₂) • x = h₂ - h₁ := by
      rw [sub_zsmul]; linarith
    have hkmem : (k₁ - k₂) • x ∈ p.H := by rw [hdiff]; exact p.H.sub_mem hh₂ hh₁
    have hwk := hw (k₁ - k₂) hkmem
    rw [hdiff, show h₂ - h₁ = h₂ + (-h₁) from sub_eq_add_neg h₂ h₁,
      p.map_add h₂ hh₂ (-h₁) (p.H.neg_mem hh₁), partialChar_map_neg p hh₁, zpow_sub] at hwk
    calc p.f h₁ * w ^ k₁ = p.f h₁ * (w ^ k₁ * (w ^ k₂)⁻¹) * w ^ k₂ := by group
      _ = p.f h₁ * (p.f h₂ * (p.f h₁)⁻¹) * w ^ k₂ := by rw [← div_eq_mul_inv] at hwk; rw [← div_eq_mul_inv, hwk]
      _ = (p.f h₁ * (p.f h₁)⁻¹) * p.f h₂ * w ^ k₂ := by ac_rfl
      _ = p.f h₂ * w ^ k₂ := by simp
  classical
  let g : ℝ → Circle := fun y =>
    if hy : y ∈ K then
      let ex := (hmemK y).mp hy
      p.f ex.choose * w ^ ex.choose_spec.2.choose
    else 1
  have hg_val : ∀ h ∈ p.H, ∀ k : ℤ, g (h + k • x) = p.f h * w ^ k := fun h hh k => by
    have hy : h + k • x ∈ K := (hmemK _).mpr ⟨h, hh, k, rfl⟩
    simp only [g, dif_pos hy]
    set ex := (hmemK (h + k • x)).mp hy
    exact hwelldef ex.choose ex.choose_spec.1 h hh ex.choose_spec.2.choose k
      ex.choose_spec.2.choose_spec.symm
  refine ⟨⟨K, g, ?_, fun y hy => dif_neg hy⟩, ⟨le_sup_left, fun h hh => ?_⟩,
    AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x), ?_⟩
  · intro y₁ hy₁ y₂ hy₂
    obtain ⟨h₁, hh₁, k₁, rfl⟩ := (hmemK y₁).mp hy₁
    obtain ⟨h₂, hh₂, k₂, rfl⟩ := (hmemK y₂).mp hy₂
    have heq : (h₁ + k₁ • x) + (h₂ + k₂ • x) = (h₁ + h₂) + (k₁ + k₂) • x := by
      rw [add_zsmul]; ring
    rw [heq, hg_val _ (p.H.add_mem hh₁ hh₂), hg_val h₁ hh₁ k₁, hg_val h₂ hh₂ k₂,
      p.map_add h₁ hh₁ h₂ hh₂, zpow_add]
    ac_rfl
  · simpa using (hg_val h hh 0).symm
  · have h1 := hg_val 0 p.H.zero_mem 1
    simpa [partialChar_map_zero] using h1

lemma exists_bohr_eq_one_on_ne_one_at (Γ : AddSubgroup ℝ) {x : ℝ} (hx : x ∉ Γ) :
    ∃ χ : BohrR, (∀ y ∈ Γ, χ.1 y = 1) ∧ χ.1 x ≠ 1 := by
  let p0 : PartialChar := ⟨Γ, fun _ => 1, fun _ _ _ _ => by simp, fun _ _ => rfl⟩
  have hex_w : ∃ w : Circle, w ≠ 1 ∧ ∀ k : ℤ, k • x ∈ Γ → w ^ k = 1 := by
    by_cases htor : ∃ n : ℕ, 0 < n ∧ (n : ℤ) • x ∈ Γ
    · classical
      let m := Nat.find htor
      have hm_spec : 0 < m ∧ (m : ℤ) • x ∈ Γ := Nat.find_spec htor
      have hm_ge2 : 2 ≤ m := by
        by_contra hlt
        push Not at hlt
        have hm1 : m = 1 := by omega
        have : x ∈ Γ := by simpa [hm1] using hm_spec.2
        exact hx this
      let w : Circle := Circle.exp (2 * Real.pi / m)
      have hw_ne : w ≠ 1 := by
        intro heq
        have hcoe : Complex.exp ((2 * Real.pi / m : ℝ) * Complex.I) = 1 := by
          have := congrArg Subtype.val heq
          simpa [w, Circle.coe_exp] using this
        rw [Complex.exp_eq_one_iff] at hcoe
        obtain ⟨k, hk⟩ := hcoe
        have hk' : (2 * Real.pi / m : ℝ) = k * (2 * Real.pi) := by
          have := congrArg Complex.im hk
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_one, mul_zero, add_zero, Complex.intCast_re, Complex.intCast_im, zero_add] at this
          simpa [mul_assoc] using this
        have hdiv : (1 : ℝ) / m = (k : ℝ) := by
          have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          have : (2 * Real.pi) * (1 / m) = (2 * Real.pi) * (k : ℝ) := by
            rw [mul_one_div, hk', mul_comm]
          exact mul_left_cancel₀ h2pi this
        have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_spec.1
        have hlt1 : (1 : ℝ) / m < 1 := by
          rw [div_lt_one hm_pos]
          have : (2 : ℝ) ≤ m := Nat.ofNat_le_cast.mpr hm_ge2
          linarith
        have hpos1 : (0 : ℝ) < 1 / m := by positivity
        have hk_pos : (0 : ℤ) < k := by
          have : (0 : ℝ) < (k : ℝ) := by linarith
          exact Int.cast_pos.mp this
        have hk_lt : k < 1 := by
          have : (k : ℝ) < (1 : ℝ) := by linarith
          exact_mod_cast this
        omega
      refine ⟨w, hw_ne, fun k hk => ?_⟩
      have hdiv : (m : ℤ) ∣ k := by
        have hmod : (k % (m : ℤ)) • x ∈ Γ := by
          have h1 : k = (m : ℤ) * (k / m) + k % m := (Int.mul_ediv_add_emod k m).symm
          have h2 : (k % (m : ℤ)) • x = k • x - (k / m) • ((m : ℤ) • x) := by
            have h1r : (k : ℝ) = ((m : ℤ) : ℝ) * ((k / m : ℤ) : ℝ) + ((k % m : ℤ) : ℝ) := by exact_mod_cast h1
            simp only [zsmul_eq_mul]
            rw [h1r]; ring
          rw [h2]
          exact Γ.sub_mem hk (Γ.zsmul_mem hm_spec.2 _)
        have hm_posZ : (0 : ℤ) < m := Int.natCast_pos.mpr hm_spec.1
        have hr_nonneg : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k hm_posZ.ne'
        have hr_lt : k % (m : ℤ) < m := Int.emod_lt_of_pos k hm_posZ
        lift (k % (m : ℤ)) to ℕ using hr_nonneg with r hr
        have hr_ltN : r < m := by exact_mod_cast hr_lt
        by_cases hr0 : r = 0
        · exact Int.dvd_iff_emod_eq_zero.mpr (by rw [← hr, hr0]; rfl)
        · exfalso
          exact Nat.find_min htor hr_ltN ⟨Nat.pos_of_ne_zero hr0, by simpa [← hr] using hmod⟩
      rcases hdiv with ⟨q, rfl⟩
      rw [zpow_mul]
      have hwm : w ^ (m : ℤ) = 1 := by
        rw [zpow_natCast, ← Circle.exp_natCast_mul]
        have hmul : (m : ℝ) * (2 * Real.pi / m) = 2 * Real.pi :=
          mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm_spec.1.ne')
        rw [hmul]
        apply Subtype.ext
        rw [Circle.coe_exp, Circle.coe_one]
        simpa [Complex.ofReal_mul, mul_assoc] using Complex.exp_two_pi_mul_I
      rw [hwm, one_zpow]
    · push Not at htor
      refine ⟨Circle.exp Real.pi, Circle.exp_pi_ne_one, fun k hk => ?_⟩
      have hk0 : k = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hpos : 0 < (-k).toNat := by omega
          have hmem : (((-k).toNat : ℤ)) • x ∈ Γ := by
            have heq : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
            rw [heq, neg_zsmul]
            exact Γ.neg_mem hk
          exact htor (-k).toNat hpos hmem
        · have hpos : 0 < k.toNat := by omega
          have hmem : ((k.toNat : ℤ)) • x ∈ Γ := by
            have heq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
            rwa [heq]
          exact htor k.toNat hpos hmem
      simp [hk0]
  obtain ⟨w, hw_ne, hwk⟩ := hex_w
  obtain ⟨p1, hp01, hx1, hfx1⟩ := partialChar_extend_one_step p0 x hx w (fun k hk => hwk k hk)
  obtain ⟨pm, hp1m, hmax⟩ := zorn_le_nonempty_Ici₀ p1 (fun c hc_sub hc_chain y hyc => by
    classical
    let Hub : AddSubgroup ℝ :=
      { carrier := ⋃ p ∈ c, (p.H : Set ℝ)
        zero_mem' := Set.mem_biUnion hyc y.H.zero_mem
        add_mem' := by
          intro a b ha hb
          rw [Set.mem_iUnion₂] at ha hb
          rcases ha with ⟨pa, hpa, ha⟩
          rcases hb with ⟨pb, hpb, hb⟩
          rcases hc_chain.total hpa hpb with hle | hle
          · exact Set.mem_biUnion hpb (pb.H.add_mem (hle.1 ha) hb)
          · exact Set.mem_biUnion hpa (pa.H.add_mem ha (hle.1 hb))
        neg_mem' := by
          intro a ha
          rw [Set.mem_iUnion₂] at ha
          rcases ha with ⟨pa, hpa, ha⟩
          exact Set.mem_biUnion hpa (pa.H.neg_mem ha) }
    let fub : ℝ → Circle := fun r =>
      if hr : ∃ p ∈ c, r ∈ p.H then (Classical.choose hr).f r else 1
    have hfub_eq : ∀ p ∈ c, ∀ r ∈ p.H, fub r = p.f r := fun p hp r hr => by
      have hex : ∃ q ∈ c, r ∈ q.H := ⟨p, hp, hr⟩
      simp only [fub, dif_pos hex]
      set q := Classical.choose hex
      have hqc : q ∈ c := (Classical.choose_spec hex).1
      have hrq : r ∈ q.H := (Classical.choose_spec hex).2
      rcases hc_chain.total hqc hp with hle | hle
      · exact hle.2 r hrq
      · exact (hle.2 r hr).symm
    let pub : PartialChar :=
      { H := Hub
        f := fub
        map_add := by
          intro a ha b hb
          change a ∈ ⋃ p ∈ c, (p.H : Set ℝ) at ha
          change b ∈ ⋃ p ∈ c, (p.H : Set ℝ) at hb
          rw [Set.mem_iUnion₂] at ha hb
          rcases ha with ⟨pa, hpa, ha⟩
          rcases hb with ⟨pb, hpb, hb⟩
          rcases hc_chain.total hpa hpb with hle | hle
          · have hab : a + b ∈ pb.H := pb.H.add_mem (hle.1 ha) hb
            rw [hfub_eq pb hpb _ hab, hfub_eq pb hpb a (hle.1 ha), hfub_eq pb hpb b hb]
            exact pb.map_add a (hle.1 ha) b hb
          · have hab : a + b ∈ pa.H := pa.H.add_mem ha (hle.1 hb)
            rw [hfub_eq pa hpa _ hab, hfub_eq pa hpa a ha, hfub_eq pa hpa b (hle.1 hb)]
            exact pa.map_add a ha b (hle.1 hb)
        outside := fun r hr => by
          have hnex : ¬ ∃ p ∈ c, r ∈ p.H := fun ⟨p, hp, hrp⟩ => hr (Set.mem_biUnion hp hrp)
          exact dif_neg hnex }
    refine ⟨pub, fun p hp => ⟨fun r hr => Set.mem_biUnion hp hr, fun r hr => (hfub_eq p hp r hr).symm⟩⟩)
    p1 le_rfl
  have htop : ∀ r : ℝ, r ∈ pm.H := by
    intro r
    by_contra hr
    have hex_u : ∃ u : Circle, ∀ k : ℤ, k • r ∈ pm.H → u ^ k = pm.f (k • r) := by
      by_cases htor : ∃ n : ℕ, 0 < n ∧ (n : ℤ) • r ∈ pm.H
      · classical
        let m := Nat.find htor
        have hm_spec : 0 < m ∧ (m : ℤ) • r ∈ pm.H := Nat.find_spec htor
        obtain ⟨u, hu⟩ := circle_divisible (pm.f ((m : ℤ) • r)) hm_spec.1
        refine ⟨u, fun k hk => ?_⟩
        have hdiv : (m : ℤ) ∣ k := by
          have hmod : (k % (m : ℤ)) • r ∈ pm.H := by
            have h1 : k = (m : ℤ) * (k / m) + k % m := (Int.mul_ediv_add_emod k m).symm
            have h2 : (k % (m : ℤ)) • r = k • r - (k / m) • ((m : ℤ) • r) := by
              have h1r : (k : ℝ) = ((m : ℤ) : ℝ) * ((k / m : ℤ) : ℝ) + ((k % m : ℤ) : ℝ) := by exact_mod_cast h1
              simp only [zsmul_eq_mul]; rw [h1r]; ring
            rw [h2]
            exact pm.H.sub_mem hk (pm.H.zsmul_mem hm_spec.2 _)
          have hm_posZ : (0 : ℤ) < m := Int.natCast_pos.mpr hm_spec.1
          have hr_nonneg : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k hm_posZ.ne'
          have hr_lt : k % (m : ℤ) < m := Int.emod_lt_of_pos k hm_posZ
          lift (k % (m : ℤ)) to ℕ using hr_nonneg with s hs
          have hs_ltN : s < m := by exact_mod_cast hr_lt
          by_cases hs0 : s = 0
          · exact Int.dvd_iff_emod_eq_zero.mpr (by rw [← hs, hs0]; rfl)
          · exfalso
            exact Nat.find_min htor hs_ltN ⟨Nat.pos_of_ne_zero hs0, by simpa [← hs] using hmod⟩
        rcases hdiv with ⟨q, rfl⟩
        rw [zpow_mul, zpow_natCast, hu, mul_comm ((m : ℤ)) q, mul_zsmul, partialChar_map_zsmul pm q hm_spec.2]
      · push Not at htor
        refine ⟨1, fun k hk => ?_⟩
        have hk0 : k = 0 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hpos : 0 < (-k).toNat := by omega
            have hmem : (((-k).toNat : ℤ)) • r ∈ pm.H := by
              have heq : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
              rw [heq, neg_zsmul]
              exact pm.H.neg_mem hk
            exact htor (-k).toNat hpos hmem
          · have hpos : 0 < k.toNat := by omega
            have hmem : ((k.toNat : ℤ)) • r ∈ pm.H := by
              have heq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
              rwa [heq]
            exact htor k.toNat hpos hmem
        simp [hk0, partialChar_map_zero]
    obtain ⟨u, hu⟩ := hex_u
    obtain ⟨q, hpmq, hrq, _⟩ := partialChar_extend_one_step pm r hr u hu
    have hqle : q ≤ pm := hmax hpmq
    exact hr (hqle.1 hrq)
  refine ⟨⟨pm.f, fun a b => pm.map_add a (htop a) b (htop b)⟩, fun y hy => ?_, ?_⟩
  · have h1 := (hp01.trans hp1m).2 y hy
    simpa [p0] using h1.symm
  · have h1 := hp1m.2 x hx1
    change pm.f x ≠ 1
    rw [← h1, hfx1]
    exact hw_ne

def AnnSubgroup (Γ : AddSubgroup ℝ) : Subgroup BohrR where
  carrier := {χ : BohrR | ∀ y ∈ Γ, χ.1 y = 1}
  mul_mem' {a b} ha hb y hy := by
    change a.1 y * b.1 y = 1
    rw [ha y hy, hb y hy, mul_one]
  one_mem' _ _ := rfl
  inv_mem' {a} ha y hy := by
    change (a.1 y)⁻¹ = 1
    rw [ha y hy, inv_one]

lemma annSubgroup_isClosed (Γ : AddSubgroup ℝ) : IsClosed (AnnSubgroup Γ : Set BohrR) := by
  have heq : (AnnSubgroup Γ : Set BohrR) = ⋂ y ∈ (Γ : Set ℝ), {χ : BohrR | χ.1 y = 1} := by
    ext χ; simp [AnnSubgroup]
  rw [heq]
  exact isClosed_biInter fun y _ =>
    isClosed_eq ((continuous_apply y).comp continuous_subtype_val) continuous_const

instance (Γ : AddSubgroup ℝ) : CompactSpace (AnnSubgroup Γ) :=
  isCompact_iff_compactSpace.mp (annSubgroup_isClosed Γ).isCompact

instance (Γ : AddSubgroup ℝ) : MeasurableSpace (AnnSubgroup Γ) := borel (AnnSubgroup Γ)
instance (Γ : AddSubgroup ℝ) : BorelSpace (AnnSubgroup Γ) := ⟨rfl⟩

noncomputable def mH_sub (Γ : AddSubgroup ℝ) : Measure (AnnSubgroup Γ) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (AnnSubgroup Γ))

instance (Γ : AddSubgroup ℝ) : (mH_sub Γ).IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _

instance (Γ : AddSubgroup ℝ) : (mH_sub Γ).Regular :=
  Measure.regular_haarMeasure

instance (Γ : AddSubgroup ℝ) : IsProbabilityMeasure (mH_sub Γ) := by
  refine ⟨?_⟩
  change Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (AnnSubgroup Γ))
    ((⊤ : TopologicalSpace.PositiveCompacts (AnnSubgroup Γ)) : Set (AnnSubgroup Γ)) = 1
  exact Measure.haarMeasure_self

noncomputable def mH (Γ : AddSubgroup ℝ) : Measure BohrR :=
  (mH_sub Γ).map Subtype.val

instance (Γ : AddSubgroup ℝ) : IsProbabilityMeasure (mH Γ) :=
  Measure.isProbabilityMeasure_map continuous_subtype_val.measurable.aemeasurable

lemma mH_compl_annSubgroup (Γ : AddSubgroup ℝ) : mH Γ (AnnSubgroup Γ : Set BohrR)ᶜ = 0 := by
  dsimp only [mH]
  rw [Measure.map_apply continuous_subtype_val.measurable (annSubgroup_isClosed Γ).measurableSet.compl]
  have hempty : Subtype.val ⁻¹' (AnnSubgroup Γ : Set BohrR)ᶜ = (∅ : Set (AnnSubgroup Γ)) :=
    Set.eq_empty_iff_forall_notMem.mpr fun h hh => hh h.2
  rw [hempty, measure_empty]

lemma integral_eChar_mH (Γ : AddSubgroup ℝ) (x : ℝ) :
    ∫ g, eChar x g ∂(mH Γ) = Set.indicator (Γ : Set ℝ) (fun _ => (1 : ℂ)) x := by
  dsimp only [mH]
  rw [integral_map continuous_subtype_val.measurable.aemeasurable (eChar x).continuous.aestronglyMeasurable]
  by_cases hx : x ∈ Γ
  · rw [Set.indicator_of_mem hx]
    have heq : (fun h : AnnSubgroup Γ => eChar x h.1) = fun _ => (1 : ℂ) := by
      funext h; simp only [eChar_apply, h.2 x hx, Circle.coe_one]
    rw [heq, integral_const, Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul]
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨χ₀, hχ₀_ann, hχ₀_ne⟩ := exists_bohr_eq_one_on_ne_one_at Γ hx
    let h₀ : AnnSubgroup Γ := ⟨χ₀, hχ₀_ann⟩
    have hinv : ∫ h : AnnSubgroup Γ, eChar x (h₀ * h).1 ∂(mH_sub Γ) =
        ∫ h : AnnSubgroup Γ, eChar x h.1 ∂(mH_sub Γ) :=
      integral_mul_left_eq_self (fun h : AnnSubgroup Γ => eChar x h.1) h₀
    have hmul : ∀ h : AnnSubgroup Γ, eChar x (h₀ * h).1 = (χ₀.1 x : ℂ) * eChar x h.1 := fun h => by
      change ((χ₀.1 x * h.1.1 x : Circle) : ℂ) = (χ₀.1 x : ℂ) * (h.1.1 x : ℂ)
      exact Circle.coe_mul _ _
    simp_rw [hmul] at hinv
    rw [integral_const_mul] at hinv
    have hne : (χ₀.1 x : ℂ) - 1 ≠ 0 := by
      intro h0
      exact hχ₀_ne (Subtype.ext (sub_eq_zero.mp h0))
    have hprod : ((χ₀.1 x : ℂ) - 1) * ∫ h : AnnSubgroup Γ, eChar x h.1 ∂(mH_sub Γ) = 0 := by
      linear_combination hinv
    exact (mul_eq_zero.mp hprod).resolve_left hne

/- Part 3E: Modulation, norm-drop rigidity, singularity annihilation, and Riemann-Lebesgue -/

noncomputable def modDual (y : ℝ) (Λ : StrongDual ℂ C(BohrR, ℂ)) : StrongDual ℂ C(BohrR, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => Λ (eChar y * f)
      map_add' := fun f g => by rw [mul_add, map_add]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [mul_smul_comm, map_smul, smul_eq_mul] }
    ‖Λ‖ (fun f => by
      calc ‖Λ (eChar y * f)‖ ≤ ‖Λ‖ * ‖eChar y * f‖ := Λ.le_opNorm _
        _ ≤ ‖Λ‖ * (‖eChar y‖ * ‖f‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg Λ)
        _ = ‖Λ‖ * ‖f‖ := by rw [norm_eChar, one_mul])

@[simp] lemma modDual_apply (y : ℝ) (Λ : StrongDual ℂ C(BohrR, ℂ)) (f : C(BohrR, ℂ)) :
    modDual y Λ f = Λ (eChar y * f) := rfl

lemma modDual_eChar (y x : ℝ) (Λ : StrongDual ℂ C(BohrR, ℂ)) :
    modDual y Λ (eChar x) = Λ (eChar (y + x)) := by
  rw [modDual_apply, ← eChar_add]

lemma modDual_zero (Λ : StrongDual ℂ C(BohrR, ℂ)) : modDual 0 Λ = Λ := by
  ext f; rw [modDual_apply, eChar_zero, one_mul]

lemma modDual_add (y₁ y₂ : ℝ) (Λ : StrongDual ℂ C(BohrR, ℂ)) :
    modDual (y₁ + y₂) Λ = modDual y₁ (modDual y₂ Λ) := by
  ext f; simp only [modDual_apply, eChar_add]; congr 1; ring

lemma norm_modDual (y : ℝ) (Λ : StrongDual ℂ C(BohrR, ℂ)) : ‖modDual y Λ‖ = ‖Λ‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg Λ) _
  · have h1 : ‖modDual (-y) (modDual y Λ)‖ ≤ ‖modDual y Λ‖ :=
      LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
    rw [← modDual_add, neg_add_cancel, modDual_zero] at h1
    exact h1

lemma modDual_sub (y : ℝ) (Λ₁ Λ₂ : StrongDual ℂ C(BohrR, ℂ)) :
    modDual y (Λ₁ - Λ₂) = modDual y Λ₁ - modDual y Λ₂ := by
  ext f; simp [modDual_apply]

lemma modDual_add_dual (y : ℝ) (Λ₁ Λ₂ : StrongDual ℂ C(BohrR, ℂ)) :
    modDual y (Λ₁ + Λ₂) = modDual y Λ₁ + modDual y Λ₂ := by
  ext f; simp [modDual_apply]

lemma continuous_modDual_weak (y : ℝ) :
    Continuous (fun μ : WeakDual ℂ C(BohrR, ℂ) =>
      StrongDual.toWeakDual (modDual y (WeakDual.toStrongDual μ))) := by
  refine WeakBilin.continuous_of_continuous_eval _ fun f => ?_
  change Continuous (fun μ : WeakDual ℂ C(BohrR, ℂ) => WeakDual.toStrongDual μ (eChar y * f))
  exact WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) (eChar y * f)

lemma isClosed_range_intCast_complex : IsClosed (Set.range (Int.cast : ℤ → ℂ)) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro z hz
  let n : ℤ := ⌊z.re⌋
  have h1 : z ≠ (n : ℂ) := fun h => hz ⟨n, h.symm⟩
  have h2 : z ≠ ((n + 1 : ℤ) : ℂ) := fun h => hz ⟨n + 1, h.symm⟩
  let r : ℝ := min (min (dist z (n : ℂ)) (dist z ((n + 1 : ℤ) : ℂ))) 1
  have hr : 0 < r := lt_min (lt_min (dist_pos.mpr h1) (dist_pos.mpr h2)) zero_lt_one
  refine ⟨r, hr, fun w hw ⟨k, hk⟩ => ?_⟩
  rw [Metric.mem_ball, ← hk] at hw
  have hdist : dist z (k : ℂ) < r := by rwa [dist_comm]
  have hre : |z.re - (k : ℝ)| ≤ dist z (k : ℂ) := by
    rw [Complex.dist_eq]
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - (k : ℂ))
  have hn_le : (n : ℝ) ≤ z.re := Int.floor_le z.re
  have hlt_n1 : z.re < (n : ℝ) + 1 := Int.lt_floor_add_one z.re
  by_cases hkn : k = n
  · rw [hkn] at hdist
    have : r ≤ dist z (n : ℂ) := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · by_cases hkn1 : k = n + 1
    · rw [hkn1] at hdist
      have : r ≤ dist z ((n + 1 : ℤ) : ℂ) := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    · have hle_or_ge : k ≤ n - 1 ∨ n + 2 ≤ k := by omega
      have hge1 : 1 ≤ |z.re - (k : ℝ)| := by
        rcases hle_or_ge with hle | hge
        · have hkr : (k : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast hle
          rw [abs_of_nonneg (by linarith)]; linarith
        · have hkr : (n : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hge
          rw [abs_of_nonpos (by linarith)]; linarith
      have : r ≤ 1 := min_le_right _ _
      linarith

lemma isClosed_nonzero_intCast_complex :
    IsClosed {z : ℂ | ∃ n : ℤ, n ≠ 0 ∧ z = (n : ℂ)} := by
  have heq : {z : ℂ | ∃ n : ℤ, n ≠ 0 ∧ z = (n : ℂ)} =
      Set.range (Int.cast : ℤ → ℂ) ∩ {z : ℂ | 1 ≤ ‖z‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_range]
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n, rfl⟩, ?_⟩
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hn
    · rintro ⟨⟨n, rfl⟩, hnorm⟩
      refine ⟨n, ?_, rfl⟩
      intro h0
      rw [h0, Int.cast_zero, norm_zero] at hnorm
      norm_num at hnorm
  rw [heq]
  exact isClosed_range_intCast_complex.inter (isClosed_le continuous_const continuous_norm)

lemma norm_sub_le_two_mul_one_sub_mul {a b z : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖a - b‖ ≤ 2 * (‖1 - z * a‖ + ‖1 - z * b‖) := by
  by_cases hz : (1 / 2 : ℝ) ≤ ‖z‖
  · have h1 : ‖z‖ * ‖a - b‖ ≤ ‖1 - z * a‖ + ‖1 - z * b‖ := by
      have heq : z * (a - b) = (1 - z * b) - (1 - z * a) := by ring
      calc ‖z‖ * ‖a - b‖ = ‖z * (a - b)‖ := (norm_mul z (a - b)).symm
        _ = ‖(1 - z * b) - (1 - z * a)‖ := by rw [heq]
        _ ≤ ‖1 - z * b‖ + ‖1 - z * a‖ := norm_sub_le _ _
        _ = ‖1 - z * a‖ + ‖1 - z * b‖ := add_comm _ _
    have h2 : ‖a - b‖ ≤ 2 * (‖z‖ * ‖a - b‖) := by nlinarith [norm_nonneg (a - b)]
    linarith
  · push Not at hz
    have hza : 1 / 2 < ‖1 - z * a‖ := by
      have h1 : ‖(1 : ℂ)‖ - ‖z * a‖ ≤ ‖1 - z * a‖ := norm_sub_norm_le 1 (z * a)
      rw [norm_one, norm_mul, ha, mul_one] at h1
      linarith
    have hzb : 1 / 2 < ‖1 - z * b‖ := by
      have h1 : ‖(1 : ℂ)‖ - ‖z * b‖ ≤ ‖1 - z * b‖ := norm_sub_norm_le 1 (z * b)
      rw [norm_one, norm_mul, hb, mul_one] at h1
      linarith
    have hab : ‖a - b‖ ≤ 2 := by
      calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
        _ = 2 := by rw [ha, hb]; norm_num
    linarith

lemma norm_one_sub_le_amgm {w : ℂ} (hw : ‖w‖ ≤ 1) {t : ℝ} (ht : 0 < t) :
    ‖1 - w‖ ≤ t * (1 - w.re) + 1 / (2 * t) := by
  have hsq : ‖1 - w‖ ^ 2 ≤ 2 * (1 - w.re) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hwsq : w.re * w.re + w.im * w.im ≤ 1 := by
      have h1 := Complex.normSq_eq_norm_sq w
      rw [Complex.normSq_apply] at h1
      nlinarith [norm_nonneg w]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, neg_mul,
      mul_neg, neg_neg]
    linarith
  have ham : ‖1 - w‖ ≤ (t / 2) * ‖1 - w‖ ^ 2 + 1 / (2 * t) := by
    have hnn : 0 ≤ (t * ‖1 - w‖ - 1) ^ 2 := sq_nonneg _
    have h2t : 0 < 2 * t := by positivity
    apply sub_nonneg.mp
    have heq : (t / 2) * ‖1 - w‖ ^ 2 + 1 / (2 * t) - ‖1 - w‖ =
        (t * ‖1 - w‖ - 1) ^ 2 / (2 * t) := by
      field_simp [ht.ne']; ring
    rw [heq]
    exact div_nonneg hnn h2t.le
  nlinarith

lemma modDual_eq_of_near_norm {η : StrongDual ℂ C(BohrR, ℂ)}
    (hint : ∀ x : ℝ, ∃ n : ℤ, η (eChar x) = (n : ℂ))
    (hη_pos : 0 < ‖η‖)
    {f : C(BohrR, ℂ)} (hf : ‖f‖ ≤ 1)
    {y₁ y₂ : ℝ}
    (hy₁ : ‖η‖ - 1 / (64 * ‖η‖) < ((modDual y₁ η) f).re)
    (hy₂ : ‖η‖ - 1 / (64 * ‖η‖) < ((modDual y₂ η) f).re) :
    modDual y₁ η = modDual y₂ η := by
  obtain ⟨P⟩ := exists_polar_rep η
  have : IsFiniteMeasure P.ν := P.hν_fin
  let ε : ℝ := 1 / (64 * ‖η‖)
  let t : ℝ := 8 * ‖η‖
  have ht : 0 < t := by positivity
  have h1_sub_lt : ∀ {y : ℝ}, ‖η‖ - ε < ((modDual y η) f).re →
      ∫ g, (1 - (f g * (eChar y g * P.u g)).re) ∂P.ν < ε := by
    intro y hy
    have hint_w : Integrable (fun g => eChar y g * f g * P.u g) P.ν :=
      Integrable.mono' (integrable_const (1 : ℝ))
        ((((eChar y).continuous.measurable.mul f.continuous.measurable).mul P.hu_meas).aestronglyMeasurable)
        (Eventually.of_forall fun g => by
          rw [norm_mul, norm_mul, norm_eChar_apply, one_mul, P.hu_norm g, mul_one]
          exact (ContinuousMap.norm_coe_le_norm f g).trans hf)
    have hre_eq : ((modDual y η) f).re = ∫ g, (f g * (eChar y g * P.u g)).re ∂P.ν := by
      rw [modDual_apply, P.hrep]
      have hcomm := Complex.reCLM.integral_comp_comm hint_w
      change Complex.reCLM (∫ g, (eChar y * f) g * P.u g ∂P.ν) = _
      have heq : (fun g => (eChar y * f) g * P.u g) = fun g => eChar y g * f g * P.u g := rfl
      rw [heq, ← hcomm]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      change (eChar y g * f g * P.u g).re = (f g * (eChar y g * P.u g)).re
      congr 1; ring
    have hint_re : Integrable (fun g => (f g * (eChar y g * P.u g)).re) P.ν := by
      have h1 := Complex.reCLM.integrable_comp hint_w
      exact h1.congr (Eventually.of_forall fun g => by
        change (eChar y g * f g * P.u g).re = (f g * (eChar y g * P.u g)).re
        congr 1; ring)
    rw [integral_sub (integrable_const _) hint_re, integral_const, Measure.real_def, P.hnorm,
      smul_eq_mul, mul_one, ← hre_eq]
    linarith
  have hlt1 := h1_sub_lt hy₁
  have hlt2 := h1_sub_lt hy₂
  have hL1 : ∫ g, ‖eChar y₁ g - eChar y₂ g‖ ∂P.ν ≤ 3 / 4 := by
    have hint_r1 : Integrable (fun g => 1 - (f g * (eChar y₁ g * P.u g)).re) P.ν :=
      (integrable_const _).sub (Integrable.mono' (integrable_const (1 : ℝ))
        (Complex.continuous_re.measurable.comp (f.continuous.measurable.mul
          ((eChar y₁).continuous.measurable.mul P.hu_meas))).aestronglyMeasurable
        (Eventually.of_forall fun g => by
          rw [Real.norm_eq_abs]
          calc |(f g * (eChar y₁ g * P.u g)).re| ≤ ‖f g * (eChar y₁ g * P.u g)‖ := Complex.abs_re_le_norm _
            _ ≤ 1 := by
              rw [norm_mul, norm_mul, norm_eChar_apply, P.hu_norm g, mul_one, mul_one]
              exact (ContinuousMap.norm_coe_le_norm f g).trans hf))
    have hint_r2 : Integrable (fun g => 1 - (f g * (eChar y₂ g * P.u g)).re) P.ν :=
      (integrable_const _).sub (Integrable.mono' (integrable_const (1 : ℝ))
        (Complex.continuous_re.measurable.comp (f.continuous.measurable.mul
          ((eChar y₂).continuous.measurable.mul P.hu_meas))).aestronglyMeasurable
        (Eventually.of_forall fun g => by
          rw [Real.norm_eq_abs]
          calc |(f g * (eChar y₂ g * P.u g)).re| ≤ ‖f g * (eChar y₂ g * P.u g)‖ := Complex.abs_re_le_norm _
            _ ≤ 1 := by
              rw [norm_mul, norm_mul, norm_eChar_apply, P.hu_norm g, mul_one, mul_one]
              exact (ContinuousMap.norm_coe_le_norm f g).trans hf))
    have hint_rhs : Integrable (fun g =>
        2 * (t * (1 - (f g * (eChar y₁ g * P.u g)).re) + 1 / (2 * t) +
          (t * (1 - (f g * (eChar y₂ g * P.u g)).re) + 1 / (2 * t)))) P.ν :=
      (((hint_r1.const_mul t).add (integrable_const _)).add
        ((hint_r2.const_mul t).add (integrable_const _))).const_mul 2
    have hle : ∫ g, ‖eChar y₁ g - eChar y₂ g‖ ∂P.ν ≤
        ∫ g, 2 * (t * (1 - (f g * (eChar y₁ g * P.u g)).re) + 1 / (2 * t) +
          (t * (1 - (f g * (eChar y₂ g * P.u g)).re) + 1 / (2 * t))) ∂P.ν := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint_rhs
        (Eventually.of_forall fun g => ?_)
      dsimp only
      have ha : ‖eChar y₁ g * P.u g‖ = 1 := by rw [norm_mul, norm_eChar_apply, P.hu_norm g, mul_one]
      have hb : ‖eChar y₂ g * P.u g‖ = 1 := by rw [norm_mul, norm_eChar_apply, P.hu_norm g, mul_one]
      have hdiff : ‖eChar y₁ g - eChar y₂ g‖ = ‖eChar y₁ g * P.u g - eChar y₂ g * P.u g‖ := by
        rw [← sub_mul, norm_mul, P.hu_norm g, mul_one]
      rw [hdiff]
      have htri := norm_sub_le_two_mul_one_sub_mul (z := f g) ha hb
      have hw1 : ‖f g * (eChar y₁ g * P.u g)‖ ≤ 1 := by
        rw [norm_mul, ha, mul_one]; exact (ContinuousMap.norm_coe_le_norm f g).trans hf
      have hw2 : ‖f g * (eChar y₂ g * P.u g)‖ ≤ 1 := by
        rw [norm_mul, hb, mul_one]; exact (ContinuousMap.norm_coe_le_norm f g).trans hf
      have ham1 := norm_one_sub_le_amgm hw1 ht
      have ham2 := norm_one_sub_le_amgm hw2 ht
      linarith
    have hrhs_eq : ∫ g, 2 * (t * (1 - (f g * (eChar y₁ g * P.u g)).re) + 1 / (2 * t) +
          (t * (1 - (f g * (eChar y₂ g * P.u g)).re) + 1 / (2 * t))) ∂P.ν =
        2 * (t * (∫ g, (1 - (f g * (eChar y₁ g * P.u g)).re) ∂P.ν) + ‖η‖ / (2 * t) +
          (t * (∫ g, (1 - (f g * (eChar y₂ g * P.u g)).re) ∂P.ν) + ‖η‖ / (2 * t))) := by
      have ha1 : Integrable (fun g => t * (1 - (f g * (eChar y₁ g * P.u g)).re) + 1 / (2 * t)) P.ν :=
        (hint_r1.const_mul t).add (integrable_const _)
      have ha2 : Integrable (fun g => t * (1 - (f g * (eChar y₂ g * P.u g)).re) + 1 / (2 * t)) P.ν :=
        (hint_r2.const_mul t).add (integrable_const _)
      rw [integral_const_mul, integral_add ha1 ha2,
        integral_add (hint_r1.const_mul t) (integrable_const _),
        integral_add (hint_r2.const_mul t) (integrable_const _),
        integral_const_mul, integral_const_mul, integral_const, Measure.real_def, P.hnorm,
        smul_eq_mul]
      ring
    rw [hrhs_eq] at hle
    have hcalc : 2 * (t * ε + ‖η‖ / (2 * t) + (t * ε + ‖η‖ / (2 * t))) = 3 / 4 := by
      dsimp only [t, ε]
      field_simp [hη_pos.ne']
      ring
    nlinarith
  apply eq_of_eq_on_eChar
  intro x
  have hnorm_diff : ‖modDual y₁ η (eChar x) - modDual y₂ η (eChar x)‖ ≤ 3 / 4 := by
    rw [modDual_apply, modDual_apply, P.hrep, P.hrep]
    have hint1 : Integrable (fun g => (eChar y₁ * eChar x) g * P.u g) P.ν :=
      Integrable.mono' (integrable_const (1 : ℝ))
        ((((eChar y₁ * eChar x).continuous.measurable).mul P.hu_meas).aestronglyMeasurable)
        (Eventually.of_forall fun g => by
          change ‖eChar y₁ g * eChar x g * P.u g‖ ≤ 1
          rw [norm_mul, norm_mul, norm_eChar_apply, norm_eChar_apply, P.hu_norm g]; norm_num)
    have hint2 : Integrable (fun g => (eChar y₂ * eChar x) g * P.u g) P.ν :=
      Integrable.mono' (integrable_const (1 : ℝ))
        ((((eChar y₂ * eChar x).continuous.measurable).mul P.hu_meas).aestronglyMeasurable)
        (Eventually.of_forall fun g => by
          change ‖eChar y₂ g * eChar x g * P.u g‖ ≤ 1
          rw [norm_mul, norm_mul, norm_eChar_apply, norm_eChar_apply, P.hu_norm g]; norm_num)
    rw [← integral_sub hint1 hint2]
    calc ‖∫ g, ((eChar y₁ * eChar x) g * P.u g - (eChar y₂ * eChar x) g * P.u g) ∂P.ν‖
        ≤ ∫ g, ‖(eChar y₁ * eChar x) g * P.u g - (eChar y₂ * eChar x) g * P.u g‖ ∂P.ν :=
          norm_integral_le_integral_norm _
      _ = ∫ g, ‖eChar y₁ g - eChar y₂ g‖ ∂P.ν := by
          refine integral_congr_ae (Eventually.of_forall fun g => ?_)
          dsimp only
          have heq : (eChar y₁ * eChar x) g * P.u g - (eChar y₂ * eChar x) g * P.u g =
              (eChar y₁ g - eChar y₂ g) * (eChar x g * P.u g) := by
            change eChar y₁ g * eChar x g * P.u g - eChar y₂ g * eChar x g * P.u g = _
            ring
          rw [heq, norm_mul, norm_mul, norm_eChar_apply, P.hu_norm g, mul_one, mul_one]
      _ ≤ 3 / 4 := hL1
  obtain ⟨n₁, hn₁⟩ := hint (y₁ + x)
  obtain ⟨n₂, hn₂⟩ := hint (y₂ + x)
  rw [modDual_eChar, modDual_eChar, hn₁, hn₂] at hnorm_diff ⊢
  have heq : n₁ = n₂ := by
    by_contra hne
    have hge1 : (1 : ℝ) ≤ ‖(n₁ : ℂ) - (n₂ : ℂ)‖ := by
      rw [← Int.cast_sub, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
    linarith
  rw [heq]

lemma zero_of_abs_le_singular (Γ : AddSubgroup ℝ)
    {σ ρ : Measure BohrR} [IsFiniteMeasure ρ] [ρ.Regular]
    (hσ_le : σ ≤ (2 : ℝ≥0∞) • ρ) (hsing : σ ⟂ₘ mH Γ)
    {q : BohrR → ℂ} (hq_int : Integrable q (mH Γ))
    (hle : ∀ f : C(BohrR, ℂ), ‖∫ g, f g * q g ∂(mH Γ)‖ ≤ ∫ g, ‖f g‖ ∂σ) :
    ∀ f : C(BohrR, ℂ), ∫ g, f g * q g ∂(mH Γ) = 0 := by
  have : IsFiniteMeasure ((2 : ℝ≥0∞) • ρ) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top (measure_lt_top ρ Set.univ)
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le ((2 : ℝ≥0∞) • ρ) hσ_le
  obtain ⟨E, hE_meas, hσE, hmHEc⟩ := hsing
  intro f
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  by_contra hpos
  push Not at hpos
  set ε : ℝ := ‖∫ g, f g * q g ∂(mH Γ)‖
  set B : ℝ := ‖f‖ + 1
  have hB_pos : 0 < B := by positivity
  -- Step 1: Truncate ‖q‖ by DCT via measurable version qm
  obtain ⟨qm, hqm_meas, hq_ae⟩ := hq_int.aestronglyMeasurable
  have hqm_int : Integrable qm (mH Γ) := hq_int.congr hq_ae
  have htail' : Tendsto (fun n : ℕ => ∫ g in {x | (n : ℝ) < ‖qm x‖}, ‖qm g‖ ∂(mH Γ))
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : BohrR, (0 : ℝ) ∂(mH Γ) := by simp
    rw [h0]
    have heq : (fun n : ℕ => ∫ g in {x | (n : ℝ) < ‖qm x‖}, ‖qm g‖ ∂(mH Γ)) =
        fun n : ℕ => ∫ g, Set.indicator {x | (n : ℝ) < ‖qm x‖} (fun x => ‖qm x‖) g ∂(mH Γ) := by
      funext n
      exact (integral_indicator (measurableSet_lt measurable_const hqm_meas.measurable.norm)).symm
    rw [heq]
    refine tendsto_integral_of_dominated_convergence (fun g => ‖qm g‖)
      (fun n => (hqm_meas.norm.indicator (measurableSet_lt measurable_const hqm_meas.measurable.norm)).aestronglyMeasurable)
      hqm_int.norm
      (fun n => Eventually.of_forall fun g => by
        rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)]
        by_cases h : g ∈ {x | (n : ℝ) < ‖qm x‖} <;> simp [h])
      (Eventually.of_forall fun g => by
        obtain ⟨N, hN⟩ := exists_nat_gt ‖qm g‖
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
        exact Set.indicator_of_notMem (by
          simp only [Set.mem_ofPred_eq, not_lt]
          linarith [show (N : ℝ) ≤ n from Nat.cast_le.mpr hn]) _)
  obtain ⟨Mnat, hMnat⟩ := (Metric.tendsto_atTop.mp htail' (ε / (4 * B)) (by positivity))
  let M : ℝ := max (Mnat : ℝ) 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let A_M : Set BohrR := {x | M < ‖qm x‖}
  have hAM_meas : MeasurableSet A_M := measurableSet_lt measurable_const hqm_meas.measurable.norm
  have hAM_int : ∫ g in A_M, ‖qm g‖ ∂(mH Γ) < ε / (4 * B) := by
    have hsub : A_M ⊆ {x | (Mnat : ℝ) < ‖qm x‖} := fun x hx =>
      lt_of_le_of_lt (le_max_left (Mnat : ℝ) 1) hx
    have h1 := setIntegral_mono_set hqm_int.norm.integrableOn (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall hsub)
    have h2 := hMnat Mnat le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (setIntegral_nonneg (measurableSet_lt measurable_const hqm_meas.measurable.norm)
        (fun _ _ => norm_nonneg _))] at h2
    exact lt_of_le_of_lt h1 h2
  -- Step 2: Compact K ⊆ E with mH Γ (E \ K) < ε / (4 * B * M)
  let E_H : Set (AnnSubgroup Γ) := Subtype.val ⁻¹' E
  have hEH_meas : MeasurableSet E_H := hE_meas.preimage continuous_subtype_val.measurable
  obtain ⟨K_H, hKH_sub, hKH_comp, hKH_lt⟩ := hEH_meas.exists_isCompact_sdiff_lt (μ := mH_sub Γ)
    (measure_ne_top _ _) (ENNReal.ofReal_pos.mpr (by positivity : 0 < ε / (4 * B * M))).ne'
  let K : Set BohrR := Subtype.val '' K_H
  have hK_comp : IsCompact K := hKH_comp.image continuous_subtype_val
  have hK_closed : IsClosed K := hK_comp.isClosed
  have hK_sub : K ⊆ E := by rintro _ ⟨h, hh, rfl⟩; exact hKH_sub hh
  have hσK : σ K = 0 := measure_mono_null hK_sub hσE
  have hmH_EK : (mH Γ (E \ K)).toReal < ε / (4 * B * M) := by
    have heq_pre : Subtype.val ⁻¹' (E \ K) = E_H \ K_H := by
      ext h
      simp only [Set.mem_preimage, Set.mem_sdiff, E_H, K, Set.mem_image, Subtype.val_inj, exists_eq_right]
    have hm_eq : mH Γ (E \ K) = mH_sub Γ (E_H \ K_H) := by
      dsimp only [mH]
      rw [Measure.map_apply continuous_subtype_val.measurable (hE_meas.diff hK_closed.measurableSet), heq_pre]
    rw [hm_eq]
    exact ENNReal.toReal_lt_of_lt_ofReal hKH_lt
  -- Step 3: Open U ⊇ K with σ U < ε / (4 * B) via inner regularity of ρ on open Kᶜ
  let δ_real : ℝ := ε / (8 * B)
  have hδ_pos : 0 < δ_real := by positivity
  have hex_C : ∃ C : Set BohrR, C ⊆ Kᶜ ∧ IsCompact C ∧ ρ (Kᶜ \ C) < ENNReal.ofReal δ_real := by
    by_cases hρ0 : ρ Kᶜ = 0
    · refine ⟨∅, Set.empty_subset _, isCompact_empty, ?_⟩
      rw [Set.sdiff_empty, hρ0]
      exact ENNReal.ofReal_pos.mpr hδ_pos
    · have hlt : ρ Kᶜ - ENNReal.ofReal δ_real < ρ Kᶜ :=
        ENNReal.sub_lt_self (measure_ne_top ρ Kᶜ) hρ0 (ENNReal.ofReal_pos.mpr hδ_pos).ne'
      obtain ⟨C, hCKc, hCc, hCgt⟩ := Measure.Regular.innerRegular hK_closed.isOpen_compl _ hlt
      refine ⟨C, hCKc, hCc, ?_⟩
      rw [measure_sdiff hCKc hCc.isClosed.measurableSet.nullMeasurableSet (measure_ne_top ρ C)]
      have hadd : ρ Kᶜ < ENNReal.ofReal δ_real + ρ C := by
        rw [add_comm]
        exact lt_of_le_of_lt le_tsub_add (ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hCgt)
      exact ENNReal.sub_lt_of_lt_add (measure_mono hCKc) hadd
  obtain ⟨C, hCKc, hCc, hρ_lt⟩ := hex_C
  let U : Set BohrR := Cᶜ
  have hU_open : IsOpen U := hCc.isClosed.isOpen_compl
  have hKU : K ⊆ U := Set.subset_compl_comm.mp hCKc
  have hUK_eq : U \ K = Kᶜ \ C := by ext g; simp [U, and_comm]
  have hσU : (σ U).toReal < ε / (4 * B) := by
    have hσU_eq : σ U = σ K + σ (U \ K) := by
      rw [← measure_union disjoint_sdiff_self_right (hU_open.measurableSet.diff hK_closed.measurableSet),
        Set.union_sdiff_cancel hKU]
    rw [hσU_eq, hσK, zero_add, hUK_eq]
    have hle2 : σ (Kᶜ \ C) ≤ 2 * ρ (Kᶜ \ C) := by
      simpa [Measure.smul_apply, smul_eq_mul] using hσ_le (Kᶜ \ C)
    have hlt2 : σ (Kᶜ \ C) < ENNReal.ofReal (ε / (4 * B)) := by
      calc σ (Kᶜ \ C) ≤ 2 * ρ (Kᶜ \ C) := hle2
        _ < 2 * ENNReal.ofReal δ_real := by
            rw [mul_comm (2 : ℝ≥0∞), mul_comm (2 : ℝ≥0∞)]
            exact ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) hρ_lt
        _ = ENNReal.ofReal (2 * δ_real) := by rw [ENNReal.ofReal_mul zero_le_two]; norm_num
        _ = ENNReal.ofReal (ε / (4 * B)) := by dsimp only [δ_real]; congr 1; ring
    exact ENNReal.toReal_lt_of_lt_ofReal hlt2
  -- Step 4: Urysohn cutoff ψ = 1 on K, ψ = 0 on C = Uᶜ, 0 ≤ ψ ≤ 1
  have hdisj : Disjoint K C := Set.disjoint_right.mpr fun g hgC hgK => hCKc hgC hgK
  obtain ⟨φ, hφK, hφC, hφIcc⟩ := exists_continuous_zero_one_of_isCompact hK_comp hCc.isClosed hdisj
  let ψ : C(BohrR, ℂ) :=
    ⟨fun g => ((1 - φ g : ℝ) : ℂ), Complex.continuous_ofReal.comp (continuous_const.sub φ.continuous)⟩
  have hψ_bd : ∀ g, ‖ψ g‖ ≤ 1 := fun g => by
    change ‖((1 - φ g : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [(hφIcc g).2])]
    linarith [(hφIcc g).1]
  have h1mψ_bd : ∀ g, ‖1 - ψ g‖ ≤ 1 := fun g => by
    change ‖(1 : ℂ) - ((1 - φ g : ℝ) : ℂ)‖ ≤ 1
    have heq : (1 : ℂ) - ((1 - φ g : ℝ) : ℂ) = ((φ g : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (hφIcc g).1]
    exact (hφIcc g).2
  have hψ_on_K : ∀ g ∈ K, ψ g = 1 := fun g hg => by
    change ((1 - φ g : ℝ) : ℂ) = 1
    rw [hφK hg]; simp
  have hψ_on_Uc : ∀ g ∈ Uᶜ, ψ g = 0 := fun g hg => by
    have hgC : g ∈ C := by simpa [U] using hg
    change ((1 - φ g : ℝ) : ℂ) = 0
    rw [hφC hgC]; simp
  -- Step 5: Split integral into f * ψ and f * (1 - ψ)
  have hint_fψq : Integrable (fun g => (f * ψ) g * q g) (mH Γ) :=
    hq_int.bdd_mul (f * ψ).continuous.aestronglyMeasurable
      (Eventually.of_forall (ContinuousMap.norm_coe_le_norm (f * ψ)))
  have hint_f1ψq : Integrable (fun g => (f * (1 - ψ)) g * q g) (mH Γ) :=
    hq_int.bdd_mul (f * (1 - ψ)).continuous.aestronglyMeasurable
      (Eventually.of_forall (ContinuousMap.norm_coe_le_norm (f * (1 - ψ))))
  have hsplit : ∫ g, f g * q g ∂(mH Γ) =
      (∫ g, (f * ψ) g * q g ∂(mH Γ)) + (∫ g, (f * (1 - ψ)) g * q g ∂(mH Γ)) := by
    rw [← integral_add hint_fψq hint_f1ψq]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change f g * q g = f g * ψ g * q g + f g * (1 - ψ g) * q g
    ring
  have hpart1 : ‖∫ g, (f * ψ) g * q g ∂(mH Γ)‖ < ε / 4 := by
    calc ‖∫ g, (f * ψ) g * q g ∂(mH Γ)‖ ≤ ∫ g, ‖(f * ψ) g‖ ∂σ := hle (f * ψ)
      _ ≤ ∫ g, Set.indicator U (fun _ => B) g ∂σ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            ((integrable_const B).indicator hU_open.measurableSet) (Eventually.of_forall fun g => ?_)
          by_cases hg : g ∈ U
          · rw [Set.indicator_of_mem hg]
            change ‖f g * ψ g‖ ≤ B
            rw [norm_mul]
            calc ‖f g‖ * ‖ψ g‖ ≤ ‖f‖ * 1 := mul_le_mul (ContinuousMap.norm_coe_le_norm f g) (hψ_bd g) (norm_nonneg _) (norm_nonneg f)
              _ ≤ B := by dsimp only [B]; linarith
          · rw [Set.indicator_of_notMem hg]
            change ‖f g * ψ g‖ ≤ 0
            rw [hψ_on_Uc g hg, mul_zero, norm_zero]
      _ = B * (σ U).toReal := by
          rw [integral_indicator_const B hU_open.measurableSet, Measure.real_def, smul_eq_mul, mul_comm]
      _ < B * (ε / (4 * B)) := mul_lt_mul_of_pos_left hσU hB_pos
      _ = ε / 4 := by field_simp [hB_pos.ne']
  have hpart2 : ‖∫ g, (f * (1 - ψ)) g * q g ∂(mH Γ)‖ ≤ ε / 2 := by
    have hE_ae : ∀ᵐ g ∂(mH Γ), g ∈ E := by
      rw [ae_iff]; exact hmHEc
    have hcongr : ∫ g, (f * (1 - ψ)) g * q g ∂(mH Γ) =
        ∫ g in E \ K, (f * (1 - ψ)) g * qm g ∂(mH Γ) := by
      rw [← integral_indicator (hE_meas.diff hK_closed.measurableSet)]
      refine integral_congr_ae ?_
      filter_upwards [hq_ae, hE_ae] with g hqg hgE
      by_cases hgK : g ∈ K
      · rw [Set.indicator_of_notMem (fun h => h.2 hgK)]
        change f g * (1 - ψ g) * q g = 0
        rw [hψ_on_K g hgK, sub_self, mul_zero, zero_mul]
      · rw [Set.indicator_of_mem (show g ∈ E \ K from ⟨hgE, hgK⟩), hqg]
    rw [hcongr]
    have hle_norm : ‖∫ g in E \ K, (f * (1 - ψ)) g * qm g ∂(mH Γ)‖ ≤
        ∫ g in E \ K, B * ‖qm g‖ ∂(mH Γ) := by
      calc ‖∫ g in E \ K, (f * (1 - ψ)) g * qm g ∂(mH Γ)‖
          ≤ ∫ g in E \ K, ‖(f * (1 - ψ)) g * qm g‖ ∂(mH Γ) := norm_integral_le_integral_norm _
        _ ≤ ∫ g in E \ K, B * ‖qm g‖ ∂(mH Γ) := by
            refine setIntegral_mono_on
              ((hqm_int.bdd_mul (f * (1 - ψ)).continuous.aestronglyMeasurable
                (Eventually.of_forall (ContinuousMap.norm_coe_le_norm (f * (1 - ψ))))).norm.integrableOn)
              (hqm_int.norm.const_mul B).integrableOn (hE_meas.diff hK_closed.measurableSet)
              fun g _ => ?_
            change ‖f g * (1 - ψ g) * qm g‖ ≤ B * ‖qm g‖
            rw [norm_mul, norm_mul]
            have h1 : ‖f g‖ * ‖1 - ψ g‖ ≤ B := by
              calc ‖f g‖ * ‖1 - ψ g‖ ≤ ‖f‖ * 1 := mul_le_mul (ContinuousMap.norm_coe_le_norm f g) (h1mψ_bd g) (norm_nonneg _) (norm_nonneg f)
                _ ≤ B := by dsimp only [B]; linarith
            exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hsplit_set : ∫ g in E \ K, B * ‖qm g‖ ∂(mH Γ) =
        (∫ g in (E \ K) ∩ A_M, B * ‖qm g‖ ∂(mH Γ)) + (∫ g in (E \ K) \ A_M, B * ‖qm g‖ ∂(mH Γ)) := by
      rw [← setIntegral_union (Set.disjoint_of_subset_left Set.inter_subset_right disjoint_sdiff_self_right)
        ((hE_meas.diff hK_closed.measurableSet).diff hAM_meas)
        (hqm_int.norm.const_mul B).integrableOn (hqm_int.norm.const_mul B).integrableOn,
        Set.inter_union_sdiff]
    have h2a : ∫ g in (E \ K) ∩ A_M, B * ‖qm g‖ ∂(mH Γ) ≤ ε / 4 := by
      rw [integral_const_mul]
      have h1 : ∫ g in (E \ K) ∩ A_M, ‖qm g‖ ∂(mH Γ) ≤ ∫ g in A_M, ‖qm g‖ ∂(mH Γ) :=
        setIntegral_mono_set hqm_int.norm.integrableOn (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall Set.inter_subset_right)
      calc B * ∫ g in (E \ K) ∩ A_M, ‖qm g‖ ∂(mH Γ)
          ≤ B * ∫ g in A_M, ‖qm g‖ ∂(mH Γ) := mul_le_mul_of_nonneg_left h1 hB_pos.le
        _ ≤ B * (ε / (4 * B)) := mul_le_mul_of_nonneg_left hAM_int.le hB_pos.le
        _ = ε / 4 := by field_simp [hB_pos.ne']
    have h2b : ∫ g in (E \ K) \ A_M, B * ‖qm g‖ ∂(mH Γ) ≤ ε / 4 := by
      have hle_M : ∫ g in (E \ K) \ A_M, B * ‖qm g‖ ∂(mH Γ) ≤
          ∫ _ in (E \ K) \ A_M, B * M ∂(mH Γ) := by
        refine setIntegral_mono_on (hqm_int.norm.const_mul B).integrableOn
          (integrable_const _).integrableOn ((hE_meas.diff hK_closed.measurableSet).diff hAM_meas)
          fun g hg => ?_
        have hnot : ¬ (M < ‖qm g‖) := hg.2
        push Not at hnot
        exact mul_le_mul_of_nonneg_left hnot hB_pos.le
      calc ∫ g in (E \ K) \ A_M, B * ‖qm g‖ ∂(mH Γ)
          ≤ (mH Γ ((E \ K) \ A_M)).toReal * (B * M) := by
            simpa [setIntegral_const, Measure.real_def, smul_eq_mul] using hle_M
        _ ≤ (mH Γ (E \ K)).toReal * (B * M) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.sdiff_subset)
        _ ≤ (ε / (4 * B * M)) * (B * M) := mul_le_mul_of_nonneg_right hmH_EK.le (by positivity)
        _ = ε / 4 := by field_simp [hB_pos.ne', hM_pos.ne']
    linarith
  have htot : ε ≤ ‖∫ g, (f * ψ) g * q g ∂(mH Γ)‖ + ‖∫ g, (f * (1 - ψ)) g * q g ∂(mH Γ)‖ := by
    dsimp only [ε]; rw [hsplit]; exact norm_add_le _ _
  linarith

noncomputable def eCharSub (Γ : AddSubgroup ℝ) (x : ℝ) : C(AnnSubgroup Γ, ℂ) :=
  ⟨fun h => eChar x h.1, (eChar x).continuous.comp continuous_subtype_val⟩

noncomputable def eCharSubStarSubalgebra (Γ : AddSubgroup ℝ) : StarSubalgebra ℂ C(AnnSubgroup Γ, ℂ) where
  carrier := (Submodule.span ℂ (Set.range (eCharSub Γ)) : Set C(AnnSubgroup Γ, ℂ))
  mul_mem' {f g} hf hg := by
    refine Submodule.span_induction (p := fun u _ => u * g ∈ Submodule.span ℂ (Set.range (eCharSub Γ)))
      ?_ (by simp) (fun u v _ _ hu hv => by rw [add_mul]; exact Submodule.add_mem _ hu hv)
      (fun c u _ hu => by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu) hf
    rintro _ ⟨x, rfl⟩
    refine Submodule.span_induction (p := fun v _ => eCharSub Γ x * v ∈ Submodule.span ℂ (Set.range (eCharSub Γ)))
      ?_ (by simp) (fun u v _ _ hu hv => by rw [mul_add]; exact Submodule.add_mem _ hu hv)
      (fun c u _ hu => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu) hg
    rintro _ ⟨y, rfl⟩
    have hmul : eCharSub Γ x * eCharSub Γ y = eCharSub Γ (x + y) := by
      ext h; change eChar x h.1 * eChar y h.1 = eChar (x + y) h.1
      rw [eChar_add]; rfl
    rw [hmul]
    exact Submodule.subset_span ⟨x + y, rfl⟩
  one_mem' := by
    have h1 : (1 : C(AnnSubgroup Γ, ℂ)) = eCharSub Γ 0 := by
      ext h; change 1 = eChar 0 h.1; rw [eChar_zero]; rfl
    rw [h1]; exact Submodule.subset_span ⟨0, rfl⟩
  add_mem' hf hg := Submodule.add_mem _ hf hg
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' c := by
    have h1 : algebraMap ℂ C(AnnSubgroup Γ, ℂ) c = c • eCharSub Γ 0 := by
      ext h; simp [eCharSub, bohrR_map_zero]
    rw [h1]; exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' {f} hf := by
    refine Submodule.span_induction (p := fun u _ => star u ∈ Submodule.span ℂ (Set.range (eCharSub Γ)))
      ?_ (by simp) (fun u v _ _ hu hv => by rw [star_add]; exact Submodule.add_mem _ hu hv)
      (fun c u _ hu => by rw [star_smul]; exact Submodule.smul_mem _ (star c) hu) hf
    rintro _ ⟨x, rfl⟩
    have hneg : star (eCharSub Γ x) = eCharSub Γ (-x) := by
      ext h
      change star (eChar x h.1) = eChar (-x) h.1
      rw [eChar_neg]; rfl
    rw [hneg]; exact Submodule.subset_span ⟨-x, rfl⟩

lemma exists_finset_eCharSub_approx (Γ : AddSubgroup ℝ) (φ : C(AnnSubgroup Γ, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℝ) (a : ℝ → ℂ), ‖φ - ∑ x ∈ s, a x • eCharSub Γ x‖ < ε := by
  have hdense : (eCharSubStarSubalgebra Γ).topologicalClosure = ⊤ := by
    refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
    intro h₁ h₂ hne
    have hne' : h₁.1.1 ≠ h₂.1.1 := fun h => hne (Subtype.ext (Subtype.ext h))
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne'
    refine ⟨eCharSub Γ x, ⟨eCharSub Γ x, Submodule.subset_span ⟨x, rfl⟩, rfl⟩, ?_⟩
    intro hval; exact hx (Subtype.ext hval)
  have hmem : φ ∈ (eCharSubStarSubalgebra Γ).topologicalClosure := by rw [hdense]; trivial
  change φ ∈ closure (eCharSubStarSubalgebra Γ : Set C(AnnSubgroup Γ, ℂ)) at hmem
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨g, hg, hdist⟩ := hmem ε hε
  change g ∈ Submodule.span ℂ (Set.range (eCharSub Γ)) at hg
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hg
  rcases hg with ⟨c, rfl⟩
  refine ⟨c.support, fun x => c x, ?_⟩
  rw [Finsupp.sum] at hdist
  rwa [dist_eq_norm] at hdist

lemma tendsto_modDual_ac_zero_of_not_coset (Γ : AddSubgroup ℝ)
    {w : BohrR → ℂ} (hw_int : Integrable w (mH Γ))
    {F : Filter ℝ} (hF : ∀ a : ℝ, ∀ᶠ y in F, y ∉ (fun z => a + z) '' (Γ : Set ℝ))
    (f : C(BohrR, ℂ)) :
    Tendsto (fun y => ∫ g, eChar y g * (f g * w g) ∂(mH Γ)) F (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfw_int : Integrable (fun g => f g * w g) (mH Γ) :=
    hw_int.bdd_mul f.continuous.aestronglyMeasurable
      (Eventually.of_forall (ContinuousMap.norm_coe_le_norm f))
  have hsub_int : Integrable (fun h : AnnSubgroup Γ => f h.1 * w h.1) (mH_sub Γ) :=
    (integrable_map_measure hfw_int.aestronglyMeasurable continuous_subtype_val.measurable.aemeasurable).mp hfw_int
  obtain ⟨φfun, _, hφ_L1, hφ_cont, _⟩ :=
    hsub_int.exists_hasCompactSupport_integral_sub_le (ε := ε / 3) (by positivity)
  let φ : C(AnnSubgroup Γ, ℂ) := ⟨φfun, hφ_cont⟩
  obtain ⟨s, a, happrox⟩ := exists_finset_eCharSub_approx Γ φ (ε := ε / 3) (by positivity)
  let P : C(AnnSubgroup Γ, ℂ) := ∑ x ∈ s, a x • eCharSub Γ x
  have hP_eval : ∀ h : AnnSubgroup Γ, P h = ∑ x ∈ s, a x * eChar x h.1 := fun h => by
    simp [P, eCharSub]
  have hL1_P : ∫ h : AnnSubgroup Γ, ‖f h.1 * w h.1 - P h‖ ∂(mH_sub Γ) < ε := by
    have hint_diff1 : Integrable (fun h : AnnSubgroup Γ => ‖f h.1 * w h.1 - φ h‖) (mH_sub Γ) :=
      (hsub_int.sub (Integrable.mono' (integrable_const ‖φ‖) φ.continuous.aestronglyMeasurable
        (Eventually.of_forall (ContinuousMap.norm_coe_le_norm φ)))).norm
    have hint_diff2 : Integrable (fun h : AnnSubgroup Γ => ‖φ h - P h‖) (mH_sub Γ) :=
      (φ - P).continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have htri : ∫ h : AnnSubgroup Γ, ‖f h.1 * w h.1 - P h‖ ∂(mH_sub Γ) ≤
        (∫ h : AnnSubgroup Γ, ‖f h.1 * w h.1 - φ h‖ ∂(mH_sub Γ)) +
          ∫ h : AnnSubgroup Γ, ‖φ h - P h‖ ∂(mH_sub Γ) := by
      rw [← integral_add hint_diff1 hint_diff2]
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hint_diff1.add hint_diff2)
        (Eventually.of_forall fun h => norm_sub_le_norm_sub_add_norm_sub _ _ _)
    have h2 : ∫ h : AnnSubgroup Γ, ‖φ h - P h‖ ∂(mH_sub Γ) ≤ ‖φ - P‖ := by
      calc ∫ h : AnnSubgroup Γ, ‖φ h - P h‖ ∂(mH_sub Γ)
          ≤ ∫ _ : AnnSubgroup Γ, ‖φ - P‖ ∂(mH_sub Γ) :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const _) (Eventually.of_forall fun h => ContinuousMap.norm_coe_le_norm (φ - P) h)
        _ = ‖φ - P‖ := by rw [integral_const, Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul]
    have h1' : ∫ h : AnnSubgroup Γ, ‖f h.1 * w h.1 - φ h‖ ∂(mH_sub Γ) ≤ ε / 3 := hφ_L1
    have h3' : ‖φ - P‖ < ε / 3 := happrox
    linarith
  have hev_all : ∀ t : Finset ℝ, ∀ᶠ y in F, ∀ x ∈ t, y ∉ (fun z => (-x) + z) '' (Γ : Set ℝ) := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty => exact Eventually.of_forall fun _ _ hx => absurd hx (Finset.notMem_empty _)
    | insert x₀ t' _ ih =>
      filter_upwards [hF (-x₀), ih] with y hy₀ hyt x hx
      rcases Finset.mem_insert.mp hx with rfl | hxt
      · exact hy₀
      · exact hyt x hxt
  have hev := hev_all s
  filter_upwards [hev] with y hy
  rw [dist_zero_right]
  have hmap_eq : ∫ g, eChar y g * (f g * w g) ∂(mH Γ) =
      ∫ h : AnnSubgroup Γ, eChar y h.1 * (f h.1 * w h.1) ∂(mH_sub Γ) := by
    dsimp only [mH]
    exact integral_map continuous_subtype_val.measurable.aemeasurable
      ((eChar y).continuous.aestronglyMeasurable.mul hfw_int.aestronglyMeasurable)
  have hP_zero : ∫ h : AnnSubgroup Γ, eChar y h.1 * P h ∂(mH_sub Γ) = 0 := by
    have heq : (fun h : AnnSubgroup Γ => eChar y h.1 * P h) =
        fun h => ∑ x ∈ s, a x * eChar (y + x) h.1 := by
      funext h
      rw [hP_eval h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [eChar_add]; change eChar y h.1 * (a x * eChar x h.1) = a x * (eChar y h.1 * eChar x h.1)
      ring
    have hint_term : ∀ x ∈ s, Integrable (fun h : AnnSubgroup Γ => a x * eChar (y + x) h.1) (mH_sub Γ) :=
      fun x _ => ((eCharSub Γ (y + x)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul (a x)
    rw [heq, integral_finsetSum s hint_term]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [integral_const_mul]
    have hnot : y + x ∉ Γ := by
      intro hmem
      exact hy x hx ⟨y + x, hmem, by ring⟩
    have hI : ∫ h : AnnSubgroup Γ, eChar (y + x) h.1 ∂(mH_sub Γ) = 0 := by
      have h1 := integral_eChar_mH Γ (y + x)
      dsimp only [mH] at h1
      rw [integral_map continuous_subtype_val.measurable.aemeasurable (eChar (y + x)).continuous.aestronglyMeasurable,
        Set.indicator_of_notMem hnot] at h1
      exact h1
    rw [hI, mul_zero]
  have hsub_eq : ∫ h : AnnSubgroup Γ, eChar y h.1 * (f h.1 * w h.1) ∂(mH_sub Γ) =
      ∫ h : AnnSubgroup Γ, eChar y h.1 * (f h.1 * w h.1 - P h) ∂(mH_sub Γ) := by
    have h1 : Integrable (fun h : AnnSubgroup Γ => eChar y h.1 * (f h.1 * w h.1)) (mH_sub Γ) :=
      hsub_int.bdd_mul (c := 1) (eCharSub Γ y).continuous.aestronglyMeasurable
        (Eventually.of_forall fun h => by change ‖eChar y h.1‖ ≤ 1; rw [norm_eChar_apply])
    have h2 : Integrable (fun h : AnnSubgroup Γ => eChar y h.1 * P h) (mH_sub Γ) :=
      ((eCharSub Γ y * P).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    rw [← sub_zero (∫ h, eChar y h.1 * (f h.1 * w h.1) ∂(mH_sub Γ)), ← hP_zero, ← integral_sub h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun h => by ring)
  rw [hmap_eq, hsub_eq]
  calc ‖∫ h : AnnSubgroup Γ, eChar y h.1 * (f h.1 * w h.1 - P h) ∂(mH_sub Γ)‖
      ≤ ∫ h : AnnSubgroup Γ, ‖eChar y h.1 * (f h.1 * w h.1 - P h)‖ ∂(mH_sub Γ) :=
        norm_integral_le_integral_norm _
    _ = ∫ h : AnnSubgroup Γ, ‖f h.1 * w h.1 - P h‖ ∂(mH_sub Γ) := by
        refine integral_congr_ae (Eventually.of_forall fun h => by
          dsimp only; rw [norm_mul, norm_eChar_apply, one_mul])
    _ < ε := hL1_P

/- Part 3F: Amemiya-Ito (1964) induction and export for `TilesR` -/

def IsCosetLinComb (f : ℝ → ℂ) : Prop :=
  ∃ L : List (ℤ × ℝ × AddSubgroup ℝ),
    ∀ x : ℝ, f x = (L.map fun p => (p.1 : ℂ) *
      Set.indicator ((fun z => p.2.1 + z) '' (p.2.2 : Set ℝ)) (fun _ => (1 : ℂ)) x).sum

lemma isCosetLinComb_zero : IsCosetLinComb (fun _ => 0) :=
  ⟨[], fun _ => by simp⟩

lemma isCosetLinComb_add {f g : ℝ → ℂ} (hf : IsCosetLinComb f) (hg : IsCosetLinComb g) :
    IsCosetLinComb (fun x => f x + g x) := by
  rcases hf with ⟨L₁, hL₁⟩
  rcases hg with ⟨L₂, hL₂⟩
  refine ⟨L₁ ++ L₂, fun x => ?_⟩
  dsimp only
  rw [List.map_append, List.sum_append, hL₁ x, hL₂ x]

lemma amemiya_ito_step {Λ : StrongDual ℂ C(BohrR, ℂ)}
    (hΛ_ne : Λ ≠ 0)
    (hint : ∀ x : ℝ, ∃ n : ℤ, Λ (eChar x) = (n : ℂ)) :
    ∃ Λ_ac Λ_s : StrongDual ℂ C(BohrR, ℂ),
      Λ = Λ_ac + Λ_s ∧
      IsCosetLinComb (fun x => Λ_ac (eChar x)) ∧
      (∀ x : ℝ, ∃ n : ℤ, Λ_s (eChar x) = (n : ℂ)) ∧
      ‖Λ_s‖ ≤ ‖Λ‖ - 1 := by
  -- Step 1: Construct compact K = closure {modDual y Λ | Λ (eChar y) ≠ 0}
  let S : Set ℝ := {y : ℝ | Λ (eChar y) ≠ 0}
  have hS_ne : S.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hΛ_ne
    apply eq_of_eq_on_eChar
    intro x
    by_contra hne
    have : x ∈ S := hne
    rw [hempty] at this
    exact this
  let orb : Set (WeakDual ℂ C(BohrR, ℂ)) :=
    (fun y : ℝ => StrongDual.toWeakDual (modDual y Λ)) '' S
  let K : Set (WeakDual ℂ C(BohrR, ℂ)) := closure orb
  have hK_sub_ball : K ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 ‖Λ‖ := by
    refine closure_minimal ?_ (WeakDual.isClosed_closedBall 0 ‖Λ‖)
    rintro _ ⟨y, _, rfl⟩
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    change ‖modDual y Λ‖ ≤ ‖Λ‖
    rw [norm_modDual]
  have hK_comp : IsCompact K := (WeakDual.isCompact_closedBall 0 ‖Λ‖).of_isClosed_subset isClosed_closure hK_sub_ball
  have hK_ne : K.Nonempty := by
    obtain ⟨y₀, hy₀⟩ := hS_ne
    exact ⟨StrongDual.toWeakDual (modDual y₀ Λ), subset_closure ⟨y₀, hy₀, rfl⟩⟩
  have hK_int : ∀ μ ∈ K, ∀ x : ℝ, ∃ n : ℤ, WeakDual.toStrongDual μ (eChar x) = (n : ℂ) := by
    intro μ hμ x
    have hcl : IsClosed {ζ : WeakDual ℂ C(BohrR, ℂ) | WeakDual.toStrongDual ζ (eChar x) ∈ Set.range (Int.cast : ℤ → ℂ)} :=
      isClosed_range_intCast_complex.preimage (WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) (eChar x))
    have hsub : K ⊆ {ζ : WeakDual ℂ C(BohrR, ℂ) | WeakDual.toStrongDual ζ (eChar x) ∈ Set.range (Int.cast : ℤ → ℂ)} := by
      refine closure_minimal ?_ hcl
      rintro _ ⟨y, _, rfl⟩
      change modDual y Λ (eChar x) ∈ Set.range (Int.cast : ℤ → ℂ)
      rw [modDual_eChar]
      obtain ⟨n, hn⟩ := hint (y + x)
      exact ⟨n, hn.symm⟩
    obtain ⟨n, hn⟩ := hsub hμ
    exact ⟨n, hn.symm⟩
  have hK_zero_ne : ∀ μ ∈ K, WeakDual.toStrongDual μ (eChar 0) ≠ 0 := by
    intro μ hμ
    have hcl : IsClosed {ζ : WeakDual ℂ C(BohrR, ℂ) |
        WeakDual.toStrongDual ζ (eChar 0) ∈ {z : ℂ | ∃ n : ℤ, n ≠ 0 ∧ z = (n : ℂ)}} :=
      isClosed_nonzero_intCast_complex.preimage (WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) (eChar 0))
    have hsub : K ⊆ {ζ : WeakDual ℂ C(BohrR, ℂ) |
        WeakDual.toStrongDual ζ (eChar 0) ∈ {z : ℂ | ∃ n : ℤ, n ≠ 0 ∧ z = (n : ℂ)}} := by
      refine closure_minimal ?_ hcl
      rintro _ ⟨y, hy, rfl⟩
      change ∃ n : ℤ, n ≠ 0 ∧ modDual y Λ (eChar 0) = (n : ℂ)
      rw [modDual_eChar, add_zero]
      obtain ⟨n, hn⟩ := hint y
      exact ⟨n, fun h0 => hy (by rw [hn, h0, Int.cast_zero]), hn⟩
    obtain ⟨n, hn0, hn⟩ := hsub hμ
    rw [hn]; exact Int.cast_ne_zero.mpr hn0
  have hK_norm_ge1 : ∀ μ ∈ K, 1 ≤ ‖WeakDual.toStrongDual μ‖ := by
    intro μ hμ
    obtain ⟨n, hn⟩ := hK_int μ hμ 0
    have hn0 : n ≠ 0 := fun h0 => hK_zero_ne μ hμ (by rw [hn, h0, Int.cast_zero])
    have h1 : (1 : ℝ) ≤ ‖WeakDual.toStrongDual μ (eChar 0)‖ := by
      rw [hn, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hn0
    calc (1 : ℝ) ≤ ‖WeakDual.toStrongDual μ (eChar 0)‖ := h1
      _ ≤ ‖WeakDual.toStrongDual μ‖ * ‖eChar 0‖ := (WeakDual.toStrongDual μ).le_opNorm _
      _ = ‖WeakDual.toStrongDual μ‖ := by rw [norm_eChar, mul_one]
  have hK_mod_mem : ∀ μ ∈ K, ∀ y : ℝ, WeakDual.toStrongDual μ (eChar y) ≠ 0 →
      StrongDual.toWeakDual (modDual y (WeakDual.toStrongDual μ)) ∈ K := by
    intro μ hμ y hy
    refine mem_closure_iff.mpr fun V hVo hVmem => ?_
    let W : Set (WeakDual ℂ C(BohrR, ℂ)) :=
      (fun ζ : WeakDual ℂ C(BohrR, ℂ) => StrongDual.toWeakDual (modDual y (WeakDual.toStrongDual ζ))) ⁻¹' V ∩
        {ζ : WeakDual ℂ C(BohrR, ℂ) | dist (WeakDual.toStrongDual ζ (eChar y)) (WeakDual.toStrongDual μ (eChar y)) < 1 / 2}
    have hWo : IsOpen W := (hVo.preimage (continuous_modDual_weak y)).inter
      (isOpen_lt ((WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) (eChar y)).dist continuous_const) continuous_const)
    have hμW : μ ∈ W := ⟨hVmem, by simp⟩
    obtain ⟨ζ, hζW, z, hzS, rfl⟩ := mem_closure_iff.mp hμ W hWo hμW
    refine ⟨StrongDual.toWeakDual (modDual (y + z) Λ), ?_, ?_⟩
    · have heq : StrongDual.toWeakDual (modDual (y + z) Λ) =
          StrongDual.toWeakDual (modDual y (WeakDual.toStrongDual (StrongDual.toWeakDual (modDual z Λ)))) := by
        rw [modDual_add]; rfl
      rw [heq]; exact hζW.1
    · refine ⟨y + z, ?_, rfl⟩
      intro h0
      have hdist : dist (Λ (eChar (y + z))) (WeakDual.toStrongDual μ (eChar y)) < 1 / 2 := by
        have h := hζW.2
        change dist (modDual z Λ (eChar y)) (WeakDual.toStrongDual μ (eChar y)) < 1 / 2 at h
        rwa [modDual_eChar, add_comm] at h
      rw [h0, dist_zero_left] at hdist
      obtain ⟨n, hn⟩ := hK_int μ hμ y
      have hn0 : n ≠ 0 := fun h => hy (by rw [hn, h, Int.cast_zero])
      have hge1 : (1 : ℝ) ≤ ‖WeakDual.toStrongDual μ (eChar y)‖ := by
        rw [hn, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hn0
      linarith
  -- Step 2: Minimal-norm element νw ∈ K via Cantor's intersection theorem
  let m : ℝ := sInf ((fun μ : WeakDual ℂ C(BohrR, ℂ) => ‖WeakDual.toStrongDual μ‖) '' K)
  have hm_bdd : BddBelow ((fun μ : WeakDual ℂ C(BohrR, ℂ) => ‖WeakDual.toStrongDual μ‖) '' K) :=
    ⟨0, by rintro _ ⟨μ, _, rfl⟩; exact norm_nonneg _⟩
  let Kn : ℕ → Set (WeakDual ℂ C(BohrR, ℂ)) := fun n =>
    K ∩ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 (m + 1 / ((n : ℝ) + 1))
  have hKn_ne : ∀ n : ℕ, (Kn n).Nonempty := fun n => by
    have hlt : m < m + 1 / ((n : ℝ) + 1) := lt_add_of_pos_right m (by positivity)
    obtain ⟨_, ⟨μ, hμK, rfl⟩, hμlt⟩ := exists_lt_of_csInf_lt (hK_ne.image _) hlt
    exact ⟨μ, hμK, by simpa [Metric.mem_closedBall, dist_zero_right] using hμlt.le⟩
  have hKn_anti : ∀ n : ℕ, Kn (n + 1) ⊆ Kn n := fun n μ ⟨hμK, hμb⟩ => by
    refine ⟨hμK, ?_⟩
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hμb ⊢
    have hmono : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      gcongr; omega
    linarith
  have hKn_cl : ∀ n : ℕ, IsClosed (Kn n) := fun n =>
    isClosed_closure.inter (WeakDual.isClosed_closedBall 0 _)
  have hK0_comp : IsCompact (Kn 0) :=
    hK_comp.of_isClosed_subset (hKn_cl 0) Set.inter_subset_left
  obtain ⟨νw, hνw_inter⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Kn hKn_anti hKn_ne hK0_comp hKn_cl
  have hνw_K : νw ∈ K := (Set.mem_iInter.mp hνw_inter 0).1
  let ν : StrongDual ℂ C(BohrR, ℂ) := WeakDual.toStrongDual νw
  have hν_min : ∀ μ ∈ K, ‖ν‖ ≤ ‖WeakDual.toStrongDual μ‖ := fun μ hμ => by
    have hm_le : m ≤ ‖WeakDual.toStrongDual μ‖ := csInf_le hm_bdd ⟨μ, hμ, rfl⟩
    have hν_le_m : ‖ν‖ ≤ m := by
      by_contra hgt
      push Not at hgt
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
      have hmem := (Set.mem_iInter.mp hνw_inter N).2
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hmem
      change ‖ν‖ ≤ m + 1 / ((N : ℝ) + 1) at hmem
      linarith
    exact hν_le_m.trans hm_le
  have hν_pos : 0 < ‖ν‖ := lt_of_lt_of_le zero_lt_one (hK_norm_ge1 νw hνw_K)
  have hν_int : ∀ x : ℝ, ∃ n : ℤ, ν (eChar x) = (n : ℂ) := hK_int νw hνw_K
  -- Step 3: B = {modDual y ν | ν (eChar y) ≠ 0} is FINITE
  let A : Set ℝ := {y : ℝ | ν (eChar y) ≠ 0}
  let B : Set (WeakDual ℂ C(BohrR, ℂ)) :=
    (fun y : ℝ => StrongDual.toWeakDual (modDual y ν)) '' A
  have hB_sub_K : B ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hK_mod_mem νw hνw_K y hy
  have hclB_sub_K : closure B ⊆ K := closure_minimal hB_sub_K isClosed_closure
  have hclB_comp : IsCompact (closure B) :=
    hK_comp.of_isClosed_subset isClosed_closure hclB_sub_K
  have hclB_norm : ∀ μ ∈ closure B, ‖WeakDual.toStrongDual μ‖ = ‖ν‖ := fun μ hμ => by
    apply le_antisymm
    · have hsub : closure B ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 ‖ν‖ := by
        refine closure_minimal ?_ (WeakDual.isClosed_closedBall 0 ‖ν‖)
        rintro _ ⟨y, _, rfl⟩
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
        change ‖modDual y ν‖ ≤ ‖ν‖
        rw [norm_modDual]
      simpa [Metric.mem_closedBall, dist_zero_right] using hsub hμ
    · exact hν_min μ (hclB_sub_K hμ)
  have hcov : ∀ μ ∈ closure B, ∃ U : Set (WeakDual ℂ C(BohrR, ℂ)),
      IsOpen U ∧ μ ∈ U ∧ (B ∩ U).Subsingleton := by
    intro μ hμ
    have hμ_norm : ‖WeakDual.toStrongDual μ‖ = ‖ν‖ := hclB_norm μ hμ
    set ε := 1 / (64 * ‖ν‖)
    have hε : 0 < ε := by positivity
    have hν_ge1 : 1 ≤ ‖ν‖ := hK_norm_ge1 νw hνw_K
    have hε_le : ε ≤ 1 / 64 := by
      dsimp only [ε]
      gcongr
      linarith
    have hlt_op : ‖ν‖ - ε < ‖WeakDual.toStrongDual μ‖ := by rw [hμ_norm]; linarith
    have hex_f : ∃ f : C(BohrR, ℂ), ‖f‖ ≤ 1 ∧ ‖ν‖ - ε < (WeakDual.toStrongDual μ f).re := by
      by_contra hnone
      push Not at hnone
      have hbound : ‖WeakDual.toStrongDual μ‖ ≤ ‖ν‖ - ε := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun g => ?_
        by_cases hg0 : g = 0
        · simp [hg0]
        · have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg0
          let g1 : C(BohrR, ℂ) := ((‖g‖⁻¹ : ℝ) : ℂ) • g
          have hg1_norm : ‖g1‖ = 1 := by
            rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hgpos.le),
              inv_mul_cancel₀ hgpos.ne']
          by_cases hv0 : WeakDual.toStrongDual μ g1 = 0
          · have hμg : WeakDual.toStrongDual μ g = 0 := by
              have h1 : ((‖g‖⁻¹ : ℝ) : ℂ) * WeakDual.toStrongDual μ g = 0 := by
                simpa [g1, map_smul, smul_eq_mul] using hv0
              exact (mul_eq_zero.mp h1).resolve_left (Complex.ofReal_ne_zero.mpr (inv_ne_zero hgpos.ne'))
            rw [hμg, norm_zero]
            nlinarith
          · let c : ℂ := star (WeakDual.toStrongDual μ g1) / (‖WeakDual.toStrongDual μ g1‖ : ℂ)
            have hc_norm : ‖c‖ = 1 := by
              rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
                div_self (norm_ne_zero_iff.mpr hv0)]
            let f : C(BohrR, ℂ) := c • g1
            have hf_norm : ‖f‖ ≤ 1 := by rw [norm_smul, hc_norm, hg1_norm, mul_one]
            have hre_f : (WeakDual.toStrongDual μ f).re = ‖WeakDual.toStrongDual μ g1‖ := by
              rw [map_smul, smul_eq_mul]
              dsimp only [c]
              have hmul : star (WeakDual.toStrongDual μ g1) / (‖WeakDual.toStrongDual μ g1‖ : ℂ) *
                  WeakDual.toStrongDual μ g1 = (‖WeakDual.toStrongDual μ g1‖ : ℂ) := by
                have hne : (‖WeakDual.toStrongDual μ g1‖ : ℂ) ≠ 0 :=
                  Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv0)
                rw [div_mul_eq_mul_div, RCLike.star_def, Complex.conj_mul', div_eq_iff hne]
                ring
              rw [hmul, Complex.ofReal_re]
            have hle_f := hnone f hf_norm
            rw [hre_f] at hle_f
            have hnorm_g1 : ‖WeakDual.toStrongDual μ g1‖ = ‖g‖⁻¹ * ‖WeakDual.toStrongDual μ g‖ := by
              rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hgpos.le)]
            rw [hnorm_g1, inv_mul_le_iff₀ hgpos] at hle_f
            linarith
      linarith
    obtain ⟨f, hf_norm, hf_re⟩ := hex_f
    let U : Set (WeakDual ℂ C(BohrR, ℂ)) :=
      {ζ : WeakDual ℂ C(BohrR, ℂ) | ‖ν‖ - ε < (WeakDual.toStrongDual ζ f).re}
    have hUo : IsOpen U :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) f))
    refine ⟨U, hUo, hf_re, ?_⟩
    rintro _ ⟨⟨y₁, _, rfl⟩, h1U⟩ _ ⟨⟨y₂, _, rfl⟩, h2U⟩
    have heq := modDual_eq_of_near_norm hν_int hν_pos hf_norm h1U h2U
    exact congrArg StrongDual.toWeakDual heq
  choose U hUo hUmem hUsub using hcov
  have hcov_sub : closure B ⊆ ⋃ μ : closure B, U μ.1 μ.2 := fun μ hμ =>
    Set.mem_iUnion.mpr ⟨⟨μ, hμ⟩, hUmem μ hμ⟩
  obtain ⟨t_fin, ht_cov⟩ := hclB_comp.elim_finite_subcover (fun μ : closure B => U μ.1 μ.2)
    (fun μ => hUo μ.1 μ.2) hcov_sub
  have hB_fin : B.Finite := by
    have hB_sub_u : B ⊆ ⋃ μ ∈ t_fin, (B ∩ U μ.1 μ.2) := fun ζ hζ => by
      have hmem := ht_cov (subset_closure hζ)
      simp only [Set.mem_iUnion] at hmem ⊢
      rcases hmem with ⟨μ, hμt, hζU⟩
      exact ⟨μ, hμt, hζ, hζU⟩
    exact (t_fin.finite_toSet.biUnion fun μ _ => (hUsub μ.1 μ.2).finite).subset hB_sub_u
  -- Step 4: Γ = {y | modDual y ν = ν} and ν = ∑ a ∈ R₀, c(a) • modDual (-a) (mH Γ)
  let Γ : AddSubgroup ℝ :=
    { carrier := {y : ℝ | modDual y ν = ν}
      zero_mem' := modDual_zero ν
      add_mem' := fun {a b} ha hb => by change modDual (a + b) ν = ν; rw [modDual_add, hb, ha]
      neg_mem' := fun {a} ha => by
        change modDual (-a) ν = ν
        have h1 : modDual (-a) (modDual a ν) = modDual (-a) ν := congrArg (modDual (-a)) ha
        rw [← modDual_add, neg_add_cancel, modDual_zero] at h1
        exact h1.symm }
  have hmod_eq_iff : ∀ y₁ y₂ : ℝ, modDual y₁ ν = modDual y₂ ν ↔ y₁ - y₂ ∈ Γ := fun y₁ y₂ => by
    change modDual y₁ ν = modDual y₂ ν ↔ modDual (y₁ - y₂) ν = ν
    constructor
    · intro h
      have h1 : modDual (-y₂) (modDual y₁ ν) = modDual (-y₂) (modDual y₂ ν) := congrArg _ h
      rw [← modDual_add, ← modDual_add, neg_add_cancel, modDual_zero] at h1
      rw [show y₁ - y₂ = -y₂ + y₁ by ring]
      exact h1
    · intro h
      have h1 : modDual y₂ (modDual (y₁ - y₂) ν) = modDual y₂ ν := congrArg _ h
      rw [← modDual_add, show y₂ + (y₁ - y₂) = y₁ by ring] at h1
      exact h1
  classical
  let Bfin : Finset (WeakDual ℂ C(BohrR, ℂ)) := hB_fin.toFinset
  have hrep_ex : ∀ ζ : Bfin, ∃ a ∈ A, StrongDual.toWeakDual (modDual a ν) = ζ.1 := fun ζ => by
    have hmem : ζ.1 ∈ B := hB_fin.mem_toFinset.mp ζ.2
    exact hmem
  let repA : Bfin → ℝ := fun ζ => (hrep_ex ζ).choose
  have hrepA_mem : ∀ ζ : Bfin, repA ζ ∈ A := fun ζ => (hrep_ex ζ).choose_spec.1
  have hrepA_eq : ∀ ζ : Bfin, StrongDual.toWeakDual (modDual (repA ζ) ν) = ζ.1 :=
    fun ζ => (hrep_ex ζ).choose_spec.2
  have hrepA_inj : ∀ ζ₁ ζ₂ : Bfin, repA ζ₁ - repA ζ₂ ∈ Γ → ζ₁ = ζ₂ := fun ζ₁ ζ₂ hsub => by
    apply Subtype.ext
    rw [← hrepA_eq ζ₁, ← hrepA_eq ζ₂]
    exact congrArg StrongDual.toWeakDual ((hmod_eq_iff _ _).mpr hsub)
  let c_int : Bfin → ℤ := fun ζ => (hν_int (repA ζ)).choose
  have hc_int_spec : ∀ ζ : Bfin, ν (eChar (repA ζ)) = (c_int ζ : ℂ) :=
    fun ζ => (hν_int (repA ζ)).choose_spec
  let p_poly : C(BohrR, ℂ) := ∑ ζ : Bfin, (c_int ζ : ℂ) • eChar (-(repA ζ))
  have hν_eq_mH : ∀ f : C(BohrR, ℂ), ν f = ∫ g, f g * p_poly g ∂(mH Γ) := by
    let ν' : StrongDual ℂ C(BohrR, ℂ) :=
      LinearMap.mkContinuous
        { toFun := fun f => ∫ g, f g * p_poly g ∂(mH Γ)
          map_add' := fun f₁ f₂ => by
            simp_rw [ContinuousMap.add_apply, add_mul]
            exact integral_add
              ((f₁ * p_poly).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
              ((f₂ * p_poly).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          map_smul' := fun c f => by
            simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
            exact integral_const_mul c _ }
        ‖p_poly‖ (fun f => by
          calc ‖∫ g, f g * p_poly g ∂(mH Γ)‖
              ≤ ∫ g, ‖f g * p_poly g‖ ∂(mH Γ) := norm_integral_le_integral_norm _
            _ ≤ ∫ _, ‖p_poly‖ * ‖f‖ ∂(mH Γ) :=
                integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                  (integrable_const _) (Eventually.of_forall fun g => by
                    dsimp only
                    rw [norm_mul, mul_comm]
                    exact mul_le_mul (ContinuousMap.norm_coe_le_norm p_poly g)
                      (ContinuousMap.norm_coe_le_norm f g) (norm_nonneg _) (norm_nonneg _))
            _ = ‖p_poly‖ * ‖f‖ := by
                rw [integral_const, Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul])
    have heq_dual : ν = ν' := by
      apply eq_of_eq_on_eChar
      intro x
      change ν (eChar x) = ∫ g, eChar x g * p_poly g ∂(mH Γ)
      have hp_eval : ∀ g, eChar x g * p_poly g = ∑ ζ : Bfin, (c_int ζ : ℂ) * eChar (x - repA ζ) g := fun g => by
        have h1 : p_poly g = ∑ ζ : Bfin, (c_int ζ : ℂ) * eChar (-(repA ζ)) g := by
          simp [p_poly]
        rw [h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ζ _ => ?_
        rw [sub_eq_add_neg, eChar_add]
        change eChar x g * ((c_int ζ : ℂ) * eChar (-(repA ζ)) g) =
          (c_int ζ : ℂ) * (eChar x g * eChar (-(repA ζ)) g)
        ring
      simp_rw [hp_eval]
      rw [integral_finsetSum Finset.univ (fun ζ _ =>
        ((eChar (x - repA ζ)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _)]
      simp_rw [integral_const_mul, integral_eChar_mH]
      by_cases hxA : x ∈ A
      · have hmemB : StrongDual.toWeakDual (modDual x ν) ∈ Bfin :=
          hB_fin.mem_toFinset.mpr ⟨x, hxA, rfl⟩
        let ζ₀ : Bfin := ⟨StrongDual.toWeakDual (modDual x ν), hmemB⟩
        have hx_sub : x - repA ζ₀ ∈ Γ := by
          rw [← hmod_eq_iff]
          have h1 := hrepA_eq ζ₀
          exact (congrArg WeakDual.toStrongDual h1).symm
        rw [Finset.sum_eq_single ζ₀]
        · rw [Set.indicator_of_mem hx_sub, mul_one, ← hc_int_spec ζ₀]
          have h2 : modDual (x - repA ζ₀) ν = ν := hx_sub
          have h3 := congrFun (congrArg DFunLike.coe h2) (eChar (repA ζ₀))
          rw [modDual_eChar, show x - repA ζ₀ + repA ζ₀ = x by ring] at h3
          exact h3
        · intro ζ _ hne
          have hnot : x - repA ζ ∉ Γ := fun hmem => by
            have hdiff : repA ζ₀ - repA ζ ∈ Γ := by
              have heq : repA ζ₀ - repA ζ = (x - repA ζ) - (x - repA ζ₀) := by ring
              rw [heq]; exact Γ.sub_mem hmem hx_sub
            exact hne (hrepA_inj ζ₀ ζ hdiff).symm
          rw [Set.indicator_of_notMem hnot, mul_zero]
        · intro h; exact absurd (Finset.mem_univ ζ₀) h
      · have hx0 : ν (eChar x) = 0 := by simpa [A] using hxA
        rw [hx0]
        symm
        refine Finset.sum_eq_zero fun ζ _ => ?_
        have hnot : x - repA ζ ∉ Γ := fun hmem => by
          have h2 : modDual (x - repA ζ) ν = ν := hmem
          have h3 := congrFun (congrArg DFunLike.coe h2) (eChar (repA ζ))
          rw [modDual_eChar, show x - repA ζ + repA ζ = x by ring, hx0] at h3
          exact hrepA_mem ζ h3.symm
        rw [Set.indicator_of_notMem hnot, mul_zero]
    intro f
    exact congrFun (congrArg DFunLike.coe heq_dual) f
  -- Step 5: Lebesgue decomposition of |Λ| with respect to mH Γ
  obtain ⟨PΛ⟩ := exists_polar_rep Λ
  have : IsFiniteMeasure PΛ.ν := PΛ.hν_fin
  have : IsFiniteMeasure PΛ.ρ := PΛ.hρ_fin
  have : PΛ.ρ.Regular := PΛ.hρ_reg
  let σ : Measure BohrR := PΛ.ν.singularPart (mH Γ)
  let wr : BohrR → ℝ≥0∞ := PΛ.ν.rnDeriv (mH Γ)
  have hσ_sing : σ ⟂ₘ mH Γ := Measure.mutuallySingular_singularPart PΛ.ν (mH Γ)
  have hdecomp_ν : PΛ.ν = σ + (mH Γ).withDensity wr := Measure.haveLebesgueDecomposition_add PΛ.ν (mH Γ)
  have hσ_le_ν : σ ≤ PΛ.ν := by rw [hdecomp_ν]; exact Measure.le_add_right le_rfl
  have hσ_le_2ρ : σ ≤ (2 : ℝ≥0∞) • PΛ.ρ := hσ_le_ν.trans PΛ.hν_le
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le PΛ.ν hσ_le_ν
  have hwd_le_ν : (mH Γ).withDensity wr ≤ PΛ.ν := Measure.withDensity_rnDeriv_le PΛ.ν (mH Γ)
  have : IsFiniteMeasure ((mH Γ).withDensity wr) := isFiniteMeasure_of_le PΛ.ν hwd_le_ν
  have hwr_meas : Measurable wr := Measure.measurable_rnDeriv PΛ.ν (mH Γ)
  have hwr_lt_top : ∀ᵐ g ∂(mH Γ), wr g < ∞ := Measure.rnDeriv_lt_top PΛ.ν (mH Γ)
  have hwr_int : Integrable (fun g => (wr g).toReal) (mH Γ) := by
    refine integrable_toReal_of_lintegral_ne_top hwr_meas.aemeasurable ?_
    have h1 : (∫⁻ g, wr g ∂(mH Γ)) = (mH Γ).withDensity wr Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h1]
    exact measure_ne_top _ _
  let wc : BohrR → ℂ := fun g => ((wr g).toReal : ℂ) * PΛ.u g
  have hwc_int : Integrable wc (mH Γ) :=
    Integrable.mono' hwr_int
      ((Complex.continuous_ofReal.measurable.comp hwr_meas.ennreal_toReal).mul PΛ.hu_meas).aestronglyMeasurable
      (Eventually.of_forall fun g => by
        dsimp only [wc]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, PΛ.hu_norm g, mul_one])
  let Λ_ac : StrongDual ℂ C(BohrR, ℂ) :=
    LinearMap.mkContinuous
      { toFun := fun f => ∫ g, f g * wc g ∂(mH Γ)
        map_add' := fun f₁ f₂ => by
          simp_rw [ContinuousMap.add_apply, add_mul]
          exact integral_add
            (hwc_int.bdd_mul f₁.continuous.aestronglyMeasurable (Eventually.of_forall (ContinuousMap.norm_coe_le_norm f₁)))
            (hwc_int.bdd_mul f₂.continuous.aestronglyMeasurable (Eventually.of_forall (ContinuousMap.norm_coe_le_norm f₂)))
        map_smul' := fun c f => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
          exact integral_const_mul c _ }
      (((mH Γ).withDensity wr Set.univ).toReal) (fun f => by
        calc ‖∫ g, f g * wc g ∂(mH Γ)‖ ≤ ∫ g, ‖f g * wc g‖ ∂(mH Γ) := norm_integral_le_integral_norm _
          _ ≤ ∫ g, (wr g).toReal * ‖f‖ ∂(mH Γ) := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                (hwr_int.mul_const ‖f‖) (Eventually.of_forall fun g => ?_)
              dsimp only [wc]
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
                PΛ.hu_norm g, mul_one, mul_comm]
              exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f g) ENNReal.toReal_nonneg
          _ = (∫ g, (wr g).toReal ∂(mH Γ)) * ‖f‖ := integral_mul_const _ _
          _ = ((mH Γ).withDensity wr Set.univ).toReal * ‖f‖ := by
              congr 1
              rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
                integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
                  hwr_meas.ennreal_toReal.aestronglyMeasurable]
              congr 1
              refine lintegral_congr_ae ?_
              filter_upwards [hwr_lt_top] with g hg
              exact ENNReal.ofReal_toReal hg.ne)
  let Λ_s : StrongDual ℂ C(BohrR, ℂ) :=
    LinearMap.mkContinuous
      { toFun := fun f => ∫ g, f g * PΛ.u g ∂σ
        map_add' := fun f₁ f₂ => by
          simp_rw [ContinuousMap.add_apply, add_mul]
          exact integral_add
            (Integrable.mono' (integrable_const ‖f₁‖) (f₁.continuous.measurable.mul PΛ.hu_meas).aestronglyMeasurable
              (Eventually.of_forall fun g => by rw [norm_mul, PΛ.hu_norm g, mul_one]; exact ContinuousMap.norm_coe_le_norm f₁ g))
            (Integrable.mono' (integrable_const ‖f₂‖) (f₂.continuous.measurable.mul PΛ.hu_meas).aestronglyMeasurable
              (Eventually.of_forall fun g => by rw [norm_mul, PΛ.hu_norm g, mul_one]; exact ContinuousMap.norm_coe_le_norm f₂ g))
        map_smul' := fun c f => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
          exact integral_const_mul c _ }
      ((σ Set.univ).toReal) (fun f => by
        calc ‖∫ g, f g * PΛ.u g ∂σ‖ ≤ ∫ g, ‖f g * PΛ.u g‖ ∂σ := norm_integral_le_integral_norm _
          _ ≤ ∫ _, ‖f‖ ∂σ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                (integrable_const _) (Eventually.of_forall fun g => by
                  dsimp only
                  rw [norm_mul, PΛ.hu_norm g, mul_one]; exact ContinuousMap.norm_coe_le_norm f g)
          _ = (σ Set.univ).toReal * ‖f‖ := by rw [integral_const, Measure.real_def, smul_eq_mul])
  have hΛ_split : Λ = Λ_ac + Λ_s := by
    ext f
    change Λ f = (∫ g, f g * wc g ∂(mH Γ)) + ∫ g, f g * PΛ.u g ∂σ
    have hint_σ : Integrable (fun g => f g * PΛ.u g) σ :=
      Integrable.mono' (integrable_const ‖f‖)
        (f.continuous.measurable.mul PΛ.hu_meas).aestronglyMeasurable
        (Eventually.of_forall fun g => by
          rw [norm_mul, PΛ.hu_norm g, mul_one]; exact ContinuousMap.norm_coe_le_norm f g)
    have hint_wd : Integrable (fun g => f g * PΛ.u g) ((mH Γ).withDensity wr) :=
      Integrable.mono' (integrable_const ‖f‖)
        (f.continuous.measurable.mul PΛ.hu_meas).aestronglyMeasurable
        (Eventually.of_forall fun g => by
          rw [norm_mul, PΛ.hu_norm g, mul_one]; exact ContinuousMap.norm_coe_le_norm f g)
    rw [PΛ.hrep f, hdecomp_ν, integral_add_measure hint_σ hint_wd,
      integral_withDensity_eq_integral_toReal_smul hwr_meas hwr_lt_top, add_comm]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    dsimp only [wc]; rw [Complex.real_smul]; ring
  have hnorm_ac_le : ‖Λ_ac‖ ≤ ((mH Γ).withDensity wr Set.univ).toReal :=
    LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _
  have hnorm_s_le : ‖Λ_s‖ ≤ (σ Set.univ).toReal :=
    LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _
  have hnorm_sum_eq : ((mH Γ).withDensity wr Set.univ).toReal + (σ Set.univ).toReal = ‖Λ‖ := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), add_comm,
      ← Measure.add_apply, ← hdecomp_ν, PΛ.hnorm]
  have hnorm_add_exact : ‖Λ_ac‖ + ‖Λ_s‖ = ‖Λ‖ := by
    have htri : ‖Λ‖ ≤ ‖Λ_ac‖ + ‖Λ_s‖ := by rw [hΛ_split]; exact norm_add_le _ _
    linarith
  -- Step 6: Filter F along which modDual y Λ → ν
  let F : Filter ℝ :=
    Filter.comap (fun y : ℝ => StrongDual.toWeakDual (modDual y Λ)) (𝓝 νw) ⊓ 𝓟 S
  have hF_ne : F.NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro U hU
    rw [Filter.mem_comap] at hU
    obtain ⟨V, hV_nhds, hV_sub⟩ := hU
    obtain ⟨ζ, hζV, y, hyS, rfl⟩ := mem_closure_iff_nhds.mp hνw_K V hV_nhds
    exact ⟨y, hV_sub hζV, hyS⟩
  have hF_tendsto : Tendsto (fun y : ℝ => StrongDual.toWeakDual (modDual y Λ)) F (𝓝 νw) :=
    tendsto_comap.mono_left inf_le_left
  have hmod_s_le : ∀ (y : ℝ) (f : C(BohrR, ℂ)), ‖modDual y Λ_s f‖ ≤ ∫ g, ‖f g‖ ∂σ := fun y f => by
    change ‖∫ g, (eChar y * f) g * PΛ.u g ∂σ‖ ≤ ∫ g, ‖f g‖ ∂σ
    calc ‖∫ g, (eChar y * f) g * PΛ.u g ∂σ‖
        ≤ ∫ g, ‖(eChar y * f) g * PΛ.u g‖ ∂σ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖f g‖ ∂σ := by
          refine integral_congr_ae (Eventually.of_forall fun g => ?_)
          change ‖eChar y g * f g * PΛ.u g‖ = ‖f g‖
          rw [norm_mul, norm_mul, norm_eChar_apply, one_mul, PΛ.hu_norm g, mul_one]
  -- Step 7: Dichotomy on whether F meets some coset a + Γ
  by_cases hcase : ∃ a : ℝ, (F ⊓ 𝓟 ((fun z => a + z) '' (Γ : Set ℝ))).NeBot
  · rcases hcase with ⟨a, hF1_ne⟩
    have : (F ⊓ 𝓟 ((fun z => a + z) '' (Γ : Set ℝ))).NeBot := hF1_ne
    let F1 := F ⊓ 𝓟 ((fun z => a + z) '' (Γ : Set ℝ))
    have hAnn_ae : ∀ᵐ g ∂(mH Γ), g ∈ (AnnSubgroup Γ : Set BohrR) := by
      rw [ae_iff]; exact mH_compl_annSubgroup Γ
    have hmod_ac_const : ∀ y ∈ (fun z => a + z) '' (Γ : Set ℝ), modDual y Λ_ac = modDual a Λ_ac := by
      rintro y ⟨z, hzΓ, rfl⟩
      ext f
      change ∫ g, (eChar (a + z) * f) g * wc g ∂(mH Γ) = ∫ g, (eChar a * f) g * wc g ∂(mH Γ)
      refine integral_congr_ae ?_
      filter_upwards [hAnn_ae] with g hgH
      change eChar (a + z) g * f g * wc g = eChar a g * f g * wc g
      rw [eChar_add]
      change (eChar a g * eChar z g) * f g * wc g = eChar a g * f g * wc g
      have hz1 : eChar z g = 1 := by simp only [eChar_apply, hgH z hzΓ, Circle.coe_one]
      rw [hz1, mul_one]
    have hdiff_le_σ : ∀ f : C(BohrR, ℂ), ‖(ν - modDual a Λ_ac) f‖ ≤ ∫ g, ‖f g‖ ∂σ := by
      intro f
      have hlim_Λ : Tendsto (fun y => modDual y Λ f) F1 (𝓝 (ν f)) :=
        ((WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) f).continuousAt.tendsto.comp hF_tendsto).mono_left inf_le_left
      have hlim_ac : Tendsto (fun y => modDual y Λ_ac f) F1 (𝓝 (modDual a Λ_ac f)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with y hy
        rw [hmod_ac_const y hy]
      have hlim_s : Tendsto (fun y => modDual y Λ_s f) F1 (𝓝 ((ν - modDual a Λ_ac) f)) := by
        have hsub : (fun y => modDual y Λ_s f) = fun y => modDual y Λ f - modDual y Λ_ac f := by
          funext y
          have h := congrFun (congrArg DFunLike.coe (modDual_add_dual y Λ_ac Λ_s)) f
          rw [← hΛ_split] at h
          change modDual y Λ f = modDual y Λ_ac f + modDual y Λ_s f at h
          linear_combination -h
        rw [hsub]
        exact hlim_Λ.sub hlim_ac
      exact le_of_tendsto hlim_s.norm (Eventually.of_forall fun y => hmod_s_le y f)
    have hdiff_zero : ν = modDual a Λ_ac := by
      ext f
      apply sub_eq_zero.mp
      change (ν - modDual a Λ_ac) f = 0
      have hrep_diff : ∀ g_map : C(BohrR, ℂ),
          (ν - modDual a Λ_ac) g_map = ∫ g, g_map g * (p_poly g - eChar a g * wc g) ∂(mH Γ) := fun g_map => by
        change ν g_map - ∫ g, (eChar a * g_map) g * wc g ∂(mH Γ) = _
        have hint1 : Integrable (fun g => g_map g * p_poly g) (mH Γ) :=
          (g_map * p_poly).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have hint2 : Integrable (fun g => (eChar a * g_map) g * wc g) (mH Γ) :=
          hwc_int.bdd_mul (eChar a * g_map).continuous.aestronglyMeasurable
            (Eventually.of_forall (ContinuousMap.norm_coe_le_norm (eChar a * g_map)))
        rw [hν_eq_mH g_map, ← integral_sub hint1 hint2]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        change g_map g * p_poly g - eChar a g * g_map g * wc g = g_map g * (p_poly g - eChar a g * wc g)
        ring
      have hq_int : Integrable (fun g => p_poly g - eChar a g * wc g) (mH Γ) :=
        (p_poly.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).sub
          (hwc_int.bdd_mul (eChar a).continuous.aestronglyMeasurable
            (Eventually.of_forall fun g => by rw [norm_eChar_apply]))
      rw [hrep_diff f]
      exact zero_of_abs_le_singular Γ hσ_le_2ρ hσ_sing hq_int
        (fun g_map => by rw [← hrep_diff g_map]; exact hdiff_le_σ g_map) f
    have hΛ_ac_eq : Λ_ac = modDual (-a) ν := by
      rw [hdiff_zero, ← modDual_add, neg_add_cancel, modDual_zero]
    have hΛ_ac_coset : IsCosetLinComb (fun x => Λ_ac (eChar x)) := by
      refine ⟨(Finset.univ : Finset Bfin).toList.map fun ζ => (c_int ζ, repA ζ + a, Γ), fun x => ?_⟩
      dsimp only
      rw [hΛ_ac_eq, modDual_eChar, hν_eq_mH]
      have hp_eval : ∀ g, eChar (-a + x) g * p_poly g =
          ∑ ζ : Bfin, (c_int ζ : ℂ) * eChar (-a + x - repA ζ) g := fun g => by
        have h1 : p_poly g = ∑ ζ : Bfin, (c_int ζ : ℂ) * eChar (-(repA ζ)) g := by simp [p_poly]
        rw [h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ζ _ => ?_
        rw [sub_eq_add_neg, eChar_add (-a + x) (-(repA ζ))]
        change eChar (-a + x) g * ((c_int ζ : ℂ) * eChar (-(repA ζ)) g) =
          (c_int ζ : ℂ) * (eChar (-a + x) g * eChar (-(repA ζ)) g)
        ring
      simp_rw [hp_eval]
      rw [integral_finsetSum Finset.univ (fun ζ _ =>
        ((eChar (-a + x - repA ζ)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _)]
      simp_rw [integral_const_mul, integral_eChar_mH]
      rw [List.map_map]
      have hlist_sum : (List.map
          ((fun p : ℤ × ℝ × AddSubgroup ℝ => (p.1 : ℂ) *
            Set.indicator ((fun z => p.2.1 + z) '' (p.2.2 : Set ℝ)) (fun _ => (1 : ℂ)) x) ∘
            fun ζ : Bfin => (c_int ζ, repA ζ + a, Γ))
          (Finset.univ : Finset Bfin).toList).sum =
          ∑ ζ : Bfin, (c_int ζ : ℂ) *
            Set.indicator ((fun z => repA ζ + a + z) '' (Γ : Set ℝ)) (fun _ => (1 : ℂ)) x := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
        rfl
      rw [hlist_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      congr 1
      by_cases hmem : -a + x - repA ζ ∈ Γ
      · have hmem' : x ∈ (fun z => repA ζ + a + z) '' (Γ : Set ℝ) :=
          ⟨-a + x - repA ζ, hmem, by ring⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
      · have hnot' : x ∉ (fun z => repA ζ + a + z) '' (Γ : Set ℝ) := by
          rintro ⟨z, hz, hzx⟩
          dsimp only at hzx
          have hzeq : -a + x - repA ζ = z := by linarith
          exact hmem (by rw [hzeq]; exact hz)
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hnot']
    have hΛ_ac_int : ∀ x : ℝ, ∃ n : ℤ, Λ_ac (eChar x) = (n : ℂ) := fun x => by
      rw [hΛ_ac_eq, modDual_eChar]; exact hν_int (-a + x)
    have hΛ_s_int : ∀ x : ℝ, ∃ n : ℤ, Λ_s (eChar x) = (n : ℂ) := fun x => by
      obtain ⟨n₁, hn₁⟩ := hint x
      obtain ⟨n₂, hn₂⟩ := hΛ_ac_int x
      refine ⟨n₁ - n₂, ?_⟩
      have h1 := congrFun (congrArg DFunLike.coe hΛ_split) (eChar x)
      change Λ (eChar x) = Λ_ac (eChar x) + Λ_s (eChar x) at h1
      rw [hn₁, hn₂] at h1
      push_cast; linear_combination h1.symm
    have hnorm_ac_ge1 : 1 ≤ ‖Λ_ac‖ := by
      rw [hΛ_ac_eq, norm_modDual]
      exact hK_norm_ge1 νw hνw_K
    refine ⟨Λ_ac, Λ_s, hΛ_split, hΛ_ac_coset, hΛ_s_int, by linarith⟩
  · -- Case 2: F avoids every coset a + Γ => contradiction (ν = 0)!
    exfalso
    push Not at hcase
    have hF_avoid : ∀ a : ℝ, ∀ᶠ y in F, y ∉ (fun z => a + z) '' (Γ : Set ℝ) := fun a =>
      Filter.inf_principal_eq_bot.mp (hcase a)
    have hν_le_σ : ∀ f : C(BohrR, ℂ), ‖ν f‖ ≤ ∫ g, ‖f g‖ ∂σ := fun f => by
      have hlim_Λ : Tendsto (fun y => modDual y Λ f) F (𝓝 (ν f)) :=
        (WeakBilin.eval_continuous (topDualPairing ℂ C(BohrR, ℂ)) f).continuousAt.tendsto.comp hF_tendsto
      have hlim_ac : Tendsto (fun y => modDual y Λ_ac f) F (𝓝 0) := by
        have heq : (fun y => modDual y Λ_ac f) = fun y => ∫ g, eChar y g * (f g * wc g) ∂(mH Γ) := by
          funext y
          change ∫ g, eChar y g * f g * wc g ∂(mH Γ) = _
          simp_rw [mul_assoc]
        rw [heq]
        exact tendsto_modDual_ac_zero_of_not_coset Γ hwc_int hF_avoid f
      have hlim_s : Tendsto (fun y => modDual y Λ_s f) F (𝓝 (ν f)) := by
        have hsub : (fun y => modDual y Λ_s f) = fun y => modDual y Λ f - modDual y Λ_ac f := by
          funext y
          have h := congrFun (congrArg DFunLike.coe (modDual_add_dual y Λ_ac Λ_s)) f
          rw [← hΛ_split] at h
          change modDual y Λ f = modDual y Λ_ac f + modDual y Λ_s f at h
          linear_combination -h
        rw [hsub, ← sub_zero (ν f)]
        exact hlim_Λ.sub hlim_ac
      exact le_of_tendsto hlim_s.norm (Eventually.of_forall fun y => hmod_s_le y f)
    have hν_zero : ν = 0 := by
      ext f
      rw [hν_eq_mH f]
      exact zero_of_abs_le_singular Γ hσ_le_2ρ hσ_sing
        (p_poly.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (fun g_map => by rw [← hν_eq_mH g_map]; exact hν_le_σ g_map) f
    have : ‖ν‖ = 0 := by rw [hν_zero, norm_zero]
    linarith

lemma exists_coset_lincomb_of_int_dual_aux :
    ∀ (N : ℕ) (Λ : StrongDual ℂ C(BohrR, ℂ)),
      ‖Λ‖ < (N : ℝ) →
      (∀ x : ℝ, ∃ n : ℤ, Λ (eChar x) = (n : ℂ)) →
      IsCosetLinComb (fun x => Λ (eChar x)) := by
  intro N
  induction N with
  | zero =>
    intro Λ hlt _
    exfalso
    simp only [Nat.cast_zero] at hlt
    linarith [norm_nonneg Λ]
  | succ N ih =>
    intro Λ hlt hint
    by_cases h0 : Λ = 0
    · simpa [h0] using isCosetLinComb_zero
    · obtain ⟨Λ_ac, Λ_s, hsplit, hcos, hs_int, hs_norm⟩ := amemiya_ito_step h0 hint
      have hs_lt : ‖Λ_s‖ < (N : ℝ) := by
        have : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        linarith
      have hs_cos := ih Λ_s hs_lt hs_int
      have hcomb := isCosetLinComb_add hcos hs_cos
      refine hcomb.imp fun L hL x => ?_
      dsimp only
      have h1 := congrFun (congrArg DFunLike.coe hsplit) (eChar x)
      change Λ (eChar x) = Λ_ac (eChar x) + Λ_s (eChar x) at h1
      rw [h1]
      exact hL x

lemma exists_coset_lincomb_of_tilesR {S T : Set ℝ}
    (hS_bdd : Bornology.IsBounded S) (hS_meas : MeasurableSet S)
    (hS_vol : volume S = 1) (htile : TilesR S T) :
    ∃ L : List (ℤ × ℝ × AddSubgroup ℝ),
      ∀ x : ℝ, Set.indicator T (fun _ => (1 : ℂ)) x =
        (L.map fun p => (p.1 : ℂ) *
          Set.indicator ((fun z => p.2.1 + z) '' (p.2.2 : Set ℝ)) (fun _ => (1 : ℂ)) x).sum := by
  obtain ⟨Z0, M, w, _, hM, hsum, hbd, hlim⟩ :=
    exists_atomic_approx_of_tilesR hS_bdd hS_meas hS_vol htile
  obtain ⟨Λ, _, hΛ⟩ := exists_bohr_dual_of_atomic_approx hM hsum hbd hlim
  obtain ⟨N, hN⟩ := exists_nat_gt ‖Λ‖
  have hint : ∀ x : ℝ, ∃ n : ℤ, Λ (eChar x) = (n : ℂ) := fun x => by
    rw [hΛ x]
    by_cases hx : x ∈ T
    · exact ⟨1, by simp [Set.indicator_of_mem hx]⟩
    · exact ⟨0, by simp [Set.indicator_of_notMem hx]⟩
  obtain ⟨L, hL⟩ := exists_coset_lincomb_of_int_dual_aux N Λ hN hint
  exact ⟨L, fun x => by rw [← hΛ x]; exact hL x⟩

/- ## Section 4: Discrete Coset Ring to Periodic Tiling -/

section DiscreteToH1
open Classical

lemma volume_preimage_sub_right (s : Set ℝ) (c : ℝ) :
    volume ((fun y : ℝ => y - c) ⁻¹' s) = volume s := by
  simp [sub_eq_add_neg, measure_preimage_add_right]

noncomputable def evalCosetList (L : List (ℤ × ℝ × AddSubgroup ℝ)) (x : ℝ) : ℤ :=
  (L.map fun p => p.1 * if x - p.2.1 ∈ p.2.2 then 1 else 0).sum

lemma evalCosetList_nil (x : ℝ) : evalCosetList [] x = 0 := rfl

lemma evalCosetList_cons (p : ℤ × ℝ × AddSubgroup ℝ) (L : List (ℤ × ℝ × AddSubgroup ℝ)) (x : ℝ) :
    evalCosetList (p :: L) x =
      p.1 * (if x - p.2.1 ∈ p.2.2 then 1 else 0) + evalCosetList L x := rfl

lemma evalCosetList_append (L₁ L₂ : List (ℤ × ℝ × AddSubgroup ℝ)) (x : ℝ) :
    evalCosetList (L₁ ++ L₂) x = evalCosetList L₁ x + evalCosetList L₂ x := by
  unfold evalCosetList
  rw [List.map_append, List.sum_append]

lemma evalCosetList_eq_of_complex {T : Set ℝ} {L : List (ℤ × ℝ × AddSubgroup ℝ)}
    (hL : ∀ x : ℝ, Set.indicator T (fun _ => (1 : ℂ)) x =
      (L.map fun p => (p.1 : ℂ) *
        Set.indicator ((fun z => p.2.1 + z) '' (p.2.2 : Set ℝ)) (fun _ => (1 : ℂ)) x).sum)
    (x : ℝ) :
    evalCosetList L x = if x ∈ T then 1 else 0 := by
  apply Int.cast_injective (α := ℂ)
  have hcast : ((evalCosetList L x : ℤ) : ℂ) =
      (L.map fun p => (p.1 : ℂ) *
        Set.indicator ((fun z => p.2.1 + z) '' (p.2.2 : Set ℝ)) (fun _ => (1 : ℂ)) x).sum := by
    unfold evalCosetList
    rw [Int.cast_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, Int.cast_mul]
    by_cases h : x - p.2.1 ∈ p.2.2
    · have hmem : x ∈ (fun z => p.2.1 + z) '' (p.2.2 : Set ℝ) := ⟨x - p.2.1, h, by ring⟩
      rw [if_pos h, Set.indicator_of_mem hmem]
      simp
    · have hnot : x ∉ (fun z => p.2.1 + z) '' (p.2.2 : Set ℝ) := by
        rintro ⟨z, hz, hzx⟩
        dsimp only at hzx
        have hzeq : x - p.2.1 = z := by linarith
        exact h (by rw [hzeq]; exact hz)
      rw [if_neg h, Set.indicator_of_notMem hnot]
      simp
  rw [hcast, ← hL x]
  by_cases hx : x ∈ T <;> simp [hx]

lemma discrete_subgroup_inter_Icc_finite {H : AddSubgroup ℝ}
    (hH : ((H : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1).Finite) (a b : ℝ) :
    ((H : Set ℝ) ∩ Set.Icc a b).Finite := by
  have hunit : ∀ c : ℝ, ((H : Set ℝ) ∩ Set.Icc c (c + 1)).Finite := by
    intro c
    by_cases hne : ((H : Set ℝ) ∩ Set.Icc c (c + 1)).Nonempty
    · obtain ⟨h₀, hh₀H, hh₀_lo, hh₀_hi⟩ := hne
      have hsub : (fun x : ℝ => x - h₀) '' ((H : Set ℝ) ∩ Set.Icc c (c + 1)) ⊆
          (H : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1 := by
        rintro y ⟨x, ⟨hxH, hx_lo, hx_hi⟩, rfl⟩
        exact ⟨H.sub_mem hxH hh₀H, by linarith, by linarith⟩
      exact Set.Finite.of_finite_image (hH.subset hsub)
        (fun x₁ _ x₂ _ h => by linarith)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  have hcov : ((H : Set ℝ) ∩ Set.Icc a b) ⊆
      ⋃ n ∈ Finset.Icc (Int.floor a) (Int.ceil b), ((H : Set ℝ) ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    rintro x ⟨hxH, hxa, hxb⟩
    simp only [Set.mem_iUnion, Finset.mem_Icc]
    refine ⟨Int.floor x, ⟨Int.floor_mono hxa, ?_⟩, hxH, Int.floor_le x, (Int.lt_floor_add_one x).le⟩
    exact Int.floor_le_ceil x |>.trans (Int.ceil_mono hxb)
  exact ((Finset.finite_toSet (Finset.Icc (Int.floor a) (Int.ceil b))).biUnion
    fun (n : ℤ) _ => hunit (n : ℝ)).subset hcov

lemma discrete_subgroup_eq_bot_or_zmultiples {H : AddSubgroup ℝ}
    (hH : ((H : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1).Finite) :
    H = ⊥ ∨ ∃ α : ℝ, 0 < α ∧ H = AddSubgroup.zmultiples α := by
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  · right
    have hex : ∃ x ∈ H, x ≠ 0 := by
      by_contra h
      push Not at h
      apply hbot
      ext x
      simp only [AddSubgroup.mem_bot]
      exact ⟨fun hx => h x hx, fun hx => hx ▸ H.zero_mem⟩
    obtain ⟨x₀, hx₀H, hx₀_ne⟩ := hex
    have hex_pos : ∃ x ∈ H, 0 < x := by
      rcases lt_or_gt_of_ne hx₀_ne with hlt | hgt
      · exact ⟨-x₀, H.neg_mem hx₀H, neg_pos.mpr hlt⟩
      · exact ⟨x₀, hx₀H, hgt⟩
    obtain ⟨x, hxH, hx_pos⟩ := hex_pos
    let S : Set ℝ := (H : Set ℝ) ∩ Set.Ioc 0 x
    have hS_fin : S.Finite :=
      (discrete_subgroup_inter_Icc_finite hH 0 x).subset fun y hy => ⟨hy.1, hy.2.1.le, hy.2.2⟩
    have hS_ne : hS_fin.toFinset.Nonempty :=
      ⟨x, hS_fin.mem_toFinset.mpr ⟨hxH, hx_pos, le_rfl⟩⟩
    let α : ℝ := hS_fin.toFinset.min' hS_ne
    have hα_mem_S : α ∈ S := hS_fin.mem_toFinset.mp (Finset.min'_mem _ hS_ne)
    have hα_H : α ∈ H := hα_mem_S.1
    have hα_pos : 0 < α := hα_mem_S.2.1
    have hα_min : ∀ y ∈ H, 0 < y → α ≤ y := by
      intro y hyH hy_pos
      by_cases hyx : y ≤ x
      · exact Finset.min'_le _ y (hS_fin.mem_toFinset.mpr ⟨hyH, hy_pos, hyx⟩)
      · exact hα_mem_S.2.2.trans (le_of_not_ge hyx)
    refine ⟨α, hα_pos, le_antisymm ?_ (AddSubgroup.zmultiples_le.mpr hα_H)⟩
    intro y hyH
    let m : ℤ := Int.floor (y / α)
    have hm_mem : (m : ℝ) * α ∈ H := by
      simpa [zsmul_eq_mul] using H.zsmul_mem hα_H m
    let r : ℝ := y - (m : ℝ) * α
    have hr_H : r ∈ H := H.sub_mem hyH hm_mem
    have hr_nonneg : 0 ≤ r := by
      have h1 : (m : ℝ) ≤ y / α := Int.floor_le (y / α)
      have h2 : (m : ℝ) * α ≤ y := (le_div_iff₀ hα_pos).mp h1
      linarith
    have hr_lt : r < α := by
      have h1 : y / α < (m : ℝ) + 1 := Int.lt_floor_add_one (y / α)
      have h2 : y < ((m : ℝ) + 1) * α := (div_lt_iff₀ hα_pos).mp h1
      linarith
    have hr_zero : r = 0 := by
      by_contra hr_ne
      have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
      linarith [hα_min r hr_H hr_pos]
    have hy_eq : m • α = y := by
      rw [zsmul_eq_mul]; linarith
    exact ⟨m, hy_eq⟩

noncomputable def diffCosetList (H : AddSubgroup ℝ) (h : ℝ) :
    List (ℤ × ℝ × AddSubgroup ℝ) → List (ℤ × ℝ × AddSubgroup ℝ)
  | [] => []
  | p :: L =>
    if p.2.2 = H then diffCosetList H h L
    else (p.1, p.2.1 - h, p.2.2) :: (-p.1, p.2.1, p.2.2) :: diffCosetList H h L

lemma evalCosetList_diffCosetList (H : AddSubgroup ℝ) {h : ℝ} (hh : h ∈ H)
    (L : List (ℤ × ℝ × AddSubgroup ℝ)) (x : ℝ) :
    evalCosetList (diffCosetList H h L) x =
      evalCosetList L (x + h) - evalCosetList L x := by
  induction L with
  | nil => simp [diffCosetList, evalCosetList]
  | cons p L ih =>
    unfold diffCosetList
    by_cases hp : p.2.2 = H
    · simp only [hp, ite_true, evalCosetList_cons]
      have hiff : x + h - p.2.1 ∈ H ↔ x - p.2.1 ∈ H := by
        have heq : x + h - p.2.1 = (x - p.2.1) + h := by ring
        rw [heq]
        exact H.add_mem_cancel_right hh
      rw [ih, if_congr hiff rfl rfl]
      ring
    · simp only [hp, ite_false, evalCosetList_cons]
      have heq : x - (p.2.1 - h) = x + h - p.2.1 := by ring
      rw [ih, heq]
      ring

lemma mem_diffCosetList_subgroup (H : AddSubgroup ℝ) (h : ℝ)
    (L : List (ℤ × ℝ × AddSubgroup ℝ)) {q : ℤ × ℝ × AddSubgroup ℝ}
    (hq : q ∈ diffCosetList H h L) :
    q.2.2 ≠ H ∧ ∃ p ∈ L, p.2.2 = q.2.2 := by
  induction L with
  | nil => simp [diffCosetList] at hq
  | cons p L ih =>
    unfold diffCosetList at hq
    by_cases hp : p.2.2 = H
    · simp only [hp, ite_true] at hq
      obtain ⟨hne, r, hrL, hrq⟩ := ih hq
      exact ⟨hne, r, List.mem_cons_of_mem _ hrL, hrq⟩
    · simp only [hp, ite_false, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq'
      · exact ⟨hp, p, List.mem_cons_self, rfl⟩
      · exact ⟨hp, p, List.mem_cons_self, rfl⟩
      · obtain ⟨hne, r, hrL, hrq⟩ := ih hq'
        exact ⟨hne, r, List.mem_cons_of_mem _ hrL, hrq⟩

lemma vanish_of_locallyFinite_support_nonDiscrete :
    ∀ (n : ℕ) (L : List (ℤ × ℝ × AddSubgroup ℝ)),
      (L.map (fun p => p.2.2)).toFinset.card ≤ n →
      (∀ p ∈ L, Set.Infinite ((p.2.2 : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1)) →
      (∀ a b : ℝ, ({x : ℝ | evalCosetList L x ≠ 0} ∩ Set.Icc a b).Finite) →
      ∀ x : ℝ, evalCosetList L x = 0 := by
  intro n
  induction n with
  | zero =>
    intro L hcard _ _ x
    cases L with
    | nil => rfl
    | cons p L =>
      exfalso
      have hmem : p.2.2 ∈ ((p :: L).map (fun q => q.2.2)).toFinset := by simp
      have hpos : 0 < ((p :: L).map (fun q => q.2.2)).toFinset.card :=
        Finset.card_pos.mpr ⟨p.2.2, hmem⟩
      omega
  | succ n ih =>
    intro L hcard hnd hlf x
    cases L with
    | nil => rfl
    | cons p₀ L₀ =>
      let L' := p₀ :: L₀
      let H := p₀.2.2
      have hper : ∀ h ∈ H, ∀ y : ℝ, evalCosetList L' (y + h) = evalCosetList L' y := by
        intro h hh y
        let D := diffCosetList H h L'
        have hD_sub : (D.map (fun q => q.2.2)).toFinset ⊂ (L'.map (fun q => q.2.2)).toFinset := by
          rw [Finset.ssubset_iff_subset_ne]
          constructor
          · intro K hK
            simp only [List.mem_toFinset, List.mem_map] at hK ⊢
            obtain ⟨q, hqD, rfl⟩ := hK
            obtain ⟨_, r, hrL, hrq⟩ := mem_diffCosetList_subgroup H h L' hqD
            exact ⟨r, hrL, hrq⟩
          · intro heq
            have hH_in : H ∈ (L'.map (fun q => q.2.2)).toFinset := by simp [L', H]
            rw [← heq] at hH_in
            simp only [List.mem_toFinset, List.mem_map] at hH_in
            obtain ⟨q, hqD, hqH⟩ := hH_in
            exact (mem_diffCosetList_subgroup H h L' hqD).1 hqH
        have hD_card : (D.map (fun q => q.2.2)).toFinset.card ≤ n := by
          have hlt := Finset.card_lt_card hD_sub
          have hcard' : (L'.map (fun q => q.2.2)).toFinset.card ≤ n + 1 := hcard
          omega
        have hD_nd : ∀ q ∈ D, Set.Infinite ((q.2.2 : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1) := by
          intro q hq
          obtain ⟨_, r, hrL, hrq⟩ := mem_diffCosetList_subgroup H h L' hq
          rw [← hrq]
          exact hnd r hrL
        have hD_lf : ∀ a b : ℝ, ({z : ℝ | evalCosetList D z ≠ 0} ∩ Set.Icc a b).Finite := by
          intro a b
          have hsub : {z : ℝ | evalCosetList D z ≠ 0} ∩ Set.Icc a b ⊆
              ({z : ℝ | evalCosetList L' (z + h) ≠ 0} ∩ Set.Icc a b) ∪
              ({z : ℝ | evalCosetList L' z ≠ 0} ∩ Set.Icc a b) := by
            rintro z ⟨hz, hza, hzb⟩
            change evalCosetList (diffCosetList H h L') z ≠ 0 at hz
            rw [evalCosetList_diffCosetList H hh L' z] at hz
            by_cases h1 : evalCosetList L' z = 0
            · left
              refine ⟨?_, hza, hzb⟩
              show evalCosetList L' (z + h) ≠ 0
              intro h2; rw [h1, h2, sub_self] at hz; exact hz rfl
            · exact Or.inr ⟨h1, hza, hzb⟩
          have hshift_fin : ({z : ℝ | evalCosetList L' (z + h) ≠ 0} ∩ Set.Icc a b).Finite := by
            have himg : (fun z => z + h) '' ({z : ℝ | evalCosetList L' (z + h) ≠ 0} ∩ Set.Icc a b) ⊆
                {w : ℝ | evalCosetList L' w ≠ 0} ∩ Set.Icc (a + h) (b + h) := by
              rintro w ⟨z, ⟨hz, hza, hzb⟩, rfl⟩
              exact ⟨hz, by linarith, by linarith⟩
            exact Set.Finite.of_finite_image ((hlf (a + h) (b + h)).subset himg)
              (fun z₁ _ z₂ _ heq => by linarith)
          exact (hshift_fin.union (hlf a b)).subset hsub
        have h0 : evalCosetList (diffCosetList H h L') y = 0 := ih D hD_card hD_nd hD_lf y
        rw [evalCosetList_diffCosetList H hh L' y] at h0
        linarith
      by_contra hne
      have hH_inf : Set.Infinite ((H : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1) := hnd p₀ List.mem_cons_self
      have himg_sub : (fun h => x + h) '' ((H : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1) ⊆
          {y : ℝ | evalCosetList L' y ≠ 0} ∩ Set.Icc (x - 1) (x + 1) := by
        rintro y ⟨h, ⟨hhH, hh1, hh2⟩, rfl⟩
        refine ⟨?_, by linarith, by linarith⟩
        show evalCosetList L' (x + h) ≠ 0
        rw [hper h hhH x]
        exact hne
      have hfin_img : ((fun h => x + h) '' ((H : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1)).Finite :=
        (hlf (x - 1) (x + 1)).subset himg_sub
      have hfin_H : ((H : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1).Finite :=
        Set.Finite.of_finite_image hfin_img (fun h₁ _ h₂ _ heq => by linarith)
      exact hH_inf hfin_H

lemma evalCosetList_filter_split (P : (ℤ × ℝ × AddSubgroup ℝ) → Prop) [DecidablePred P]
    (L : List (ℤ × ℝ × AddSubgroup ℝ)) (x : ℝ) :
    evalCosetList L x =
      evalCosetList (L.filter (fun p => decide (P p))) x +
      evalCosetList (L.filter (fun p => decide (¬ P p))) x := by
  induction L with
  | nil => simp [evalCosetList]
  | cons p L ih =>
    by_cases hp : P p
    · simp [hp, evalCosetList_cons, ih, add_assoc]
    · simp only [List.filter_cons, hp, decide_false, Bool.false_eq_true, ite_false, not_false_eq_true,
        decide_true, ite_true, evalCosetList_cons]
      linarith

def Commens (α β : ℝ) : Prop :=
  ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * α = (q : ℝ) * β

lemma commens_refl (α : ℝ) : Commens α α := ⟨1, 1, Nat.one_pos, Nat.one_pos, rfl⟩

lemma commens_symm {α β : ℝ} (h : Commens α β) : Commens β α := by
  obtain ⟨p, q, hp, hq, heq⟩ := h
  exact ⟨q, p, hq, hp, heq.symm⟩

lemma commens_trans {α β γ : ℝ} (h1 : Commens α β) (h2 : Commens β γ) : Commens α γ := by
  obtain ⟨p₁, q₁, hp₁, hq₁, heq₁⟩ := h1
  obtain ⟨p₂, q₂, hp₂, hq₂, heq₂⟩ := h2
  refine ⟨p₁ * p₂, q₁ * q₂, Nat.mul_pos hp₁ hp₂, Nat.mul_pos hq₁ hq₂, ?_⟩
  push_cast
  calc (p₁ : ℝ) * (p₂ : ℝ) * α = (p₂ : ℝ) * ((p₁ : ℝ) * α) := by ring
    _ = (p₂ : ℝ) * ((q₁ : ℝ) * β) := by rw [heq₁]
    _ = (q₁ : ℝ) * ((p₂ : ℝ) * β) := by ring
    _ = (q₁ : ℝ) * ((q₂ : ℝ) * γ) := by rw [heq₂]
    _ = (q₁ : ℝ) * (q₂ : ℝ) * γ := by ring

structure PerClass where
  M : ℝ
  hM : 0 < M
  f : ℝ → ℤ
  hper : ∀ x : ℝ, f (x + M) = f x
  supp : Finset ℝ
  hsupp : ∀ x : ℝ, f x ≠ 0 → ∃ a ∈ supp, ∃ k : ℤ, x = a + (k : ℝ) * M

lemma PerClass.periodic_int_mul (c : PerClass) (x : ℝ) (k : ℤ) :
    c.f (x + (k : ℝ) * c.M) = c.f x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have heq : x + (((n : ℤ) + 1 : ℤ) : ℝ) * c.M = (x + ((n : ℤ) : ℝ) * c.M) + c.M := by
      push_cast; ring
    rw [heq, c.hper, ih]
  | pred n ih =>
    have heq : x + (((-(n : ℤ) - 1 : ℤ)) : ℝ) * c.M + c.M = x + ((-(n : ℤ) : ℤ) : ℝ) * c.M := by
      push_cast; ring
    rw [← c.hper (x + (((-(n : ℤ) - 1 : ℤ)) : ℝ) * c.M), heq, ih]

noncomputable def mergePerClass (c₁ c₂ : PerClass) (hc : Commens c₁.M c₂.M) : PerClass := by
  classical
  let p := Classical.choose hc
  let q := Classical.choose (Classical.choose_spec hc)
  have hpq := Classical.choose_spec (Classical.choose_spec hc)
  have hp : 0 < p := hpq.1
  have hq : 0 < q := hpq.2.1
  have heq : (p : ℝ) * c₁.M = (q : ℝ) * c₂.M := hpq.2.2
  refine {
    M := (p : ℝ) * c₁.M
    hM := mul_pos (Nat.cast_pos.mpr hp) c₁.hM
    f := fun x => c₁.f x + c₂.f x
    hper := fun x => by
      have h1 : c₁.f (x + (p : ℝ) * c₁.M) = c₁.f x := by
        simpa using c₁.periodic_int_mul x (p : ℤ)
      have h2 : c₂.f (x + (p : ℝ) * c₁.M) = c₂.f x := by
        rw [heq]
        simpa using c₂.periodic_int_mul x (q : ℤ)
      rw [h1, h2]
    supp :=
      (c₁.supp.biUnion fun a => (Finset.range p).image fun (r : ℕ) => a + (r : ℝ) * c₁.M) ∪
      (c₂.supp.biUnion fun b => (Finset.range q).image fun (r : ℕ) => b + (r : ℝ) * c₂.M)
    hsupp := fun x hx => by
      have hne : c₁.f x ≠ 0 ∨ c₂.f x ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (by rw [h.1, h.2, add_zero])
      rcases hne with h1 | h2
      · obtain ⟨a, ha, k, rfl⟩ := c₁.hsupp x h1
        let m : ℤ := k / (p : ℤ)
        let r : ℤ := k % (p : ℤ)
        have hp_pos : (0 : ℤ) < (p : ℤ) := Int.natCast_pos.mpr hp
        have hr0 : 0 ≤ r := Int.emod_nonneg k (ne_of_gt hp_pos)
        have hr_lt : r < (p : ℤ) := Int.emod_lt_of_pos k hp_pos
        have hdiv : (p : ℤ) * m + r = k := Int.mul_ediv_add_emod k (p : ℤ)
        refine ⟨a + (r.toNat : ℝ) * c₁.M, ?_, m, ?_⟩
        · apply Finset.mem_union_left
          rw [Finset.mem_biUnion]
          refine ⟨a, ha, Finset.mem_image.mpr ⟨r.toNat, Finset.mem_range.mpr (by omega), rfl⟩⟩
        · have hr_cast : (r.toNat : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hr0
          have hk_cast : (k : ℝ) = (p : ℝ) * (m : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
          rw [hr_cast, hk_cast]
          ring
      · obtain ⟨b, hb, k, rfl⟩ := c₂.hsupp x h2
        let m : ℤ := k / (q : ℤ)
        let r : ℤ := k % (q : ℤ)
        have hq_pos : (0 : ℤ) < (q : ℤ) := Int.natCast_pos.mpr hq
        have hr0 : 0 ≤ r := Int.emod_nonneg k (ne_of_gt hq_pos)
        have hr_lt : r < (q : ℤ) := Int.emod_lt_of_pos k hq_pos
        have hdiv : (q : ℤ) * m + r = k := Int.mul_ediv_add_emod k (q : ℤ)
        refine ⟨b + (r.toNat : ℝ) * c₂.M, ?_, m, ?_⟩
        · apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          refine ⟨b, hb, Finset.mem_image.mpr ⟨r.toNat, Finset.mem_range.mpr (by omega), rfl⟩⟩
        · have hr_cast : (r.toNat : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hr0
          have hk_cast : (k : ℝ) = (q : ℝ) * (m : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
          rw [hr_cast, hk_cast, heq]
          ring
  }

lemma mergePerClass_commens_left (c₁ c₂ : PerClass) (hc : Commens c₁.M c₂.M) :
    Commens (mergePerClass c₁ c₂ hc).M c₁.M := by
  classical
  let p := Classical.choose hc
  have hp : 0 < p := (Classical.choose_spec (Classical.choose_spec hc)).1
  exact ⟨1, p, Nat.one_pos, hp, by simp [mergePerClass, p]⟩

lemma mergePerClass_f (c₁ c₂ : PerClass) (hc : Commens c₁.M c₂.M) (x : ℝ) :
    (mergePerClass c₁ c₂ hc).f x = c₁.f x + c₂.f x := rfl

lemma insertPerClass_exists (c : PerClass) (cls : List PerClass)
    (hpw : cls.Pairwise (fun a b => ¬ Commens a.M b.M)) :
    ∃ cls' : List PerClass,
      cls'.Pairwise (fun a b => ¬ Commens a.M b.M) ∧
      (∀ d ∈ cls', Commens d.M c.M ∨ ∃ e ∈ cls, Commens d.M e.M) ∧
      (∀ x : ℝ, (cls'.map fun d => d.f x).sum = c.f x + (cls.map fun d => d.f x).sum) := by
  classical
  induction cls with
  | nil =>
    refine ⟨[c], List.pairwise_singleton _ _, ?_, ?_⟩
    · intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      exact Or.inl (commens_refl _)
    · intro x; simp
  | cons c₁ rest ih =>
    obtain ⟨h1_rest, hpw_rest⟩ := List.pairwise_cons.mp hpw
    by_cases hc : Commens c.M c₁.M
    · let m := mergePerClass c c₁ hc
      have hm_c1 : Commens m.M c₁.M := commens_trans (mergePerClass_commens_left c c₁ hc) hc
      refine ⟨m :: rest, List.pairwise_cons.mpr ⟨?_, hpw_rest⟩, ?_, ?_⟩
      · intro d hd hmd
        exact h1_rest d hd (commens_trans (commens_symm hm_c1) hmd)
      · intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inl (mergePerClass_commens_left c c₁ hc)
        · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, commens_refl _⟩
      · intro x
        simp only [List.map_cons, List.sum_cons, m, mergePerClass_f]
        ring
    · obtain ⟨rest', hpw', hcomm', hsum'⟩ := ih hpw_rest
      refine ⟨c₁ :: rest', List.pairwise_cons.mpr ⟨?_, hpw'⟩, ?_, ?_⟩
      · intro d hd hc1d
        rcases hcomm' d hd with hdc | ⟨e, he, hde⟩
        · exact hc (commens_symm (commens_trans hc1d hdc))
        · exact h1_rest e he (commens_trans hc1d hde)
      · intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inr ⟨d, List.mem_cons_self, commens_refl _⟩
        · rcases hcomm' d hd with hdc | ⟨e, he, hde⟩
          · exact Or.inl hdc
          · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hde⟩
      · intro x
        simp only [List.map_cons, List.sum_cons, hsum' x]
        ring

lemma split_discrete_cosetList (L : List (ℤ × ℝ × AddSubgroup ℝ))
    (hL : ∀ p ∈ L, p.2.2 = ⊥ ∨ ∃ α : ℝ, 0 < α ∧ p.2.2 = AddSubgroup.zmultiples α) :
    ∃ (B_fin : ℝ) (f_fin : ℝ → ℤ) (cls : List PerClass),
      0 ≤ B_fin ∧
      (∀ x : ℝ, B_fin < |x| → f_fin x = 0) ∧
      cls.Pairwise (fun a b => ¬ Commens a.M b.M) ∧
      (∀ x : ℝ, evalCosetList L x = f_fin x + (cls.map fun c => c.f x).sum) := by
  classical
  induction L with
  | nil =>
    exact ⟨0, fun _ => 0, [], le_rfl, fun _ _ => rfl, List.Pairwise.nil, fun _ => by simp [evalCosetList]⟩
  | cons p L ih =>
    obtain ⟨B_fin, f_fin, cls, hB, hf_fin, hpw, hsum⟩ :=
      ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    rcases hL p List.mem_cons_self with hbot | ⟨α, hα_pos, hzmul⟩
    · refine ⟨max B_fin |p.2.1|,
        fun x => f_fin x + p.1 * (if x = p.2.1 then 1 else 0),
        cls, le_trans hB (le_max_left _ _), ?_, hpw, ?_⟩
      · intro x hx
        dsimp only
        have hx1 : B_fin < |x| := lt_of_le_of_lt (le_max_left _ _) hx
        have hx2 : |p.2.1| < |x| := lt_of_le_of_lt (le_max_right _ _) hx
        have hne : x ≠ p.2.1 := fun heq => by rw [heq] at hx2; exact lt_irrefl _ hx2
        rw [hf_fin x hx1, if_neg hne, mul_zero, add_zero]
      · intro x
        rw [evalCosetList_cons, hsum x, hbot]
        have hiff : x - p.2.1 ∈ (⊥ : AddSubgroup ℝ) ↔ x = p.2.1 := by
          simp [sub_eq_zero]
        rw [if_congr hiff rfl rfl]
        ring
    · let c_new : PerClass := {
        M := α
        hM := hα_pos
        f := fun x => p.1 * (if x - p.2.1 ∈ p.2.2 then 1 else 0)
        hper := fun x => by
          have hiff : x + α - p.2.1 ∈ p.2.2 ↔ x - p.2.1 ∈ p.2.2 := by
            have hα_mem : α ∈ p.2.2 := by rw [hzmul]; exact ⟨1, one_zsmul α⟩
            have heq : x + α - p.2.1 = (x - p.2.1) + α := by ring
            rw [heq]
            exact p.2.2.add_mem_cancel_right hα_mem
          rw [if_congr hiff rfl rfl]
        supp := {p.2.1}
        hsupp := fun x hx => by
          have hmem : x - p.2.1 ∈ p.2.2 := by
            by_contra hnot
            rw [if_neg hnot, mul_zero] at hx
            exact hx rfl
          rw [hzmul] at hmem
          obtain ⟨k, hk⟩ := hmem
          dsimp only at hk
          rw [zsmul_eq_mul] at hk
          exact ⟨p.2.1, Finset.mem_singleton_self _, k, by linarith⟩
      }
      obtain ⟨cls', hpw', _, hsum'⟩ := insertPerClass_exists c_new cls hpw
      refine ⟨B_fin, f_fin, cls', hB, hf_fin, hpw', fun x => ?_⟩
      rw [evalCosetList_cons, hsum x, hsum' x]
      change p.1 * (if x - p.2.1 ∈ p.2.2 then 1 else 0) +
          (f_fin x + (cls.map fun c => c.f x).sum) =
        f_fin x + (p.1 * (if x - p.2.1 ∈ p.2.2 then 1 else 0) +
          (cls.map fun c => c.f x).sum)
      ring

lemma dirichlet_small_combo {M₀ M₁ δ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hδ : 0 < δ)
    (hnc : ¬ Commens M₀ M₁) :
    ∃ (d p : ℕ), 0 < d ∧ 0 < p ∧
      0 < |(d : ℝ) * M₀ - (p : ℝ) * M₁| ∧ |(d : ℝ) * M₀ - (p : ℝ) * M₁| < δ := by
  let δ' : ℝ := min δ (M₀ / 2)
  have hδ' : 0 < δ' := lt_min hδ (by linarith)
  let Q : ℕ := Nat.floor (M₁ / δ') + 1
  have hQ_pos : 0 < Q := Nat.succ_pos _
  have hQ_gt : M₁ / δ' < (Q : ℝ) := by
    simpa [Q, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (M₁ / δ')
  have hMQ : M₁ / (Q : ℝ) < δ' := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hQ_pos)]
    have := (div_lt_iff₀ hδ').mp hQ_gt
    linarith
  let r : Fin (Q + 1) → ℝ := fun j =>
    ((j.val : ℝ) * M₀ / M₁) - (Int.floor ((j.val : ℝ) * M₀ / M₁) : ℝ)
  have hr_nonneg : ∀ j, 0 ≤ r j := fun j =>
    sub_nonneg.mpr (Int.floor_le _)
  have hr_lt_one : ∀ j, r j < 1 := fun j => by
    have := Int.lt_floor_add_one ((j.val : ℝ) * M₀ / M₁)
    linarith
  let bin : Fin (Q + 1) → Fin Q := fun j =>
    ⟨Nat.floor ((Q : ℝ) * r j), by
      have h1 : (Q : ℝ) * r j < (Q : ℝ) := by
        have := mul_lt_mul_of_pos_left (hr_lt_one j) (Nat.cast_pos.mpr hQ_pos)
        linarith
      exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg Q) (hr_nonneg j))).mpr h1⟩
  have hcard : Fintype.card (Fin Q) < Fintype.card (Fin (Q + 1)) := by simp
  obtain ⟨i₀, j₀, hne_ij, hbin_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt bin hcard
  have hordered : ∃ i j : Fin (Q + 1), i.val < j.val ∧ bin i = bin j := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne_ij) with hlt | hgt
    · exact ⟨i₀, j₀, hlt, hbin_eq⟩
    · exact ⟨j₀, i₀, hgt, hbin_eq.symm⟩
  obtain ⟨i, j, hij, hbin⟩ := hordered
  let d : ℕ := j.val - i.val
  have hd_pos : 0 < d := Nat.sub_pos_of_lt hij
  let q_i : ℤ := Int.floor ((i.val : ℝ) * M₀ / M₁)
  let q_j : ℤ := Int.floor ((j.val : ℝ) * M₀ / M₁)
  have hfloor_eq : Nat.floor ((Q : ℝ) * r i) = Nat.floor ((Q : ℝ) * r j) :=
    congrArg Fin.val hbin
  have hri_lo : (Nat.floor ((Q : ℝ) * r i) : ℝ) ≤ (Q : ℝ) * r i :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (hr_nonneg i))
  have hri_hi : (Q : ℝ) * r i < (Nat.floor ((Q : ℝ) * r i) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hrj_lo : (Nat.floor ((Q : ℝ) * r i) : ℝ) ≤ (Q : ℝ) * r j :=
    hfloor_eq ▸ Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (hr_nonneg j))
  have hrj_hi : (Q : ℝ) * r j < (Nat.floor ((Q : ℝ) * r i) : ℝ) + 1 :=
    hfloor_eq ▸ Nat.lt_floor_add_one _
  have hdiff_Q : |(Q : ℝ) * (r j - r i)| < 1 := by
    rw [mul_sub, abs_lt]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos (Nat.cast_pos.mpr hQ_pos)] at hdiff_Q
  have hdiff_r : |r j - r i| < 1 / (Q : ℝ) := by
    rw [lt_div_iff₀ (Nat.cast_pos.mpr hQ_pos)]
    linarith
  have hd_cast : (d : ℝ) = (j.val : ℝ) - (i.val : ℝ) := by
    exact_mod_cast Nat.cast_sub hij.le
  have hcomb_eq : (d : ℝ) * M₀ - ((q_j - q_i : ℤ) : ℝ) * M₁ = M₁ * (r j - r i) := by
    have h1 : r j - r i = ((d : ℝ) * M₀ / M₁) - ((q_j - q_i : ℤ) : ℝ) := by
      simp only [r, q_j, q_i, Int.cast_sub, hd_cast]
      ring
    rw [h1]
    field_simp [ne_of_gt hM₁]
  have hcomb_lt' : |(d : ℝ) * M₀ - ((q_j - q_i : ℤ) : ℝ) * M₁| < δ' := by
    rw [hcomb_eq, abs_mul, abs_of_pos hM₁]
    calc M₁ * |r j - r i| < M₁ * (1 / (Q : ℝ)) := mul_lt_mul_of_pos_left hdiff_r hM₁
      _ = M₁ / (Q : ℝ) := by ring
      _ < δ' := hMQ
  have hq_pos_R : (0 : ℝ) < ((q_j - q_i : ℤ) : ℝ) * M₁ := by
    have h1 : (d : ℝ) * M₀ - ((q_j - q_i : ℤ) : ℝ) * M₁ < δ' := (abs_lt.mp hcomb_lt').2
    have h2 : δ' ≤ M₀ / 2 := min_le_right _ _
    have h3 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
    have h4 : M₀ ≤ (d : ℝ) * M₀ := by nlinarith
    linarith
  have hq_pos_Z : (0 : ℤ) < q_j - q_i := by
    have h1 : (0 : ℝ) < ((q_j - q_i : ℤ) : ℝ) := pos_of_mul_pos_left hq_pos_R hM₁.le
    exact_mod_cast h1
  let p : ℕ := (q_j - q_i).toNat
  have hp_pos : 0 < p := by omega
  have hp_cast : (p : ℝ) = ((q_j - q_i : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hq_pos_Z.le
  have hcomb_ne : (d : ℝ) * M₀ - (p : ℝ) * M₁ ≠ 0 := by
    intro h0
    exact hnc ⟨d, p, hd_pos, hp_pos, by linarith⟩
  refine ⟨d, p, hd_pos, hp_pos, abs_pos.mpr hcomb_ne, ?_⟩
  rw [hp_cast]
  exact lt_of_lt_of_le hcomb_lt' (min_le_left _ _)

lemma incommens_hits_finite {c₀ c₁ : PerClass} (hnc : ¬ Commens c₀.M c₁.M) (x₀ : ℝ) :
    {m : ℤ | c₁.f (x₀ + (m : ℝ) * c₀.M) ≠ 0}.Finite := by
  have hsub : {m : ℤ | c₁.f (x₀ + (m : ℝ) * c₀.M) ≠ 0} ⊆
      ⋃ a ∈ c₁.supp, {m : ℤ | ∃ k : ℤ, x₀ + (m : ℝ) * c₀.M = a + (k : ℝ) * c₁.M} := by
    intro m hm
    obtain ⟨a, ha, k, hk⟩ := c₁.hsupp _ hm
    exact Set.mem_biUnion ha ⟨k, hk⟩
  refine ((Finset.finite_toSet c₁.supp).biUnion fun a _ => ?_).subset hsub
  refine Set.Subsingleton.finite ?_
  rintro m₁ ⟨k₁, hk₁⟩ m₂ ⟨k₂, hk₂⟩
  by_contra hne
  have hdiff : ((m₁ - m₂ : ℤ) : ℝ) * c₀.M = ((k₁ - k₂ : ℤ) : ℝ) * c₁.M := by
    push_cast; linarith
  have habs : ((m₁ - m₂).natAbs : ℝ) * c₀.M = ((k₁ - k₂).natAbs : ℝ) * c₁.M := by
    have h1 := congrArg abs hdiff
    simp only [abs_mul, abs_of_pos c₀.hM, abs_of_pos c₁.hM, ← Int.cast_abs, Int.abs_eq_natAbs,
      Int.cast_natCast] at h1
    exact h1
  have hm_pos : 0 < (m₁ - m₂).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hk_pos : 0 < (k₁ - k₂).natAbs := by
    by_contra hk0
    have hk_eq : (k₁ - k₂).natAbs = 0 := by omega
    rw [hk_eq, Nat.cast_zero, zero_mul] at habs
    have hpos : (0 : ℝ) < ((m₁ - m₂).natAbs : ℝ) * c₀.M :=
      mul_pos (Nat.cast_pos.mpr hm_pos) c₀.hM
    linarith
  exact hnc ⟨(m₁ - m₂).natAbs, (k₁ - k₂).natAbs, hm_pos, hk_pos, habs⟩

lemma exists_int_gt_of_finite {F : Set ℤ} (hF : F.Finite) :
    ∃ N : ℤ, ∀ m : ℤ, N ≤ m → m ∉ F := by
  by_cases hne : hF.toFinset.Nonempty
  · refine ⟨hF.toFinset.max' hne + 1, fun m hm hmem => ?_⟩
    have hle := Finset.le_max' hF.toFinset m (hF.mem_toFinset.mpr hmem)
    omega
  · refine ⟨0, fun m _ hmem => ?_⟩
    exact hne ⟨m, hF.mem_toFinset.mpr hmem⟩

lemma linear_abs_le_finite (x₀ M B : ℝ) (hM : 0 < M) :
    {m : ℤ | |x₀ + (m : ℝ) * M| ≤ B}.Finite := by
  let lo : ℤ := Int.floor ((-B - x₀) / M)
  let hi : ℤ := Int.ceil ((B - x₀) / M)
  refine (Finset.finite_toSet (Finset.Icc lo hi)).subset fun m hm => ?_
  rw [Finset.mem_coe, Finset.mem_Icc]
  have habs := abs_le.mp (show |x₀ + (m : ℝ) * M| ≤ B from hm)
  have h1 : (-B - x₀) / M ≤ (m : ℝ) := (div_le_iff₀ hM).mpr (by linarith)
  have h2 : (m : ℝ) ≤ (B - x₀) / M := (le_div_iff₀ hM).mpr (by linarith)
  exact ⟨Int.floor_le_iff.mpr (by linarith),
    Int.le_ceil_iff.mpr (by linarith)⟩

lemma exists_periodic_tiling_of_tilesR {S T : Set ℝ}
    (hS_bdd : Bornology.IsBounded S) (hS_meas : MeasurableSet S)
    (hS_vol : volume S = 1) (htile : TilesR S T) :
    ∃ (M : ℝ) (A0 : Finset ℝ),
      0 < M ∧
      (∀ a ∈ A0, 0 ≤ a ∧ a < M) ∧
      TilesR S (⋃ a ∈ A0, ⋃ m : ℤ, {a + (m : ℝ) * M}) := by
  classical
  obtain ⟨L, hL_C⟩ := exists_coset_lincomb_of_tilesR hS_bdd hS_meas hS_vol htile
  have hL : ∀ x : ℝ, evalCosetList L x = if x ∈ T then 1 else 0 :=
    evalCosetList_eq_of_complex hL_C
  obtain ⟨δ, hδ_pos, hsep⟩ := tilesR_uniform_sep hS_meas hS_vol htile
  let isDisc : (ℤ × ℝ × AddSubgroup ℝ) → Prop :=
    fun p => ((p.2.2 : Set ℝ) ∩ Set.Icc (-1 : ℝ) 1).Finite
  let L_disc := L.filter (fun p => decide (isDisc p))
  let L_nd := L.filter (fun p => decide (¬ isDisc p))
  have hL_disc_lf : ∀ a b : ℝ, ({x : ℝ | evalCosetList L_disc x ≠ 0} ∩ Set.Icc a b).Finite := by
    intro a b
    have hsub : {x : ℝ | evalCosetList L_disc x ≠ 0} ∩ Set.Icc a b ⊆
        ⋃ p ∈ L_disc.toFinset, ((fun z => p.2.1 + z) '' ((p.2.2 : Set ℝ) ∩ Set.Icc (a - p.2.1) (b - p.2.1))) := by
      rintro x ⟨hx, hxa, hxb⟩
      have hex : ∃ p ∈ L_disc, x - p.2.1 ∈ p.2.2 := by
        by_contra hnone
        push Not at hnone
        apply hx
        unfold evalCosetList
        apply List.sum_eq_zero
        intro v hv
        rw [List.mem_map] at hv
        obtain ⟨p, hp, rfl⟩ := hv
        rw [if_neg (hnone p hp), mul_zero]
      obtain ⟨p, hp, hmem⟩ := hex
      exact Set.mem_biUnion (List.mem_toFinset.mpr hp)
        ⟨x - p.2.1, ⟨hmem, by linarith, by linarith⟩, by ring⟩
    refine ((Finset.finite_toSet L_disc.toFinset).biUnion fun p hp => ?_).subset hsub
    have hp_disc : isDisc p := by
      have hp' := List.mem_toFinset.mp hp
      simp only [L_disc, List.mem_filter, decide_eq_true_eq] at hp'
      exact hp'.2
    exact (discrete_subgroup_inter_Icc_finite hp_disc (a - p.2.1) (b - p.2.1)).image _
  have hL_nd_zero : ∀ x : ℝ, evalCosetList L_nd x = 0 := by
    refine vanish_of_locallyFinite_support_nonDiscrete
      (L_nd.map (fun p => p.2.2)).toFinset.card L_nd le_rfl ?_ ?_
    · intro p hp
      simp only [L_nd, List.mem_filter, decide_eq_true_eq] at hp
      exact hp.2
    · intro a b
      have hsub : {x : ℝ | evalCosetList L_nd x ≠ 0} ∩ Set.Icc a b ⊆
          (T ∩ Set.Icc a b) ∪ ({x : ℝ | evalCosetList L_disc x ≠ 0} ∩ Set.Icc a b) := by
        rintro x ⟨hx, hxa, hxb⟩
        have hsplit := evalCosetList_filter_split isDisc L x
        rw [hL x] at hsplit
        by_cases hxT : x ∈ T
        · exact Or.inl ⟨hxT, hxa, hxb⟩
        · right
          refine ⟨?_, hxa, hxb⟩
          intro h0
          rw [if_neg hxT, h0, zero_add] at hsplit
          exact hx hsplit.symm
      exact ((separated_inter_Icc_finite_and_card_le hδ_pos hsep a b).1.union
        (hL_disc_lf a b)).subset hsub
  have hL_disc_eq : ∀ x : ℝ, evalCosetList L_disc x = if x ∈ T then 1 else 0 := by
    intro x
    have hsplit := evalCosetList_filter_split isDisc L x
    rw [hL x, hL_nd_zero x, add_zero] at hsplit
    exact hsplit.symm
  have hL_disc_class : ∀ p ∈ L_disc,
      p.2.2 = ⊥ ∨ ∃ α : ℝ, 0 < α ∧ p.2.2 = AddSubgroup.zmultiples α := by
    intro p hp
    simp only [L_disc, List.mem_filter, decide_eq_true_eq] at hp
    exact discrete_subgroup_eq_bot_or_zmultiples hp.2
  obtain ⟨B_fin, f_fin, cls, hB_fin, hf_fin, hpw, hcls_sum⟩ :=
    split_discrete_cosetList L_disc hL_disc_class
  let cls' := cls.filter (fun c => decide (∃ x : ℝ, c.f x ≠ 0))
  have hpw' : cls'.Pairwise (fun a b => ¬ Commens a.M b.M) := hpw.filter _
  have hcls'_nz : ∀ c ∈ cls', ∃ x : ℝ, c.f x ≠ 0 := by
    intro c hc
    simp only [cls', List.mem_filter, decide_eq_true_eq] at hc
    exact hc.2
  have hcls'_sum : ∀ x : ℝ, (cls'.map fun c => c.f x).sum = (cls.map fun c => c.f x).sum := by
    intro x
    have haux : ∀ (l : List PerClass),
        ((l.filter (fun c => decide (∃ y : ℝ, c.f y ≠ 0))).map fun c => c.f x).sum =
        (l.map fun c => c.f x).sum := by
      intro l
      induction l with
      | nil => rfl
      | cons c l ih =>
        by_cases hc : ∃ y : ℝ, c.f y ≠ 0
        · simp [hc, ih]
        · push Not at hc
          simp [hc, ih]
    exact haux cls
  have hT_eq : ∀ x : ℝ, (if x ∈ T then (1 : ℤ) else 0) =
      f_fin x + (cls'.map fun c => c.f x).sum := by
    intro x
    rw [hcls'_sum x, ← hcls_sum x, hL_disc_eq x]
  obtain ⟨R₀, hR₀⟩ := hS_bdd.subset_closedBall (0 : ℝ)
  let R : ℝ := max R₀ 0
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  have hS_bd : ∀ s ∈ S, |s| ≤ R := fun s hs => by
    have h1 := hR₀ hs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    exact le_trans h1 (le_max_left _ _)
  cases hcls' : cls' with
  | nil =>
    exfalso
    have hT_bdd : ∀ t ∈ T, |t| ≤ B_fin := by
      intro t ht
      by_contra hgt
      push Not at hgt
      have h1 := hT_eq t
      rw [if_pos ht, hcls', List.map_nil, List.sum_nil, add_zero, hf_fin t hgt] at h1
      omega
    have hsub : Set.Icc (R + B_fin + 1) (R + B_fin + 2) ⊆
        Set.univ \ ⋃ t ∈ T, {x : ℝ | x - t ∈ S} := by
      intro x hx
      refine ⟨Set.mem_univ x, ?_⟩
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
      intro t ht hxt
      have h1 := hS_bd (x - t) hxt
      have h2 := hT_bdd t ht
      have h3 : |x| ≤ R + B_fin := by
        have := abs_add_le (x - t) t
        have heq : (x - t) + t = x := by ring
        rw [heq] at this
        linarith
      have h4 : R + B_fin + 1 ≤ x := hx.1
      linarith [le_abs_self x]
    have hvol0 : volume (Set.Icc (R + B_fin + 1) (R + B_fin + 2)) = 0 :=
      measure_mono_null hsub htile.2.1
    rw [Real.volume_Icc] at hvol0
    have h1 : (R + B_fin + 2) - (R + B_fin + 1) = 1 := by ring
    rw [h1, ENNReal.ofReal_one] at hvol0
    exact one_ne_zero hvol0
  | cons c₀ tail =>
    cases tail with
    | nil =>
      -- Single periodic class c₀!
      let M : ℝ := c₀.M
      have hM : 0 < M := c₀.hM
      let T₀ : Set ℝ := {x : ℝ | c₀.f x ≠ 0}
      have hT₀_per : ∀ x : ℝ, ∀ k : ℤ, x + (k : ℝ) * M ∈ T₀ ↔ x ∈ T₀ := fun x k => by
        simp only [T₀, Set.mem_ofPred_eq]
        rw [show M = c₀.M from rfl, c₀.periodic_int_mul x k]
      have hT_agree : ∀ x : ℝ, B_fin < |x| → (x ∈ T ↔ x ∈ T₀) := by
        intro x hx
        have h1 := hT_eq x
        rw [hcls', hf_fin x hx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero, zero_add] at h1
        constructor
        · intro hxT
          rw [if_pos hxT] at h1
          show c₀.f x ≠ 0
          omega
        · intro hxT₀
          by_contra hxT
          rw [if_neg hxT] at h1
          exact hxT₀ h1.symm
      have hIco_fin : (T₀ ∩ Set.Ico 0 M).Finite := by
        have hsub : T₀ ∩ Set.Ico 0 M ⊆
            ⋃ a ∈ c₀.supp, {x : ℝ | x ∈ Set.Ico 0 M ∧ ∃ k : ℤ, x = a + (k : ℝ) * M} := by
          rintro x ⟨hxT₀, hxIco⟩
          obtain ⟨a, ha, k, hk⟩ := c₀.hsupp x hxT₀
          exact Set.mem_biUnion ha ⟨hxIco, k, hk⟩
        refine ((Finset.finite_toSet c₀.supp).biUnion fun a _ => ?_).subset hsub
        refine Set.Subsingleton.finite ?_
        rintro x₁ ⟨⟨hx₁0, hx₁M⟩, k₁, rfl⟩ x₂ ⟨⟨hx₂0, hx₂M⟩, k₂, rfl⟩
        have hdiff : |((k₁ - k₂ : ℤ) : ℝ) * M| < M := by
          rw [abs_lt]
          push_cast
          constructor <;> linarith
        rw [abs_mul, abs_of_pos hM] at hdiff
        have hlt1 : |((k₁ - k₂ : ℤ) : ℝ)| < 1 := by nlinarith
        have hlt1_Z : |k₁ - k₂| < 1 := by exact_mod_cast hlt1
        have hk_eq : k₁ = k₂ := by have := abs_lt.mp hlt1_Z; omega
        rw [hk_eq]
      let A0 : Finset ℝ := hIco_fin.toFinset
      have hA0_Ico : ∀ a ∈ A0, 0 ≤ a ∧ a < M := fun a ha =>
        (hIco_fin.mem_toFinset.mp ha).2
      have hT₀_eq : T₀ = ⋃ a ∈ A0, ⋃ m : ℤ, {a + (m : ℝ) * M} := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_singleton_iff]
        constructor
        · intro hxT₀
          let m : ℤ := Int.floor (x / M)
          let a : ℝ := x - (m : ℝ) * M
          have ha0 : 0 ≤ a := by
            have := (le_div_iff₀ hM).mp (Int.floor_le (x / M))
            linarith
          have haM : a < M := by
            have := (div_lt_iff₀ hM).mp (Int.lt_floor_add_one (x / M))
            linarith
          have haT₀ : a ∈ T₀ := by
            have heq : a = x + ((-m : ℤ) : ℝ) * M := by push_cast; ring
            rw [heq]
            exact (hT₀_per x (-m)).mpr hxT₀
          exact ⟨a, hIco_fin.mem_toFinset.mpr ⟨haT₀, ha0, haM⟩, m, by ring⟩
        · rintro ⟨a, ha, m, rfl⟩
          exact (hT₀_per a m).mpr (hIco_fin.mem_toFinset.mp ha).1
      refine ⟨M, A0, hM, hA0_Ico, ?_⟩
      rw [← hT₀_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [hT₀_eq]
        exact (Finset.countable_toSet A0).biUnion fun a _ =>
          Set.countable_iUnion fun m => Set.countable_singleton _
      · have huniv : Set.univ \ ⋃ t ∈ T₀, {x : ℝ | x - t ∈ S} =
            ⋃ n : ℤ, (Set.Icc (n : ℝ) ((n : ℝ) + 1) \ ⋃ t ∈ T₀, {x : ℝ | x - t ∈ S}) := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_iUnion, Set.mem_Icc]
          constructor
          · intro hx
            exact ⟨Int.floor x, ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩, hx⟩
          · rintro ⟨_, _, hx⟩
            exact hx
        rw [huniv]
        refine measure_iUnion_null fun n => ?_
        let k : ℤ := Int.floor ((B_fin + R - (n : ℝ)) / M) + 1
        have hk_gt : B_fin + R < (n : ℝ) + (k : ℝ) * M := by
          have h1 : (B_fin + R - (n : ℝ)) / M < (k : ℝ) := by
            simp [k, Int.lt_floor_add_one]
          have h2 := (div_lt_iff₀ hM).mp h1
          linarith
        have hpre_sub : (fun y : ℝ => y - (k : ℝ) * M) ⁻¹'
              (Set.Icc (n : ℝ) ((n : ℝ) + 1) \ ⋃ t ∈ T₀, {x : ℝ | x - t ∈ S}) ⊆
            Set.univ \ ⋃ t ∈ T, {y : ℝ | y - t ∈ S} := by
          intro y hy
          simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_Icc, Set.mem_iUnion,
            Set.mem_ofPred_eq, not_exists] at hy
          refine ⟨Set.mem_univ y, ?_⟩
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
          intro t ht hyt
          have hy_gt : B_fin + R < y := by linarith [hy.1.1]
          have hyt_bd : |y - t| ≤ R := hS_bd (y - t) hyt
          have ht_gt : B_fin < t := by linarith [(abs_le.mp hyt_bd).2]
          have ht_abs : B_fin < |t| := lt_of_lt_of_le ht_gt (le_abs_self t)
          have htT₀ : t ∈ T₀ := (hT_agree t ht_abs).mp ht
          have ht'_T₀ : t - (k : ℝ) * M ∈ T₀ := by
            have heq : t - (k : ℝ) * M = t + ((-k : ℤ) : ℝ) * M := by push_cast; ring
            rw [heq]
            exact (hT₀_per t (-k)).mpr htT₀
          have hsub_eq : (y - (k : ℝ) * M) - (t - (k : ℝ) * M) = y - t := by ring
          exact hy.2 (t - (k : ℝ) * M) ht'_T₀ (by rwa [hsub_eq])
        have hvol_shift : volume ((fun y : ℝ => y - (k : ℝ) * M) ⁻¹'
              (Set.Icc (n : ℝ) ((n : ℝ) + 1) \ ⋃ t ∈ T₀, {x : ℝ | x - t ∈ S})) =
            volume (Set.Icc (n : ℝ) ((n : ℝ) + 1) \ ⋃ t ∈ T₀, {x : ℝ | x - t ∈ S}) :=
          volume_preimage_sub_right _ ((k : ℝ) * M)
        rw [← hvol_shift]
        exact measure_mono_null hpre_sub htile.2.1
      · intro t₁ ht₁ t₂ ht₂ hne
        let k : ℤ := Int.floor ((B_fin + max |t₁| |t₂|) / M) + 1
        have hk_gt : B_fin + max |t₁| |t₂| < (k : ℝ) * M := by
          have h1 : (B_fin + max |t₁| |t₂|) / M < (k : ℝ) := by
            simp [k, Int.lt_floor_add_one]
          exact (div_lt_iff₀ hM).mp h1
        have ht1_abs : B_fin < |t₁ + (k : ℝ) * M| := by
          have h1 : -t₁ ≤ |t₁| := neg_le_abs t₁
          have h2 : |t₁| ≤ max |t₁| |t₂| := le_max_left _ _
          have h3 : B_fin < t₁ + (k : ℝ) * M := by linarith
          exact lt_of_lt_of_le h3 (le_abs_self _)
        have ht2_abs : B_fin < |t₂ + (k : ℝ) * M| := by
          have h1 : -t₂ ≤ |t₂| := neg_le_abs t₂
          have h2 : |t₂| ≤ max |t₁| |t₂| := le_max_right _ _
          have h3 : B_fin < t₂ + (k : ℝ) * M := by linarith
          exact lt_of_lt_of_le h3 (le_abs_self _)
        have ht1' : t₁ + (k : ℝ) * M ∈ T := (hT_agree _ ht1_abs).mpr ((hT₀_per t₁ k).mpr ht₁)
        have ht2' : t₂ + (k : ℝ) * M ∈ T := (hT_agree _ ht2_abs).mpr ((hT₀_per t₂ k).mpr ht₂)
        have hne' : t₁ + (k : ℝ) * M ≠ t₂ + (k : ℝ) * M := fun h => hne (by linarith)
        have hpre : (fun x : ℝ => x - (k : ℝ) * M) ⁻¹'
              ({x : ℝ | x - t₁ ∈ S} ∩ {x : ℝ | x - t₂ ∈ S}) =
            {x : ℝ | x - (t₁ + (k : ℝ) * M) ∈ S} ∩ {x : ℝ | x - (t₂ + (k : ℝ) * M) ∈ S} := by
          ext x
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
          have h1 : x - (k : ℝ) * M - t₁ = x - (t₁ + (k : ℝ) * M) := by ring
          have h2 : x - (k : ℝ) * M - t₂ = x - (t₂ + (k : ℝ) * M) := by ring
          rw [h1, h2]
        rw [← volume_preimage_sub_right _ ((k : ℝ) * M), hpre]
        exact htile.2.2 _ ht1' _ ht2' hne'
    | cons c₁ rest =>
      -- At least 2 pairwise-incommensurate nonzero periodic classes => contradiction with separation!
      exfalso
      rw [hcls'] at hpw'
      obtain ⟨h0_tail, hpw1⟩ := List.pairwise_cons.mp hpw'
      obtain ⟨h1_rest, _⟩ := List.pairwise_cons.mp hpw1
      have hnc01 : ¬ Commens c₀.M c₁.M := h0_tail c₁ List.mem_cons_self
      obtain ⟨x₀, hx₀⟩ := hcls'_nz c₀ (by rw [hcls']; exact List.mem_cons_self)
      obtain ⟨x₁, hx₁⟩ := hcls'_nz c₁ (by rw [hcls']; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hF0_fin : ({m : ℤ | |x₀ + (m : ℝ) * c₀.M| ≤ B_fin} ∪
          ⋃ c ∈ (c₁ :: rest).toFinset, {m : ℤ | c.f (x₀ + (m : ℝ) * c₀.M) ≠ 0}).Finite := by
        refine (linear_abs_le_finite x₀ c₀.M B_fin c₀.hM).union ?_
        exact (Finset.finite_toSet _).biUnion fun c hc =>
          incommens_hits_finite (h0_tail c (List.mem_toFinset.mp hc)) x₀
      obtain ⟨N₀, hN₀⟩ := exists_int_gt_of_finite hF0_fin
      have hseq0 : ∀ m : ℤ, N₀ ≤ m → x₀ + (m : ℝ) * c₀.M ∈ T := by
        intro m hm
        have hnot := hN₀ m hm
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, List.mem_toFinset,
          not_or, not_exists] at hnot
        have hgt : B_fin < |x₀ + (m : ℝ) * c₀.M| := lt_of_not_ge hnot.1
        have hrest0 : ((c₁ :: rest).map fun c => c.f (x₀ + (m : ℝ) * c₀.M)).sum = 0 := by
          apply List.sum_eq_zero
          intro v hv
          rw [List.mem_map] at hv
          obtain ⟨c, hc, rfl⟩ := hv
          by_contra hne
          exact hnot.2 c hc hne
        have h1 := hT_eq (x₀ + (m : ℝ) * c₀.M)
        rw [hcls', hf_fin _ hgt, List.map_cons, List.sum_cons, hrest0, add_zero, zero_add,
          c₀.periodic_int_mul x₀ m] at h1
        by_contra hnotT
        rw [if_neg hnotT] at h1
        exact hx₀ h1.symm
      have hF1_fin : ({n : ℤ | |x₁ + (n : ℝ) * c₁.M| ≤ B_fin} ∪
          ⋃ c ∈ (c₀ :: rest).toFinset, {n : ℤ | c.f (x₁ + (n : ℝ) * c₁.M) ≠ 0}).Finite := by
        refine (linear_abs_le_finite x₁ c₁.M B_fin c₁.hM).union ?_
        refine (Finset.finite_toSet _).biUnion fun c hc => ?_
        have hc' := List.mem_toFinset.mp hc
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc_rest
        · exact incommens_hits_finite (fun h => hnc01 (commens_symm h)) x₁
        · exact incommens_hits_finite (h1_rest c hc_rest) x₁
      obtain ⟨N₁, hN₁⟩ := exists_int_gt_of_finite hF1_fin
      have hseq1 : ∀ n : ℤ, N₁ ≤ n → x₁ + (n : ℝ) * c₁.M ∈ T := by
        intro n hn
        have hnot := hN₁ n hn
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, List.mem_toFinset,
          not_or, not_exists] at hnot
        have hgt : B_fin < |x₁ + (n : ℝ) * c₁.M| := lt_of_not_ge hnot.1
        have hc0_zero : c₀.f (x₁ + (n : ℝ) * c₁.M) = 0 := by
          by_contra hne; exact hnot.2 c₀ List.mem_cons_self hne
        have hrest0 : (rest.map fun c => c.f (x₁ + (n : ℝ) * c₁.M)).sum = 0 := by
          apply List.sum_eq_zero
          intro v hv
          rw [List.mem_map] at hv
          obtain ⟨c, hc, rfl⟩ := hv
          by_contra hne
          exact hnot.2 c (List.mem_cons_of_mem _ hc) hne
        have h1 := hT_eq (x₁ + (n : ℝ) * c₁.M)
        rw [hcls', hf_fin _ hgt, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
          hc0_zero, hrest0, add_zero, zero_add, zero_add, c₁.periodic_int_mul x₁ n] at h1
        by_contra hnotT
        rw [if_neg hnotT] at h1
        exact hx₁ h1.symm
      obtain ⟨d, p, _, _, hε_pos, hε_lt⟩ :=
        dirichlet_small_combo c₀.hM c₁.hM (show 0 < δ / 2 by linarith) hnc01
      let ε : ℝ := (d : ℝ) * c₀.M - (p : ℝ) * c₁.M
      let y : ℝ := (x₀ + (N₀ : ℝ) * c₀.M) - (x₁ + (N₁ : ℝ) * c₁.M)
      have hclose : ∃ k l : ℕ,
          0 < |y + (k : ℝ) * c₀.M - (l : ℝ) * c₁.M| ∧
          |y + (k : ℝ) * c₀.M - (l : ℝ) * c₁.M| < δ := by
        have hε_ne : ε ≠ 0 := abs_pos.mp hε_pos
        rcases lt_or_gt_of_ne hε_ne with hε_neg | hε_gt
        · let s : ℝ := -ε
          have hs_pos : 0 < s := by linarith
          have hs_lt : s < δ / 2 := by
            have := hε_lt; change |ε| < δ / 2 at this; rw [abs_of_neg hε_neg] at this; exact this
          let k₀ : ℕ := Nat.floor (max 0 (-y / c₀.M)) + 1
          have hz_pos : 0 < y + (k₀ : ℝ) * c₀.M := by
            have h1 : max 0 (-y / c₀.M) < (k₀ : ℝ) := by
              simpa [k₀, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (max 0 (-y / c₀.M))
            have h2 : -y / c₀.M < (k₀ : ℝ) := lt_of_le_of_lt (le_max_right _ _) h1
            have h3 := (div_lt_iff₀ c₀.hM).mp h2
            linarith
          let z : ℝ := y + (k₀ : ℝ) * c₀.M
          let t : ℕ := Nat.floor (z / s) + 1
          have ht_gt : z / s < (t : ℝ) := by
            simpa [t, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (z / s)
          have ht_le : ((t : ℝ) - 1) * s ≤ z := by
            have h1 : (Nat.floor (z / s) : ℝ) ≤ z / s := Nat.floor_le (div_nonneg hz_pos.le hs_pos.le)
            have h2 : (t : ℝ) - 1 = (Nat.floor (z / s) : ℝ) := by simp [t]
            rw [h2]
            exact (le_div_iff₀ hs_pos).mp h1
          have hzt_neg : z - (t : ℝ) * s < 0 := by
            have := (div_lt_iff₀ hs_pos).mp ht_gt; linarith
          have hzt_lo : -s ≤ z - (t : ℝ) * s := by linarith
          have hcomb : y + ((k₀ + t * d : ℕ) : ℝ) * c₀.M - ((t * p : ℕ) : ℝ) * c₁.M =
              z - (t : ℝ) * s := by
            push_cast; simp only [z, s, ε]; ring
          refine ⟨k₀ + t * d, t * p, ?_, ?_⟩
          · rw [hcomb, abs_of_neg hzt_neg]; linarith
          · rw [hcomb, abs_of_neg hzt_neg]; linarith
        · have hε_lt' : ε < δ / 2 := by
            have := hε_lt; change |ε| < δ / 2 at this; rw [abs_of_pos hε_gt] at this; exact this
          let l₀ : ℕ := Nat.floor (max 0 (y / c₁.M)) + 1
          have hz_neg : y - (l₀ : ℝ) * c₁.M < 0 := by
            have h1 : max 0 (y / c₁.M) < (l₀ : ℝ) := by
              simpa [l₀, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (max 0 (y / c₁.M))
            have h2 : y / c₁.M < (l₀ : ℝ) := lt_of_le_of_lt (le_max_right _ _) h1
            have h3 := (div_lt_iff₀ c₁.hM).mp h2
            linarith
          let z : ℝ := y - (l₀ : ℝ) * c₁.M
          let t : ℕ := Nat.floor ((-z) / ε) + 1
          have ht_gt : (-z) / ε < (t : ℝ) := by
            simpa [t, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((-z) / ε)
          have ht_le : ((t : ℝ) - 1) * ε ≤ -z := by
            have h1 : (Nat.floor ((-z) / ε) : ℝ) ≤ (-z) / ε :=
              Nat.floor_le (div_nonneg (by linarith) hε_gt.le)
            have h2 : (t : ℝ) - 1 = (Nat.floor ((-z) / ε) : ℝ) := by simp [t]
            rw [h2]
            exact (le_div_iff₀ hε_gt).mp h1
          have hzt_pos : 0 < z + (t : ℝ) * ε := by
            have := (div_lt_iff₀ hε_gt).mp ht_gt; linarith
          have hzt_hi : z + (t : ℝ) * ε ≤ ε := by linarith
          have hcomb : y + ((t * d : ℕ) : ℝ) * c₀.M - ((l₀ + t * p : ℕ) : ℝ) * c₁.M =
              z + (t : ℝ) * ε := by
            push_cast; simp only [z, ε]; ring
          refine ⟨t * d, l₀ + t * p, ?_, ?_⟩
          · rw [hcomb, abs_of_pos hzt_pos]; exact hzt_pos
          · rw [hcomb, abs_of_pos hzt_pos]; linarith
      obtain ⟨k, l, hpos_gap, hlt_gap⟩ := hclose
      let t₁ : ℝ := x₀ + ((N₀ + (k : ℤ) : ℤ) : ℝ) * c₀.M
      let t₂ : ℝ := x₁ + ((N₁ + (l : ℤ) : ℤ) : ℝ) * c₁.M
      have ht₁ : t₁ ∈ T := hseq0 (N₀ + (k : ℤ)) (by omega)
      have ht₂ : t₂ ∈ T := hseq1 (N₁ + (l : ℤ)) (by omega)
      have hdiff : t₁ - t₂ = y + (k : ℝ) * c₀.M - (l : ℝ) * c₁.M := by
        simp only [t₁, t₂, y, Int.cast_add, Int.cast_natCast]; ring
      have hne : t₁ ≠ t₂ := fun heq => by
        rw [heq, sub_self] at hdiff
        rw [← hdiff, abs_zero] at hpos_gap
        exact lt_irrefl _ hpos_gap
      have hsep12 := hsep t₁ ht₁ t₂ ht₂ hne
      rw [hdiff] at hsep12
      linarith

/- ## Section 5: Rationality of the Periodic Tiling -/

def tileBadSet (S T : Set ℝ) : Set ℝ :=
  (Set.univ \ ⋃ t ∈ T, {x : ℝ | x - t ∈ S}) ∪
  (⋃ t₁ ∈ T, ⋃ t₂ ∈ T, ⋃ (_ : t₁ ≠ t₂), ({x : ℝ | x - t₁ ∈ S} ∩ {x : ℝ | x - t₂ ∈ S}))

lemma volume_tileBadSet_eq_zero {S T : Set ℝ} (htile : TilesR S T) :
    volume (tileBadSet S T) = 0 := by
  unfold tileBadSet
  refine measure_union_null htile.2.1 ?_
  refine (measure_biUnion_null_iff htile.1).mpr fun t₁ ht₁ => ?_
  refine (measure_biUnion_null_iff htile.1).mpr fun t₂ ht₂ => ?_
  exact measure_iUnion_null fun hne => htile.2.2 t₁ ht₁ t₂ ht₂ hne

lemma existsUnique_of_notMem_tileBadSet {S T : Set ℝ} {x : ℝ} (hx : x ∉ tileBadSet S T) :
    ∃! t : ℝ, t ∈ T ∧ x - t ∈ S := by
  simp only [tileBadSet, Set.mem_union, Set.mem_sdiff, Set.mem_univ, true_and,
    Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, not_or, not_exists] at hx
  obtain ⟨hcov, hdisj⟩ := hx
  push Not at hcov
  obtain ⟨t, ht, hxt⟩ := hcov
  refine ⟨t, ⟨ht, hxt⟩, fun t' ⟨ht', hxt'⟩ => ?_⟩
  by_contra hne
  exact hdisj t' ht' t ht hne ⟨hxt', hxt⟩

lemma periodic_rep_unique {M : ℝ} (hM : 0 < M) {a₁ a₂ : ℝ}
    (ha₁ : 0 ≤ a₁ ∧ a₁ < M) (ha₂ : 0 ≤ a₂ ∧ a₂ < M) {m₁ m₂ : ℤ}
    (heq : a₁ + (m₁ : ℝ) * M = a₂ + (m₂ : ℝ) * M) :
    a₁ = a₂ ∧ m₁ = m₂ := by
  have hdiff : |((m₁ - m₂ : ℤ) : ℝ) * M| < M := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hM] at hdiff
  have hlt1 : |((m₁ - m₂ : ℤ) : ℝ)| < 1 := by nlinarith
  have hlt1_Z : |m₁ - m₂| < 1 := by exact_mod_cast hlt1
  have hm : m₁ = m₂ := by have := abs_lt.mp hlt1_Z; omega
  subst hm
  exact ⟨by linarith, rfl⟩

lemma periodic_tiling_period_eq_card {S : Set ℝ}
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1)
    {M : ℝ} {A0 : Finset ℝ} (hM : 0 < M)
    (hA0_Ico : ∀ a ∈ A0, 0 ≤ a ∧ a < M)
    (htile : TilesR S (⋃ a ∈ A0, ⋃ m : ℤ, {a + (m : ℝ) * M})) :
    M = (A0.card : ℝ) ∧ 0 < A0.card := by
  let T₀ : Set ℝ := ⋃ a ∈ A0, ⋃ m : ℤ, {a + (m : ℝ) * M}
  let g : ℝ → ℝ≥0∞ := fun x =>
    ∑ a ∈ A0, ∑' m : ℤ, Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} (fun _ => (1 : ℝ≥0∞)) x
  have hg_ae : ∀ᵐ x : ℝ, g x = 1 := by
    have hbad : ∀ᵐ x : ℝ, x ∉ tileBadSet S T₀ := by
      have hset : {x : ℝ | ¬ x ∉ tileBadSet S T₀} = tileBadSet S T₀ := by ext x; simp
      rw [ae_iff, hset]
      exact volume_tileBadSet_eq_zero htile
    filter_upwards [hbad] with x hx
    obtain ⟨t, ⟨htT₀, hxtS⟩, huniq⟩ := existsUnique_of_notMem_tileBadSet hx
    simp only [T₀, Set.mem_iUnion, Set.mem_singleton_iff] at htT₀
    obtain ⟨a₀, ha₀, m₀, rfl⟩ := htT₀
    have hiff : ∀ a ∈ A0, ∀ m : ℤ,
        x - (a + (m : ℝ) * M) ∈ S ↔ a = a₀ ∧ m = m₀ := by
      intro a ha m
      constructor
      · intro hS
        have ht' : a + (m : ℝ) * M ∈ T₀ := by
          simp only [T₀, Set.mem_iUnion, Set.mem_singleton_iff]
          exact ⟨a, ha, m, rfl⟩
        have heq := huniq (a + (m : ℝ) * M) ⟨ht', hS⟩
        exact periodic_rep_unique hM (hA0_Ico a ha) (hA0_Ico a₀ ha₀) heq
      · rintro ⟨rfl, rfl⟩
        exact hxtS
    dsimp only [g]
    rw [Finset.sum_eq_single a₀]
    · rw [tsum_eq_single m₀]
      · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | y - (a₀ + (m₀ : ℝ) * M) ∈ S} from hxtS)]
      · intro m hm
        have hnot : x ∉ {y : ℝ | y - (a₀ + (m : ℝ) * M) ∈ S} := fun h => hm ((hiff a₀ ha₀ m).mp h).2
        rw [Set.indicator_of_notMem hnot]
    · intro a ha hne
      have h0 : ∀ m : ℤ, Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S}
          (fun _ => (1 : ℝ≥0∞)) x = 0 := fun m => by
        have hnot : x ∉ {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} := fun h => hne ((hiff a ha m).mp h).1
        rw [Set.indicator_of_notMem hnot]
      simp [h0]
    · intro hnot; exact absurd ha₀ hnot
  have hLHS : ∫⁻ x in Set.Ico 0 M, g x = ENNReal.ofReal M := by
    calc ∫⁻ x in Set.Ico 0 M, g x
        = ∫⁻ _x in Set.Ico 0 M, (1 : ℝ≥0∞) :=
          lintegral_congr_ae (ae_restrict_of_ae hg_ae)
      _ = volume (Set.Ico 0 M) := by simp
      _ = ENNReal.ofReal M := by rw [Real.volume_Ico, sub_zero]
  have hRHS : ∫⁻ x in Set.Ico 0 M, g x = (A0.card : ℝ≥0∞) := by
    have hmeas_am : ∀ (a : ℝ) (m : ℤ),
        Measurable (Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} (fun _ => (1 : ℝ≥0∞))) :=
      fun a m => measurable_const.indicator (hS_meas.preimage (measurable_id.sub measurable_const))
    have hmeas_a : ∀ a ∈ A0, Measurable (fun x : ℝ =>
        ∑' m : ℤ, Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} (fun _ => (1 : ℝ≥0∞)) x) := by
      intro a _
      have heq : (fun x : ℝ => ∑' m : ℤ, Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S}
          (fun _ => (1 : ℝ≥0∞)) x) =
          fun x : ℝ => ⨆ s : Finset ℤ, ∑ m ∈ s,
            Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} (fun _ => (1 : ℝ≥0∞)) x :=
        funext fun _ => ENNReal.tsum_eq_iSup_sum
      rw [heq]
      exact Measurable.iSup fun s => Finset.measurable_sum s fun m _ => hmeas_am a m
    dsimp only [g]
    rw [lintegral_finsetSum _ (fun a ha => hmeas_a a ha)]
    have hterm : ∀ a ∈ A0,
        ∫⁻ x in Set.Ico 0 M,
          (∑' m : ℤ, Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} (fun _ => (1 : ℝ≥0∞)) x) = 1 := by
      intro a _
      rw [lintegral_tsum (fun m => (hmeas_am a m).aemeasurable)]
      have hstep : ∀ m : ℤ,
          ∫⁻ x in Set.Ico 0 M,
            Set.indicator {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} (fun _ => (1 : ℝ≥0∞)) x =
          volume (S ∩ Set.Ico (-(a + (m : ℝ) * M)) (M - (a + (m : ℝ) * M))) := by
        intro m
        have hm_meas : MeasurableSet {y : ℝ | y - (a + (m : ℝ) * M) ∈ S} :=
          hS_meas.preimage (measurable_id.sub measurable_const)
        rw [lintegral_indicator hm_meas]
        simp only [lintegral_one, Measure.restrict_apply_univ,
          Measure.restrict_apply hm_meas]
        have hpre : (fun s : ℝ => s + (a + (m : ℝ) * M)) ⁻¹'
              ({y : ℝ | y - (a + (m : ℝ) * M) ∈ S} ∩ Set.Ico 0 M) =
            S ∩ Set.Ico (-(a + (m : ℝ) * M)) (M - (a + (m : ℝ) * M)) := by
          ext s
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico]
          constructor
          · rintro ⟨hs, h0, hlt⟩
            have heq : s + (a + (m : ℝ) * M) - (a + (m : ℝ) * M) = s := by ring
            rw [heq] at hs
            exact ⟨hs, by linarith, by linarith⟩
          · rintro ⟨hs, hlo, hhi⟩
            have heq : s + (a + (m : ℝ) * M) - (a + (m : ℝ) * M) = s := by ring
            rw [heq]
            exact ⟨hs, by linarith, by linarith⟩
        rw [← measure_preimage_add_right volume (a + (m : ℝ) * M), hpre]
      simp_rw [hstep]
      let E : ℤ → Set ℝ := fun m =>
        S ∩ Set.Ico (-(a + (m : ℝ) * M)) (M - (a + (m : ℝ) * M))
      have hE_meas : ∀ m : ℤ, MeasurableSet (E m) := fun m => hS_meas.inter measurableSet_Ico
      have hE_disj : Pairwise (Function.onFun Disjoint E) := by
        intro m₁ m₂ hne
        dsimp only [Function.onFun]
        rw [Set.disjoint_left]
        rintro s ⟨_, hlo₁, hhi₁⟩ ⟨_, hlo₂, hhi₂⟩
        have hdiff : |((m₁ - m₂ : ℤ) : ℝ) * M| < M := by
          rw [abs_lt]; push_cast; constructor <;> linarith
        rw [abs_mul, abs_of_pos hM] at hdiff
        have hlt1 : |((m₁ - m₂ : ℤ) : ℝ)| < 1 := by nlinarith
        have hlt1_Z : |m₁ - m₂| < 1 := by exact_mod_cast hlt1
        exact hne (by have := abs_lt.mp hlt1_Z; omega)
      have hE_union : ⋃ m : ℤ, E m = S := by
        ext s
        simp only [Set.mem_iUnion, E, Set.mem_inter_iff, Set.mem_Ico]
        constructor
        · rintro ⟨_, hs, _, _⟩; exact hs
        · intro hs
          let k : ℤ := Int.floor ((s + a) / M)
          refine ⟨-k, hs, ?_, ?_⟩
          · have h1 := (le_div_iff₀ hM).mp (Int.floor_le ((s + a) / M))
            push_cast; linarith
          · have h1 := (div_lt_iff₀ hM).mp (Int.lt_floor_add_one ((s + a) / M))
            push_cast; linarith
      rw [← measure_iUnion hE_disj hE_meas, hE_union, hS_vol]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hM_eq : M = (A0.card : ℝ) := by
    have h1 : ENNReal.ofReal M = ENNReal.ofReal (A0.card : ℝ) := by
      rw [← hLHS, hRHS, ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_eq_ofReal_iff hM.le (Nat.cast_nonneg _)).mp h1
  have hcard_pos : 0 < A0.card := by
    have : (0 : ℝ) < (A0.card : ℝ) := by linarith
    exact_mod_cast this
  exact ⟨hM_eq, hcard_pos⟩

lemma tilesR_translate_set {S T : Set ℝ} (htile : TilesR S T) (c : ℝ) :
    TilesR S ((fun t => t - c) '' T) := by
  refine ⟨htile.1.image _, ?_, ?_⟩
  · have hpre : (fun x : ℝ => x + c) ⁻¹' (Set.univ \ ⋃ t ∈ T, {y : ℝ | y - t ∈ S}) =
        Set.univ \ ⋃ t' ∈ (fun t => t - c) '' T, {x : ℝ | x - t' ∈ S} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_univ, true_and,
        Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro h ⟨t', ⟨t, ht, rfl⟩, hxt⟩
        apply h
        refine ⟨t, ht, ?_⟩
        have heq : x + c - t = x - (t - c) := by ring
        rwa [heq]
      · rintro h ⟨t, ht, hxt⟩
        apply h
        refine ⟨t - c, ⟨t, ht, rfl⟩, ?_⟩
        have heq : x - (t - c) = x + c - t := by ring
        rwa [heq]
    rw [← hpre, measure_preimage_add_right, htile.2.1]
  · intro t₁' ht₁' t₂' ht₂' hne'
    rcases ht₁' with ⟨t₁, ht₁, rfl⟩
    rcases ht₂' with ⟨t₂, ht₂, rfl⟩
    have hne : t₁ ≠ t₂ := fun h => hne' (by rw [h])
    have hpre : (fun x : ℝ => x + c) ⁻¹'
          ({y : ℝ | y - t₁ ∈ S} ∩ {y : ℝ | y - t₂ ∈ S}) =
        {x : ℝ | x - (t₁ - c) ∈ S} ∩ {x : ℝ | x - (t₂ - c) ∈ S} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
      have h1 : x + c - t₁ = x - (t₁ - c) := by ring
      have h2 : x + c - t₂ = x - (t₂ - c) := by ring
      rw [h1, h2]
    rw [← hpre, measure_preimage_add_right]
    exact htile.2.2 t₁ ht₁ t₂ ht₂ hne

def periodizeSet (S : Set ℝ) (M : ℝ) : Set ℝ :=
  ⋃ m : ℤ, {x : ℝ | x - (m : ℝ) * M ∈ S}

noncomputable def periodizeInd (S : Set ℝ) (M : ℝ) (x : ℝ) : ℕ :=
  if x ∈ periodizeSet S M then 1 else 0

lemma subset_periodizeSet (S : Set ℝ) (M : ℝ) : S ⊆ periodizeSet S M := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨(0 : ℤ), by simpa using hx⟩

lemma mem_periodizeSet_add_int_mul {S : Set ℝ} {M : ℝ} (x : ℝ) (k : ℤ) :
    x + (k : ℝ) * M ∈ periodizeSet S M ↔ x ∈ periodizeSet S M := by
  simp only [periodizeSet, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m - k, ?_⟩
    have heq : x - ((m - k : ℤ) : ℝ) * M = x + (k : ℝ) * M - (m : ℝ) * M := by push_cast; ring
    rwa [heq]
  · rintro ⟨m, hm⟩
    refine ⟨m + k, ?_⟩
    have heq : x + (k : ℝ) * M - ((m + k : ℤ) : ℝ) * M = x - (m : ℝ) * M := by push_cast; ring
    rwa [heq]

lemma ae_sum_periodizeInd_eq_one {S : Set ℝ} {M : ℝ} {A1 : Finset ℝ} (hM : 0 < M)
    (hA1_Ico : ∀ a ∈ A1, 0 ≤ a ∧ a < M)
    (htile : TilesR S (⋃ a ∈ A1, ⋃ m : ℤ, {a + (m : ℝ) * M})) :
    ∀ᵐ x : ℝ, ∑ a ∈ A1, periodizeInd S M (x - a) = 1 := by
  let T₁ : Set ℝ := ⋃ a ∈ A1, ⋃ m : ℤ, {a + (m : ℝ) * M}
  have hbad : ∀ᵐ x : ℝ, x ∉ tileBadSet S T₁ := by
    have hset : {x : ℝ | ¬ x ∉ tileBadSet S T₁} = tileBadSet S T₁ := by ext x; simp
    rw [ae_iff, hset]
    exact volume_tileBadSet_eq_zero htile
  filter_upwards [hbad] with x hx
  obtain ⟨t, ⟨htT₁, hxtS⟩, huniq⟩ := existsUnique_of_notMem_tileBadSet hx
  simp only [T₁, Set.mem_iUnion, Set.mem_singleton_iff] at htT₁
  obtain ⟨a₀, ha₀, m₀, rfl⟩ := htT₁
  rw [Finset.sum_eq_single a₀]
  · have hmem : x - a₀ ∈ periodizeSet S M := by
      refine Set.mem_iUnion.mpr ⟨m₀, ?_⟩
      show x - a₀ - (m₀ : ℝ) * M ∈ S
      have heq : x - a₀ - (m₀ : ℝ) * M = x - (a₀ + (m₀ : ℝ) * M) := by ring
      rwa [heq]
    rw [periodizeInd, if_pos hmem]
  · intro a ha hne
    have hnot : x - a ∉ periodizeSet S M := by
      rintro hmem
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hmem
      change x - a - (m : ℝ) * M ∈ S at hm
      have hxt' : x - (a + (m : ℝ) * M) ∈ S := by
        have heq : x - (a + (m : ℝ) * M) = x - a - (m : ℝ) * M := by ring
        rwa [heq]
      have ht' : a + (m : ℝ) * M ∈ T₁ := by
        simp only [T₁, Set.mem_iUnion, Set.mem_singleton_iff]
        exact ⟨a, ha, m, rfl⟩
      have heq := huniq (a + (m : ℝ) * M) ⟨ht', hxt'⟩
      exact hne (periodic_rep_unique hM (hA1_Ico a ha) (hA1_Ico a₀ ha₀) heq).1
    rw [periodizeInd, if_neg hnot]
  · intro hnot; exact absurd ha₀ hnot

lemma ae_sum_fin_pow {φ : ℝ → ℕ} {M_nat : ℕ} {B : Finset ℝ}
    (hB_card : B.card = M_nat)
    (hφ_tile : ∀ᵐ x : ℝ, ∑ b ∈ B, φ (x - b) = 1) :
    ∀ k : ℕ, 1 ≤ k →
      ∀ᵐ x : ℝ, ∑ v : Fin k → {b // b ∈ B}, φ (x - ∑ i : Fin k, (v i).1) = M_nat ^ (k - 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      filter_upwards [hφ_tile] with x hx
      have h1 : ∑ v : Fin 1 → {b // b ∈ B}, φ (x - ∑ i : Fin 1, (v i).1) =
          ∑ b : {b // b ∈ B}, φ (x - b.1) := by
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) {b // b ∈ B}) _ _ fun v => ?_
        simp
      rw [h1, Finset.sum_coe_sort B (fun b => φ (x - b)), hx]
      simp
    | succ k =>
      have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
      have hih := ih hk1
      have hshift : ∀ b₀ : {b // b ∈ B},
          ∀ᵐ x : ℝ, ∑ w : Fin (k + 1) → {b // b ∈ B},
            φ ((x - b₀.1) - ∑ j : Fin (k + 1), (w j).1) = M_nat ^ k := fun b₀ => by
        have hmp := measurePreserving_sub_right (volume : Measure ℝ) b₀.1
        have hqmp := hmp.quasiMeasurePreserving
        simpa using hqmp.ae hih
      have hall : ∀ᵐ x : ℝ, ∀ b₀ : {b // b ∈ B},
          ∑ w : Fin (k + 1) → {b // b ∈ B},
            φ ((x - b₀.1) - ∑ j : Fin (k + 1), (w j).1) = M_nat ^ k :=
        ae_all_iff.mpr hshift
      filter_upwards [hall] with x hx
      let e : (Fin (k + 2) → {b // b ∈ B}) ≃
          {b // b ∈ B} × (Fin (k + 1) → {b // b ∈ B}) :=
        (Fin.consEquiv (fun _ : Fin (k + 2) => {b // b ∈ B})).symm
      have heq : ∑ v : Fin (k + 2) → {b // b ∈ B}, φ (x - ∑ i : Fin (k + 2), (v i).1) =
          ∑ p : {b // b ∈ B} × (Fin (k + 1) → {b // b ∈ B}),
            φ ((x - p.1.1) - ∑ j : Fin (k + 1), (p.2 j).1) := by
        refine Fintype.sum_equiv e _ _ fun v => ?_
        have hsum : ∑ i : Fin (k + 2), (v i).1 =
            (v 0).1 + ∑ j : Fin (k + 1), (v j.succ).1 := Fin.sum_univ_succ _
        change φ (x - ∑ i : Fin (k + 2), (v i).1) =
          φ ((x - (v 0).1) - ∑ j : Fin (k + 1), (v j.succ).1)
        rw [hsum, sub_add_eq_sub_sub]
      rw [heq, Fintype.sum_prod_type]
      simp_rw [hx]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hB_card, smul_eq_mul]
      change M_nat * M_nat ^ k = M_nat ^ (k + 1)
      rw [pow_succ']

lemma frobenius_dilation_prime {φ : ℝ → ℕ} {M_nat p : ℕ}
    (hM : 0 < M_nat) (hp : Nat.Prime p) (hpM : M_nat < p)
    (hφ_le : ∀ x : ℝ, φ x ≤ 1)
    {B : Finset ℝ} (hB_card : B.card = M_nat)
    (hφ_tile : ∀ᵐ x : ℝ, ∑ b ∈ B, φ (x - b) = 1) :
    ∀ᵐ x : ℝ, ∑ b ∈ B, φ (x - (p : ℝ) * b) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpow := ae_sum_fin_pow hB_card hφ_tile p hp.pos
  let eFin : Fin p ≃ ZMod p :=
    Fintype.equivOfCardEq (by simp [ZMod.card])
  let eFun : (ZMod p → {b // b ∈ B}) ≃ (Fin p → {b // b ∈ B}) :=
    Equiv.arrowCongr eFin.symm (Equiv.refl _)
  filter_upwards [hpow] with x hx
  let F : (ZMod p → {b // b ∈ B}) → ℕ := fun v => φ (x - ∑ i : ZMod p, (v i).1)
  have htot : ∑ v : ZMod p → {b // b ∈ B}, F v = M_nat ^ (p - 1) := by
    rw [← hx]
    refine Fintype.sum_equiv eFun _ _ fun v => ?_
    dsimp only [F, eFun, Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.symm_symm]
    congr 2
    exact (eFin.sum_comp fun j => (v j).1).symm
  let isConst : (ZMod p → {b // b ∈ B}) → Prop := fun v => ∀ i j : ZMod p, v i = v j
  let constSet : Finset (ZMod p → {b // b ∈ B}) := Finset.univ.filter isConst
  let nonConst : Finset (ZMod p → {b // b ∈ B}) := Finset.univ.filter (fun v => ¬ isConst v)
  have hsplit : ∑ v : ZMod p → {b // b ∈ B}, F v =
      (∑ v ∈ constSet, F v) + (∑ v ∈ nonConst, F v) := by
    simpa [constSet, nonConst] using (Finset.sum_filter_add_sum_filter_not Finset.univ isConst F).symm
  have hconst_sum : ∑ v ∈ constSet, F v = ∑ b ∈ B, φ (x - (p : ℝ) * b) := by
    have h1 : ∑ v ∈ constSet, F v = ∑ b : {b // b ∈ B}, F (fun _ => b) := by
      symm
      refine Finset.sum_bij (fun b _ => (fun _ : ZMod p => b)) ?_ ?_ ?_ ?_
      · intro b _
        simp only [constSet, Finset.mem_filter, Finset.mem_univ, true_and, isConst]
        intro _ _; trivial
      · intro b₁ _ b₂ _ heq
        exact congrFun heq 0
      · intro v hv
        simp only [constSet, Finset.mem_filter, Finset.mem_univ, true_and, isConst] at hv
        refine ⟨v 0, Finset.mem_univ _, ?_⟩
        funext i
        exact hv 0 i
      · intro _ _; rfl
    rw [h1]
    have h2 : ∀ b : {b // b ∈ B}, F (fun _ => b) = φ (x - (p : ℝ) * b.1) := fun b => by
      dsimp only [F]
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    simp_rw [h2]
    exact Finset.sum_coe_sort B (fun b => φ (x - (p : ℝ) * b))
  have hdvd : p ∣ ∑ v ∈ nonConst, F v := by
    let shift : ZMod p → (ZMod p → {b // b ∈ B}) → (ZMod p → {b // b ∈ B}) :=
      fun s v i => v (i + s)
    let orb : (ZMod p → {b // b ∈ B}) → Finset (ZMod p → {b // b ∈ B}) :=
      fun v => Finset.univ.image (fun s : ZMod p => shift s v)
    have hshift_add : ∀ s₁ s₂ v, shift s₁ (shift s₂ v) = shift (s₂ + s₁) v := by
      intro s₁ s₂ v; funext i; simp only [shift, add_assoc, add_comm s₁ s₂]
    have hshift_F : ∀ s v, F (shift s v) = F v := by
      intro s v
      dsimp only [F, shift]
      congr 2
      exact Equiv.sum_comp (Equiv.addRight s) (fun i => (v i).1)
    have horb_eq : ∀ v w, w ∈ orb v → orb w = orb v := by
      intro v w hw
      simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hw
      obtain ⟨s₀, rfl⟩ := hw
      ext u
      simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s₀ + s, (hshift_add s s₀ v).symm⟩
      · rintro ⟨s, rfl⟩
        refine ⟨s - s₀, ?_⟩
        rw [hshift_add, add_sub_cancel]
    have hshift_nonConst : ∀ s v, v ∈ nonConst → shift s v ∈ nonConst := by
      intro s v hv
      simp only [nonConst, Finset.mem_filter, Finset.mem_univ, true_and, isConst] at hv ⊢
      intro hc
      apply hv
      intro i j
      have h1 := hc (i - s) (j - s)
      simpa [shift, sub_add_cancel] using h1
    have hshift_inj : ∀ v ∈ nonConst, Function.Injective (fun s : ZMod p => shift s v) := by
      intro v hv s₁ s₂ heq
      by_contra hne
      let d : ZMod p := s₂ - s₁
      have hd_ne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hper_d : ∀ i : ZMod p, v (i + d) = v i := fun i => by
        have h1 := congrFun heq (i - s₁)
        dsimp only [shift] at h1
        have h2 : i - s₁ + s₁ = i := sub_add_cancel i s₁
        have h3 : i - s₁ + s₂ = i + d := by simp only [d]; ring
        rw [h2, h3] at h1
        exact h1.symm
      have hper_nat : ∀ n : ℕ, v ((n : ZMod p) * d) = v 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hper_d, ih]
      have hconst : isConst v := by
        intro i j
        have hi : v i = v 0 := by
          have h1 : ((i * d⁻¹).val : ZMod p) * d = i := by
            rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hd_ne, mul_one]
          rw [← h1, hper_nat]
        have hj : v j = v 0 := by
          have h1 : ((j * d⁻¹).val : ZMod p) * d = j := by
            rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hd_ne, mul_one]
          rw [← h1, hper_nat]
        rw [hi, hj]
      simp only [nonConst, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hv hconst
    rw [← Finset.sum_fiberwise_of_maps_to (t := nonConst.image orb)
      (fun v hv => Finset.mem_image_of_mem orb hv) F]
    refine Finset.dvd_sum fun O hO => ?_
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hO
    have hfib : nonConst.filter (fun w => orb w = orb v₀) = orb v₀ := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, hwO⟩
        rw [← hwO]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by funext i; simp [shift]⟩
      · intro hw
        have hw_nc : w ∈ nonConst := by
          obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hw
          exact hshift_nonConst s v₀ hv₀
        exact ⟨hw_nc, horb_eq v₀ w hw⟩
    rw [hfib]
    have hF_const : ∀ w ∈ orb v₀, F w = F v₀ := fun w hw => by
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hw
      exact hshift_F s v₀
    rw [Finset.sum_congr rfl hF_const, Finset.sum_const, smul_eq_mul]
    have hcard_orb : (orb v₀).card = p := by
      rw [Finset.card_image_of_injective _ (hshift_inj v₀ hv₀), Finset.card_univ, ZMod.card]
    rw [hcard_orb]
    exact dvd_mul_right p (F v₀)
  let G : ℕ := ∑ b ∈ B, φ (x - (p : ℝ) * b)
  have hG_eq_tot : G + (∑ v ∈ nonConst, F v) = M_nat ^ (p - 1) := by
    dsimp only [G]
    rw [← hconst_sum, ← hsplit, htot]
  have hG_zmod : (G : ZMod p) = 1 := by
    have hcast := congrArg (Nat.cast (R := ZMod p)) hG_eq_tot
    rw [Nat.cast_add, (ZMod.natCast_eq_zero_iff _ p).mpr hdvd, add_zero, Nat.cast_pow] at hcast
    have hM_ne : (M_nat : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact absurd (Nat.le_of_dvd hM h0) (not_le.mpr hpM)
    rw [hcast, ZMod.pow_card_sub_one_eq_one hM_ne]
  have hG_lt : G < p := by
    have hle : G ≤ M_nat := by
      calc G = ∑ b ∈ B, φ (x - (p : ℝ) * b) := rfl
        _ ≤ ∑ _b ∈ B, 1 := Finset.sum_le_sum fun b _ => hφ_le _
        _ = B.card := by simp
        _ = M_nat := hB_card
    exact lt_of_le_of_lt hle hpM
  have hval := congrArg ZMod.val hG_zmod
  rw [ZMod.val_natCast_of_lt hG_lt, ZMod.val_one] at hval
  exact hval

lemma frobenius_dilation_coprime {φ : ℝ → ℕ} {M_nat : ℕ}
    (hM : 0 < M_nat) (hφ_le : ∀ x : ℝ, φ x ≤ 1)
    {A1 : Finset ℝ} (hA1_card : A1.card = M_nat)
    (hφ_tile : ∀ᵐ x : ℝ, ∑ a ∈ A1, φ (x - a) = 1) :
    ∀ r : ℕ, 0 < r → (∀ p : ℕ, Nat.Prime p → p ∣ r → M_nat < p) →
      ∀ᵐ x : ℝ, ∑ a ∈ A1, φ (x - (r : ℝ) * a) = 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr_pos hr_primes
    by_cases hr1 : r = 1
    · subst hr1
      simpa using hφ_tile
    · let p := r.minFac
      have hp_prime : Nat.Prime p := Nat.minFac_prime hr1
      have hp_dvd : p ∣ r := Nat.minFac_dvd r
      have hp_gt : M_nat < p := hr_primes p hp_prime hp_dvd
      let r' := r / p
      have hr_eq : p * r' = r := Nat.mul_div_cancel' hp_dvd
      have hr'_pos : 0 < r' := Nat.div_pos (Nat.le_of_dvd hr_pos hp_dvd) hp_prime.pos
      have hr'_lt : r' < r := Nat.div_lt_self hr_pos hp_prime.one_lt
      have hr'_primes : ∀ q : ℕ, Nat.Prime q → q ∣ r' → M_nat < q := fun q hq hq_dvd =>
        hr_primes q hq (dvd_trans hq_dvd ⟨p, by linarith⟩)
      have hih := ih r' hr'_lt hr'_pos hr'_primes
      let B : Finset ℝ := A1.image (fun a => (r' : ℝ) * a)
      have hinj : Function.Injective (fun a : ℝ => (r' : ℝ) * a) := fun a₁ a₂ heq =>
        mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr'_pos)) heq
      have hB_card : B.card = M_nat := by
        rw [Finset.card_image_of_injective A1 hinj, hA1_card]
      have hB_tile : ∀ᵐ x : ℝ, ∑ b ∈ B, φ (x - b) = 1 := by
        filter_upwards [hih] with x hx
        rw [Finset.sum_image (fun a₁ _ a₂ _ h => hinj h)]
        exact hx
      have hstep := frobenius_dilation_prime hM hp_prime hp_gt hφ_le hB_card hB_tile
      filter_upwards [hstep] with x hx
      rw [Finset.sum_image (fun a₁ _ a₂ _ h => hinj h)] at hx
      have hcast : ∀ a : ℝ, (p : ℝ) * ((r' : ℝ) * a) = (r : ℝ) * a := fun a => by
        rw [← mul_assoc]
        have : (p : ℝ) * (r' : ℝ) = (r : ℝ) := by exact_mod_cast hr_eq
        rw [this]
      simpa [hcast] using hx

lemma periodic_tiling_rational {S : Set ℝ}
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1)
    {M_nat : ℕ} {A1 : Finset ℝ} (hM_pos : 0 < M_nat)
    (hA1_card : A1.card = M_nat) (h0_mem : (0 : ℝ) ∈ A1)
    (hA1_Ico : ∀ a ∈ A1, 0 ≤ a ∧ a < (M_nat : ℝ))
    (htile : TilesR S (⋃ a ∈ A1, ⋃ m : ℤ, {a + (m : ℝ) * (M_nat : ℝ)})) :
    ∀ a ∈ A1, ∃ q : ℚ, (q : ℝ) = a := by
  intro a₀ ha₀
  by_contra hirr
  push Not at hirr
  have ha₀_ne0 : a₀ ≠ 0 := fun h => hirr 0 (by simpa using h.symm)
  have ha₀_pos : 0 < a₀ := lt_of_le_of_ne (hA1_Ico a₀ ha₀).1 (Ne.symm ha₀_ne0)
  have ha₀_ltM : a₀ < (M_nat : ℝ) := (hA1_Ico a₀ ha₀).2
  have hM_R : (0 : ℝ) < (M_nat : ℝ) := Nat.cast_pos.mpr hM_pos
  let φ := periodizeInd S (M_nat : ℝ)
  have hφ_le : ∀ x : ℝ, φ x ≤ 1 := fun x => by
    unfold φ periodizeInd
    split_ifs <;> omega
  have hφ_tile : ∀ᵐ x : ℝ, ∑ a ∈ A1, φ (x - a) = 1 :=
    ae_sum_periodizeInd_eq_one hM_R hA1_Ico htile
  have hauto_zero : ∀ (m : ℕ) (k : ℤ),
      hAuto S (((1 + m * M_nat.factorial : ℕ) : ℝ) * a₀ - (k : ℝ) * (M_nat : ℝ)) = 0 := by
    intro m k
    let r : ℕ := 1 + m * M_nat.factorial
    have hr_pos : 0 < r := by omega
    have hr_primes : ∀ p : ℕ, Nat.Prime p → p ∣ r → M_nat < p := by
      intro p hp hpdvd
      by_contra hle
      push Not at hle
      have hfac : p ∣ M_nat.factorial := Nat.dvd_factorial hp.pos hle
      have hmul : p ∣ m * M_nat.factorial := dvd_mul_of_dvd_right hfac m
      have h1 : p ∣ 1 := by
        have hsub := (Nat.dvd_add_iff_left hmul).mpr hpdvd
        exact hsub
      exact hp.not_dvd_one h1
    have hdil := frobenius_dilation_coprime hM_pos hφ_le hA1_card hφ_tile r hr_pos hr_primes
    have hpair_null : volume (periodizeSet S (M_nat : ℝ) ∩
        {x : ℝ | x - (r : ℝ) * a₀ ∈ periodizeSet S (M_nat : ℝ)}) = 0 := by
      have hsub : periodizeSet S (M_nat : ℝ) ∩
          {x : ℝ | x - (r : ℝ) * a₀ ∈ periodizeSet S (M_nat : ℝ)} ⊆
          {x : ℝ | ∑ a ∈ A1, φ (x - (r : ℝ) * a) ≠ 1} := by
        rintro x ⟨hx1, hx2⟩ hsum
        have hpair_sub : ({(0 : ℝ), a₀} : Finset ℝ) ⊆ A1 := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact h0_mem
          · exact ha₀
        have hle := Finset.sum_le_sum_of_subset hpair_sub
          (f := fun a => φ (x - (r : ℝ) * a))
        rw [Finset.sum_pair ha₀_ne0.symm, mul_zero, sub_zero, hsum] at hle
        have h1 : φ x = 1 := by rw [show φ x = periodizeInd S (M_nat : ℝ) x from rfl, periodizeInd, if_pos hx1]
        have h2 : φ (x - (r : ℝ) * a₀) = 1 := by
          rw [show φ (x - (r : ℝ) * a₀) = periodizeInd S (M_nat : ℝ) (x - (r : ℝ) * a₀) from rfl,
            periodizeInd, if_pos (show x - (r : ℝ) * a₀ ∈ periodizeSet S (M_nat : ℝ) from hx2)]
        omega
      have hae0 : volume {x : ℝ | ∑ a ∈ A1, φ (x - (r : ℝ) * a) ≠ 1} = 0 := by
        simpa [ae_iff] using hdil
      exact measure_mono_null hsub hae0
    have hS_sub : S ∩ {x : ℝ | x - ((r : ℝ) * a₀ - (k : ℝ) * (M_nat : ℝ)) ∈ S} ⊆
        periodizeSet S (M_nat : ℝ) ∩
          {x : ℝ | x - (r : ℝ) * a₀ ∈ periodizeSet S (M_nat : ℝ)} := by
      rintro x ⟨hxS, hxkS⟩
      refine ⟨subset_periodizeSet S (M_nat : ℝ) hxS, ?_⟩
      refine Set.mem_iUnion.mpr ⟨-k, ?_⟩
      show x - (r : ℝ) * a₀ - ((-k : ℤ) : ℝ) * (M_nat : ℝ) ∈ S
      have heq : x - (r : ℝ) * a₀ - ((-k : ℤ) : ℝ) * (M_nat : ℝ) =
          x - ((r : ℝ) * a₀ - (k : ℝ) * (M_nat : ℝ)) := by push_cast; ring
      rwa [heq]
    have hvol0 : volume (S ∩ {x : ℝ | x - ((r : ℝ) * a₀ - (k : ℝ) * (M_nat : ℝ)) ∈ S}) = 0 :=
      measure_mono_null hS_sub hpair_null
    rw [hAuto_eq_volume_inter hS_meas, hvol0]
    simp
  have hcont := continuous_hAuto hS_meas hS_vol
  have h0_eq : hAuto S 0 = 1 := hAuto_zero hS_meas hS_vol
  have hnhds : {y : ℝ | (1 / 2 : ℝ) < hAuto S y} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt continuous_const hcont).mem_nhds (by show (1 / 2 : ℝ) < hAuto S 0; linarith)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.mem_nhds_iff.mp hnhds
  let θ : ℝ := (M_nat.factorial : ℝ) * a₀
  have hfac_pos : 0 < M_nat.factorial := Nat.factorial_pos M_nat
  have hθ_pos : 0 < θ := mul_pos (Nat.cast_pos.mpr hfac_pos) ha₀_pos
  have hnc : ¬ Commens θ (M_nat : ℝ) := by
    rintro ⟨p, q, hp, _, heq⟩
    have hden_ne : ((p * M_nat.factorial : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hp hfac_pos))
    let q_val : ℚ := ((q * M_nat : ℕ) : ℚ) / ((p * M_nat.factorial : ℕ) : ℚ)
    have ha_rat : (q_val : ℝ) = a₀ := by
      simp only [q_val, Rat.cast_div, Rat.cast_natCast]
      rw [div_eq_iff hden_ne]
      simp only [θ, Nat.cast_mul] at heq ⊢
      linarith
    exact hirr q_val ha_rat
  obtain ⟨d, p, _, _, hε_pos, hε_lt⟩ := dirichlet_small_combo hθ_pos hM_R hδ_pos hnc
  let ε : ℝ := (d : ℝ) * θ - (p : ℝ) * (M_nat : ℝ)
  have hε_ne : ε ≠ 0 := abs_pos.mp hε_pos
  have hex_mk : ∃ (m : ℕ) (k : ℤ),
      |((1 + m * M_nat.factorial : ℕ) : ℝ) * a₀ - (k : ℝ) * (M_nat : ℝ)| < δ := by
    rcases lt_or_gt_of_ne hε_ne with hε_neg | hε_gt
    · let s : ℝ := -ε
      have hs_pos : 0 < s := by linarith
      have hs_lt : s < δ := by
        have := hε_lt; change |ε| < δ at this; rw [abs_of_neg hε_neg] at this; exact this
      let t : ℕ := Nat.floor (a₀ / s)
      have ht_lo : (t : ℝ) * s ≤ a₀ := (le_div_iff₀ hs_pos).mp (Nat.floor_le (div_nonneg ha₀_pos.le hs_pos.le))
      have ht_hi : a₀ < ((t : ℝ) + 1) * s := (div_lt_iff₀ hs_pos).mp (Nat.lt_floor_add_one (a₀ / s))
      refine ⟨t * d, ((t * p : ℕ) : ℤ), ?_⟩
      have heq : ((1 + (t * d) * M_nat.factorial : ℕ) : ℝ) * a₀ -
          (((t * p : ℕ) : ℤ) : ℝ) * (M_nat : ℝ) = a₀ - (t : ℝ) * s := by
        push_cast; simp only [s, ε, θ]; ring
      rw [heq, abs_of_nonneg (by linarith)]
      linarith
    · have hε_lt' : ε < δ := by
        have := hε_lt; change |ε| < δ at this; rw [abs_of_pos hε_gt] at this; exact this
      let t : ℕ := Nat.floor (((M_nat : ℝ) - a₀) / ε)
      have ht_lo : (t : ℝ) * ε ≤ (M_nat : ℝ) - a₀ :=
        (le_div_iff₀ hε_gt).mp (Nat.floor_le (div_nonneg (by linarith) hε_gt.le))
      have ht_hi : (M_nat : ℝ) - a₀ < ((t : ℝ) + 1) * ε :=
        (div_lt_iff₀ hε_gt).mp (Nat.lt_floor_add_one (((M_nat : ℝ) - a₀) / ε))
      refine ⟨t * d, ((t * p + 1 : ℕ) : ℤ), ?_⟩
      have heq : ((1 + (t * d) * M_nat.factorial : ℕ) : ℝ) * a₀ -
          (((t * p + 1 : ℕ) : ℤ) : ℝ) * (M_nat : ℝ) = a₀ + (t : ℝ) * ε - (M_nat : ℝ) := by
        push_cast; simp only [ε, θ]; ring
      rw [heq, abs_of_nonpos (by linarith)]
      linarith
  obtain ⟨m, k, hlt⟩ := hex_mk
  have hmem : ((1 + m * M_nat.factorial : ℕ) : ℝ) * a₀ - (k : ℝ) * (M_nat : ℝ) ∈
      Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hlt
  have hpos : (1 / 2 : ℝ) <
      hAuto S (((1 + m * M_nat.factorial : ℕ) : ℝ) * a₀ - (k : ℝ) * (M_nat : ℝ)) := hδ hmem
  rw [hauto_zero m k] at hpos
  norm_num at hpos

lemma exists_rational_periodic_tiling {S : Set ℝ}
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1)
    {M : ℝ} {A0 : Finset ℝ} (hM : 0 < M)
    (hA0_Ico : ∀ a ∈ A0, 0 ≤ a ∧ a < M)
    (htile : TilesR S (⋃ a ∈ A0, ⋃ m : ℤ, {a + (m : ℝ) * M})) :
    ∃ (k L : ℕ) (A : Finset (ZMod L)),
      0 < k ∧ 0 < L ∧ A.card * k = L ∧
      TilesR S {t : ℝ | ∃ z : ℤ, (z : ZMod L) ∈ A ∧ t = (z : ℝ) / (k : ℝ)} := by
  obtain ⟨hM_eq, hcard_pos⟩ := periodic_tiling_period_eq_card hS_meas hS_vol hM hA0_Ico htile
  let M_nat : ℕ := A0.card
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp hcard_pos
  have ha₀_Ico := hA0_Ico a₀ ha₀
  let shiftMod : ℝ → ℝ := fun a => if a₀ ≤ a then a - a₀ else a - a₀ + M
  let A1 : Finset ℝ := A0.image shiftMod
  have hshift_Ico : ∀ a ∈ A0, 0 ≤ shiftMod a ∧ shiftMod a < M := by
    intro a ha
    have ha_Ico := hA0_Ico a ha
    dsimp only [shiftMod]
    split_ifs with hle
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hshift_inj : Set.InjOn shiftMod A0 := by
    intro a₁ ha₁ a₂ ha₂ heq
    have h1 := hA0_Ico a₁ ha₁
    have h2 := hA0_Ico a₂ ha₂
    dsimp only [shiftMod] at heq
    split_ifs at heq <;> linarith
  have hA1_card : A1.card = M_nat := Finset.card_image_of_injOn hshift_inj
  have h0_mem : (0 : ℝ) ∈ A1 :=
    Finset.mem_image.mpr ⟨a₀, ha₀, by simp [shiftMod]⟩
  have hA1_Ico : ∀ a ∈ A1, 0 ≤ a ∧ a < (M_nat : ℝ) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    rw [← hM_eq]
    exact hshift_Ico b hb
  have hT1_eq : (⋃ a ∈ A1, ⋃ m : ℤ, {a + (m : ℝ) * (M_nat : ℝ)}) =
      (fun t => t - a₀) '' (⋃ a ∈ A0, ⋃ m : ℤ, {a + (m : ℝ) * M}) := by
    rw [← hM_eq]
    ext x
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_image, A1, Finset.mem_image]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, m, rfl⟩
      dsimp only [shiftMod]
      split_ifs with hle
      · exact ⟨b + (m : ℝ) * M, ⟨b, hb, m, rfl⟩, by ring⟩
      · refine ⟨b + ((m + 1 : ℤ) : ℝ) * M, ⟨b, hb, m + 1, rfl⟩, ?_⟩
        push_cast; ring
    · rintro ⟨_, ⟨b, hb, m, rfl⟩, rfl⟩
      dsimp only [shiftMod]
      by_cases hle : a₀ ≤ b
      · refine ⟨b - a₀, ⟨b, hb, if_pos hle⟩, m, by ring⟩
      · refine ⟨b - a₀ + M, ⟨b, hb, if_neg hle⟩, m - 1, ?_⟩
        push_cast; ring
  have htile1 : TilesR S (⋃ a ∈ A1, ⋃ m : ℤ, {a + (m : ℝ) * (M_nat : ℝ)}) := by
    rw [hT1_eq]
    exact tilesR_translate_set htile a₀
  have hrat := periodic_tiling_rational hS_meas hS_vol hcard_pos hA1_card h0_mem hA1_Ico htile1
  let qOf : ℝ → ℚ := fun a => if h : a ∈ A1 then Classical.choose (hrat a h) else 0
  have hqOf : ∀ a ∈ A1, ((qOf a : ℚ) : ℝ) = a := fun a ha => by
    simp only [qOf, dif_pos ha]
    exact Classical.choose_spec (hrat a ha)
  let k : ℕ := ∏ a ∈ A1, (qOf a).den
  have hk_pos : 0 < k := Finset.prod_pos fun a _ => (qOf a).den_pos
  have hk_R_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  let L : ℕ := k * M_nat
  have hL_pos : 0 < L := Nat.mul_pos hk_pos hcard_pos
  let zOf : ℝ → ℤ := fun a => (qOf a).num * ((k / (qOf a).den : ℕ) : ℤ)
  have hzOf_div : ∀ a ∈ A1, (zOf a : ℝ) / (k : ℝ) = a := by
    intro a ha
    have hdvd : (qOf a).den ∣ k := Finset.dvd_prod_of_mem (fun b => (qOf b).den) ha
    have hk_eq : (qOf a).den * (k / (qOf a).den) = k := Nat.mul_div_cancel' hdvd
    have hq_eq : ((qOf a : ℚ) : ℝ) = ((qOf a).num : ℝ) / ((qOf a).den : ℝ) :=
      Rat.cast_def (qOf a)
    have h1 : (zOf a : ℝ) = ((qOf a).num : ℝ) * ((k / (qOf a).den : ℕ) : ℝ) := by
      simp only [zOf, Int.cast_mul, Int.cast_natCast]
    have h2 : (k : ℝ) = ((qOf a).den : ℝ) * ((k / (qOf a).den : ℕ) : ℝ) := by
      exact_mod_cast hk_eq.symm
    have hdiv_ne : ((k / (qOf a).den : ℕ) : ℝ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h2
      linarith
    rw [h1, h2, mul_div_mul_right _ _ hdiv_ne, ← hq_eq, hqOf a ha]
  have hzOf_bounds : ∀ a ∈ A1, 0 ≤ zOf a ∧ zOf a < (L : ℤ) := by
    intro a ha
    have ha_Ico := hA1_Ico a ha
    have hdiv := hzOf_div a ha
    have h1 : 0 ≤ (zOf a : ℝ) := by
      have hmul : 0 ≤ (zOf a : ℝ) / (k : ℝ) * (k : ℝ) := mul_nonneg (by linarith) hk_R_pos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hk_R_pos)] at hmul
    have h2 : (zOf a : ℝ) < (L : ℝ) := by
      have hL_cast : (L : ℝ) = (k : ℝ) * (M_nat : ℝ) := by simp [L]
      rw [hL_cast]
      have : (zOf a : ℝ) / (k : ℝ) < (M_nat : ℝ) := by linarith
      have := (div_lt_iff₀ hk_R_pos).mp this
      linarith
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  let A : Finset (ZMod L) := A1.image (fun a => (zOf a : ZMod L))
  have hA_inj : Set.InjOn (fun a => (zOf a : ZMod L)) A1 := by
    intro a₁ ha₁ a₂ ha₂ heq
    have hb₁ := hzOf_bounds a₁ ha₁
    have hb₂ := hzOf_bounds a₂ ha₂
    have hn₁ : ((zOf a₁).toNat : ℤ) = zOf a₁ := Int.toNat_of_nonneg hb₁.1
    have hn₂ : ((zOf a₂).toNat : ℤ) = zOf a₂ := Int.toNat_of_nonneg hb₂.1
    have hlt₁ : (zOf a₁).toNat < L := by omega
    have hlt₂ : (zOf a₂).toNat < L := by omega
    have heq_nat : ((zOf a₁).toNat : ZMod L) = ((zOf a₂).toNat : ZMod L) := by
      have h1 : (((zOf a₁).toNat : ℤ) : ZMod L) = (((zOf a₂).toNat : ℤ) : ZMod L) := by
        rw [hn₁, hn₂]; exact heq
      rwa [Int.cast_natCast, Int.cast_natCast] at h1
    have hval := congrArg ZMod.val heq_nat
    rw [ZMod.val_natCast_of_lt hlt₁, ZMod.val_natCast_of_lt hlt₂] at hval
    have hz_eq : zOf a₁ = zOf a₂ := by omega
    rw [← hzOf_div a₁ ha₁, ← hzOf_div a₂ ha₂, hz_eq]
  have hA_card : A.card * k = L := by
    rw [Finset.card_image_of_injOn hA_inj, hA1_card]
    simp [L, mul_comm]
  have hset_eq : {t : ℝ | ∃ z : ℤ, (z : ZMod L) ∈ A ∧ t = (z : ℝ) / (k : ℝ)} =
      ⋃ a ∈ A1, ⋃ m : ℤ, {a + (m : ℝ) * (M_nat : ℝ)} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff, A, Finset.mem_image]
    constructor
    · rintro ⟨z, ⟨a, ha, hz_mod⟩, rfl⟩
      have hdvd : (L : ℤ) ∣ z - zOf a :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (zOf a) z L).mp hz_mod
      obtain ⟨m, hm⟩ := hdvd
      refine ⟨a, ha, m, ?_⟩
      have hz_eq : (z : ℝ) = (zOf a : ℝ) + (m : ℝ) * ((k : ℝ) * (M_nat : ℝ)) := by
        have h1 : z = zOf a + (L : ℤ) * m := by linarith
        have h2 : (z : ℝ) = (zOf a : ℝ) + (L : ℝ) * (m : ℝ) := by exact_mod_cast h1
        have hL_cast : (L : ℝ) = (k : ℝ) * (M_nat : ℝ) := by simp [L]
        rw [h2, hL_cast]; ring
      rw [hz_eq, add_div, hzOf_div a ha]
      field_simp [ne_of_gt hk_R_pos]
    · rintro ⟨a, ha, m, rfl⟩
      let z : ℤ := zOf a + m * (L : ℤ)
      refine ⟨z, ⟨a, ha, ?_⟩, ?_⟩
      · simp only [z, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
          mul_zero, add_zero]
      · have hz_cast : (z : ℝ) = (zOf a : ℝ) + (m : ℝ) * ((k : ℝ) * (M_nat : ℝ)) := by
          have hL_cast : (L : ℝ) = (k : ℝ) * (M_nat : ℝ) := by simp [L]
          simp only [z, Int.cast_add, Int.cast_mul, Int.cast_natCast, hL_cast]
        rw [hz_cast, add_div, hzOf_div a ha]
        field_simp [ne_of_gt hk_R_pos]
  refine ⟨k, L, A, hk_pos, hL_pos, hA_card, ?_⟩
  rw [hset_eq]
  exact htile1

/- ## Section 6: Rational Periodic Tiling to Fiber Decomposition (`H1`) -/

lemma h1_proof : OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1.H1 := by
  intro Ω hΩ_bdd hΩ_meas hΩ_vol htile_Ω
  obtain ⟨hS_bdd, hS_meas, hS_vol, T_orig, htile_orig⟩ :=
    tilesByTranslation_to_tilesR hΩ_bdd hΩ_meas hΩ_vol htile_Ω
  let S : Set ℝ := (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' Ω
  change Bornology.IsBounded S at hS_bdd
  change MeasurableSet S at hS_meas
  change volume S = 1 at hS_vol
  change TilesR S T_orig at htile_orig
  obtain ⟨M, A0, hM, hA0_Ico, htile_per⟩ :=
    exists_periodic_tiling_of_tilesR hS_bdd hS_meas hS_vol htile_orig
  obtain ⟨k, L, A, hk_pos, hL_pos, hA_card, htile_rat⟩ :=
    exists_rational_periodic_tiling hS_meas hS_vol hM hA0_Ico htile_per
  have : NeZero L := ⟨Nat.ne_of_gt hL_pos⟩
  have hk_R_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  let T_rat : Set ℝ := {t : ℝ | ∃ z : ℤ, (z : ZMod L) ∈ A ∧ t = (z : ℝ) / (k : ℝ)}
  obtain ⟨R₀, hR₀⟩ := hS_bdd.subset_closedBall (0 : ℝ)
  let R : ℝ := max R₀ 0
  have hS_bd : ∀ s ∈ S, |s| ≤ R := fun s hs => by
    have h1 := hR₀ hs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    exact le_trans h1 (le_max_left _ _)
  let K : ℕ := Nat.ceil ((R + 1 / (k : ℝ)) * (k : ℝ))
  have hK_ge : R + 1 / (k : ℝ) ≤ (K : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_R_pos]
    exact Nat.le_ceil _
  let I_K : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hmem_IK : ∀ t ∈ Set.Ico (0 : ℝ) (1 / (k : ℝ)), ∀ b : ℤ,
      t + (b : ℝ) / (k : ℝ) ∈ S → b ∈ I_K := by
    intro t ht b hbS
    have h1 : |t + (b : ℝ) / (k : ℝ)| ≤ R := hS_bd _ hbS
    have h2 : |t| ≤ 1 / (k : ℝ) := by
      rw [abs_of_nonneg ht.1]; exact ht.2.le
    have h3 : |(b : ℝ) / (k : ℝ)| ≤ (K : ℝ) / (k : ℝ) := by
      have htri := abs_sub_le (t + (b : ℝ) / (k : ℝ)) t 0
      have htri2 : |(b : ℝ) / (k : ℝ)| ≤ |t + (b : ℝ) / (k : ℝ)| + |t| := by
        have := abs_add_le (t + (b : ℝ) / (k : ℝ)) (-t)
        simpa [add_sub_cancel_left] using this
      linarith
    rw [abs_div, abs_of_pos hk_R_pos] at h3
    have h4 : |(b : ℝ)| ≤ (K : ℝ) := (div_le_div_iff_of_pos_right hk_R_pos).mp h3
    have h5 : |b| ≤ (K : ℤ) := by exact_mod_cast h4
    rw [Finset.mem_Icc]
    exact abs_le.mp h5
  let fiber : ℝ → Finset ℤ := fun t => I_K.filter (fun b => t + (b : ℝ) / (k : ℝ) ∈ S)
  let goodFiber : Finset ℤ → Prop := fun B =>
    B.card = k ∧ ∀ z : ZMod L,
      ∃! p : {a // a ∈ A} × {b // b ∈ B}, p.1.1 + (p.2.1 : ZMod L) = z
  let ℬ : Finset (Finset ℤ) := I_K.powerset.filter goodFiber
  let T : Finset ℤ → Set ℝ := fun B =>
    {t : ℝ | t ∈ Set.Ico (0 : ℝ) (1 / (k : ℝ)) ∧ fiber t = B}
  have hT_meas : ∀ B ∈ ℬ, MeasurableSet (T B) ∧ T B ⊆ Set.Ico 0 (1 / (k : ℝ)) := by
    intro B hB
    have hB_sub : B ⊆ I_K := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    refine ⟨?_, fun t ht => ht.1⟩
    have heq : T B = Set.Ico (0 : ℝ) (1 / (k : ℝ)) ∩
        (⋂ b ∈ B, {t : ℝ | t + (b : ℝ) / (k : ℝ) ∈ S}) ∩
        (⋂ b ∈ I_K \ B, {t : ℝ | t + (b : ℝ) / (k : ℝ) ∈ S}ᶜ) := by
      ext t
      simp only [T, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_sdiff]
      constructor
      · rintro ⟨htIco, hfib⟩
        refine ⟨⟨htIco, fun b hb => ?_⟩, fun b ⟨hbIK, hbnot⟩ => ?_⟩
        · rw [← hfib] at hb
          exact (Finset.mem_filter.mp hb).2
        · intro hbS
          have hmem : b ∈ fiber t := Finset.mem_filter.mpr ⟨hbIK, hbS⟩
          rw [hfib] at hmem
          exact hbnot hmem
      · rintro ⟨⟨htIco, hin⟩, hout⟩
        refine ⟨htIco, ?_⟩
        ext b
        simp only [fiber, Finset.mem_filter]
        constructor
        · rintro ⟨hbIK, hbS⟩
          by_contra hbnot
          exact hout b ⟨hbIK, hbnot⟩ hbS
        · intro hb
          exact ⟨hB_sub hb, hin b hb⟩
    rw [heq]
    refine (measurableSet_Ico.inter ?_).inter ?_
    · exact MeasurableSet.biInter (Finset.countable_toSet B) fun b _ =>
        hS_meas.preimage (measurable_id.add measurable_const)
    · exact MeasurableSet.biInter (Finset.countable_toSet (I_K \ B)) fun b _ =>
        (hS_meas.preimage (measurable_id.add measurable_const)).compl
  have hT_disj : ∀ B₁ ∈ ℬ, ∀ B₂ ∈ ℬ, B₁ ≠ B₂ → Disjoint (T B₁) (T B₂) := by
    intro B₁ _ B₂ _ hne
    rw [Set.disjoint_left]
    rintro t ⟨_, h1⟩ ⟨_, h2⟩
    exact hne (h1.symm.trans h2)
  have hcov_null : volume (Set.Ico (0 : ℝ) (1 / (k : ℝ)) \ ⋃ B ∈ ℬ, T B) = 0 := by
    let Bad : Set ℝ := ⋃ w : ℤ, {t : ℝ | t + (w : ℝ) / (k : ℝ) ∈ tileBadSet S T_rat}
    have hBad_null : volume Bad = 0 := by
      refine measure_iUnion_null fun w => ?_
      have hpre : {t : ℝ | t + (w : ℝ) / (k : ℝ) ∈ tileBadSet S T_rat} =
          (fun t : ℝ => t + (w : ℝ) / (k : ℝ)) ⁻¹' tileBadSet S T_rat := rfl
      rw [hpre, measure_preimage_add_right]
      exact volume_tileBadSet_eq_zero htile_rat
    have hsub : Set.Ico (0 : ℝ) (1 / (k : ℝ)) \ ⋃ B ∈ ℬ, T B ⊆ Bad := by
      rintro t ⟨htIco, htnot⟩
      by_contra htgood
      have hgood : goodFiber (fiber t) := by
        have huniq_z : ∀ z₀ : ZMod L,
            ∃! p : {a // a ∈ A} × {b // b ∈ fiber t}, p.1.1 + (p.2.1 : ZMod L) = z₀ := by
          intro z₀
          let w : ℤ := (z₀.val : ℤ)
          have hw_not_bad : t + (w : ℝ) / (k : ℝ) ∉ tileBadSet S T_rat := fun h =>
            htgood (Set.mem_iUnion.mpr ⟨w, h⟩)
          obtain ⟨u, ⟨huT, huS⟩, huniq_u⟩ := existsUnique_of_notMem_tileBadSet hw_not_bad
          obtain ⟨z, hzA, rfl⟩ := huT
          let b₀ : ℤ := w - z
          have hb₀S : t + (b₀ : ℝ) / (k : ℝ) ∈ S := by
            have heq : t + (b₀ : ℝ) / (k : ℝ) = t + (w : ℝ) / (k : ℝ) - (z : ℝ) / (k : ℝ) := by
              simp only [b₀, Int.cast_sub]; ring
            rwa [heq]
          have hb₀_fib : b₀ ∈ fiber t :=
            Finset.mem_filter.mpr ⟨hmem_IK t htIco b₀ hb₀S, hb₀S⟩
          have hsum_z₀ : (z : ZMod L) + (b₀ : ZMod L) = z₀ := by
            simp only [b₀, Int.cast_sub, add_sub_cancel, w, Int.cast_natCast,
              ZMod.natCast_zmod_val]
          refine ⟨(⟨(z : ZMod L), hzA⟩, ⟨b₀, hb₀_fib⟩), hsum_z₀, ?_⟩
          rintro ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩ hsum₁
          dsimp only at hsum₁
          let z₁ : ℤ := w - b₁
          have hz₁_mod : (z₁ : ZMod L) = a₁ := by
            simp only [z₁, Int.cast_sub, w, Int.cast_natCast, ZMod.natCast_zmod_val]
            rw [← hsum₁, add_sub_cancel_right]
          have hz₁_T : (z₁ : ℝ) / (k : ℝ) ∈ T_rat := ⟨z₁, hz₁_mod.symm ▸ ha₁, rfl⟩
          have hz₁_S : t + (w : ℝ) / (k : ℝ) - (z₁ : ℝ) / (k : ℝ) ∈ S := by
            have heq : t + (w : ℝ) / (k : ℝ) - (z₁ : ℝ) / (k : ℝ) = t + (b₁ : ℝ) / (k : ℝ) := by
              simp only [z₁, Int.cast_sub]; ring
            rw [heq]
            exact (Finset.mem_filter.mp hb₁).2
          have hdiv_eq : (z₁ : ℝ) / (k : ℝ) = (z : ℝ) / (k : ℝ) :=
            huniq_u ((z₁ : ℝ) / (k : ℝ)) ⟨hz₁_T, hz₁_S⟩
          have hz₁_eq_R : (z₁ : ℝ) = (z : ℝ) := (div_left_inj' (ne_of_gt hk_R_pos)).mp hdiv_eq
          have hz₁_eq : z₁ = z := by exact_mod_cast hz₁_eq_R
          have hb_eq : b₁ = b₀ := by omega
          have ha_eq : a₁ = (z : ZMod L) := by rw [← hz₁_mod, hz₁_eq]
          apply Prod.ext <;> apply Subtype.ext
          · exact ha_eq
          · exact hb_eq
        have hcard_fib : (fiber t).card = k := by
          let f : {a // a ∈ A} × {b // b ∈ fiber t} → ZMod L :=
            fun p => p.1.1 + (p.2.1 : ZMod L)
          have hbij : Function.Bijective f := by
            constructor
            · intro p₁ p₂ heq
              obtain ⟨p₀, _, huniq⟩ := huniq_z (f p₂)
              exact (huniq p₁ heq).trans (huniq p₂ rfl).symm
            · intro z₀
              obtain ⟨p₀, hp₀, _⟩ := huniq_z z₀
              exact ⟨p₀, hp₀⟩
          have hcard_eq := Fintype.card_of_bijective hbij
          rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, ZMod.card] at hcard_eq
          have hA_pos : 0 < A.card := by
            by_contra h0
            have : A.card = 0 := by omega
            rw [this, zero_mul] at hA_card
            omega
          exact Nat.eq_of_mul_eq_mul_left hA_pos (hcard_eq.trans hA_card.symm)
        exact ⟨hcard_fib, huniq_z⟩
      have hfib_mem : fiber t ∈ ℬ :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), hgood⟩
      exact htnot (Set.mem_biUnion hfib_mem ⟨htIco, rfl⟩)
    exact measure_mono_null hsub hBad_null
  have hsymm_null : volume (symmDiff Ω (⋃ B ∈ ℬ, {x : Fin 1 → ℝ | ∃ t ∈ T B, ∃ b ∈ B,
      x 0 = t + (b : ℝ) / (k : ℝ)})) = 0 := by
    let U_R : Set ℝ := ⋃ B ∈ ℬ, {y : ℝ | ∃ t ∈ T B, ∃ b ∈ B, y = t + (b : ℝ) / (k : ℝ)}
    have hU_eq : (⋃ B ∈ ℬ, {x : Fin 1 → ℝ | ∃ t ∈ T B, ∃ b ∈ B,
        x 0 = t + (b : ℝ) / (k : ℝ)}) = {x : Fin 1 → ℝ | x 0 ∈ U_R} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, U_R]
    have hsymm_eq : symmDiff Ω {x : Fin 1 → ℝ | x 0 ∈ U_R} =
        {x : Fin 1 → ℝ | x 0 ∈ symmDiff S U_R} := by
      have hΩ_eq : Ω = {x : Fin 1 → ℝ | x 0 ∈ S} := proj1_equiv_eq Ω
      rw [hΩ_eq]
      ext x
      simp only [Set.mem_symmDiff, Set.mem_ofPred_eq]
    rw [hU_eq, hsymm_eq, volume_preimage_apply0]
    let E : Set ℝ := Set.Ico (0 : ℝ) (1 / (k : ℝ)) \ ⋃ B ∈ ℬ, T B
    have hE_null : volume E = 0 := hcov_null
    have hsub : symmDiff S U_R ⊆ ⋃ m : ℤ, {y : ℝ | y - (m : ℝ) / (k : ℝ) ∈ E} := by
      intro y hy
      by_contra hnot
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hnot
      let m : ℤ := Int.floor (y * (k : ℝ))
      let t : ℝ := y - (m : ℝ) / (k : ℝ)
      have htIco : t ∈ Set.Ico (0 : ℝ) (1 / (k : ℝ)) := by
        constructor
        · have h1 : (m : ℝ) ≤ y * (k : ℝ) := Int.floor_le (y * (k : ℝ))
          have h2 : (m : ℝ) / (k : ℝ) ≤ y := (div_le_iff₀ hk_R_pos).mpr h1
          linarith
        · have h1 : y * (k : ℝ) < (m : ℝ) + 1 := Int.lt_floor_add_one (y * (k : ℝ))
          have h2 : y - (m : ℝ) / (k : ℝ) < 1 / (k : ℝ) := by
            rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hk_R_pos]
            linarith
          exact h2
      have ht_notE : t ∉ E := hnot m
      have ht_inU : t ∈ ⋃ B ∈ ℬ, T B := by
        by_contra hnu
        exact ht_notE ⟨htIco, hnu⟩
      simp only [Set.mem_iUnion] at ht_inU
      obtain ⟨B, hB, htTB⟩ := ht_inU
      have hiff : y ∈ S ↔ y ∈ U_R := by
        constructor
        · intro hyS
          have htm : t + (m : ℝ) / (k : ℝ) ∈ S := by
            have heq : t + (m : ℝ) / (k : ℝ) = y := by simp only [t]; ring
            rwa [heq]
          have hm_fib : m ∈ fiber t :=
            Finset.mem_filter.mpr ⟨hmem_IK t htIco m htm, htm⟩
          rw [htTB.2] at hm_fib
          simp only [U_R, Set.mem_iUnion, Set.mem_ofPred_eq]
          exact ⟨B, hB, t, htTB, m, hm_fib, by simp only [t]; ring⟩
        · intro hyU
          simp only [U_R, Set.mem_iUnion, Set.mem_ofPred_eq] at hyU
          obtain ⟨_, _, _, ht'TB, _, hb'B, hy_eq⟩ := hyU
          rw [← ht'TB.2] at hb'B
          have hb'S := (Finset.mem_filter.mp hb'B).2
          rwa [← hy_eq] at hb'S
      rcases hy with ⟨hyS, hyU⟩ | ⟨hyU, hyS⟩
      · exact hyU (hiff.mp hyS)
      · exact hyS (hiff.mpr hyU)
    refine measure_mono_null hsub (measure_iUnion_null fun m => ?_)
    have hpre : {y : ℝ | y - (m : ℝ) / (k : ℝ) ∈ E} =
        (fun y : ℝ => y - (m : ℝ) / (k : ℝ)) ⁻¹' E := rfl
    rw [hpre, volume_preimage_sub_right]
    exact hE_null
  exact ⟨k, L, A, ℬ, T, hk_pos, hL_pos,
    fun B hB => (Finset.mem_filter.mp hB).2,
    hT_meas, hT_disj, hcov_null, hsymm_null⟩

end DiscreteToH1

end FugledeR1H1

theorem OMA.solution : OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1.H1 :=
  FugledeR1H1.h1_proof
