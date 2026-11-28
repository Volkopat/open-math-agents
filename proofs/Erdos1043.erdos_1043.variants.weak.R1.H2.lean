import OMAReductions.R_Erdos1043_erdos_1043_variants_weak_R1

/-!
# Proof of `Erdos1043.erdos_1043.variants.weak.R1.H2`

We prove Pommerenke's Cauchy–Crofton projection inequality for polygonal enclosures in `ℂ`:
if `K ⊆ ⋃ i, convexHull ℝ (v i '' Set.Iic (n i))` where each `v i` is a closed polygonal loop
(`v i (n i) = v i 0`) and the total perimeter satisfies
`∑ i, ∑ j ∈ range (n i), ‖v i (j + 1) - v i j‖ < π * C`,
then there exists a unit vector `u : ℂ` such that the 1-dimensional Lebesgue measure of the
orthogonal projection of `K` onto `ℝ ∙ u` is at most `ENNReal.ofReal C`.

Proof outline:
1. For any unit vector `u`, the map `t ↦ t • u` is a linear isometry equivalence
   `ℝ ≃ₗᵢ[ℝ] (ℝ ∙ u)`, hence measure-preserving, and `(ℝ ∙ u).orthogonalProjectionOnto z`
   corresponds to the real inner product `⟪u, z⟫`.
2. For each closed loop `v i`, the projected convex hull lies inside the interval `[a_i, b_i]`
   spanned by its vertices. Because the loop is closed, any two vertices are connected by two
   complementary arcs partitioning `range (n i)`, giving
   `b_i - a_i ≤ (1 / 2) * ∑ j ∈ range (n i), |⟪u, v i (j + 1) - v i j⟫|`.
3. Averaging over unit vectors `u(θ) = ⟨cos θ, sin θ⟩` for `θ ∈ [0, π]` uses
   `∫ θ in 0..π, |⟪u(θ), w⟫| = 2 * ‖w‖`, so the integral of the upper bound over `[0, π]`
   equals the total perimeter `< π * C = ∫ θ in 0..π, C`. Hence some `θ ∈ [0, π]` attains `≤ C`.
-/

namespace OMA.Proof_Erdos1043_H2

noncomputable section

open Finset MeasureTheory Real
open scoped RealInnerProductSpace

/- ### Step 1: Linear isometry equivalence between `ℝ` and `ℝ ∙ u`, and projection formula -/

private def lineEquiv (u : ℂ) (hu : ‖u‖ = 1) : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ u) where
  toFun t := ⟨t • u, Submodule.smul_mem _ t (Submodule.mem_span_singleton_self u)⟩
  invFun y := ⟪u, (y : ℂ)⟫
  map_add' s t := by
    ext
    simp [add_smul]
  map_smul' r t := by
    ext
    simp [mul_smul]
  left_inv t := by
    change ⟪u, t • u⟫ = t
    rw [inner_smul_right, real_inner_self_eq_norm_sq, hu]
    ring
  right_inv y := by
    rcases Submodule.mem_span_singleton.mp y.2 with ⟨t, ht⟩
    ext
    change ⟪u, (y : ℂ)⟫ • u = (y : ℂ)
    rw [← ht, inner_smul_right, real_inner_self_eq_norm_sq, hu]
    simp
  norm_map' t := by
    change ‖t • u‖ = ‖t‖
    rw [norm_smul, hu, mul_one]

private lemma orthogonalProjectionOnto_eq_lineEquiv (u : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    (ℝ ∙ u).orthogonalProjectionOnto z = lineEquiv u hu ⟪u, z⟫ := by
  have hmem : ((ℝ ∙ u).orthogonalProjectionOnto z : ℂ) ∈ ℝ ∙ u :=
    ((ℝ ∙ u).orthogonalProjectionOnto z).2
  rcases Submodule.mem_span_singleton.mp hmem with ⟨t, ht⟩
  have horth : ⟪z - (ℝ ∙ u).starProjection z, u⟫ = 0 :=
    Submodule.starProjection_inner_eq_zero z u (Submodule.mem_span_singleton_self u)
  have hproj : (ℝ ∙ u).starProjection z = t • u := ht.symm
  rw [hproj, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hu] at horth
  simp only [RCLike.conj_to_real, one_pow, mul_one, sub_eq_zero] at horth
  have htu : t = ⟪u, z⟫ := by
    rw [real_inner_comm]
    exact horth.symm
  ext
  change ((ℝ ∙ u).orthogonalProjectionOnto z : ℂ) = ⟪u, z⟫ • u
  rw [← ht, htu]

private lemma volume_image_lineEquiv_Icc (u : ℂ) (hu : ‖u‖ = 1) (a b : ℝ) :
    volume (lineEquiv u hu '' Set.Icc a b) = ENNReal.ofReal (b - a) := by
  have himg : lineEquiv u hu '' Set.Icc a b = (lineEquiv u hu).symm ⁻¹' Set.Icc a b := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa using ht
    · intro hy
      exact ⟨(lineEquiv u hu).symm y, hy, by simp⟩
  rw [himg, (lineEquiv u hu).symm.measurePreserving.measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc]

/- ### Step 2: Closed-loop projection diameter bound -/

private lemma sum_Ico_sub (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (g (j + 1) - g j) = g b - g a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hka ih =>
    rw [Finset.sum_Ico_succ_top hka, ih]
    ring

private lemma closed_loop_oscillation {g : ℕ → ℝ} {N : ℕ} (hclosed : g N = g 0)
    {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) :
    2 * |g b - g a| ≤ ∑ j ∈ Finset.range N, |g (j + 1) - g j| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm]
    exact this hb ha (by omega)
  have h1 : |g b - g a| ≤ ∑ j ∈ Finset.Ico a b, |g (j + 1) - g j| := by
    rw [← sum_Ico_sub g hab]
    exact Finset.abs_sum_le_sum_abs _ _
  have h2_eq : g a - g b =
      (∑ j ∈ Finset.Ico 0 a, (g (j + 1) - g j)) + (∑ j ∈ Finset.Ico b N, (g (j + 1) - g j)) := by
    rw [sum_Ico_sub g (Nat.zero_le a), sum_Ico_sub g hb, hclosed]
    ring
  have h2 : |g b - g a| ≤
      (∑ j ∈ Finset.Ico 0 a, |g (j + 1) - g j|) + (∑ j ∈ Finset.Ico b N, |g (j + 1) - g j|) := by
    rw [abs_sub_comm, h2_eq]
    exact (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
      (Finset.abs_sum_le_sum_abs _ _))
  have hsplit : (∑ j ∈ Finset.Ico 0 a, |g (j + 1) - g j|) +
      (∑ j ∈ Finset.Ico a b, |g (j + 1) - g j|) +
      (∑ j ∈ Finset.Ico b N, |g (j + 1) - g j|) =
      ∑ j ∈ Finset.range N, |g (j + 1) - g j| := by
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le a) hab,
      Finset.sum_Ico_consecutive _ (Nat.zero_le b) hb, Nat.Ico_zero_eq_range]
  linarith

private lemma volume_projection_loop_le (u : ℂ) (hu : ‖u‖ = 1) (N : ℕ) (w : ℕ → ℂ)
    (hclosed : w N = w 0) :
    volume ((ℝ ∙ u).orthogonalProjectionOnto '' convexHull ℝ (w '' Set.Iic N)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * ∑ j ∈ Finset.range N, |⟪u, w (j + 1) - w j⟫|) := by
  let g : ℕ → ℝ := fun j => ⟪u, w j⟫
  let S : Finset ℕ := Finset.range (N + 1)
  have hS : S.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  let a : ℝ := S.inf' hS g
  let b : ℝ := S.sup' hS g
  obtain ⟨ja, hja_mem, hja_eq⟩ := Finset.exists_mem_eq_inf' hS g
  obtain ⟨jb, hjb_mem, hjb_eq⟩ := Finset.exists_mem_eq_sup' hS g
  have hja : ja ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hja_mem)
  have hjb : jb ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjb_mem)
  have hab : a ≤ b := by
    dsimp only [a, b]
    rw [hja_eq]
    exact Finset.le_sup' g hja_mem
  have hsub : (ℝ ∙ u).orthogonalProjectionOnto '' convexHull ℝ (w '' Set.Iic N) ⊆
      lineEquiv u hu '' Set.Icc a b := by
    let φ : ℂ →ₗ[ℝ] ℝ := innerSL ℝ u
    have hconv : Convex ℝ (φ ⁻¹' Set.Icc a b) := (convex_Icc a b).linear_preimage φ
    have hverts : w '' Set.Iic N ⊆ φ ⁻¹' Set.Icc a b := by
      rintro _ ⟨j, hj, rfl⟩
      have hjS : j ∈ S := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
      exact ⟨Finset.inf'_le g hjS, Finset.le_sup' g hjS⟩
    have hhull : convexHull ℝ (w '' Set.Iic N) ⊆ φ ⁻¹' Set.Icc a b :=
      convexHull_min hverts hconv
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟪u, z⟫, hhull hz, (orthogonalProjectionOnto_eq_lineEquiv u hu z).symm⟩
  calc volume ((ℝ ∙ u).orthogonalProjectionOnto '' convexHull ℝ (w '' Set.Iic N))
      ≤ volume (lineEquiv u hu '' Set.Icc a b) := measure_mono hsub
    _ = ENNReal.ofReal (b - a) := volume_image_lineEquiv_Icc u hu a b
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * ∑ j ∈ Finset.range N, |⟪u, w (j + 1) - w j⟫|) := by
        apply ENNReal.ofReal_le_ofReal
        have hg_closed : g N = g 0 := by simp [g, hclosed]
        have hosc := closed_loop_oscillation hg_closed hja hjb
        have hba : b - a = |g jb - g ja| := by
          rw [← hjb_eq, ← hja_eq, abs_of_nonneg (sub_nonneg.mpr hab)]
        have hdiff : ∀ j, |g (j + 1) - g j| = |⟪u, w (j + 1) - w j⟫| := by
          intro j
          simp [g, inner_sub_right]
        simp_rw [hdiff] at hosc
        linarith

private lemma volume_projection_union_le (u : ℂ) (hu : ‖u‖ = 1) (K : Set ℂ)
    (m : ℕ) (n : Fin m → ℕ) (v : Fin m → ℕ → ℂ)
    (hclosed : ∀ i, v i (n i) = v i 0)
    (hcov : K ⊆ ⋃ i, convexHull ℝ (v i '' Set.Iic (n i))) :
    volume ((ℝ ∙ u).orthogonalProjectionOnto '' K) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin m, ∑ j ∈ Finset.range (n i),
        |⟪u, v i (j + 1) - v i j⟫|) := by
  calc volume ((ℝ ∙ u).orthogonalProjectionOnto '' K)
      ≤ volume (⋃ i : Fin m,
          (ℝ ∙ u).orthogonalProjectionOnto '' convexHull ℝ (v i '' Set.Iic (n i))) := by
        apply measure_mono
        rw [← Set.image_iUnion]
        exact Set.image_mono hcov
    _ ≤ ∑ i : Fin m, volume ((ℝ ∙ u).orthogonalProjectionOnto ''
          convexHull ℝ (v i '' Set.Iic (n i))) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin m, ENNReal.ofReal ((1 / 2 : ℝ) *
          ∑ j ∈ Finset.range (n i), |⟪u, v i (j + 1) - v i j⟫|) := by
        exact Finset.sum_le_sum fun i _ => volume_projection_loop_le u hu (n i) (v i) (hclosed i)
    _ = ENNReal.ofReal (∑ i : Fin m, (1 / 2 : ℝ) *
          ∑ j ∈ Finset.range (n i), |⟪u, v i (j + 1) - v i j⟫|) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i _
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ = ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin m, ∑ j ∈ Finset.range (n i),
          |⟪u, v i (j + 1) - v i j⟫|) := by
        rw [Finset.mul_sum]

/- ### Step 3: Cauchy's projection integral over `[0, π]` -/

private def unitVec (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩

private lemma norm_unitVec (θ : ℝ) : ‖unitVec θ‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  dsimp only [unitVec]
  rw [← sq, ← sq, Real.cos_sq_add_sin_sq, Real.sqrt_one]

private lemma inner_unitVec (θ : ℝ) (w : ℂ) :
    ⟪unitVec θ, w⟫ = w.re * Real.cos θ + w.im * Real.sin θ := by
  rw [Complex.inner]
  simp [unitVec]

private lemma abs_inner_unitVec (θ : ℝ) (w : ℂ) :
    |⟪unitVec θ, w⟫| = ‖w‖ * |Real.cos (θ - w.arg)| := by
  rw [inner_unitVec]
  by_cases hw : w = 0
  · subst hw; simp
  · have hre : w.re = ‖w‖ * Real.cos w.arg := by
      have := Complex.cos_arg hw
      field_simp [norm_ne_zero_iff.mpr hw] at this ⊢
      linarith
    have him : w.im = ‖w‖ * Real.sin w.arg := by
      have := Complex.sin_arg w
      field_simp [norm_ne_zero_iff.mpr hw] at this ⊢
      linarith
    rw [hre, him, show ‖w‖ * Real.cos w.arg * Real.cos θ + ‖w‖ * Real.sin w.arg * Real.sin θ =
        ‖w‖ * (Real.cos θ * Real.cos w.arg + Real.sin θ * Real.sin w.arg) by ring,
      ← Real.cos_sub, abs_mul, abs_of_nonneg (norm_nonneg w)]

private lemma integral_abs_cos_zero_pi :
    ∫ t in (0 : ℝ)..Real.pi, |Real.cos t| = 2 := by
  have hcont : Continuous (fun t : ℝ => |Real.cos t|) := Real.continuous_cos.abs
  have h1 : IntervalIntegrable (fun t : ℝ => |Real.cos t|) volume 0 (Real.pi / 2) :=
    hcont.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => |Real.cos t|) volume (Real.pi / 2) Real.pi :=
    hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hint1 : ∫ t in (0 : ℝ)..(Real.pi / 2), |Real.cos t| = 1 := by
    have hcongr : Set.EqOn (fun t => |Real.cos t|) Real.cos (Set.uIcc 0 (Real.pi / 2)) := by
      intro t ht
      rw [Set.uIcc_of_le (by positivity)] at ht
      exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    rw [intervalIntegral.integral_congr hcongr, integral_cos, Real.sin_pi_div_two, Real.sin_zero,
      sub_zero]
  have hint2 : ∫ t in (Real.pi / 2)..Real.pi, |Real.cos t| = 1 := by
    have hcongr : Set.EqOn (fun t => |Real.cos t|) (fun t => -Real.cos t)
        (Set.uIcc (Real.pi / 2) Real.pi) := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
      exact abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht.2, Real.pi_pos]))
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg, integral_cos,
      Real.sin_pi, Real.sin_pi_div_two]
    norm_num
  linarith

private lemma integral_abs_inner_unitVec (w : ℂ) :
    ∫ θ in (0 : ℝ)..Real.pi, |⟪unitVec θ, w⟫| = 2 * ‖w‖ := by
  simp_rw [abs_inner_unitVec]
  rw [intervalIntegral.integral_const_mul]
  have hper : Function.Periodic (fun t : ℝ => |Real.cos t|) Real.pi := by
    intro t
    simp [Real.cos_add_pi]
  have hshift : ∫ θ in (0 : ℝ)..Real.pi, |Real.cos (θ - w.arg)| =
      ∫ t in (0 : ℝ)..Real.pi, |Real.cos t| := by
    rw [intervalIntegral.integral_comp_sub_right (fun t => |Real.cos t|) w.arg]
    have heq : (0 - w.arg) + Real.pi = Real.pi - w.arg := by ring
    rw [← heq]
    simpa [zero_add] using hper.intervalIntegral_add_eq (0 - w.arg) 0
  rw [hshift, integral_abs_cos_zero_pi]
  ring

private lemma continuous_abs_inner_unitVec (w : ℂ) :
    Continuous (fun θ : ℝ => |⟪unitVec θ, w⟫|) := by
  simp_rw [inner_unitVec]
  exact ((continuous_const.mul Real.continuous_cos).add
    (continuous_const.mul Real.continuous_sin)).abs

end

end OMA.Proof_Erdos1043_H2

open scoped RealInnerProductSpace

theorem OMA.solution : OMA.R_Erdos1043_erdos_1043_variants_weak_R1.H2 := by
  intro K m n v C hclosed hcov hperim
  let g : ℝ → ℝ := fun θ =>
    (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j ∈ Finset.range (n i),
      |⟪OMA.Proof_Erdos1043_H2.unitVec θ, v i (j + 1) - v i j⟫|
  have hg_cont : Continuous g := by
    dsimp only [g]
    refine continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ =>
        OMA.Proof_Erdos1043_H2.continuous_abs_inner_unitVec _)
  have hg_int : ∫ θ in (0 : ℝ)..Real.pi, g θ =
      ∑ i : Fin m, ∑ j ∈ Finset.range (n i), ‖v i (j + 1) - v i j‖ := by
    dsimp only [g]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_finsetSum (fun j _ =>
        (OMA.Proof_Erdos1043_H2.continuous_abs_inner_unitVec _).intervalIntegrable _ _)]
      simp_rw [OMA.Proof_Erdos1043_H2.integral_abs_inner_unitVec]
      simp_rw [← Finset.mul_sum]
      ring
    · intro i _
      exact (continuous_finsetSum _ fun j _ =>
        OMA.Proof_Erdos1043_H2.continuous_abs_inner_unitVec _).intervalIntegrable _ _
  have hex : ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, g θ ≤ C := by
    by_contra h
    push Not at h
    have hle : ∫ _θ in (0 : ℝ)..Real.pi, C ≤ ∫ θ in (0 : ℝ)..Real.pi, g θ := by
      apply intervalIntegral.integral_mono_on Real.pi_pos.le
        intervalIntegrable_const (hg_cont.intervalIntegrable _ _)
      intro θ hθ
      exact le_of_lt (h θ hθ)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, hg_int] at hle
    linarith
  obtain ⟨θ, _, hθ⟩ := hex
  refine ⟨OMA.Proof_Erdos1043_H2.unitVec θ, OMA.Proof_Erdos1043_H2.norm_unitVec θ, ?_⟩
  exact (OMA.Proof_Erdos1043_H2.volume_projection_union_le
    (OMA.Proof_Erdos1043_H2.unitVec θ) (OMA.Proof_Erdos1043_H2.norm_unitVec θ)
    K m n v hclosed hcov).trans (ENNReal.ofReal_le_ofReal hθ)
