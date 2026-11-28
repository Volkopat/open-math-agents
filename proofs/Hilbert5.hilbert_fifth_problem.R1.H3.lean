import OMAReductions.R_Hilbert5_hilbert_fifth_problem_R1
import Mathlib

/-!
# Cartan's Automatic Analyticity (`Hilbert5.R1.H3`)

Every continuous group homomorphism `α : L →* L` of a finite-dimensional real-analytic
Lie group is real-analytic (`ContMDiff (𝓡 n) (𝓡 n) ω α`).

Proof outline:
1. By left-translation invariance of `LieGroup (𝓡 n) ω L`, reduce to `AnalyticAt ℝ f 0`
   for the chart-conjugate continuous local homomorphism `f : E → E` of the real-analytic
   local group `(μ, ι)` on `E = EuclideanSpace ℝ (Fin n)`.
2. Prove `HasFDerivAt f A 0` by averaging against a smooth compactly supported bump
   `ContDiffBump.normed`, applying the change of variables formula (`integral_image_eq_integral_abs_det_fderiv_smul`),
   differentiation under the integral (`hasFDerivAt_integral_of_dominated_loc_of_lip`),
   and the strict local inverse theorem (`HasStrictFDerivAt.localInverse`).
3. Translate `HasFDerivAt f A 0` via `f u = μ (f x, f (μ (ι x, u)))` to obtain the
   real-analytic radial ODE `z'(t) = F (z t) v` for `z(t) = (t • v, f (t • v))`.
4. Solve `z'(t) = F (z t) v` with an explicit multilinear power series `c_k` bounded by
   the Cauchy majorant `A * B^(k - 1) / k^2`, identify `z` with the series via Gronwall
   uniqueness (`ODE_solution_unique_of_mem_Icc`), and conclude `AnalyticAt ℝ f 0`.

Credit: @yhay81
-/

namespace Hilbert5R1H3

open Filter Set Topology Metric MeasureTheory
open scoped Manifold ContDiff BigOperators ENNReal NNReal

/- ### Part 0: Smoothness of `ContinuousLinearMap.det` on `EuclideanSpace ℝ (Fin n)` -/

private lemma contDiff_det_euclidean (n : ℕ) :
    ContDiff ℝ ∞ (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T.det) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hdet : (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T.det) =
      fun T => ∑ σ : Equiv.Perm (Fin n),
        (Equiv.Perm.sign σ : ℝ) * ∏ i : Fin n, (T (b i)) (σ i) := by
    ext T
    change LinearMap.det (T.toLinearMap) = _
    rw [← LinearMap.det_toMatrix b.toBasis, Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    change (LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap) (σ i) i = (T (b i)) (σ i)
    simp [LinearMap.toMatrix_apply, b]
  rw [hdet]
  refine ContDiff.sum (fun σ _ => ContDiff.mul contDiff_const (contDiff_prod (fun i _ => ?_)))
  have hlin : ContDiff ℝ ∞
      (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        (EuclideanSpace.proj (σ i)).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (b i)) T) :=
    ContinuousLinearMap.contDiff _
  exact hlin

/- ### Part 1: Local-group structure and bump-averaging differentiability at 0 -/

private structure LocalAnalyticGroupHom (n : ℕ) where
  μ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  ι : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  ρ : ℝ
  hρ : 0 < ρ
  hμ_an : AnalyticAt ℝ μ (0, 0)
  hι_an : AnalyticAt ℝ ι 0
  hf_cont : ContinuousOn f (ball 0 ρ)
  hf_zero : f 0 = 0
  hι_zero : ι 0 = 0
  hμ_left_id : ∀ y ∈ ball 0 ρ, μ (0, y) = y
  hμ_right_id : ∀ x ∈ ball 0 ρ, μ (x, 0) = x
  hμ_assoc : ∀ x ∈ ball 0 ρ, ∀ y ∈ ball 0 ρ, ∀ z ∈ ball 0 ρ, μ (x, μ (y, z)) = μ (μ (x, y), z)
  hμ_inv_left : ∀ x ∈ ball 0 ρ, ∀ y ∈ ball 0 ρ, μ (ι x, μ (x, y)) = y
  hμ_inv_right : ∀ x ∈ ball 0 ρ, ∀ z ∈ ball 0 ρ, μ (x, μ (ι x, z)) = z
  hf_hom : ∀ x ∈ ball 0 ρ, ∀ y ∈ ball 0 ρ, f (μ (x, y)) = μ (f x, f y)

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma exists_radius_contDiffOn {n : ℕ} (G : LocalAnalyticGroupHom n) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ρ₁ ≤ G.ρ ∧
      ContDiffOn ℝ 2 G.μ (ball (0, 0) ρ₁) ∧
      ContDiffOn ℝ 2 G.ι (ball 0 ρ₁) := by
  have hμ2 : ContDiffAt ℝ 2 G.μ (0, 0) :=
    (G.hμ_an.contDiffAt (n := ω)).of_le (by simp)
  have hι2 : ContDiffAt ℝ 2 G.ι 0 :=
    (G.hι_an.contDiffAt (n := ω)).of_le (by simp)
  obtain ⟨u, hu, hμu⟩ := hμ2.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨v, hv, hιv⟩ := hι2.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r₁, hr₁, hbr₁⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨r₂, hr₂, hbr₂⟩ := Metric.mem_nhds_iff.mp hv
  have hρ_pos : 0 < G.ρ := G.hρ
  refine ⟨min G.ρ (min r₁ r₂), by positivity, min_le_left _ _, ?_, ?_⟩
  · exact hμu.mono ((Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))).trans hbr₁)
  · exact hιv.mono ((Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))).trans hbr₂)

private lemma hasFDerivAt_D1_D2_at_zero {n : ℕ} (G : LocalAnalyticGroupHom n) :
    (fderiv ℝ G.μ (0, 0)).comp (ContinuousLinearMap.inl ℝ (E n) (E n)) =
      ContinuousLinearMap.id ℝ (E n) ∧
    (fderiv ℝ G.μ (0, 0)).comp (ContinuousLinearMap.inr ℝ (E n) (E n)) =
      ContinuousLinearMap.id ℝ (E n) := by
  have hμ_diff : HasFDerivAt G.μ (fderiv ℝ G.μ (0, 0)) (0, 0) :=
    G.hμ_an.differentiableAt.hasFDerivAt
  constructor
  · have hcomp : HasFDerivAt (fun x : E n => G.μ (x, 0))
        ((fderiv ℝ G.μ (0, 0)).comp (ContinuousLinearMap.inl ℝ (E n) (E n))) 0 := by
      have hμ' : HasFDerivAt G.μ (fderiv ℝ G.μ (0, 0)) ((ContinuousLinearMap.inl ℝ (E n) (E n)) 0) := by
        simpa using hμ_diff
      exact HasFDerivAt.comp 0 (g := G.μ) (f := ContinuousLinearMap.inl ℝ (E n) (E n))
        hμ' (ContinuousLinearMap.inl ℝ (E n) (E n)).hasFDerivAt
    have heq : (fun x : E n => G.μ (x, 0)) =ᶠ[𝓝 0] id :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 G.hρ) (fun x hx => G.hμ_right_id x hx)
    exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id 0)
  · have hcomp : HasFDerivAt (fun y : E n => G.μ (0, y))
        ((fderiv ℝ G.μ (0, 0)).comp (ContinuousLinearMap.inr ℝ (E n) (E n))) 0 := by
      have hμ' : HasFDerivAt G.μ (fderiv ℝ G.μ (0, 0)) ((ContinuousLinearMap.inr ℝ (E n) (E n)) 0) := by
        simpa using hμ_diff
      exact HasFDerivAt.comp 0 (g := G.μ) (f := ContinuousLinearMap.inr ℝ (E n) (E n))
        hμ' (ContinuousLinearMap.inr ℝ (E n) (E n)).hasFDerivAt
    have heq : (fun y : E n => G.μ (0, y)) =ᶠ[𝓝 0] id :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 G.hρ) (fun y hy => G.hμ_left_id y hy)
    exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id 0)

set_option maxHeartbeats 800000 in
private lemma hasFDerivAt_zero_of_local_hom {n : ℕ} (G : LocalAnalyticGroupHom n) :
    ∃ A : E n →L[ℝ] E n, HasFDerivAt G.f A 0 := by
  obtain ⟨ρ₁, hρ₁, hρ₁_le, hμ2, hι2⟩ := exists_radius_contDiffOn G
  have hμ_diff : ∀ p ∈ ball (0, 0) ρ₁, DifferentiableAt ℝ G.μ p := fun p hp =>
    (hμ2.contDiffAt (Metric.isOpen_ball.mem_nhds hp)).differentiableAt (by decide)
  have hι_diff : ∀ x ∈ ball 0 ρ₁, DifferentiableAt ℝ G.ι x := fun x hx =>
    (hι2.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by decide)
  let D1 : E n × E n → (E n →L[ℝ] E n) :=
    fun p => (fderiv ℝ G.μ p).comp (ContinuousLinearMap.inl ℝ (E n) (E n))
  let D2 : E n × E n → (E n →L[ℝ] E n) :=
    fun p => (fderiv ℝ G.μ p).comp (ContinuousLinearMap.inr ℝ (E n) (E n))
  have hD1_cont : ContDiffOn ℝ 1 D1 (ball (0, 0) ρ₁) := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ G.μ) (ball (0, 0) ρ₁) :=
      hμ2.fderiv_of_isOpen Metric.isOpen_ball (m := 1) (by decide)
    exact (ContinuousLinearMap.compL ℝ (E n) (E n × E n) (E n)
      |>.flip (ContinuousLinearMap.inl ℝ (E n) (E n))).contDiff.comp_contDiffOn hfd
  have hD2_cont : ContDiffOn ℝ 1 D2 (ball (0, 0) ρ₁) := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ G.μ) (ball (0, 0) ρ₁) :=
      hμ2.fderiv_of_isOpen Metric.isOpen_ball (m := 1) (by decide)
    exact (ContinuousLinearMap.compL ℝ (E n) (E n × E n) (E n)
      |>.flip (ContinuousLinearMap.inr ℝ (E n) (E n))).contDiff.comp_contDiffOn hfd
  have hD1_zero : D1 (0, 0) = ContinuousLinearMap.id ℝ (E n) := (hasFDerivAt_D1_D2_at_zero G).1
  have hD2_zero : D2 (0, 0) = ContinuousLinearMap.id ℝ (E n) := (hasFDerivAt_D1_D2_at_zero G).2
  have hf_contAt0 : ContinuousAt G.f 0 := G.hf_cont.continuousAt (Metric.ball_mem_nhds 0 G.hρ)
  have hι_contAt0 : ContinuousAt G.ι 0 := G.hι_an.continuousAt
  -- Choose r₁ > 0 small enough that f and ι stay inside ball 0 (ρ₁ / 4) and ‖D1 (0, f y) - id‖ ≤ 1/2
  have hD1_ev : ∀ᶠ y in 𝓝 (0 : E n),
      G.f y ∈ ball 0 (ρ₁ / 4) ∧ ‖D1 (0, G.f y) - ContinuousLinearMap.id ℝ (E n)‖ ≤ 1 / 2 := by
    have h1 : ∀ᶠ y in 𝓝 (0 : E n), G.f y ∈ ball 0 (ρ₁ / 4) :=
      hf_contAt0.eventually (by rw [G.hf_zero]; exact Metric.ball_mem_nhds 0 (by positivity))
    have h2 : ContinuousAt (fun y => D1 (0, G.f y)) 0 := by
      have hD1_at0 : ContinuousAt D1 (0, G.f 0) := by
        rw [G.hf_zero]
        exact hD1_cont.continuousOn.continuousAt (Metric.ball_mem_nhds (0, 0) hρ₁)
      have hpair : ContinuousAt (fun y : E n => ((0 : E n), G.f y)) 0 :=
        continuousAt_const.prodMk hf_contAt0
      exact ContinuousAt.comp (g := D1) (f := fun y : E n => ((0 : E n), G.f y)) hD1_at0 hpair
    have h3 : ∀ᶠ y in 𝓝 (0 : E n), ‖D1 (0, G.f y) - ContinuousLinearMap.id ℝ (E n)‖ < 1 / 2 := by
      have := h2.eventually (Metric.ball_mem_nhds (D1 (0, G.f 0)) (by norm_num : (0 : ℝ) < 1 / 2))
      filter_upwards [this] with y hy
      simpa [G.hf_zero, hD1_zero, Metric.mem_ball, dist_eq_norm] using hy
    filter_upwards [h1, h3] with y hy1 hy3
    exact ⟨hy1, hy3.le⟩
  obtain ⟨r_a, hr_a, hbr_a⟩ := Metric.mem_nhds_iff.mp hD1_ev
  obtain ⟨r_ι, hr_ι, hbr_ι⟩ := Metric.mem_nhds_iff.mp
    (hι_contAt0.eventually (by rw [G.hι_zero]; exact Metric.ball_mem_nhds 0 (by positivity : 0 < ρ₁ / 4)))
  set r₁ : ℝ := min (ρ₁ / 8) (min (r_a / 4) (r_ι / 4))
  have hr₁ : 0 < r₁ := by positivity
  have h4r₁ : 4 * r₁ ≤ ρ₁ / 2 := by
    have : r₁ ≤ ρ₁ / 8 := min_le_left _ _; linarith
  have hr₁_ra : 3 * r₁ < r_a := by
    have : r₁ ≤ r_a / 4 := le_trans (min_le_right _ _) (min_le_left _ _); linarith
  have hr₁_rι : 3 * r₁ < r_ι := by
    have : r₁ ≤ r_ι / 4 := le_trans (min_le_right _ _) (min_le_right _ _); linarith
  -- Construct normalized smooth bump ψ supported in ball 0 r₁
  let φ : ContDiffBump (0 : E n) := ⟨r₁ / 2, r₁, by positivity, by linarith⟩
  let ψ : E n → ℝ := φ.normed volume
  have hψ_nonneg : ∀ y, 0 ≤ ψ y := φ.nonneg_normed
  have hψ_int1 : ∫ y in ball 0 r₁, ψ y = 1 := by
    have hsupp : Function.support ψ ⊆ ball 0 r₁ := by rw [φ.support_normed_eq]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact φ.integral_normed
    · intro y hy
      by_contra hne
      exact hy (hsupp hne)
  have hψ_contDiff : ContDiff ℝ 1 ψ := φ.contDiff_normed
  -- Choose r₀ > 0 small enough for change of variables and positive determinant on closedBall 0 (2*r₁)
  have hK_compact : IsCompact (closedBall (0 : E n) (2 * r₁)) := isCompact_closedBall 0 (2 * r₁)
  have hdet_pos : ∀ᶠ x in 𝓝 (0 : E n), ∀ z ∈ closedBall (0 : E n) (2 * r₁),
      0 < (D2 (G.ι x, z)).det ∧ G.μ (G.ι x, z) ∈ ball 0 (3 * r₁) := by
    have htube : ∀ z : E n, ∃ U V : Set (E n),
        z ∈ closedBall (0 : E n) (2 * r₁) →
          U ∈ 𝓝 (0 : E n) ∧ V ∈ 𝓝 z ∧ ∀ x ∈ U, ∀ w ∈ V,
            0 < (D2 (G.ι x, w)).det ∧ G.μ (G.ι x, w) ∈ ball 0 (3 * r₁) := by
      intro z
      by_cases hz : z ∈ closedBall (0 : E n) (2 * r₁)
      · have hz_ball : z ∈ ball (0 : E n) ρ₁ := by
          rw [Metric.mem_ball, dist_zero_right]
          have := Metric.mem_closedBall.mp hz; rw [dist_zero_right] at this; linarith only [this, h4r₁, hr₁]
        have hfst : ContinuousAt (fun q : E n × E n => G.ι q.1) (0, z) :=
          ContinuousAt.comp (g := G.ι) (f := Prod.fst) hι_contAt0 continuousAt_fst
        have hpair_at : ContinuousAt (fun q : E n × E n => (G.ι q.1, q.2)) (0, z) :=
          hfst.prodMk continuousAt_snd
        have h0z : ((0 : E n), z) ∈ ball ((0 : E n), (0 : E n)) ρ₁ := by
          rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
          exact ⟨hρ₁, Metric.mem_ball.mp hz_ball⟩
        have hD2_at : ContinuousAt D2 (G.ι 0, z) := by
          rw [G.hι_zero]
          exact hD2_cont.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0z)
        have hdet_at : ContinuousAt (fun q : E n × E n => (D2 (G.ι q.1, q.2)).det) (0, z) := by
          have h1 : ContinuousAt (fun T : E n →L[ℝ] E n => T.det) (D2 (G.ι 0, z)) :=
            (contDiff_det_euclidean n).continuous.continuousAt
          have h2 : ContinuousAt (fun q : E n × E n => D2 (G.ι q.1, q.2)) (0, z) :=
            ContinuousAt.comp (g := D2) (f := fun q : E n × E n => (G.ι q.1, q.2)) hD2_at hpair_at
          exact ContinuousAt.comp (g := fun T : E n →L[ℝ] E n => T.det)
            (f := fun q : E n × E n => D2 (G.ι q.1, q.2)) h1 h2
        have hD2_0z : D2 (0, z) = ContinuousLinearMap.id ℝ (E n) := by
          have hμ_at : HasFDerivAt G.μ (fderiv ℝ G.μ (0, z)) (0, z) := (hμ_diff (0, z) h0z).hasFDerivAt
          have hcomp : HasFDerivAt (fun w : E n => G.μ (0, w)) (D2 (0, z)) z :=
            hμ_at.comp z ((hasFDerivAt_const (0 : E n) z).prodMk (hasFDerivAt_id z))
          have heq : (fun w : E n => G.μ (0, w)) =ᶠ[𝓝 z] id :=
            Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρ₁_le hz_ball))
              (fun w hw => G.hμ_left_id w hw)
          exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id z)
        have hdet_val : (D2 (G.ι 0, z)).det = 1 := by
          rw [G.hι_zero, hD2_0z]; exact LinearMap.det_id
        have hμ_at : ContinuousAt (fun q : E n × E n => G.μ (G.ι q.1, q.2)) (0, z) := by
          have h1 : ContinuousAt G.μ (G.ι 0, z) := by
            rw [G.hι_zero]; exact (hμ_diff (0, z) h0z).continuousAt
          exact ContinuousAt.comp (g := G.μ) (f := fun q : E n × E n => (G.ι q.1, q.2)) h1 hpair_at
        have hμ_val : G.μ (G.ι 0, z) ∈ ball 0 (3 * r₁) := by
          rw [G.hι_zero, G.hμ_left_id z (Metric.ball_subset_ball hρ₁_le hz_ball)]
          rw [Metric.mem_ball, dist_zero_right]
          have := Metric.mem_closedBall.mp hz; rw [dist_zero_right] at this; linarith only [this, hr₁]
        have hev1 : ∀ᶠ q in 𝓝 ((0 : E n), z), 0 < (D2 (G.ι q.1, q.2)).det :=
          hdet_at.eventually (by dsimp only; rw [hdet_val]; exact Ioi_mem_nhds zero_lt_one)
        have hev2 : ∀ᶠ q in 𝓝 ((0 : E n), z), G.μ (G.ι q.1, q.2) ∈ ball 0 (3 * r₁) :=
          hμ_at.eventually (Metric.isOpen_ball.mem_nhds hμ_val)
        rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev1 hev2
        obtain ⟨p1, hp1, q1, hq1, hpq1⟩ := hev1
        obtain ⟨p2, hp2, q2, hq2, hpq2⟩ := hev2
        refine ⟨{x | p1 x ∧ p2 x}, {w | q1 w ∧ q2 w}, fun _ =>
          ⟨Filter.inter_mem hp1 hp2, Filter.inter_mem hq1 hq2, fun x hx w hw =>
            ⟨hpq1 hx.1 hw.1, hpq2 hx.2 hw.2⟩⟩⟩
      · exact ⟨univ, univ, fun h => (hz h).elim⟩
    choose U V hUV using htube
    have hcov : closedBall (0 : E n) (2 * r₁) ⊆ ⋃ z ∈ closedBall (0 : E n) (2 * r₁), interior (V z) := by
      intro z hz
      exact Set.mem_biUnion hz (mem_interior_iff_mem_nhds.mpr (hUV z hz).2.1)
    obtain ⟨t, ht_sub, ht_fin, ht_cov⟩ := hK_compact.elim_finite_subcover_image
      (fun z _ => isOpen_interior) hcov
    have hU_mem : (⋂ z ∈ t, U z) ∈ 𝓝 (0 : E n) :=
      (Filter.biInter_mem ht_fin).mpr (fun z hz => (hUV z (ht_sub hz)).1)
    filter_upwards [hU_mem] with x hx z hz
    obtain ⟨z₀, hz₀t, hzz₀⟩ := Set.mem_iUnion₂.mp (ht_cov hz)
    exact (hUV z₀ (ht_sub hz₀t)).2.2 x (Set.mem_iInter₂.mp hx z₀ hz₀t) z (interior_subset hzz₀)
  have hshift_ball : ∀ᶠ x in 𝓝 (0 : E n), ∀ y ∈ closedBall (0 : E n) r₁,
      G.μ (x, y) ∈ ball 0 (2 * r₁) := by
    have htube : ∀ y : E n, ∃ U V : Set (E n),
        y ∈ closedBall (0 : E n) r₁ →
          U ∈ 𝓝 (0 : E n) ∧ V ∈ 𝓝 y ∧ ∀ x ∈ U, ∀ w ∈ V, G.μ (x, w) ∈ ball 0 (2 * r₁) := by
      intro y
      by_cases hy : y ∈ closedBall (0 : E n) r₁
      · have hy_ball : y ∈ ball (0 : E n) ρ₁ := by
          rw [Metric.mem_ball, dist_zero_right]
          have := Metric.mem_closedBall.mp hy; rw [dist_zero_right] at this; linarith only [this, h4r₁, hr₁]
        have h0y : ((0 : E n), y) ∈ ball ((0 : E n), (0 : E n)) ρ₁ := by
          rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
          exact ⟨hρ₁, Metric.mem_ball.mp hy_ball⟩
        have hμ_at : ContinuousAt G.μ (0, y) := (hμ_diff (0, y) h0y).continuousAt
        have hval : G.μ (0, y) ∈ ball 0 (2 * r₁) := by
          rw [G.hμ_left_id y (Metric.ball_subset_ball hρ₁_le hy_ball), Metric.mem_ball, dist_zero_right]
          have := Metric.mem_closedBall.mp hy; rw [dist_zero_right] at this; linarith only [this, hr₁]
        have hev : ∀ᶠ q in 𝓝 ((0 : E n), y), G.μ q ∈ ball 0 (2 * r₁) :=
          hμ_at.eventually (Metric.isOpen_ball.mem_nhds hval)
        rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev
        obtain ⟨p1, hp1, q1, hq1, hpq⟩ := hev
        exact ⟨{x | p1 x}, {w | q1 w}, fun _ => ⟨hp1, hq1, fun x hx w hw => hpq hx hw⟩⟩
      · exact ⟨univ, univ, fun h => (hy h).elim⟩
    choose U V hUV using htube
    have hcov : closedBall (0 : E n) r₁ ⊆ ⋃ y ∈ closedBall (0 : E n) r₁, interior (V y) :=
      fun y hy => Set.mem_biUnion hy (mem_interior_iff_mem_nhds.mpr (hUV y hy).2.1)
    obtain ⟨t, ht_sub, ht_fin, ht_cov⟩ := (isCompact_closedBall (0 : E n) r₁).elim_finite_subcover_image
      (fun y _ => isOpen_interior) hcov
    have hU_mem : (⋂ y ∈ t, U y) ∈ 𝓝 (0 : E n) :=
      (Filter.biInter_mem ht_fin).mpr (fun y hy => (hUV y (ht_sub hy)).1)
    filter_upwards [hU_mem] with x hx y hy
    obtain ⟨y₀, hy₀t, hyy₀⟩ := Set.mem_iUnion₂.mp (ht_cov hy)
    exact (hUV y₀ (ht_sub hy₀t)).2.2 x (Set.mem_iInter₂.mp hx y₀ hy₀t) y (interior_subset hyy₀)
  obtain ⟨r₀, hr₀, hbr₀⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hdet_pos hshift_ball)
  set r₂ : ℝ := min (r₀ / 2) (r₁ / 2)
  have hr₂ : 0 < r₂ := by positivity
  -- Define Ψ and H
  let Ψ : E n → E n := fun w => ∫ y in ball 0 r₁, ψ y • G.μ (w, G.f y)
  let K : E n × E n → ℝ := fun p => (D2 (G.ι p.1, p.2)).det * ψ (G.μ (G.ι p.1, p.2))
  let H : E n → E n := fun x => ∫ z in ball 0 (2 * r₁), K (x, z) • G.f z
  -- Prove Ψ (G.f x) = H x for x ∈ ball 0 r₂
  have hΨH : ∀ x ∈ ball 0 r₂, Ψ (G.f x) = H x := by
    intro x hx
    have hxr₀ : x ∈ ball 0 r₀ := Metric.ball_subset_ball (by
      have : r₂ ≤ r₀ / 2 := min_le_left _ _; linarith) hx
    have hxr₁ : x ∈ ball 0 r₁ := Metric.ball_subset_ball (by
      have : r₂ ≤ r₁ / 2 := min_le_right _ _; linarith) hx
    have hxrρ : x ∈ ball 0 G.ρ := Metric.ball_subset_ball (by linarith) hxr₁
    have hιx_ball : G.ι x ∈ ball 0 (ρ₁ / 4) := hbr_ι (Metric.ball_subset_ball (by linarith) hxr₁)
    let S : E n → E n := fun z => G.μ (G.ι x, z)
    let U : Set (E n) := ball 0 (2 * r₁)
    have hS_fderiv : ∀ z ∈ U, HasFDerivWithinAt S (D2 (G.ι x, z)) U z := by
      intro z hz
      have hp : (G.ι x, z) ∈ ball ((0 : E n), (0 : E n)) ρ₁ := by
        rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        exact ⟨by have := Metric.mem_ball.mp hιx_ball; linarith,
               by have := Metric.mem_ball.mp hz; linarith⟩
      have h1 : HasFDerivAt G.μ (fderiv ℝ G.μ (G.ι x, z)) (G.ι x, z) := (hμ_diff _ hp).hasFDerivAt
      have h2 : HasFDerivAt S (D2 (G.ι x, z)) z :=
        h1.comp z ((hasFDerivAt_const (G.ι x) z).prodMk (hasFDerivAt_id z))
      exact h2.hasFDerivWithinAt
    have hS_inj : Set.InjOn S U := by
      intro z₁ hz₁ z₂ hz₂ heq
      have hz₁ρ : z₁ ∈ ball 0 G.ρ := Metric.ball_subset_ball (by linarith) hz₁
      have hz₂ρ : z₂ ∈ ball 0 G.ρ := Metric.ball_subset_ball (by linarith) hz₂
      have h1 := G.hμ_inv_right x hxrρ z₁ hz₁ρ
      have h2 := G.hμ_inv_right x hxrρ z₂ hz₂ρ
      calc z₁ = G.μ (x, S z₁) := h1.symm
        _ = G.μ (x, S z₂) := by rw [heq]
        _ = z₂ := h2
    have hcov_ball : ball 0 r₁ ⊆ S '' U := by
      intro y hy
      have hy_cl : y ∈ closedBall 0 r₁ := Metric.ball_subset_closedBall hy
      have hzU : G.μ (x, y) ∈ U := (hbr₀ hxr₀).2 y hy_cl
      refine ⟨G.μ (x, y), hzU, ?_⟩
      exact G.hμ_inv_left x hxrρ y (Metric.ball_subset_ball (by linarith) hy)
    have hchg := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
      Metric.isOpen_ball.measurableSet hS_fderiv hS_inj (fun y => ψ y • G.f (G.μ (x, y)))
    have hS_cont : ContinuousOn S U := fun z hz => (hS_fderiv z hz).continuousWithinAt
    have hSU_meas : NullMeasurableSet (S '' U) volume :=
      (Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hS_cont hS_inj).nullMeasurableSet
    have hLHS : ∫ y in S '' U, ψ y • G.f (G.μ (x, y)) = Ψ (G.f x) := by
      have heq1 : ∫ y in S '' U, ψ y • G.f (G.μ (x, y)) = ∫ y in ball 0 r₁, ψ y • G.f (G.μ (x, y)) := by
        apply MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hSU_meas hcov_ball
        filter_upwards with y hy
        have hy_not : y ∉ Function.support ψ := by rw [φ.support_normed_eq]; exact hy.2
        simp [Function.notMem_support.mp hy_not]
      rw [heq1]
      apply MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro y hy
      dsimp only
      rw [G.hf_hom x hxrρ y (Metric.ball_subset_ball (by linarith only [h4r₁, hr₁, hρ₁_le]) hy)]
    have hRHS : ∫ z in U, |(D2 (G.ι x, z)).det| • (ψ (S z) • G.f (G.μ (x, S z))) = H x := by
      apply MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro z hz
      have hz_cl : z ∈ closedBall 0 (2 * r₁) := Metric.ball_subset_closedBall hz
      have hdet_gt : 0 < (D2 (G.ι x, z)).det := ((hbr₀ hxr₀).1 z hz_cl).1
      dsimp only
      rw [abs_of_pos hdet_gt, G.hμ_inv_right x hxrρ z (Metric.ball_subset_ball (by linarith only [h4r₁, hr₁, hρ₁_le]) hz),
        smul_smul]
    rw [← hLHS, hchg, hRHS]
  -- Step A: HasFDerivAt H H' 0
  have hH_diff : DifferentiableAt ℝ H 0 := by
    have hK_c1 : ContDiffOn ℝ 1 K (ball 0 (3 * r₂ / 2) ×ˢ ball 0 (5 * r₁ / 2)) := by
      have hι_c1 : ContDiffOn ℝ 1 G.ι (ball 0 (3 * r₂ / 2)) :=
        (hι2.of_le (by decide)).mono (Metric.ball_subset_ball (by
          have : r₂ ≤ r₁ / 2 := min_le_right _ _; linarith only [this, h4r₁, hr₁]))
      have hpair : ContDiffOn ℝ 1 (fun p : E n × E n => (G.ι p.1, p.2))
          (ball 0 (3 * r₂ / 2) ×ˢ ball 0 (5 * r₁ / 2)) :=
        (hι_c1.comp contDiffOn_fst (fun p hp => hp.1)).prodMk contDiffOn_snd
      have hmaps : MapsTo (fun p : E n × E n => (G.ι p.1, p.2))
          (ball 0 (3 * r₂ / 2) ×ˢ ball 0 (5 * r₁ / 2)) (ball (0, 0) ρ₁) := by
        intro p hp
        rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        have hr2_r1 : r₂ ≤ r₁ / 2 := min_le_right _ _
        have hp1 : p.1 ∈ ball 0 r_ι := Metric.ball_subset_ball (by linarith only [hr2_r1, hr₁_rι, hr₁]) hp.1
        have hιp_mem : G.ι p.1 ∈ ball 0 (ρ₁ / 4) := hbr_ι hp1
        have hιp := Metric.mem_ball.mp hιp_mem
        have hp2 := Metric.mem_ball.mp hp.2
        exact ⟨by linarith only [hιp, hρ₁], by linarith only [hp2, h4r₁, hr₁]⟩
      have h1 : ContDiffOn ℝ 1 (fun p : E n × E n => (D2 (G.ι p.1, p.2)).det)
          (ball 0 (3 * r₂ / 2) ×ˢ ball 0 (5 * r₁ / 2)) :=
        ((contDiff_det_euclidean n).of_le (by decide)).comp_contDiffOn (hD2_cont.comp hpair hmaps)
      have h2 : ContDiffOn ℝ 1 (fun p : E n × E n => ψ (G.μ (G.ι p.1, p.2)))
          (ball 0 (3 * r₂ / 2) ×ˢ ball 0 (5 * r₁ / 2)) :=
        hψ_contDiff.comp_contDiffOn ((hμ2.of_le (by decide)).comp hpair hmaps)
      exact h1.mul h2
    have hK_c1_sub : ContDiffOn ℝ 1 K (closedBall 0 r₂ ×ˢ closedBall 0 (2 * r₁)) :=
      hK_c1.mono (Set.prod_mono (Metric.closedBall_subset_ball (by linarith))
        (Metric.closedBall_subset_ball (by linarith)))
    let Kx : E n × E n → (E n →L[ℝ] ℝ) := fun p =>
      (fderiv ℝ K p).comp (ContinuousLinearMap.inl ℝ (E n) (E n))
    have hKx_cont : ContinuousOn Kx (closedBall 0 r₂ ×ˢ closedBall 0 (2 * r₁)) := by
      have hfd : ContinuousOn (fderiv ℝ K) (ball 0 (3 * r₂ / 2) ×ˢ ball 0 (5 * r₁ / 2)) :=
        hK_c1.continuousOn_fderiv_of_isOpen (Metric.isOpen_ball.prod Metric.isOpen_ball) le_rfl
      have hsub : closedBall (0 : E n) r₂ ×ˢ closedBall (0 : E n) (2 * r₁) ⊆
          ball (0 : E n) (3 * r₂ / 2) ×ˢ ball (0 : E n) (5 * r₁ / 2) :=
        Set.prod_mono (Metric.closedBall_subset_ball (by linarith only [hr₂]))
          (Metric.closedBall_subset_ball (by linarith only [hr₁]))
      exact ((ContinuousLinearMap.compL ℝ (E n) (E n × E n) ℝ
        |>.flip (ContinuousLinearMap.inl ℝ (E n) (E n))).continuous.comp_continuousOn (hfd.mono hsub))
    obtain ⟨M_K, hMK⟩ := ((isCompact_closedBall (0 : E n) r₂).prod hK_compact).exists_bound_of_continuousOn hKx_cont
    obtain ⟨M_f, hMf⟩ := hK_compact.exists_bound_of_continuousOn
      (G.hf_cont.mono (Metric.closedBall_subset_ball (by linarith)))
    set M : ℝ := max 0 M_K * max 0 M_f
    have hM_nn : 0 ≤ M := by positivity
    let μU : Measure (E n) := volume.restrict (ball 0 (2 * r₁))
    have : IsFiniteMeasure μU := ⟨by
      rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top⟩
    have hK_fderiv : ∀ x ∈ ball 0 r₂, ∀ z ∈ ball 0 (2 * r₁),
        HasFDerivAt (fun x' => K (x', z) • G.f z) ((Kx (x, z)).smulRight (G.f z)) x := by
      intro x hx z hz
      have hp : (x, z) ∈ ball 0 (3 * r₂ / 2) ×ˢ ball 0 (5 * r₁ / 2) :=
        ⟨Metric.ball_subset_ball (by linarith) hx, Metric.ball_subset_ball (by linarith) hz⟩
      have hKd : HasFDerivAt K (fderiv ℝ K (x, z)) (x, z) :=
        (hK_c1.differentiableOn (by decide) (x, z) hp).differentiableAt
          ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hp) |>.hasFDerivAt
      have hKxd : HasFDerivAt (fun x' => K (x', z)) (Kx (x, z)) x := by
        have hpair : HasFDerivAt (fun x' : E n => (x', z)) (ContinuousLinearMap.inl ℝ (E n) (E n)) x :=
          (hasFDerivAt_id x).prodMk (hasFDerivAt_const z x)
        exact HasFDerivAt.comp x (g := K) (f := fun x' : E n => (x', z)) hKd hpair
      exact hKxd.smul_const (G.f z)
    have hres := hasFDerivAt_integral_of_dominated_loc_of_lip
      (μ := μU) (s := ball 0 r₂) (x₀ := 0) (bound := fun _ => M)
      (F := fun x z => K (x, z) • G.f z) (F' := fun z => (Kx (0, z)).smulRight (G.f z))
      (Metric.ball_mem_nhds 0 hr₂)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr₂) fun x hx => by
        refine (ContinuousOn.aestronglyMeasurable ?_ Metric.isOpen_ball.measurableSet)
        have h1 : ContinuousOn (fun z => K (x, z)) (ball 0 (2 * r₁)) :=
          hK_c1_sub.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
            (fun z hz => ⟨Metric.ball_subset_closedBall hx, Metric.ball_subset_closedBall hz⟩)
        exact h1.smul (G.hf_cont.mono (Metric.ball_subset_ball (by linarith))))
      (by
        have hcont : ContinuousOn (fun z => K (0, z) • G.f z) (closedBall 0 (2 * r₁)) := by
          have h1 : ContinuousOn (fun z => K (0, z)) (closedBall 0 (2 * r₁)) :=
            hK_c1_sub.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
              (fun z hz => ⟨Metric.mem_closedBall_self hr₂.le, hz⟩)
          exact h1.smul (G.hf_cont.mono (Metric.closedBall_subset_ball (by linarith)))
        exact (hcont.integrableOn_compact hK_compact).mono_set Metric.ball_subset_closedBall)
      (by
        refine ContinuousOn.aestronglyMeasurable ?_ Metric.isOpen_ball.measurableSet
        have h1 : ContinuousOn (fun z => Kx (0, z)) (ball 0 (2 * r₁)) :=
          hKx_cont.comp (continuousOn_const.prodMk continuousOn_id)
            (fun z hz => ⟨Metric.mem_closedBall_self hr₂.le, Metric.ball_subset_closedBall hz⟩)
        have h2 : ContinuousOn G.f (ball 0 (2 * r₁)) :=
          G.hf_cont.mono (Metric.ball_subset_ball (by linarith))
        have hsmul : Continuous (fun p : (E n →L[ℝ] ℝ) × E n => p.1.smulRight p.2) :=
          (ContinuousLinearMap.smulRightL ℝ (E n) (E n)).continuous₂
        exact hsmul.comp_continuousOn (h1.prodMk h2))
      (by
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
        have hconv := convex_ball (0 : E n) r₂
        refine hconv.lipschitzOnWith_of_nnnorm_fderiv_le
          (fun x hx => (hK_fderiv x hx z hz).differentiableAt) ?_
        intro x hx
        rw [(hK_fderiv x hx z hz).fderiv]
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg hM_nn]
        have h1 : ‖(Kx (x, z)).smulRight (G.f z)‖ ≤ ‖Kx (x, z)‖ * ‖G.f z‖ :=
          le_of_eq (ContinuousLinearMap.norm_smulRight_apply _ _)
        have h2 : ‖Kx (x, z)‖ ≤ max 0 M_K :=
          (hMK (x, z) ⟨Metric.ball_subset_closedBall hx, Metric.ball_subset_closedBall hz⟩).trans (le_max_right _ _)
        have h3 : ‖G.f z‖ ≤ max 0 M_f :=
          (hMf z (Metric.ball_subset_closedBall hz)).trans (le_max_right _ _)
        exact h1.trans (mul_le_mul h2 h3 (norm_nonneg _) (le_max_left _ _)))
      (integrable_const M)
      (by
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
        exact hK_fderiv 0 (Metric.mem_ball_self hr₂) z hz)
    exact hres.2.differentiableAt
  -- Step B: HasStrictFDerivAt Ψ (Ψ' 0) 0 with Ψ' 0 invertible
  let Ψ' : E n → (E n →L[ℝ] E n) := fun w => ∫ y in ball 0 r₁, ψ y • D1 (w, G.f y)
  have hsub_prod : closedBall (0 : E n) (ρ₁ / 3) ×ˢ closedBall (0 : E n) (ρ₁ / 3) ⊆
      ball ((0 : E n), (0 : E n)) ρ₁ := by
    intro p hp
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by have := Metric.mem_closedBall.mp hp.1; linarith only [this, hρ₁],
           by have := Metric.mem_closedBall.mp hp.2; linarith only [this, hρ₁]⟩
  have hΨ_fderiv : ∀ w ∈ ball 0 (ρ₁ / 4), HasFDerivAt Ψ (Ψ' w) w := by
    obtain ⟨M_D1, hMD1⟩ := ((isCompact_closedBall (0 : E n) (ρ₁ / 3)).prod
      (isCompact_closedBall (0 : E n) (ρ₁ / 3))).exists_bound_of_continuousOn
      (hD1_cont.continuousOn.mono hsub_prod)
    obtain ⟨M_ψ, hMψ⟩ := (isCompact_closedBall (0 : E n) r₁).exists_bound_of_continuousOn
      hψ_contDiff.continuous.continuousOn
    set M := max 0 M_ψ * max 0 M_D1
    have hM_nn : 0 ≤ M := by positivity
    let μB : Measure (E n) := volume.restrict (ball 0 r₁)
    have : IsFiniteMeasure μB := ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hterm_diff : ∀ w ∈ ball 0 (ρ₁ / 3), ∀ y ∈ ball 0 r₁,
        HasFDerivAt (fun w' => ψ y • G.μ (w', G.f y)) (ψ y • D1 (w, G.f y)) w := by
      intro w hw y hy
      have hfy : G.f y ∈ ball 0 (ρ₁ / 4) := (hbr_a (Metric.ball_subset_ball (by linarith) hy)).1
      have hp : (w, G.f y) ∈ ball ((0 : E n), (0 : E n)) ρ₁ := by
        rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        exact ⟨by have := Metric.mem_ball.mp hw; linarith,
               by have := Metric.mem_ball.mp hfy; linarith⟩
      have h1 : HasFDerivAt G.μ (fderiv ℝ G.μ (w, G.f y)) (w, G.f y) := (hμ_diff _ hp).hasFDerivAt
      have h2 : HasFDerivAt (fun w' => G.μ (w', G.f y)) (D1 (w, G.f y)) w := by
        have hpair : HasFDerivAt (fun w' : E n => (w', G.f y)) (ContinuousLinearMap.inl ℝ (E n) (E n)) w :=
          (hasFDerivAt_id w).prodMk (hasFDerivAt_const (G.f y) w)
        exact HasFDerivAt.comp w (g := G.μ) (f := fun w' : E n => (w', G.f y)) h1 hpair
      exact h2.const_smul (ψ y)
    intro w hw
    have hw_ball : w ∈ ball (0 : E n) (ρ₁ / 3) := Metric.ball_subset_ball (by linarith only [hρ₁]) hw
    have hres := hasFDerivAt_integral_of_dominated_loc_of_lip
      (μ := μB) (s := ball 0 (ρ₁ / 3)) (x₀ := w) (bound := fun _ => M)
      (F := fun w' y => ψ y • G.μ (w', G.f y)) (F' := fun y => ψ y • D1 (w, G.f y))
      (Metric.isOpen_ball.mem_nhds hw_ball)
      (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hw_ball)
        fun w' hw' => by
          refine ContinuousOn.aestronglyMeasurable ?_ Metric.isOpen_ball.measurableSet
          have hf_on : ContinuousOn G.f (ball 0 r₁) := G.hf_cont.mono (Metric.ball_subset_ball (by linarith only [h4r₁, hr₁, hρ₁_le]))
          have hpair : ContinuousOn (fun y => (w', G.f y)) (ball 0 r₁) := continuousOn_const.prodMk hf_on
          have hmaps : MapsTo (fun y => (w', G.f y)) (ball 0 r₁) (ball (0, 0) ρ₁) := by
            intro y hy
            rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
            have hfy := Metric.mem_ball.mp (hbr_a (Metric.ball_subset_ball (by linarith only [hr₁_ra, hr₁]) hy)).1
            have hw'd := Metric.mem_ball.mp hw'
            exact ⟨by linarith only [hw'd, hρ₁], by linarith only [hfy, hρ₁]⟩
          exact hψ_contDiff.continuous.continuousOn.smul (hμ2.continuousOn.comp hpair hmaps))
      (by
        have hcont : ContinuousOn (fun y => ψ y • G.μ (w, G.f y)) (closedBall 0 r₁) := by
          have hf_on : ContinuousOn G.f (closedBall 0 r₁) :=
            G.hf_cont.mono (Metric.closedBall_subset_ball (by linarith))
          have hpair : ContinuousOn (fun y => (w, G.f y)) (closedBall 0 r₁) := continuousOn_const.prodMk hf_on
          have hmaps : MapsTo (fun y => (w, G.f y)) (closedBall 0 r₁) (ball (0, 0) ρ₁) := by
            intro y hy
            rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
            have hfy := Metric.mem_ball.mp (hbr_a (Metric.closedBall_subset_ball (by linarith) hy)).1
            exact ⟨by have := Metric.mem_ball.mp hw; linarith, by linarith⟩
          exact hψ_contDiff.continuous.continuousOn.smul (hμ2.continuousOn.comp hpair hmaps)
        exact (hcont.integrableOn_compact (isCompact_closedBall 0 r₁)).mono_set Metric.ball_subset_closedBall)
      (by
        refine ContinuousOn.aestronglyMeasurable ?_ Metric.isOpen_ball.measurableSet
        have hf_on : ContinuousOn G.f (ball 0 r₁) := G.hf_cont.mono (Metric.ball_subset_ball (by linarith))
        have hpair : ContinuousOn (fun y => (w, G.f y)) (ball 0 r₁) := continuousOn_const.prodMk hf_on
        have hmaps : MapsTo (fun y => (w, G.f y)) (ball 0 r₁) (ball (0, 0) ρ₁) := by
          intro y hy
          rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
          have hfy := Metric.mem_ball.mp (hbr_a (Metric.ball_subset_ball (by linarith) hy)).1
          exact ⟨by have := Metric.mem_ball.mp hw; linarith, by linarith⟩
        exact hψ_contDiff.continuous.continuousOn.smul (hD1_cont.continuousOn.comp hpair hmaps))
      (by
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
        refine (convex_ball (0 : E n) (ρ₁ / 3)).lipschitzOnWith_of_nnnorm_fderiv_le
          (fun w' hw' => (hterm_diff w' hw' y hy).differentiableAt) ?_
        intro w' hw'
        rw [(hterm_diff w' hw' y hy).fderiv]
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg hM_nn, norm_smul]
        have h1 : ‖ψ y‖ ≤ max 0 M_ψ := (hMψ y (Metric.ball_subset_closedBall hy)).trans (le_max_right _ _)
        have hfy : G.f y ∈ closedBall 0 (ρ₁ / 3) :=
          Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith)
            (hbr_a (Metric.ball_subset_ball (by linarith) hy)).1)
        have h2 : ‖D1 (w', G.f y)‖ ≤ max 0 M_D1 :=
          (hMD1 (w', G.f y) ⟨Metric.ball_subset_closedBall hw', hfy⟩).trans (le_max_right _ _)
        exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_left _ _))
      (integrable_const M)
      (by
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
        exact hterm_diff w (Metric.ball_subset_ball (by linarith) hw) y hy)
    exact hres.2
  have hΨ'_cont : ContinuousAt Ψ' 0 := by
    obtain ⟨M_D1, hMD1⟩ := ((isCompact_closedBall (0 : E n) (ρ₁ / 3)).prod
      (isCompact_closedBall (0 : E n) (ρ₁ / 3))).exists_bound_of_continuousOn
      (hD1_cont.continuousOn.mono hsub_prod)
    obtain ⟨M_ψ, hMψ⟩ := (isCompact_closedBall (0 : E n) r₁).exists_bound_of_continuousOn
      hψ_contDiff.continuous.continuousOn
    set M := max 0 M_ψ * max 0 M_D1
    let μB : Measure (E n) := volume.restrict (ball 0 r₁)
    have : IsFiniteMeasure μB := ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    refine MeasureTheory.continuousAt_of_dominated (μ := μB)
      (F := fun w y => ψ y • D1 (w, G.f y)) (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
    · filter_upwards [Metric.ball_mem_nhds 0 (by positivity : 0 < ρ₁ / 3)] with w hw
      refine ContinuousOn.aestronglyMeasurable ?_ Metric.isOpen_ball.measurableSet
      have hf_on : ContinuousOn G.f (ball 0 r₁) := G.hf_cont.mono (Metric.ball_subset_ball (by linarith))
      have hpair : ContinuousOn (fun y => (w, G.f y)) (ball 0 r₁) := continuousOn_const.prodMk hf_on
      have hmaps : MapsTo (fun y => (w, G.f y)) (ball 0 r₁) (ball (0, 0) ρ₁) := by
        intro y hy
        rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        have hfy := Metric.mem_ball.mp (hbr_a (Metric.ball_subset_ball (by linarith) hy)).1
        exact ⟨by have := Metric.mem_ball.mp hw; linarith, by linarith⟩
      exact hψ_contDiff.continuous.continuousOn.smul (hD1_cont.continuousOn.comp hpair hmaps)
    · filter_upwards [Metric.ball_mem_nhds 0 (by positivity : 0 < ρ₁ / 3)] with w hw
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
      rw [norm_smul]
      have h1 : ‖ψ y‖ ≤ max 0 M_ψ := (hMψ y (Metric.ball_subset_closedBall hy)).trans (le_max_right _ _)
      have hfy : G.f y ∈ closedBall 0 (ρ₁ / 3) :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith)
          (hbr_a (Metric.ball_subset_ball (by linarith) hy)).1)
      have h2 : ‖D1 (w, G.f y)‖ ≤ max 0 M_D1 :=
        (hMD1 (w, G.f y) ⟨Metric.ball_subset_closedBall hw, hfy⟩).trans (le_max_right _ _)
      exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_left _ _)
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
      have hfy : G.f y ∈ ball 0 (ρ₁ / 4) := (hbr_a (Metric.ball_subset_ball (by linarith) hy)).1
      have hp : ((0 : E n), G.f y) ∈ ball ((0 : E n), (0 : E n)) ρ₁ := by
        rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
        exact ⟨hρ₁, by have := Metric.mem_ball.mp hfy; linarith⟩
      have h1 : ContinuousAt (fun w => D1 (w, G.f y)) 0 :=
        ContinuousAt.comp (g := D1) (f := fun w : E n => (w, G.f y))
          (hD1_cont.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hp))
          (continuousAt_id.prodMk continuousAt_const)
      exact (continuousAt_const (y := ψ y)).smul h1
  have hΨ_strict : HasStrictFDerivAt Ψ (Ψ' 0) 0 :=
    hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
      (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 (by positivity : 0 < ρ₁ / 4)) hΨ_fderiv)
      hΨ'_cont
  -- Show ‖id - Ψ' 0‖ ≤ 1/2 < 1 so Ψ' 0 is invertible
  have hΨ'_unit : IsUnit (Ψ' 0) := by
    have hnorm : ‖ContinuousLinearMap.id ℝ (E n) - Ψ' 0‖ < 1 := by
      have hid_eq : ContinuousLinearMap.id ℝ (E n) =
          ∫ y in ball 0 r₁, ψ y • ContinuousLinearMap.id ℝ (E n) := by
        rw [integral_smul_const, hψ_int1, one_smul]
      have hint1 : IntegrableOn (fun y => ψ y • ContinuousLinearMap.id ℝ (E n)) (ball 0 r₁) volume :=
        (φ.integrable_normed.integrableOn).smul_const _
      have hint2 : IntegrableOn (fun y => ψ y • D1 (0, G.f y)) (ball 0 r₁) volume := by
        have hcont : ContinuousOn (fun y => ψ y • D1 (0, G.f y)) (closedBall 0 r₁) := by
          have hf_on : ContinuousOn G.f (closedBall 0 r₁) :=
            G.hf_cont.mono (Metric.closedBall_subset_ball (by linarith))
          have hpair : ContinuousOn (fun y => ((0 : E n), G.f y)) (closedBall 0 r₁) :=
            continuousOn_const.prodMk hf_on
          have hmaps : MapsTo (fun y => ((0 : E n), G.f y)) (closedBall 0 r₁) (ball (0, 0) ρ₁) := by
            intro y hy
            rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
            have hfy := Metric.mem_ball.mp (hbr_a (Metric.closedBall_subset_ball (by linarith) hy)).1
            exact ⟨hρ₁, by linarith⟩
          exact hψ_contDiff.continuous.continuousOn.smul (hD1_cont.continuousOn.comp hpair hmaps)
        exact (hcont.integrableOn_compact (isCompact_closedBall 0 r₁)).mono_set Metric.ball_subset_closedBall
      have hsub : ContinuousLinearMap.id ℝ (E n) - Ψ' 0 =
          ∫ y in ball 0 r₁, ψ y • (ContinuousLinearMap.id ℝ (E n) - D1 (0, G.f y)) := by
        conv_lhs => rw [hid_eq]
        rw [← MeasureTheory.integral_sub hint1 hint2]
        apply MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        intro y _; dsimp only; rw [smul_sub]
      rw [hsub]
      have hle : ‖∫ y in ball 0 r₁, ψ y • (ContinuousLinearMap.id ℝ (E n) - D1 (0, G.f y))‖ ≤
          ∫ y in ball 0 r₁, (1 / 2 : ℝ) * ψ y := by
        calc ‖∫ y in ball 0 r₁, ψ y • (ContinuousLinearMap.id ℝ (E n) - D1 (0, G.f y))‖
            ≤ ∫ y in ball 0 r₁, ‖ψ y • (ContinuousLinearMap.id ℝ (E n) - D1 (0, G.f y))‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ y in ball 0 r₁, (1 / 2 : ℝ) * ψ y := by
              apply MeasureTheory.setIntegral_mono_on
                ((hint1.sub hint2).congr_fun (fun y _ => (smul_sub (ψ y) _ _).symm) Metric.isOpen_ball.measurableSet |>.norm)
                (φ.integrable_normed.integrableOn.const_mul (1 / 2)) Metric.isOpen_ball.measurableSet
              intro y hy
              rw [norm_smul, Real.norm_of_nonneg (hψ_nonneg y), norm_sub_rev]
              have hle2 := (hbr_a (Metric.ball_subset_ball (by linarith) hy)).2
              have hnn := hψ_nonneg y
              nlinarith
      rw [MeasureTheory.integral_const_mul, hψ_int1, mul_one] at hle
      linarith
    have hu := isUnit_one_sub_of_norm_lt_one hnorm
    simpa [ContinuousLinearMap.one_def] using hu
  -- Invert Ψ locally via HasStrictFDerivAt.localInverse and deduce HasFDerivAt f A 0
  let uΨ : (E n →L[ℝ] E n)ˣ := hΨ'_unit.unit
  let eΨ : E n ≃L[ℝ] E n := ContinuousLinearEquiv.ofUnit uΨ
  have heΨ : (eΨ : E n →L[ℝ] E n) = Ψ' 0 := rfl
  have hΨ_strict' : HasStrictFDerivAt Ψ (eΨ : E n →L[ℝ] E n) 0 := by rwa [heΨ]
  let Ψ_inv := hΨ_strict'.localInverse Ψ eΨ 0
  have hinv_diff : DifferentiableAt ℝ Ψ_inv (Ψ 0) := hΨ_strict'.to_localInverse.hasFDerivAt.differentiableAt
  have hH0 : H 0 = Ψ 0 := by
    have := hΨH 0 (Metric.mem_ball_self hr₂)
    rw [G.hf_zero] at this; exact this.symm
  have hf_eq : G.f =ᶠ[𝓝 0] (Ψ_inv ∘ H) := by
    have h1 : ∀ᶠ x in 𝓝 (0 : E n), Ψ_inv (Ψ (G.f x)) = G.f x :=
      hf_contAt0.eventually (by rw [G.hf_zero]; exact hΨ_strict'.eventually_left_inverse)
    have h2 : ∀ᶠ x in 𝓝 (0 : E n), Ψ (G.f x) = H x :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr₂) hΨH
    filter_upwards [h1, h2] with x hx1 hx2
    change G.f x = Ψ_inv (H x)
    rw [← hx2, hx1]
  have hcomp_diff : DifferentiableAt ℝ (Ψ_inv ∘ H) 0 :=
    (hH0.symm ▸ hinv_diff).comp 0 hH_diff
  exact ⟨fderiv ℝ (Ψ_inv ∘ H) 0, hcomp_diff.hasFDerivAt.congr_of_eventuallyEq hf_eq⟩

/- ### Part 2: Autonomous analytic radial ODE from `HasFDerivAt f A 0` -/

private lemma hasDerivAt_radial_ode {n : ℕ} (G : LocalAnalyticGroupHom n)
    {A : E n →L[ℝ] E n} (hA : HasFDerivAt G.f A 0) :
    ∃ (F : E n × E n → (E n →L[ℝ] E n × E n)) (r_v : ℝ),
      0 < r_v ∧ r_v ≤ G.ρ ∧
      AnalyticAt ℝ F (0, 0) ∧
      ContinuousOn G.f (ball 0 (2 * r_v)) ∧
      ∀ v ∈ ball 0 r_v, ∀ t ∈ Ioo (-1.5 : ℝ) 1.5,
        HasDerivAt (fun s : ℝ => (s • v, G.f (s • v))) (F (t • v, G.f (t • v)) v) t := by
  let D2 : E n × E n → (E n →L[ℝ] E n) :=
    fun p => (fderiv ℝ G.μ p).comp (ContinuousLinearMap.inr ℝ (E n) (E n))
  let L : E n → (E n →L[ℝ] E n) := fun w => D2 (w, 0)
  let R : E n → (E n →L[ℝ] E n) := fun x => D2 (G.ι x, x)
  let F : E n × E n → (E n →L[ℝ] E n × E n) := fun p =>
    (ContinuousLinearMap.id ℝ (E n)).prod ((L p.2).comp (A.comp (R p.1)))
  have hD2_an : AnalyticAt ℝ D2 (0, 0) :=
    (ContinuousLinearMap.compL ℝ (E n) (E n × E n) (E n)
      |>.flip (ContinuousLinearMap.inr ℝ (E n) (E n))).analyticAt _ |>.comp G.hμ_an.fderiv
  have hL_an : AnalyticAt ℝ L 0 := by
    have hp : AnalyticAt ℝ (fun w : E n => (w, (0 : E n))) 0 := analyticAt_id.prod analyticAt_const
    exact hD2_an.comp (f := fun w : E n => (w, (0 : E n))) hp
  have hR_an : AnalyticAt ℝ R 0 := by
    have hpair : AnalyticAt ℝ (fun x : E n => (G.ι x, x)) 0 := G.hι_an.prod analyticAt_id
    have hD2' : AnalyticAt ℝ D2 (G.ι 0, 0) := by rwa [G.hι_zero]
    exact AnalyticAt.comp (g := D2) (f := fun x : E n => (G.ι x, x)) hD2' hpair
  have hF_an : AnalyticAt ℝ F (0, 0) := by
    have h1 : AnalyticAt ℝ (fun p : E n × E n => L p.2) (0, 0) :=
      AnalyticAt.comp (g := L) (f := Prod.snd) hL_an analyticAt_snd
    have h2 : AnalyticAt ℝ (fun p : E n × E n => A.comp (R p.1)) (0, 0) :=
      ((ContinuousLinearMap.compL ℝ (E n) (E n) (E n) A).analyticAt _).comp
        (AnalyticAt.comp (g := R) (f := Prod.fst) hR_an analyticAt_fst)
    have h3 : AnalyticAt ℝ (fun p : E n × E n => (L p.2).comp (A.comp (R p.1))) (0, 0) :=
      h1.mul h2
    let hprod_lin : (E n →L[ℝ] E n) →L[ℝ] (E n →L[ℝ] E n × E n) :=
      ContinuousLinearMap.compL ℝ (E n) (E n) (E n × E n)
        (ContinuousLinearMap.inr ℝ (E n) (E n))
    have hF_eq : F = fun p =>
        ((ContinuousLinearMap.id ℝ (E n)).prod (0 : E n →L[ℝ] E n)) +
          hprod_lin ((L p.2).comp (A.comp (R p.1))) := by
      ext p v <;> simp [F, hprod_lin]
    rw [hF_eq]
    exact analyticAt_const.add ((hprod_lin.analyticAt _).comp h3)
  -- Find r_v > 0 so that for all x ∈ ball 0 (2 * r_v), x, ι x, f x are small enough for chain rule
  obtain ⟨ρ₁, hρ₁, hρ₁_le, hμ2, hι2⟩ := exists_radius_contDiffOn G
  have hμ_diff : ∀ p ∈ ball (0, 0) ρ₁, DifferentiableAt ℝ G.μ p := fun p hp =>
    (hμ2.contDiffAt (Metric.isOpen_ball.mem_nhds hp)).differentiableAt (by norm_num)
  have hf_cont0 : ContinuousAt G.f 0 := G.hf_cont.continuousAt (Metric.ball_mem_nhds 0 G.hρ)
  have hev : ∀ᶠ x in 𝓝 (0 : E n),
      x ∈ ball 0 (ρ₁ / 2) ∧ G.ι x ∈ ball 0 (ρ₁ / 2) ∧ G.f x ∈ ball 0 (ρ₁ / 2) ∧
      G.μ (G.ι x, x) = 0 := by
    have h1 : ∀ᶠ x in 𝓝 (0 : E n), x ∈ ball 0 (ρ₁ / 2) := Metric.ball_mem_nhds 0 (by positivity)
    have h2 : ∀ᶠ x in 𝓝 (0 : E n), G.ι x ∈ ball 0 (ρ₁ / 2) :=
      G.hι_an.continuousAt.eventually (by rw [G.hι_zero]; exact Metric.ball_mem_nhds 0 (by positivity))
    have h3 : ∀ᶠ x in 𝓝 (0 : E n), G.f x ∈ ball 0 (ρ₁ / 2) :=
      hf_cont0.eventually (by rw [G.hf_zero]; exact Metric.ball_mem_nhds 0 (by positivity))
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    refine ⟨hx1, hx2, hx3, ?_⟩
    have hxρ : x ∈ ball 0 G.ρ := Metric.ball_subset_ball (by linarith) hx1
    have h0ρ : (0 : E n) ∈ ball 0 G.ρ := Metric.mem_ball_self G.hρ
    calc G.μ (G.ι x, x) = G.μ (G.ι x, G.μ (x, 0)) := by rw [G.hμ_right_id x hxρ]
      _ = 0 := G.hμ_inv_left x hxρ 0 h0ρ
  obtain ⟨r₂, hr₂, hbr₂⟩ := Metric.mem_nhds_iff.mp hev
  set r_v : ℝ := min (G.ρ / 4) (r₂ / 4)
  have hr_v : 0 < r_v := by have := G.hρ; positivity
  refine ⟨F, r_v, hr_v, by have : r_v ≤ G.ρ / 4 := min_le_left _ _; linarith, hF_an,
    G.hf_cont.mono (Metric.ball_subset_ball (by have : r_v ≤ G.ρ / 4 := min_le_left _ _; linarith)), ?_⟩
  intro v hv t ht
  set x : E n := t • v
  have hx_2rv : x ∈ ball 0 (2 * r_v) := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have hv' := Metric.mem_ball.mp hv; rw [dist_zero_right] at hv'
    have ht_abs : |t| < 1.5 := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hv_nn : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith
  have hx_r₂ : x ∈ ball 0 r₂ := Metric.ball_subset_ball (by
    have : r_v ≤ r₂ / 4 := min_le_right _ _; linarith) hx_2rv
  have ⟨hx1, hx2, hx3, hx_inv⟩ := hbr₂ hx_r₂
  have hxρ : x ∈ ball 0 G.ρ := Metric.ball_subset_ball (by linarith) hx1
  -- Show HasFDerivAt G.f ((L (G.f x)).comp (A.comp (R x))) x
  have hf_x : HasFDerivAt G.f ((L (G.f x)).comp (A.comp (R x))) x := by
    have hμ_inv_pt : (G.ι x, x) ∈ ball ((0 : E n), (0 : E n)) ρ₁ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨by have := Metric.mem_ball.mp hx2; linarith,
             by have := Metric.mem_ball.mp hx1; linarith⟩
    have h1 : HasFDerivAt (fun u => G.μ (G.ι x, u)) (R x) x :=
      (hμ_diff _ hμ_inv_pt).hasFDerivAt.comp x ((hasFDerivAt_const (G.ι x) x).prodMk (hasFDerivAt_id x))
    have h2 : HasFDerivAt (fun u => G.f (G.μ (G.ι x, u))) (A.comp (R x)) x := by
      have hA' : HasFDerivAt G.f A (G.μ (G.ι x, x)) := by rwa [hx_inv]
      exact hA'.comp x h1
    have hμ_fx_pt : (G.f x, (0 : E n)) ∈ ball ((0 : E n), (0 : E n)) ρ₁ := by
      rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
      exact ⟨by have := Metric.mem_ball.mp hx3; linarith, hρ₁⟩
    have h3 : HasFDerivAt (fun w => G.μ (G.f x, w)) (L (G.f x)) (G.f (G.μ (G.ι x, x))) := by
      rw [hx_inv, G.hf_zero]
      exact (hμ_diff _ hμ_fx_pt).hasFDerivAt.comp 0
        ((hasFDerivAt_const (G.f x) 0).prodMk (hasFDerivAt_id 0))
    have hcomp : HasFDerivAt (fun u => G.μ (G.f x, G.f (G.μ (G.ι x, u))))
        ((L (G.f x)).comp (A.comp (R x))) x :=
      HasFDerivAt.comp x (g := fun w => G.μ (G.f x, w)) (f := fun u => G.f (G.μ (G.ι x, u))) h3 h2
    have heq : G.f =ᶠ[𝓝 x] fun u => G.μ (G.f x, G.f (G.μ (G.ι x, u))) := by
      have h1_ev : ∀ᶠ u in 𝓝 x, u ∈ ball 0 G.ρ := Metric.isOpen_ball.mem_nhds hxρ
      have h2_ev : ∀ᶠ u in 𝓝 x, G.μ (G.ι x, u) ∈ ball 0 G.ρ :=
        h1.continuousAt.eventually (by dsimp only; rw [hx_inv]; exact Metric.ball_mem_nhds 0 G.hρ)
      filter_upwards [h1_ev, h2_ev] with u hu1 hu2
      rw [← G.hf_hom x hxρ (G.μ (G.ι x, u)) hu2, G.hμ_inv_right x hxρ u hu1]
    exact hcomp.congr_of_eventuallyEq heq
  have hline : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hf_line : HasDerivAt (fun s : ℝ => G.f (s • v)) ((L (G.f x)).comp (A.comp (R x)) v) t :=
    hf_x.comp_hasDerivAt t hline
  exact hline.prodMk hf_line

/- ### Part 3: Cauchy Majorant Multilinear Power Series ODE Solver -/

private noncomputable def mlTensor {E A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {j r : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) (A →L[ℝ] B)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (j + r) => E) B :=
  MultilinearMap.mkContinuous
    { toFun := fun v => g (fun i => v (Fin.natAdd j i)) (f (fun i => v (Fin.castAdd r i)))
      map_update_add' := fun m i x y => by
        have hne : ∀ (a : Fin j) (b : Fin r), Fin.castAdd r a ≠ Fin.natAdd j b := by
          intro a b h; have := congrArg Fin.val h; simp at this; omega
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
        · have hnat : ∀ z, (fun k : Fin r => Function.update m (Fin.castAdd r i₁) z (Fin.natAdd j k)) =
              fun k => m (Fin.natAdd j k) := by
            intro z; ext k; exact Function.update_of_ne (hne i₁ k).symm _ _
          have hcast : ∀ z, (fun k : Fin j => Function.update m (Fin.castAdd r i₁) z (Fin.castAdd r k)) =
              Function.update (fun k => m (Fin.castAdd r k)) i₁ z := by
            intro z; ext k
            by_cases hk : k = i₁
            · subst hk; simp
            · have hne' : Fin.castAdd r k ≠ Fin.castAdd r i₁ := fun h =>
                hk (Fin.ext (by have := congrArg Fin.val h; simpa using this))
              simp [hk, hne']
          rw [hnat, hnat, hnat, hcast, hcast, hcast, f.map_update_add, map_add]
        · have hcast : ∀ z, (fun k : Fin j => Function.update m (Fin.natAdd j i₂) z (Fin.castAdd r k)) =
              fun k => m (Fin.castAdd r k) := by
            intro z; ext k; exact Function.update_of_ne (hne k i₂) _ _
          have hnat : ∀ z, (fun k : Fin r => Function.update m (Fin.natAdd j i₂) z (Fin.natAdd j k)) =
              Function.update (fun k => m (Fin.natAdd j k)) i₂ z := by
            intro z; ext k
            by_cases hk : k = i₂
            · subst hk; simp
            · have hne' : Fin.natAdd j k ≠ Fin.natAdd j i₂ := fun h =>
                hk (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
              simp [hk, hne']
          rw [hcast, hcast, hcast, hnat, hnat, hnat, g.map_update_add]
          rfl
      map_update_smul' := fun m i c x => by
        have hne : ∀ (a : Fin j) (b : Fin r), Fin.castAdd r a ≠ Fin.natAdd j b := by
          intro a b h; have := congrArg Fin.val h; simp at this; omega
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
        · have hnat : ∀ z, (fun k : Fin r => Function.update m (Fin.castAdd r i₁) z (Fin.natAdd j k)) =
              fun k => m (Fin.natAdd j k) := by
            intro z; ext k; exact Function.update_of_ne (hne i₁ k).symm _ _
          have hcast : ∀ z, (fun k : Fin j => Function.update m (Fin.castAdd r i₁) z (Fin.castAdd r k)) =
              Function.update (fun k => m (Fin.castAdd r k)) i₁ z := by
            intro z; ext k
            by_cases hk : k = i₁
            · subst hk; simp
            · have hne' : Fin.castAdd r k ≠ Fin.castAdd r i₁ := fun h =>
                hk (Fin.ext (by have := congrArg Fin.val h; simpa using this))
              simp [hk, hne']
          rw [hnat, hnat, hcast, hcast, f.map_update_smul, map_smul]
        · have hcast : ∀ z, (fun k : Fin j => Function.update m (Fin.natAdd j i₂) z (Fin.castAdd r k)) =
              fun k => m (Fin.castAdd r k) := by
            intro z; ext k; exact Function.update_of_ne (hne k i₂) _ _
          have hnat : ∀ z, (fun k : Fin r => Function.update m (Fin.natAdd j i₂) z (Fin.natAdd j k)) =
              Function.update (fun k => m (Fin.natAdd j k)) i₂ z := by
            intro z; ext k
            by_cases hk : k = i₂
            · subst hk; simp
            · have hne' : Fin.natAdd j k ≠ Fin.natAdd j i₂ := fun h =>
                hk (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
              simp [hk, hne']
          rw [hcast, hcast, hnat, hnat, g.map_update_smul]
          rfl }
    (‖f‖ * ‖g‖)
    (fun v => by
      calc ‖g (fun i => v (Fin.natAdd j i)) (f (fun i => v (Fin.castAdd r i)))‖
          ≤ ‖g (fun i => v (Fin.natAdd j i))‖ * ‖f (fun i => v (Fin.castAdd r i))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖g‖ * ∏ i : Fin r, ‖v (Fin.natAdd j i)‖) *
              (‖f‖ * ∏ i : Fin j, ‖v (Fin.castAdd r i)‖) :=
            mul_le_mul (g.le_opNorm _) (f.le_opNorm _) (norm_nonneg _) (by positivity)
        _ = (‖f‖ * ‖g‖) * ((∏ i : Fin j, ‖v (Fin.castAdd r i)‖) *
              ∏ i : Fin r, ‖v (Fin.natAdd j i)‖) := by ring
        _ = (‖f‖ * ‖g‖) * ∏ i : Fin (j + r), ‖v i‖ := by
            rw [← Fin.prod_univ_add (fun i : Fin (j + r) => ‖v i‖)])

private lemma norm_mlTensor_le {E A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {j r : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) (A →L[ℝ] B)) :
    ‖mlTensor f g‖ ≤ ‖f‖ * ‖g‖ :=
  MultilinearMap.mkContinuous_norm_le _ (by positivity) _

private noncomputable def mlEval {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {k : ℕ} (g : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (E →L[ℝ] B)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) B :=
  MultilinearMap.mkContinuous
    { toFun := fun v => g (Fin.tail v) (v 0)
      map_update_add' := fun m i x y => by
        cases i using Fin.cases with
        | zero =>
          have htail : ∀ z, Fin.tail (Function.update m 0 z) = Fin.tail m := fun z => by
            ext j; simp [Fin.tail]
          simp only [htail, Function.update_self, map_add]
        | succ i' =>
          have h0 : ∀ z, Function.update m i'.succ z 0 = m 0 := fun z =>
            Function.update_of_ne (Fin.succ_ne_zero i').symm _ _
          have htail : ∀ z, Fin.tail (Function.update m i'.succ z) = Function.update (Fin.tail m) i' z := fun z => by
            ext j
            by_cases hj : j = i'
            · subst hj; simp [Fin.tail]
            · simp [Fin.tail, hj, (Fin.succ_injective _).ne hj]
          simp only [h0, htail, g.map_update_add]; rfl
      map_update_smul' := fun m i c x => by
        cases i using Fin.cases with
        | zero =>
          have htail : ∀ z, Fin.tail (Function.update m 0 z) = Fin.tail m := fun z => by
            ext j; simp [Fin.tail]
          simp only [htail, Function.update_self, map_smul]
        | succ i' =>
          have h0 : ∀ z, Function.update m i'.succ z 0 = m 0 := fun z =>
            Function.update_of_ne (Fin.succ_ne_zero i').symm _ _
          have htail : ∀ z, Fin.tail (Function.update m i'.succ z) = Function.update (Fin.tail m) i' z := fun z => by
            ext j
            by_cases hj : j = i'
            · subst hj; simp [Fin.tail]
            · simp [Fin.tail, hj, (Fin.succ_injective _).ne hj]
          simp only [h0, htail, g.map_update_smul]; rfl }
    ‖g‖
    (fun v => by
      calc ‖g (Fin.tail v) (v 0)‖
          ≤ ‖g (Fin.tail v)‖ * ‖v 0‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖g‖ * ∏ i : Fin k, ‖Fin.tail v i‖) * ‖v 0‖ :=
            mul_le_mul_of_nonneg_right (g.le_opNorm _) (norm_nonneg _)
        _ = ‖g‖ * (‖v 0‖ * ∏ i : Fin k, ‖v i.succ‖) := by simp [Fin.tail]; ring
        _ = ‖g‖ * ∏ i : Fin (k + 1), ‖v i‖ := by
            rw [Fin.prod_univ_succ (fun i : Fin (k + 1) => ‖v i‖)])

private lemma mlEval_diag {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {k : ℕ} (g : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (E →L[ℝ] B)) (v : E) :
    mlEval g (fun _ => v) = g (fun _ => v) v := rfl

private lemma norm_mlEval_le {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {k : ℕ} (g : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (E →L[ℝ] B)) :
    ‖mlEval g‖ ≤ ‖g‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

/- Compositions of `k` into `m` positive parts -/

private def compList : ℕ → ℕ → List (List ℕ)
  | 0, k => if k = 0 then [[]] else []
  | m + 1, k => (List.range k).flatMap fun i =>
      (compList m (k - (i + 1))).map fun l => (i + 1) :: l

private lemma mem_compList : ∀ {m k : ℕ} {l : List ℕ},
    l ∈ compList m k ↔ l.length = m ∧ l.sum = k ∧ ∀ j ∈ l, 1 ≤ j
  | 0, k, l => by
    unfold compList
    by_cases hk : k = 0
    · subst hk; simp only [ite_true, List.mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl; simp
      · rintro ⟨rfl, _, _⟩; rfl
    · simp only [hk, ite_false, List.not_mem_nil, false_iff, not_and]
      intro hlen hsum _; rw [List.length_eq_zero_iff.mp hlen] at hsum; exact hk hsum.symm
  | m + 1, k, l => by
    unfold compList
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨i, hi, l', hl', rfl⟩
      have h' := (mem_compList (m := m) (k := k - (i + 1)) (l := l')).mp hl'
      refine ⟨by simp [h'.1], by simp [h'.2.1]; omega, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj'
      · omega
      · exact h'.2.2 j hj'
    · rintro ⟨hlen, hsum, hpos⟩
      cases l with
      | nil => simp at hlen
      | cons a l' =>
        have ha : 1 ≤ a := hpos a (List.mem_cons_self ..)
        have hsum' : a + l'.sum = k := by simpa using hsum
        refine ⟨a - 1, by omega, l', ?_, by simp; omega⟩
        rw [mem_compList]
        refine ⟨by simpa using hlen, by omega, fun j hj => hpos j (List.mem_cons_of_mem _ hj)⟩

private lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rcases n with _ | m
    · simp
    · have hIcc : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      -- Stronger inductive bound: <= 2 - 1/(N+1)
      have hstrong : ∀ M : ℕ, 1 ≤ M → ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 - 1 / (M : ℝ) := by
        intro M hM
        induction M, hM using Nat.le_induction with
        | base => simp; norm_num
        | succ k hk ihk =>
          have hI : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.sum_insert (by simp)]
          have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
          have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            push_cast
            have h1 : 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
              field_simp; ring
            rw [h1]
            exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
          linarith
      have h1 := hstrong (m + 2) (by omega)
      have hpos : (0 : ℝ) ≤ 1 / ((m + 2 : ℕ) : ℝ) := by positivity
      linarith

private lemma conv_inv_sq_le {k : ℕ} (hk : 2 ≤ k) :
    ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2) ≤ 16 / (k : ℝ) ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hterm : ∀ j ∈ Finset.Ico 1 k,
      (1 : ℝ) / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2) ≤
        (4 / (k : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2 + 1 / ((k - j : ℕ) : ℝ) ^ 2) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjk : j < k := (Finset.mem_Ico.mp hj).2
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hkjpos : (0 : ℝ) < (k - j : ℕ) := by exact_mod_cast (show 0 < k - j by omega)
    have hsum : (j : ℝ) + ((k - j : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Nat.add_sub_of_le hjk.le
    rcases le_total (j : ℝ) ((k - j : ℕ) : ℝ) with hle | hge
    · have hhalf : (k : ℝ) ≤ 2 * ((k - j : ℕ) : ℝ) := by linarith
      have hsq : (k : ℝ) ^ 2 ≤ 4 * ((k - j : ℕ) : ℝ) ^ 2 := by nlinarith
      have h1 : (1 : ℝ) / ((k - j : ℕ) : ℝ) ^ 2 ≤ 4 / (k : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      calc (1 : ℝ) / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2)
          = (1 / ((k - j : ℕ) : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) := by ring
        _ ≤ (4 / (k : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (4 / (k : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2 + 1 / ((k - j : ℕ) : ℝ) ^ 2) := by
            gcongr; linarith [show (0 : ℝ) ≤ 1 / ((k - j : ℕ) : ℝ) ^ 2 by positivity]
    · have hhalf : (k : ℝ) ≤ 2 * (j : ℝ) := by linarith
      have hsq : (k : ℝ) ^ 2 ≤ 4 * (j : ℝ) ^ 2 := by nlinarith
      have h1 : (1 : ℝ) / (j : ℝ) ^ 2 ≤ 4 / (k : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      calc (1 : ℝ) / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2)
          = (1 / (j : ℝ) ^ 2) * (1 / ((k - j : ℕ) : ℝ) ^ 2) := by ring
        _ ≤ (4 / (k : ℝ) ^ 2) * (1 / ((k - j : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (4 / (k : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2 + 1 / ((k - j : ℕ) : ℝ) ^ 2) := by
            gcongr; linarith [show (0 : ℝ) ≤ 1 / (j : ℝ) ^ 2 by positivity]
  have h1 : ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
    have hsub : Finset.Ico 1 k ⊆ Finset.Icc 1 k := Finset.Ico_subset_Icc_self
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (sum_inv_sq_le_two k)
  have h2 : ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / ((k - j : ℕ) : ℝ) ^ 2 ≤ 2 := by
    have hbij : ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / ((k - j : ℕ) : ℝ) ^ 2 =
        ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / (j : ℝ) ^ 2 := by
      refine Finset.sum_bij (fun j _ => k - j) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj; exact ⟨k - j, by simp only [Finset.mem_Ico]; omega, by omega⟩
      · intro _ _; rfl
    rw [hbij]; exact h1
  calc ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2)
      ≤ ∑ j ∈ Finset.Ico 1 k, (4 / (k : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2 + 1 / ((k - j : ℕ) : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (4 / (k : ℝ) ^ 2) * (∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / (j : ℝ) ^ 2 +
          ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / ((k - j : ℕ) : ℝ) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (4 / (k : ℝ) ^ 2) * (2 + 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 16 / (k : ℝ) ^ 2 := by ring

private lemma compList_zero_of_pos {m : ℕ} (hm : 1 ≤ m) : compList m 0 = [] := by
  cases m with
  | zero => omega
  | succ m' => simp [compList]

private lemma compList_one {k : ℕ} (hk : 1 ≤ k) : compList 1 k = [[k]] := by
  have hk_eq : k = (k - 1) + 1 := by omega
  conv_lhs => rw [show (1 : ℕ) = 0 + 1 from rfl, compList, hk_eq, List.range_succ, List.flatMap_append]
  have hleft : ((List.range (k - 1)).flatMap fun i =>
      (compList 0 ((k - 1 + 1) - (i + 1))).map fun l => (i + 1) :: l) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro i hi
    have hik : i < k - 1 := List.mem_range.mp hi
    have hne : k - 1 - i ≠ 0 := by omega
    simp [compList, hne]
  rw [hleft, List.nil_append]
  simp [compList, ← hk_eq]

private lemma list_sum_flatMap {α : Type*} (L : List α) (f : α → List ℝ) :
    (L.flatMap f).sum = (L.map (fun a => (f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

private lemma list_sum_map_mul_left {α : Type*} (L : List α) (c : ℝ) (f : α → ℝ) :
    (L.map (fun a => c * f a)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih, mul_add]

private lemma list_sum_range_eq_finset {k : ℕ} (f : ℕ → ℝ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma compList_inv_sq_sum : ∀ (m : ℕ), 1 ≤ m → ∀ (k : ℕ), 1 ≤ k →
    ((compList m k).map (fun l => (l.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod)).sum ≤
      (16 : ℝ) ^ (m - 1) / (k : ℝ) ^ 2
  | 0, hm, _, _ => by omega
  | 1, _, k, hk => by
    rw [compList_one hk]
    simp
  | m + 2, _, k, hk => by
    let w : List ℕ → ℝ := fun l => (l.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod
    have hstep : ((compList (m + 2) k).map w).sum =
        ∑ i ∈ Finset.range k,
          ((1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) * ((compList (m + 1) (k - (i + 1))).map w).sum := by
      change (((List.range k).flatMap fun i =>
          (compList (m + 1) (k - (i + 1))).map fun l => (i + 1) :: l).map w).sum = _
      rw [List.map_flatMap, list_sum_flatMap, ← list_sum_range_eq_finset]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [List.map_map]
      have hcomp : w ∘ (fun l : List ℕ => (i + 1) :: l) =
          fun l => ((1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) * w l := by
        ext l; simp [w]
      rw [hcomp, list_sum_map_mul_left]
    rw [hstep]
    rcases eq_or_lt_of_le hk with rfl | hk2
    · simp [compList_zero_of_pos (show 1 ≤ m + 1 by omega)]
    · have hsplit : Finset.range k = insert (k - 1) (Finset.range (k - 1)) := by
        ext i; simp only [Finset.mem_range, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have hlast : k - (k - 1 + 1) = 0 := by omega
      rw [hlast, compList_zero_of_pos (show 1 ≤ m + 1 by omega)]
      simp only [List.map_nil, List.sum_nil, mul_zero, zero_add]
      have hbound : ∑ i ∈ Finset.range (k - 1),
          ((1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) * ((compList (m + 1) (k - (i + 1))).map w).sum ≤
          (16 : ℝ) ^ m * ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        have hbij : ∑ i ∈ Finset.range (k - 1),
            ((1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) * ((compList (m + 1) (k - (i + 1))).map w).sum =
            ∑ j ∈ Finset.Ico 1 k,
              ((1 : ℝ) / (j : ℝ) ^ 2) * ((compList (m + 1) (k - j)).map w).sum := by
          refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
          · intro i hi; simp only [Finset.mem_range, Finset.mem_Ico] at hi ⊢; omega
          · intro a _ b _ hab; omega
          · intro j hj; simp only [Finset.mem_Ico] at hj
            exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
          · intro i _; rfl
        rw [hbij]
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j < k := (Finset.mem_Ico.mp hj).2
        have hih := compList_inv_sq_sum (m + 1) (by omega) (k - j) (by omega)
        have heq : (16 : ℝ) ^ m * (1 / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2)) =
            (1 / (j : ℝ) ^ 2) * ((16 : ℝ) ^ m / ((k - j : ℕ) : ℝ) ^ 2) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by simpa [w] using hih) (by positivity)
      calc ∑ i ∈ Finset.range (k - 1),
            ((1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) * ((compList (m + 1) (k - (i + 1))).map w).sum
          ≤ (16 : ℝ) ^ m * ∑ j ∈ Finset.Ico 1 k, (1 : ℝ) / ((j : ℝ) ^ 2 * ((k - j : ℕ) : ℝ) ^ 2) := hbound
        _ ≤ (16 : ℝ) ^ m * (16 / (k : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (conv_inv_sq_le hk2) (by positivity)
        _ = (16 : ℝ) ^ (m + 2 - 1) / (k : ℝ) ^ 2 := by
            simp only [show m + 2 - 1 = m + 1 by omega, pow_succ]; ring

/- List and tsum helpers + Front-coordinate currying and multilinear list composition -/

private lemma list_norm_sum_le {V : Type} [SeminormedAddCommGroup V] (L : List V) :
    ‖L.sum‖ ≤ (L.map (fun x => ‖x‖)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

private lemma list_map_attach_val {α β : Type} (L : List α) (f : α → β) :
    L.attach.map (fun x => f x.1) = L.map f := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.attach_cons, List.map_cons, List.map_map]
    congr 1

private lemma tsum_nat_zero_add {M : Type} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [T2Space M] {f : ℕ → M} (hf : Summable f) :
    ∑' n : ℕ, f n = f 0 + ∑' n : ℕ, f (n + 1) := by
  have h1 : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hf
  exact h1.hasSum.zero_add.tsum_eq

private noncomputable def mlPopFront {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ}
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Z) W) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) (Z →L[ℝ] W) :=
  MultilinearMap.mkContinuous
    { toFun := fun u =>
        LinearMap.mkContinuous
          { toFun := fun z => Q (Fin.cons (α := fun _ => Z) z u)
            map_add' := fun z₁ z₂ => by
              have h := Q.map_update_add (Fin.cons (α := fun _ => Z) z₁ u) 0 z₁ z₂
              simpa [Fin.update_cons_zero] using h
            map_smul' := fun c z => by
              have h := Q.map_update_smul (Fin.cons (α := fun _ => Z) z u) 0 c z
              simpa [Fin.update_cons_zero] using h }
          (‖Q‖ * ∏ i : Fin m, ‖u i‖)
          (fun z => by
            let consZ : Z → (Fin m → Z) → (Fin (m + 1) → Z) := fun z u => Fin.cons z u
            calc ‖Q (consZ z u)‖
                ≤ ‖Q‖ * ∏ i : Fin (m + 1), ‖consZ z u i‖ := Q.le_opNorm (consZ z u)
              _ = ‖Q‖ * (‖z‖ * ∏ i : Fin m, ‖u i‖) := by
                  rw [Fin.prod_univ_succ (fun i : Fin (m + 1) => ‖consZ z u i‖)]; simp [consZ]
              _ = (‖Q‖ * ∏ i : Fin m, ‖u i‖) * ‖z‖ := by ring)
      map_update_add' := fun u i x y => by
        ext z
        let consZ : Z → (Fin m → Z) → (Fin (m + 1) → Z) := fun z u => Fin.cons z u
        have hupd : ∀ w : Z, Function.update (consZ z u) i.succ w = consZ z (Function.update u i w) := by
          intro w; ext k; cases k using Fin.cases with
          | zero => simp [consZ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
          | succ k' =>
            by_cases hk : k' = i
            · subst hk; simp [consZ]
            · simp [consZ, hk, (Fin.succ_injective _).ne hk]
        change Q (consZ z (Function.update u i (x + y))) =
          Q (consZ z (Function.update u i x)) + Q (consZ z (Function.update u i y))
        rw [← hupd, ← hupd, ← hupd]
        exact Q.map_update_add (consZ z u) i.succ x y
      map_update_smul' := fun u i c x => by
        ext z
        let consZ : Z → (Fin m → Z) → (Fin (m + 1) → Z) := fun z u => Fin.cons z u
        have hupd : ∀ w : Z, Function.update (consZ z u) i.succ w = consZ z (Function.update u i w) := by
          intro w; ext k; cases k using Fin.cases with
          | zero => simp [consZ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
          | succ k' =>
            by_cases hk : k' = i
            · subst hk; simp [consZ]
            · simp [consZ, hk, (Fin.succ_injective _).ne hk]
        change Q (consZ z (Function.update u i (c • x))) =
          c • Q (consZ z (Function.update u i x))
        rw [← hupd, ← hupd]
        exact Q.map_update_smul (consZ z u) i.succ c x }
    ‖Q‖
    (fun u => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun z => by
      let consZ : Z → (Fin m → Z) → (Fin (m + 1) → Z) := fun z u => Fin.cons z u
      change ‖Q (consZ z u)‖ ≤ (‖Q‖ * ∏ i : Fin m, ‖u i‖) * ‖z‖
      calc ‖Q (consZ z u)‖
          ≤ ‖Q‖ * ∏ i : Fin (m + 1), ‖consZ z u i‖ := Q.le_opNorm (consZ z u)
        _ = ‖Q‖ * (‖z‖ * ∏ i : Fin m, ‖u i‖) := by
            rw [Fin.prod_univ_succ (fun i : Fin (m + 1) => ‖consZ z u i‖)]; simp [consZ]
        _ = (‖Q‖ * ∏ i : Fin m, ‖u i‖) * ‖z‖ := by ring))

private lemma norm_mlPopFront_le {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ}
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Z) W) :
    ‖mlPopFront Q‖ ≤ ‖Q‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg Q) _

private lemma mlPopFront_apply {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ}
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Z) W) (u : Fin m → Z) (z : Z) :
    mlPopFront Q u z = Q (Fin.cons z u) := rfl

private noncomputable def evalList {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    ∀ {m : ℕ}, ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W →
      (ℕ → Z) → (l : List ℕ) → l.length = m → W
  | 0, Q, _, [], _ => Q ![]
  | m + 1, Q, a, j :: l', hlen =>
      evalList (mlPopFront Q) a l' (by simpa using hlen) (a j)

private lemma norm_evalList_le {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    ∀ {m : ℕ} (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W)
      (a : ℕ → Z) (l : List ℕ) (hlen : l.length = m),
      ‖evalList Q a l hlen‖ ≤ ‖Q‖ * (l.map (fun j => ‖a j‖)).prod
  | 0, Q, _, [], _ => by
      simp only [evalList, List.map_nil, List.prod_nil, mul_one]
      simpa only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] using Q.le_opNorm ![]
  | m + 1, Q, a, j :: l', hlen => by
      simp only [evalList, List.map_cons, List.prod_cons]
      have h1 : ‖evalList (mlPopFront Q) a l' (by simpa using hlen) (a j)‖ ≤
          ‖evalList (mlPopFront Q) a l' (by simpa using hlen)‖ * ‖a j‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h2 := norm_evalList_le (mlPopFront Q) a l' (by simpa using hlen)
      have h3 := norm_mlPopFront_le Q
      have hprod_nn : 0 ≤ (l'.map (fun k => ‖a k‖)).prod :=
        List.prod_nonneg (fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact norm_nonneg _)
      calc ‖evalList (mlPopFront Q) a l' (by simpa using hlen) (a j)‖
          ≤ ‖evalList (mlPopFront Q) a l' (by simpa using hlen)‖ * ‖a j‖ := h1
        _ ≤ (‖mlPopFront Q‖ * (l'.map (fun k => ‖a k‖)).prod) * ‖a j‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ (‖Q‖ * (l'.map (fun k => ‖a k‖)).prod) * ‖a j‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hprod_nn) (norm_nonneg _)
        _ = ‖Q‖ * (‖a j‖ * (l'.map (fun k => ‖a k‖)).prod) := by ring

private noncomputable def mlApplyList {E Z W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (c : ∀ j : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin j => E) Z) :
    ∀ {m : ℕ}, ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W →
      (l : List ℕ) → l.length = m →
      ContinuousMultilinearMap ℝ (fun _ : Fin l.sum => E) W
  | 0, Q, [], _ => ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (Q ![])
  | m + 1, Q, j :: l', hlen =>
      mlTensor (c j) (mlApplyList c (mlPopFront Q) l' (by simpa using hlen))

private lemma mlApplyList_diag {E Z W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (c : ∀ j : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin j => E) Z) :
    ∀ {m : ℕ} (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W)
      (l : List ℕ) (hlen : l.length = m) (v : E),
      mlApplyList c Q l hlen (fun _ => v) = evalList Q (fun j => c j (fun _ => v)) l hlen
  | 0, _, [], _, _ => rfl
  | m + 1, Q, j :: l', hlen, v => by
      change mlApplyList c (mlPopFront Q) l' (by simpa using hlen) (fun _ => v) (c j (fun _ => v)) = _
      rw [mlApplyList_diag c (mlPopFront Q) l' (by simpa using hlen) v]
      rfl

private lemma norm_mlApplyList_le {E Z W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (c : ∀ j : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin j => E) Z) :
    ∀ {m : ℕ} (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W)
      (l : List ℕ) (hlen : l.length = m),
      ‖mlApplyList c Q l hlen‖ ≤ ‖Q‖ * (l.map (fun j => ‖c j‖)).prod
  | 0, Q, [], _ => by
      change ‖ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (Q ![])‖ ≤ ‖Q‖ * 1
      rw [mul_one]
      refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg Q) (fun x => ?_)
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      simpa only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] using Q.le_opNorm ![]
  | m + 1, Q, j :: l', hlen => by
      simp only [mlApplyList, List.map_cons, List.prod_cons]
      have h1 := norm_mlTensor_le (c j) (mlApplyList c (mlPopFront Q) l' (by simpa using hlen))
      have h2 := norm_mlApplyList_le c (mlPopFront Q) l' (by simpa using hlen)
      have h3 := norm_mlPopFront_le Q
      have hprod_nn : 0 ≤ (l'.map (fun k => ‖c k‖)).prod :=
        List.prod_nonneg (fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact norm_nonneg _)
      calc ‖mlTensor (c j) (mlApplyList c (mlPopFront Q) l' (by simpa using hlen))‖
          ≤ ‖c j‖ * ‖mlApplyList c (mlPopFront Q) l' (by simpa using hlen)‖ := h1
        _ ≤ ‖c j‖ * (‖mlPopFront Q‖ * (l'.map (fun k => ‖c k‖)).prod) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ ≤ ‖c j‖ * (‖Q‖ * (l'.map (fun k => ‖c k‖)).prod) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hprod_nn) (norm_nonneg _)
        _ = ‖Q‖ * (‖c j‖ * (l'.map (fun k => ‖c k‖)).prod) := by ring

private lemma mlApplyList_congr {E Z W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {c₁ c₂ : ∀ j : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin j => E) Z} :
    ∀ {m : ℕ} (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W)
      (l : List ℕ) (hlen : l.length = m),
      (∀ j ∈ l, c₁ j = c₂ j) → mlApplyList c₁ Q l hlen = mlApplyList c₂ Q l hlen
  | 0, _, [], _, _ => rfl
  | m + 1, Q, j :: l', hlen, hEq => by
      simp only [mlApplyList]
      rw [hEq j (List.mem_cons_self ..),
          mlApplyList_congr (mlPopFront Q) l' (by simpa using hlen)
            (fun k hk => hEq k (List.mem_cons_of_mem _ hk))]

/- Cauchy product for m-multilinear map evaluated on a power series -/

private noncomputable def sumEvalList {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ}
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W) (a : ℕ → Z) (k : ℕ) : W :=
  ((compList m k).attach.map (fun l => evalList Q a l.1 (mem_compList.mp l.2).1)).sum

private lemma sumEvalList_eq_zero_of_nil {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ}
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W) (a : ℕ → Z) (k : ℕ)
    (h : compList m k = []) : sumEvalList Q a k = 0 := by
  unfold sumEvalList
  have hattach : (compList m k).attach = [] := by rw [h]; rfl
  rw [hattach]; simp

private lemma norm_sumEvalList_le {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ}
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W) (a : ℕ → Z) (k : ℕ) :
    ‖sumEvalList Q a k‖ ≤ ‖Q‖ * ((compList m k).map (fun l => (l.map (fun j => ‖a j‖)).prod)).sum := by
  have h1 : ‖sumEvalList Q a k‖ ≤
      (((compList m k).attach.map (fun l => ‖evalList Q a l.1 (mem_compList.mp l.2).1‖)).sum) := by
    unfold sumEvalList
    simpa only [List.map_map, Function.comp_def] using list_norm_sum_le
      ((compList m k).attach.map (fun l => evalList Q a l.1 (mem_compList.mp l.2).1))
  have h2 : (((compList m k).attach.map (fun l => ‖evalList Q a l.1 (mem_compList.mp l.2).1‖)).sum) ≤
      ((compList m k).map (fun l => ‖Q‖ * (l.map (fun j => ‖a j‖)).prod)).sum := by
    rw [← list_map_attach_val (compList m k) (fun l => ‖Q‖ * (l.map (fun j => ‖a j‖)).prod)]
    exact List.sum_le_sum (fun l _ => norm_evalList_le Q a l.1 (mem_compList.mp l.2).1)
  rw [list_sum_map_mul_left] at h2
  exact h1.trans h2

private lemma hasSum_compList_prod {b : ℕ → ℝ} (hb_nn : ∀ j, 0 ≤ b j)
    (hb_sum : Summable (fun i : ℕ => b (i + 1))) :
    ∀ m : ℕ, HasSum (fun k : ℕ => ((compList m k).map (fun l => (l.map b).prod)).sum)
      ((∑' i : ℕ, b (i + 1)) ^ m)
  | 0 => by
    have h0 : (fun k : ℕ => ((compList 0 k).map (fun l => (l.map b).prod)).sum) =
        fun k => if k = 0 then (1 : ℝ) else 0 := by
      ext k; by_cases hk : k = 0 <;> simp [compList, hk]
    rw [h0, pow_zero]
    exact hasSum_ite_eq 0 (1 : ℝ)
  | m + 1 => by
    have hih := hasSum_compList_prod hb_nn hb_sum m
    let f : ℕ → ℝ := fun k => if k = 0 then 0 else b k
    have hf_sum : HasSum f (∑' i : ℕ, b (i + 1)) := by
      have := (hasSum_nat_add_iff' 1 (f := f)).mp (by simpa [f] using hb_sum.hasSum)
      exact this
    have hf_norm : Summable (fun k => ‖f k‖) := by
      have : (fun k => ‖f k‖) = f := by
        ext k; by_cases hk : k = 0 <;> simp [f, hk, Real.norm_of_nonneg (hb_nn k)]
      rw [this]; exact hf_sum.summable
    have hih_norm : Summable (fun k => ‖((compList m k).map (fun l => (l.map b).prod)).sum‖) := by
      have : (fun k => ‖((compList m k).map (fun l => (l.map b).prod)).sum‖) =
          fun k => ((compList m k).map (fun l => (l.map b).prod)).sum := by
        ext k
        apply Real.norm_of_nonneg
        apply List.sum_nonneg
        intro r hr
        rcases List.mem_map.mp hr with ⟨l, _, rfl⟩
        exact List.prod_nonneg (fun _ hx => by rcases List.mem_map.mp hx with ⟨j, _, rfl⟩; exact hb_nn j)
      rw [this]; exact hih.summable
    have hsum_anti : Summable (fun k => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal k,
        f kl.1 * ((compList m kl.2).map (fun l => (l.map b).prod)).sum) :=
      (summable_norm_sum_mul_antidiagonal_of_summable_norm hf_norm hih_norm).of_norm
    have htsum_eq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf_norm hih_norm
    rw [hf_sum.tsum_eq, hih.tsum_eq] at htsum_eq
    have hcauchy : HasSum (fun k => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal k,
        f kl.1 * ((compList m kl.2).map (fun l => (l.map b).prod)).sum)
        ((∑' i : ℕ, b (i + 1)) * (∑' i : ℕ, b (i + 1)) ^ m) :=
      htsum_eq ▸ hsum_anti.hasSum
    rw [pow_succ']
    refine hcauchy.congr_fun fun k => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * ((compList m j).map (fun l => (l.map b).prod)).sum)]
    symm
    -- Show ∑ i ∈ range (k+1), f i * S_m (k - i) = ((compList (m+1) k).map prod).sum
    change (∑ i ∈ Finset.range (k + 1),
      f i * ((compList m (k - i)).map (fun l => (l.map b).prod)).sum) =
      ((compList (m + 1) k).map (fun l => (l.map b).prod)).sum
    rw [Finset.sum_range_succ']
    simp only [f, ite_true, zero_mul, add_zero]
    have hstep : ((compList (m + 1) k).map (fun l => (l.map b).prod)).sum =
        ∑ i ∈ Finset.range k,
          b (i + 1) * ((compList m (k - (i + 1))).map (fun l => (l.map b).prod)).sum := by
      change (((List.range k).flatMap fun i =>
          (compList m (k - (i + 1))).map fun l => (i + 1) :: l).map (fun l => (l.map b).prod)).sum = _
      rw [List.map_flatMap, list_sum_flatMap, ← list_sum_range_eq_finset]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [List.map_map]
      have hcomp : (fun l : List ℕ => (l.map b).prod) ∘ (fun l : List ℕ => (i + 1) :: l) =
          fun l => b (i + 1) * (l.map b).prod := by ext l; simp
      rw [hcomp, list_sum_map_mul_left]
    rw [hstep]
    apply Finset.sum_congr rfl
    intro i _
    simp

private lemma list_sum_map_eval_apply {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {α : Type} (L : List α)
    (g : α → (Z →L[ℝ] W)) (x : Z) :
    (L.map g).sum x = (L.map (fun a => g a x)).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih]

private lemma sumEvalList_succ {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ}
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Z) W) (a : ℕ → Z) (k : ℕ) :
    sumEvalList Q a k =
      ∑ i ∈ Finset.range k, sumEvalList (mlPopFront Q) a (k - (i + 1)) (a (i + 1)) := by
  -- Use Finset.sum via list_sum_flatMap on unattached compList by defining a total wrapper
  have h1 : ∀ (L : List (List ℕ)) (hL : ∀ l ∈ L, l.length = m + 1),
      (L.attach.map (fun l => evalList Q a l.1 (hL l.1 l.2))).sum =
      (L.map (fun l => if h : l.length = m + 1 then evalList Q a l h else 0)).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons x xs ih =>
      simp only [List.attach_cons, List.map_cons, List.sum_cons, List.map_map]
      rw [dif_pos (hL x (List.mem_cons_self ..))]
      congr 1
      exact ih (fun l hl => hL l (List.mem_cons_of_mem _ hl))
  have h2 : ∀ (L : List (List ℕ)) (hL : ∀ l ∈ L, l.length = m),
      (L.attach.map (fun l => evalList (mlPopFront Q) a l.1 (hL l.1 l.2))).sum =
      (L.map (fun l => if h : l.length = m then evalList (mlPopFront Q) a l h else 0)).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons x xs ih =>
      simp only [List.attach_cons, List.map_cons, List.sum_cons, List.map_map]
      rw [dif_pos (hL x (List.mem_cons_self ..))]
      congr 1
      exact ih (fun l hl => hL l (List.mem_cons_of_mem _ hl))
  unfold sumEvalList
  rw [h1 _ (fun l hl => (mem_compList.mp hl).1)]
  change (((List.range k).flatMap fun i =>
      (compList m (k - (i + 1))).map fun l => (i + 1) :: l).map
        (fun l => if h : l.length = m + 1 then evalList Q a l h else 0)).sum = _
  rw [List.map_flatMap]
  -- Prove list sum over flatMap in W
  have hflat : ∀ (L : List ℕ) (f : ℕ → List W),
      (L.flatMap f).sum = (L.map (fun x => (f x).sum)).sum := by
    intro L f
    induction L with
    | nil => simp
    | cons x xs ih => simp [List.flatMap_cons, List.sum_append, ih]
  have hrange : ∀ (n : ℕ) (f : ℕ → W), ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    intro n f
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [hflat, hrange]
  apply Finset.sum_congr rfl
  intro i _
  rw [h2 _ (fun l hl => (mem_compList.mp hl).1), list_sum_map_eval_apply, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hlen : l.length = m := (mem_compList.mp hl).1
  have hlen' : ((i + 1) :: l).length = m + 1 := by simp [hlen]
  simp only [Function.comp_apply, dif_pos hlen, dif_pos hlen']
  rfl

private lemma hasSum_sumEvalList {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace Z] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {a : ℕ → Z} {t : ℝ} (hsum : Summable (fun i : ℕ => ‖a (i + 1)‖ * |t| ^ (i + 1))) :
    ∀ {m : ℕ} (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Z) W),
      HasSum (fun k : ℕ => (t ^ k) • sumEvalList Q a k)
        (Q (fun _ => ∑' i : ℕ, (t ^ (i + 1)) • a (i + 1)))
  | 0, Q => by
    have h0 : (fun k : ℕ => (t ^ k) • sumEvalList Q a k) =
        fun k => if k = 0 then Q ![] else 0 := by
      ext k
      by_cases hk : k = 0
      · subst hk; simp [sumEvalList, compList, evalList]
      · have hnil : compList 0 k = [] := by unfold compList; simp [hk]
        have hzero : sumEvalList Q a k = 0 := by
          unfold sumEvalList
          have hattach : (compList 0 k).attach = [] := by rw [hnil]; rfl
          rw [hattach]; simp
        simp [hzero, hk]
    rw [h0]
    have hQ : Q (fun _ => ∑' i : ℕ, (t ^ (i + 1)) • a (i + 1)) = Q ![] := by
      congr 1; ext i; exact Fin.elim0 i
    rw [hQ]
    exact hasSum_ite_eq 0 (Q ![])
  | m + 1, Q => by
    set z : Z := ∑' i : ℕ, (t ^ (i + 1)) • a (i + 1)
    have hih := hasSum_sumEvalList hsum (mlPopFront Q)
    have hz_sum : HasSum (fun i : ℕ => (t ^ (i + 1)) • a (i + 1)) z := by
      refine Summable.hasSum (Summable.of_norm ?_)
      refine hsum.congr (fun i => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]
    let g : ℕ → Z := fun k => if k = 0 then 0 else (t ^ k) • a k
    have hg_sum : HasSum g z :=
      (hasSum_nat_add_iff' 1 (f := g)).mp (by simpa [g] using hz_sum)
    have hg_norm : Summable (fun k => ‖g k‖) := by
      have h1 : Summable (fun i => ‖g (i + 1)‖) := by
        refine hsum.congr (fun i => ?_)
        simp only [g, Nat.succ_ne_zero, ite_false, norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]
      exact (summable_nat_add_iff 1).mp h1
    let S : ℕ → (Z →L[ℝ] W) := fun r => (t ^ r) • sumEvalList (mlPopFront Q) a r
    have hS_norm : Summable (fun r => ‖S r‖) := by
      let b : ℕ → ℝ := fun j => ‖a j‖ * |t| ^ j
      have hb_nn : ∀ j, 0 ≤ b j := fun j => by positivity
      have hb_sum : Summable (fun i => b (i + 1)) := hsum
      have hcomp_sum := (hasSum_compList_prod hb_nn hb_sum m).summable.mul_left ‖mlPopFront Q‖
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => ?_) hcomp_sum
      have h1 := norm_sumEvalList_le (mlPopFront Q) a r
      have h2 : ‖S r‖ = |t| ^ r * ‖sumEvalList (mlPopFront Q) a r‖ := by
        simp [S, norm_smul, Real.norm_eq_abs]
      rw [h2]
      have hprod_eq : |t| ^ r * ((compList m r).map (fun l => (l.map (fun j => ‖a j‖)).prod)).sum =
          ((compList m r).map (fun l => (l.map b).prod)).sum := by
        rw [← list_sum_map_mul_left]
        congr 1
        apply List.map_congr_left
        intro l hl
        have hsum_l : l.sum = r := (mem_compList.mp hl).2.1
        rw [← hsum_l]
        clear hsum_l hl
        induction l with
        | nil => simp
        | cons j ls ih =>
          simp only [List.sum_cons, List.map_cons, List.prod_cons, pow_add, b]
          rw [mul_assoc, ← ih]; ring
      calc |t| ^ r * ‖sumEvalList (mlPopFront Q) a r‖
          ≤ |t| ^ r * (‖mlPopFront Q‖ * ((compList m r).map (fun l => (l.map (fun j => ‖a j‖)).prod)).sum) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖mlPopFront Q‖ * (|t| ^ r * ((compList m r).map (fun l => (l.map (fun j => ‖a j‖)).prod)).sum) := by ring
        _ = ‖mlPopFront Q‖ * ((compList m r).map (fun l => (l.map b).prod)).sum := by rw [hprod_eq]
    -- Bilinear Cauchy product of HasSum S (mlPopFront Q (fun _ => z)) and HasSum g z
    have hprod_summable : Summable (fun p : ℕ × ℕ => S p.2 (g p.1)) := by
      refine Summable.of_norm ?_
      have hmul : Summable (fun p : ℕ × ℕ => ‖S p.2‖ * ‖g p.1‖) :=
        (hg_norm.mul_of_nonneg hS_norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
          (fun p => mul_comm _ _)
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hmul
      exact ContinuousLinearMap.le_opNorm (S p.2) (g p.1)
    have hsum_prod : HasSum (fun p : ℕ × ℕ => S p.2 (g p.1)) (mlPopFront Q (fun _ => z) z) := by
      have h1 : HasSum (fun i => ∑' r, S r (g i)) (mlPopFront Q (fun _ => z) z) := by
        have heq : ∀ i, ∑' r, S r (g i) = mlPopFront Q (fun _ => z) (g i) := by
          intro i
          exact ((ContinuousLinearMap.apply ℝ W (g i)).hasSum hih).tsum_eq
        simp_rw [heq]
        exact (mlPopFront Q (fun _ => z)).hasSum hg_sum
      have ht := hprod_summable.tsum_prod
      have hval : ∑' p : ℕ × ℕ, S p.2 (g p.1) = mlPopFront Q (fun _ => z) z := by
        rw [ht]
        exact h1.tsum_eq
      exact hval ▸ hprod_summable.hasSum
    -- Group hsum_prod by diagonal k = p.1 + p.2 via Equiv.sigmaFiberEquiv
    have hgroup : HasSum (fun k : ℕ => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, S p.2 (g p.1))
        (mlPopFront Q (fun _ => z) z) := by
      have hEq : (fun k : ℕ => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, S p.2 (g p.1)) =
          fun k => ∑' x : {p : ℕ × ℕ // p.1 + p.2 = k}, S x.1.2 (g x.1.1) := by
        ext k
        let e : (Finset.HasAntidiagonal.antidiagonal k) ≃ {p : ℕ × ℕ // p.1 + p.2 = k} :=
          { toFun := fun p => ⟨p.1, Finset.HasAntidiagonal.mem_antidiagonal.mp p.2⟩
            invFun := fun x => ⟨x.1, Finset.HasAntidiagonal.mem_antidiagonal.mpr x.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← e.tsum_eq, tsum_fintype]
        simp only [e, Equiv.coe_fn_mk]
        exact (Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal k) (fun p => S p.2 (g p.1))).symm
      rw [hEq]
      have hsig := (Equiv.sigmaFiberEquiv (fun p : ℕ × ℕ => p.1 + p.2)).hasSum_iff.mpr hsum_prod
      exact hsig.sigma (fun k => (hprod_summable.subtype _).hasSum)
    have hQeq : Q (fun _ => z) = mlPopFront Q (fun _ => z) z := by
      rw [mlPopFront_apply]
      congr 1; ext i; cases i using Fin.cases <;> rfl
    rw [hQeq]
    refine hgroup.congr_fun fun k => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => S j (g i)), Finset.sum_range_succ', sumEvalList_succ]
    simp only [g, ite_true, map_zero, add_zero, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    simp only [S, Nat.succ_ne_zero, ite_false, smul_apply, map_smul, smul_smul]
    congr 1
    rw [← pow_add]
    congr 1
    omega

/- Structural recursion for the Cauchy-majorant multilinear power series `c` -/

private noncomputable def cSeq {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z)) :
    ℕ → ∀ k : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin k => E) Z
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => mlEval (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (P 0 ![]))
  | N + 1, k + 2 =>
      ((k + 2 : ℝ)⁻¹) • ∑ m ∈ Finset.Icc 1 (k + 1),
        ((compList m (k + 1)).attach.map fun l =>
          mlEval ((mlApplyList (cSeq P N) (P m) l.1 (mem_compList.mp l.2).1).domDomCongr
            (finCongr (mem_compList.mp l.2).2.1))).sum

private lemma cSeq_stable {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z)) :
    ∀ k N₁ N₂, k ≤ N₁ → k ≤ N₂ → cSeq P N₁ k = cSeq P N₂ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro N₁ N₂ h₁ h₂
    match k with
    | 0 =>
      cases N₁ <;> cases N₂ <;> rfl
    | 1 =>
      obtain ⟨n₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₁ ≠ 0)
      obtain ⟨n₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₂ ≠ 0)
      rfl
    | k' + 2 =>
      obtain ⟨n₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₁ ≠ 0)
      obtain ⟨n₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₂ ≠ 0)
      simp only [cSeq]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      congr 1
      apply List.map_congr_left
      intro l _
      congr 2
      apply mlApplyList_congr
      intro j hj
      have hj_le : j ≤ k' + 1 := by
        have hsum := (mem_compList.mp l.2).2.1
        have hle := List.le_sum_of_mem hj
        omega
      exact ih j (by omega) n₁ n₂ (by omega) (by omega)

private noncomputable def cSer {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z)) : FormalMultilinearSeries ℝ E Z :=
  fun k => cSeq P k k

private lemma cSer_zero {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z)) : cSer P 0 = 0 := rfl

private lemma cSer_one_diag {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z)) (v : E) :
    cSer P 1 (fun _ => v) = P 0 ![] v := rfl

private lemma cSer_succ_succ {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z)) (k : ℕ) :
    cSer P (k + 2) = ((k + 2 : ℝ)⁻¹) • ∑ m ∈ Finset.Icc 1 (k + 1),
      ((compList m (k + 1)).attach.map fun l =>
        mlEval ((mlApplyList (cSer P) (P m) l.1 (mem_compList.mp l.2).1).domDomCongr
          (finCongr (mem_compList.mp l.2).2.1))).sum := by
  change cSeq P (k + 2) (k + 2) = _
  simp only [cSeq]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  apply List.map_congr_left
  intro l _
  congr 2
  apply mlApplyList_congr
  intro j hj
  have hj_le : j ≤ k + 1 := by
    have hsum := (mem_compList.mp l.2).2.1
    have hle := List.le_sum_of_mem hj
    omega
  exact cSeq_stable P j (k + 1) j hj_le le_rfl

private lemma cSer_succ_succ_diag {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z)) (k : ℕ) (v : E) :
    ((k + 2 : ℝ)) • cSer P (k + 2) (fun _ => v) =
      ∑ m ∈ Finset.Icc 1 (k + 1),
        sumEvalList (P m) (fun j => cSer P j (fun _ => v)) (k + 1) v := by
  rw [cSer_succ_succ]
  simp only [smul_apply, smul_smul,
    mul_inv_cancel₀ (by positivity : (k + 2 : ℝ) ≠ 0), one_smul,
    sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  have hlist_eval : ∀ (L : List (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 2) => E) Z)),
      L.sum (fun _ => v) = (L.map (fun g => g (fun _ => v))).sum := by
    intro L; induction L with
    | nil => simp
    | cons x xs ih => simp [ih]
  rw [hlist_eval, List.map_map, sumEvalList, list_sum_map_eval_apply]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, mlEval_diag, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  exact mlApplyList_diag (cSer P) (P m) l.1 _ v

private lemma norm_cSer_le {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : FormalMultilinearSeries ℝ Z (E →L[ℝ] Z))
    {M R : ℝ} (hM : 1 ≤ M) (hR : 0 < R) (hP : ∀ m, ‖P m‖ ≤ M * R⁻¹ ^ m) :
    let A := M
    let B := 64 * (M + 1) * (A + 1) / R
    ∀ k : ℕ, 1 ≤ k → ‖cSer P k‖ ≤ A * B ^ (k - 1) / (k : ℝ) ^ 2 := by
  intro A B
  have hA : 1 ≤ A := hM
  have hB_pos : 0 < B := by positivity
  have hratio : 16 * A / (R * B) ≤ 1 / 2 := by
    have hRB : R * B = 64 * (M + 1) * (A + 1) := by dsimp [B]; field_simp [hR.ne']
    rw [div_le_iff₀ (by positivity), hRB]
    nlinarith
  have hpref : 8 * M * A / (R * B) ≤ A := by
    have hRB : R * B = 64 * (M + 1) * (A + 1) := by dsimp [B]; field_simp [hR.ne']
    rw [div_le_iff₀ (by positivity), hRB]
    have h1 : 8 * M ≤ 64 * (M + 1) * (A + 1) := by nlinarith
    nlinarith
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    match k with
    | 0 => omega
    | 1 =>
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.cast_one, one_pow, div_one]
      change ‖mlEval (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (P 0 ![]))‖ ≤ A
      calc ‖mlEval (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (P 0 ![]))‖
          ≤ ‖ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (P 0 ![])‖ := norm_mlEval_le _
        _ = ‖P 0 ![]‖ := by simp [ContinuousMultilinearMap.norm_constOfIsEmpty]
        _ ≤ ‖P 0‖ := by simpa only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] using (P 0).le_opNorm ![]
        _ ≤ M * R⁻¹ ^ 0 := hP 0
        _ = A := by simp [A]
    | n + 2 =>
      set s := n + 1
      have hs1 : 1 ≤ s := Nat.succ_pos n
      rw [cSer_succ_succ, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hsum_norm :
          ‖∑ m ∈ Finset.Icc 1 s, ((compList m s).attach.map fun l =>
            mlEval ((mlApplyList (cSer P) (P m) l.1 (mem_compList.mp l.2).1).domDomCongr
              (finCongr (mem_compList.mp l.2).2.1))).sum‖ ≤
          ∑ m ∈ Finset.Icc 1 s,
            (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * ((16 : ℝ) ^ (m - 1) / (s : ℝ) ^ 2) := by
        calc _ ≤ ∑ m ∈ Finset.Icc 1 s,
              ‖((compList m s).attach.map fun l =>
                mlEval ((mlApplyList (cSer P) (P m) l.1 (mem_compList.mp l.2).1).domDomCongr
                  (finCongr (mem_compList.mp l.2).2.1))).sum‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ Finset.Icc 1 s,
              (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * ((16 : ℝ) ^ (m - 1) / (s : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
            have hms : m ≤ s := (Finset.mem_Icc.mp hm).2
            have h1 : ‖((compList m s).attach.map fun l =>
                mlEval ((mlApplyList (cSer P) (P m) l.1 (mem_compList.mp l.2).1).domDomCongr
                  (finCongr (mem_compList.mp l.2).2.1))).sum‖ ≤
                ((compList m s).attach.map fun l =>
                  (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * (l.1.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod).sum := by
              refine (list_norm_sum_le _).trans ?_
              rw [List.map_map]
              refine List.sum_le_sum fun l _ => ?_
              dsimp only [Function.comp_apply]
              have hlen := (mem_compList.mp l.2).1
              have hsuml := (mem_compList.mp l.2).2.1
              have hposl := (mem_compList.mp l.2).2.2
              have hn1 := norm_mlEval_le ((mlApplyList (cSer P) (P m) l.1 hlen).domDomCongr (finCongr hsuml))
              rw [ContinuousMultilinearMap.norm_domDomCongr] at hn1
              have hn2 := norm_mlApplyList_le (cSer P) (P m) l.1 hlen
              have hprod_le : (l.1.map (fun j => ‖cSer P j‖)).prod ≤
                  A ^ m * B ^ (s - m) * (l.1.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod := by
                have hgen : ∀ (L : List ℕ), (∀ j ∈ L, 1 ≤ j ∧ j ≤ s) →
                    (L.map (fun j => ‖cSer P j‖)).prod ≤
                      A ^ L.length * B ^ (L.sum - L.length) * (L.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod := by
                  intro L hL
                  induction L with
                  | nil => simp
                  | cons j ls ihL =>
                    have hj1 := (hL j (List.mem_cons_self ..)).1
                    have hjs := (hL j (List.mem_cons_self ..)).2
                    have hcj := ih j (by omega) hj1
                    have hls := ihL (fun r hr => hL r (List.mem_cons_of_mem _ hr))
                    have hls_len : ls.length ≤ ls.sum := by
                      have haux : ∀ L' : List ℕ, (∀ r ∈ L', 1 ≤ r) → L'.length ≤ L'.sum := by
                        intro L' hL'
                        induction L' with
                        | nil => simp
                        | cons a t iht =>
                          have ha1 := hL' a (List.mem_cons_self ..)
                          have ht := iht (fun r hr => hL' r (List.mem_cons_of_mem _ hr))
                          simp; omega
                      exact haux ls (fun r hr => (hL r (List.mem_cons_of_mem _ hr)).1)
                    simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons]
                    calc ‖cSer P j‖ * (ls.map (fun r => ‖cSer P r‖)).prod
                        ≤ (A * B ^ (j - 1) / (j : ℝ) ^ 2) *
                            (A ^ ls.length * B ^ (ls.sum - ls.length) *
                              (ls.map (fun r => (1 : ℝ) / (r : ℝ) ^ 2)).prod) :=
                          mul_le_mul hcj hls
                            (List.prod_nonneg (fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact norm_nonneg _))
                            (by positivity)
                      _ = A ^ (ls.length + 1) * (B ^ (j - 1) * B ^ (ls.sum - ls.length)) *
                            ((1 / (j : ℝ) ^ 2) * (ls.map (fun r => (1 : ℝ) / (r : ℝ) ^ 2)).prod) := by
                          rw [pow_succ]; ring
                      _ = A ^ (ls.length + 1) * B ^ (j + ls.sum - (ls.length + 1)) *
                            ((1 / (j : ℝ) ^ 2) * (ls.map (fun r => (1 : ℝ) / (r : ℝ) ^ 2)).prod) := by
                          rw [← pow_add, show (j - 1) + (ls.sum - ls.length) = j + ls.sum - (ls.length + 1) by omega]
                have := hgen l.1 (fun j hj => ⟨hposl j hj, (List.le_sum_of_mem hj).trans hsuml.le⟩)
                rwa [hlen, hsuml] at this
              have hprod_nn : 0 ≤ (l.1.map (fun j => ‖cSer P j‖)).prod :=
                List.prod_nonneg (fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact norm_nonneg _)
              calc _ ≤ ‖P m‖ * (l.1.map (fun j => ‖cSer P j‖)).prod := hn1.trans hn2
                _ ≤ (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m) * (l.1.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod) :=
                    mul_le_mul (hP m) hprod_le hprod_nn (by positivity)
                _ = (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * (l.1.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod := by ring
            have hmap : ((compList m s).attach.map fun l =>
                (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * (l.1.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod).sum =
                (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) *
                  ((compList m s).map (fun l => (l.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod)).sum := by
              rw [list_map_attach_val (compList m s) (fun l =>
                (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * (l.map (fun j => (1 : ℝ) / (j : ℝ) ^ 2)).prod),
                list_sum_map_mul_left]
            rw [hmap] at h1
            exact h1.trans (mul_le_mul_of_nonneg_left (compList_inv_sq_sum m hm1 s hs1) (by positivity))
      -- Bound the sum over m ∈ Icc 1 s by geometric series
      have hgeom : ∑ m ∈ Finset.Icc 1 s,
          (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * ((16 : ℝ) ^ (m - 1) / (s : ℝ) ^ 2) ≤
          (2 * M * A / (R * B)) * (B ^ s / (s : ℝ) ^ 2) := by
        have hterm : ∀ m ∈ Finset.Icc 1 s,
            (M * R⁻¹ ^ m) * (A ^ m * B ^ (s - m)) * ((16 : ℝ) ^ (m - 1) / (s : ℝ) ^ 2) =
            (M * A / (R * B)) * (B ^ s / (s : ℝ) ^ 2) * (16 * A / (R * B)) ^ (m - 1) := by
          intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hms : m ≤ s := (Finset.mem_Icc.mp hm).2
          have hBs : B ^ s = B ^ (s - m) * B ^ (m - 1) * B := by
            rw [← pow_add, ← pow_succ, show s - m + (m - 1) + 1 = s by omega]
          have hRm : R⁻¹ ^ m = R⁻¹ * R⁻¹ ^ (m - 1) := by
            rw [← pow_succ', show m - 1 + 1 = m by omega]
          have hAm : A ^ m = A * A ^ (m - 1) := by
            rw [← pow_succ', show m - 1 + 1 = m by omega]
          have h16 : (16 * A / (R * B)) ^ (m - 1) =
              16 ^ (m - 1) * A ^ (m - 1) * R⁻¹ ^ (m - 1) * B⁻¹ ^ (m - 1) := by
            rw [div_eq_mul_inv, mul_inv, mul_pow, mul_pow, mul_pow]; ring
          have hB1 : B * B⁻¹ = 1 := mul_inv_cancel₀ hB_pos.ne'
          have hBm : B ^ (m - 1) * B⁻¹ ^ (m - 1) = 1 := by rw [← mul_pow, hB1, one_pow]
          have hRB_div : M * A / (R * B) = M * A * R⁻¹ * B⁻¹ := by rw [div_eq_mul_inv, mul_inv]; ring
          rw [hBs, hRm, hAm, h16, hRB_div]
          calc (M * (R⁻¹ * R⁻¹ ^ (m - 1))) * (A * A ^ (m - 1) * B ^ (s - m)) * ((16 : ℝ) ^ (m - 1) / (s : ℝ) ^ 2)
              = (M * A * R⁻¹ * R⁻¹ ^ (m - 1) * A ^ (m - 1) * 16 ^ (m - 1) / (s : ℝ) ^ 2) * B ^ (s - m) * 1 * 1 := by ring
            _ = (M * A * R⁻¹ * R⁻¹ ^ (m - 1) * A ^ (m - 1) * 16 ^ (m - 1) / (s : ℝ) ^ 2) * B ^ (s - m) *
                  (B ^ (m - 1) * B⁻¹ ^ (m - 1)) * (B * B⁻¹) := by rw [hBm, hB1]
            _ = M * A * R⁻¹ * B⁻¹ * (B ^ (s - m) * B ^ (m - 1) * B / (s : ℝ) ^ 2) *
                  (16 ^ (m - 1) * A ^ (m - 1) * R⁻¹ ^ (m - 1) * B⁻¹ ^ (m - 1)) := by ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        have hhalf : ∑ m ∈ Finset.Icc 1 s, (16 * A / (R * B)) ^ (m - 1) ≤ 2 := by
          calc ∑ m ∈ Finset.Icc 1 s, (16 * A / (R * B)) ^ (m - 1)
              ≤ ∑ m ∈ Finset.Icc 1 s, (1 / 2 : ℝ) ^ (m - 1) :=
                Finset.sum_le_sum (fun m _ => pow_le_pow_left₀ (by positivity) hratio _)
            _ = ∑ j ∈ Finset.range s, (1 / 2 : ℝ) ^ j := by
                refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
                · intro m hm; simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢; omega
                · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
                · intro j hj; simp only [Finset.mem_range] at hj
                  exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
                · intro _ _; rfl
            _ = 2 - 2 * (1 / 2 : ℝ) ^ s := by
                rw [geom_sum_eq (by norm_num)]; ring
            _ ≤ 2 := by
                have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ s := by positivity
                linarith
        calc (M * A / (R * B)) * (B ^ s / (s : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 s, (16 * A / (R * B)) ^ (m - 1)
            ≤ (M * A / (R * B)) * (B ^ s / (s : ℝ) ^ 2) * 2 :=
              mul_le_mul_of_nonneg_left hhalf (by positivity)
          _ = (2 * M * A / (R * B)) * (B ^ s / (s : ℝ) ^ 2) := by ring
      have hsq : (1 : ℝ) / (s : ℝ) ^ 2 ≤ 4 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hsR : ((n + 2 : ℕ) : ℝ) = (s : ℝ) + 1 := by dsimp [s]; push_cast; ring
        rw [hsR]
        have h1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
        nlinarith
      have hinv_le1 : ((n + 2 : ℕ) : ℝ)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ n + 2 by omega))
      calc ((n + 2 : ℝ))⁻¹ * ‖∑ m ∈ Finset.Icc 1 s, ((compList m s).attach.map fun l =>
              mlEval ((mlApplyList (cSer P) (P m) l.1 (mem_compList.mp l.2).1).domDomCongr
                (finCongr (mem_compList.mp l.2).2.1))).sum‖
          ≤ 1 * ((2 * M * A / (R * B)) * (B ^ s / (s : ℝ) ^ 2)) :=
            mul_le_mul (by exact_mod_cast hinv_le1) (hsum_norm.trans hgeom) (norm_nonneg _) zero_le_one
        _ = (2 * M * A / (R * B)) * B ^ s * (1 / (s : ℝ) ^ 2) := by ring
        _ ≤ (2 * M * A / (R * B)) * B ^ s * (4 / ((n + 2 : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (8 * M * A / (R * B)) * (B ^ s / ((n + 2 : ℕ) : ℝ) ^ 2) := by ring
        _ ≤ A * (B ^ s / ((n + 2 : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hpref (by positivity)
        _ = A * B ^ (n + 2 - 1) / ((n + 2 : ℕ) : ℝ) ^ 2 := by
            rw [show n + 2 - 1 = s from rfl]; ring

/- Identify ODE solution with power series `cSer P` via Gronwall uniqueness -/

private lemma summable_compList_prod_bound {b : ℕ → ℝ} (hb_nn : ∀ j, 0 ≤ b j)
    (hb_sum : Summable (fun i : ℕ => b (i + 1))) {M R C : ℝ} (hM : 0 ≤ M) (hR : 0 < R) (hC : 0 ≤ C)
    (hSb : ∑' i : ℕ, b (i + 1) ≤ R / 2) :
    Summable (fun p : ℕ × ℕ => (M * R⁻¹ ^ p.1 * C) * ((compList p.1 p.2).map (fun l => (l.map b).prod)).sum) := by
  have hSb_nn : 0 ≤ ∑' i : ℕ, b (i + 1) := tsum_nonneg (fun i => hb_nn (i + 1))
  have houter : Summable (fun m : ℕ => (M * R⁻¹ ^ m * C) * (∑' i : ℕ, b (i + 1)) ^ m) := by
    have hgeo : Summable (fun m : ℕ => (M * C) * (1 / 2 : ℝ) ^ m) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) hgeo
    have h1 : R⁻¹ * ∑' i : ℕ, b (i + 1) ≤ 1 / 2 := by
      rw [← div_eq_inv_mul, div_le_iff₀ hR]; linarith
    calc (M * R⁻¹ ^ m * C) * (∑' i : ℕ, b (i + 1)) ^ m
        = (M * C) * (R⁻¹ * ∑' i : ℕ, b (i + 1)) ^ m := by rw [mul_pow]; ring
      _ ≤ (M * C) * (1 / 2 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 m) (by positivity)
  refine (summable_prod_of_nonneg (fun p => by
    refine mul_nonneg (by positivity) (List.sum_nonneg fun _ hx => ?_)
    rcases List.mem_map.mp hx with ⟨l, _, rfl⟩
    exact List.prod_nonneg fun _ hy => by rcases List.mem_map.mp hy with ⟨j, _, rfl⟩; exact hb_nn j)).mpr ?_
  refine ⟨fun m => (hasSum_compList_prod hb_nn hb_sum m).summable.mul_left (M * R⁻¹ ^ m * C), ?_⟩
  refine houter.congr fun m => ?_
  dsimp only
  rw [tsum_mul_left, (hasSum_compList_prod hb_nn hb_sum m).tsum_eq]

set_option maxHeartbeats 800000 in
private lemma analyticAt_of_radial_ode {n : ℕ}
    {F : E n × E n → (E n →L[ℝ] E n × E n)} {z_fn : E n → E n × E n} {r_v : ℝ}
    (hr_v : 0 < r_v) (hF_an : AnalyticAt ℝ F (0, 0))
    (hz0 : z_fn 0 = (0, 0)) (hz_cont : ContinuousOn z_fn (ball 0 (2 * r_v)))
    (hode : ∀ v ∈ ball 0 r_v, ∀ t ∈ Ioo (-1.5 : ℝ) 1.5,
      HasDerivAt (fun s : ℝ => z_fn (s • v)) (F (z_fn (t • v)) v) t) :
    AnalyticAt ℝ z_fn 0 := by
  obtain ⟨P, r_P, hP⟩ := hF_an
  have hr_P_pos : 0 < r_P := hP.r_pos
  -- Extract R > 0 with (R : ℝ≥0∞) < r_P and M ≥ 1 with ‖P m‖ ≤ M * R⁻¹ ^ m
  obtain ⟨R₀, hR₀_pos, hR₀_lt⟩ : ∃ R₀ : ℝ≥0, 0 < R₀ ∧ (R₀ : ℝ≥0∞) < r_P := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hr_P_pos with ⟨R₀, h1, h2⟩
    exact ⟨R₀, by exact_mod_cast h1, h2⟩
  set R : ℝ := (R₀ : ℝ) / 2
  have hR_pos : 0 < R := by positivity
  have hR_lt_rP : (ENNReal.ofReal R) < r_P := by
    have : ENNReal.ofReal R < (R₀ : ℝ≥0∞) := by
      rw [show (R₀ : ℝ≥0∞) = ENNReal.ofReal (R₀ : ℝ) by simp]
      exact (ENNReal.ofReal_lt_ofReal_iff (R₀.coe_pos.mpr hR₀_pos)).mpr
        (by dsimp [R]; linarith [R₀.coe_pos.mpr hR₀_pos])
    exact this.trans hR₀_lt
  have hP_sum_R : Summable (fun m : ℕ => ‖P m‖ * R ^ m) := by
    let Rnn : ℝ≥0 := ⟨R, hR_pos.le⟩
    have hlt_rad : (ENNReal.ofReal R) < P.radius := hR_lt_rP.trans_le hP.r_le
    have hlt_rad' : (Rnn : ℝ≥0∞) < P.radius := by
      rwa [ENNReal.ofReal_eq_coe_nnreal hR_pos.le] at hlt_rad
    exact P.summable_norm_mul_pow (r := Rnn) hlt_rad'
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ m : ℕ, ‖P m‖ * R ^ m ≤ M₀ := by
    have hbd := hP_sum_R.tendsto_atTop_zero.bddAbove_range
    obtain ⟨M₀, hM₀⟩ := hbd
    exact ⟨M₀, fun m => hM₀ ⟨m, rfl⟩⟩
  set M : ℝ := max 1 M₀
  have hM1 : 1 ≤ M := le_max_left _ _
  have hP_bd : ∀ m : ℕ, ‖P m‖ ≤ M * R⁻¹ ^ m := by
    intro m
    have h1 : ‖P m‖ * R ^ m ≤ M := (hM₀ m).trans (le_max_right _ _)
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hR_pos m)]
    exact h1
  -- Also get a Lipschitz constant K_F for F on closedBall 0 (R / 2)
  have hF_c1 : ContDiffOn ℝ 1 F (ball 0 R) := by
    have h1 : AnalyticOnNhd ℝ F (Metric.eball (0 : E n × E n) r_P) := hP.analyticOnNhd
    have hsub : ball (0 : E n × E n) R ⊆ Metric.eball (0 : E n × E n) r_P := by
      intro z hz
      rw [Metric.mem_eball, edist_dist]
      have hz' := Metric.mem_ball.mp hz
      exact (ENNReal.ofReal_lt_ofReal_iff hR_pos |>.mpr hz').trans hR_lt_rP
    exact ((h1.mono hsub).contDiffOn Metric.isOpen_ball.uniqueDiffOn).of_le le_top
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : E n × E n) (R / 2)).exists_bound_of_continuousOn
    ((hF_c1.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).mono
      (Metric.closedBall_subset_ball (by linarith)))
  set K_F : ℝ≥0 := ⟨max 0 K₀, le_max_left _ _⟩
  have hF_lip : LipschitzOnWith K_F F (closedBall (0 : E n × E n) (R / 2)) := by
    refine (convex_closedBall (0 : E n × E n) (R / 2)).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hF_c1.differentiableOn (by decide) z (Metric.closedBall_subset_ball (by linarith) hz)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball (by linarith) hz))) ?_
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hK₀ z hz).trans (le_max_right _ _)
  -- Set up c = cSer P and its convergence radius
  set A : ℝ := M
  set B : ℝ := 64 * (M + 1) * (A + 1) / R
  have hB_pos : 0 < B := by positivity
  have hc_bd : ∀ k : ℕ, 1 ≤ k → ‖cSer P k‖ ≤ A * B ^ (k - 1) / (k : ℝ) ^ 2 :=
    norm_cSer_le P hM1 hR_pos hP_bd
  -- Pick r_g small enough so both z_fn(t•v) and g(t, v) stay in closedBall 0 (R / 2) for t ∈ [-1.2, 1.2]
  have hz_small : ∀ᶠ v in 𝓝 (0 : E n), z_fn v ∈ closedBall (0 : E n × E n) (R / 2) :=
    (hz_cont.continuousAt (Metric.ball_mem_nhds 0 (by positivity))).eventually
      (by rw [hz0]; exact Metric.closedBall_mem_nhds 0 (by positivity))
  obtain ⟨r_z, hr_z, hbr_z⟩ := Metric.mem_nhds_iff.mp hz_small
  set r_g : ℝ := min (r_v / 2) (min (r_z / 2) (min (1 / (8 * B)) (R / (16 * A))))
  have hr_g : 0 < r_g := by positivity
  have hrg_rv : r_g < r_v := by have := min_le_left (r_v / 2) (min (r_z / 2) (min (1 / (8 * B)) (R / (16 * A)))); linarith
  have hrg_rz : 1.5 * r_g < r_z := by
    have : r_g ≤ r_z / 2 := le_trans (min_le_right _ _) (min_le_left _ _); linarith
  have hrg_B : 1.5 * r_g * B ≤ 1 / 4 := by
    have : r_g ≤ 1 / (8 * B) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have h1 : r_g * B ≤ 1 / 8 := by rw [le_div_iff₀ (by positivity)] at this; linarith
    linarith
  have hrg_A : 4 * A * (1.5 * r_g) ≤ R / 2 := by
    have : r_g ≤ R / (16 * A) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have h1 : 16 * A * r_g ≤ R := by rw [le_div_iff₀ (by positivity)] at this; linarith
    linarith
  -- Show z_fn v = ∑' k, cSer P k (fun _ => v) for every v ∈ ball 0 r_g
  have hmain_eq : ∀ v ∈ ball 0 r_g, HasSum (fun k => cSer P k (fun _ => v)) (z_fn v) := by
    intro v hv
    have hv_norm : ‖v‖ < r_g := by simpa [Metric.mem_ball, dist_zero_right] using hv
    let g : ℝ → E n × E n := fun t => ∑' k : ℕ, (t ^ k) • cSer P k (fun _ => v)
    let u : ℕ → ℝ := fun k => if k = 0 then 0 else (A / B) * (1 / 4 : ℝ) ^ k * 2
    -- Wait: uniform bound on derivative term ‖k * t^(k-1) • c_k(v)‖ for |t| < 1.5
    have hterm_bd : ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, |t| ≤ 1.5 →
        ‖(t ^ k) • cSer P k (fun _ => v)‖ ≤ A * (1.5 * r_g) * (1 / 4 : ℝ) ^ (k - 1) ∧
        ‖((k : ℝ) * t ^ (k - 1)) • cSer P k (fun _ => v)‖ ≤ A * r_g * (1 / 4 : ℝ) ^ (k - 1) := by
      intro k hk t ht
      have hcv : ‖cSer P k (fun _ => v)‖ ≤ (A * B ^ (k - 1) / (k : ℝ) ^ 2) * r_g ^ k := by
        calc ‖cSer P k (fun _ => v)‖
            ≤ ‖cSer P k‖ * ∏ _i : Fin k, ‖v‖ := (cSer P k).le_opNorm _
          _ = ‖cSer P k‖ * ‖v‖ ^ k := by simp
          _ ≤ (A * B ^ (k - 1) / (k : ℝ) ^ 2) * r_g ^ k :=
              mul_le_mul (hc_bd k hk) (pow_le_pow_left₀ (norm_nonneg v) hv_norm.le k) (by positivity) (by positivity)
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hpow_rg : r_g ^ k = r_g * r_g ^ (k - 1) := by
        rw [← pow_succ', show k - 1 + 1 = k by omega]
      have hpow_t : |t| ^ k ≤ (1.5 : ℝ) ^ k := pow_le_pow_left₀ (abs_nonneg t) ht k
      have hpow_t1 : |t| ^ (k - 1) ≤ (1.5 : ℝ) ^ (k - 1) := pow_le_pow_left₀ (abs_nonneg t) ht (k - 1)
      have hprod_pow : (1.5 : ℝ) ^ (k - 1) * (B ^ (k - 1) * r_g ^ (k - 1)) ≤ (1 / 4 : ℝ) ^ (k - 1) := by
        rw [← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) (k - 1)
      constructor
      · rw [norm_smul, Real.norm_eq_abs, abs_pow]
        calc |t| ^ k * ‖cSer P k (fun _ => v)‖
            ≤ (1.5 : ℝ) ^ k * ((A * B ^ (k - 1) / (k : ℝ) ^ 2) * r_g ^ k) :=
              mul_le_mul hpow_t hcv (norm_nonneg _) (by positivity)
          _ ≤ (1.5 : ℝ) ^ k * ((A * B ^ (k - 1) / 1) * r_g ^ k) := by
              gcongr; nlinarith
          _ = A * (1.5 * r_g) * ((1.5 : ℝ) ^ (k - 1) * (B ^ (k - 1) * r_g ^ (k - 1))) := by
              rw [hpow_rg, show (1.5 : ℝ) ^ k = 1.5 * (1.5 : ℝ) ^ (k - 1) by
                rw [← pow_succ', show k - 1 + 1 = k by omega]]; ring
          _ ≤ A * (1.5 * r_g) * (1 / 4 : ℝ) ^ (k - 1) :=
              mul_le_mul_of_nonneg_left hprod_pow (by positivity)
      · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k), abs_pow]
        calc (k : ℝ) * |t| ^ (k - 1) * ‖cSer P k (fun _ => v)‖
            ≤ (k : ℝ) * (1.5 : ℝ) ^ (k - 1) * ((A * B ^ (k - 1) / (k : ℝ) ^ 2) * r_g ^ k) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hpow_t1 (by positivity)) hcv (norm_nonneg _) (by positivity)
          _ = (1 / (k : ℝ)) * (A * r_g * ((1.5 : ℝ) ^ (k - 1) * (B ^ (k - 1) * r_g ^ (k - 1)))) := by
              rw [hpow_rg]; field_simp
          _ ≤ 1 * (A * r_g * (1 / 4 : ℝ) ^ (k - 1)) :=
              mul_le_mul ((div_le_one (by positivity)).mpr hk1)
                (mul_le_mul_of_nonneg_left hprod_pow (by positivity)) (by positivity) zero_le_one
          _ = A * r_g * (1 / 4 : ℝ) ^ (k - 1) := one_mul _
    -- Prove HasDerivAt g (F (g t) v) t for all t ∈ Ioo (-1.5) 1.5
    have hg_deriv : ∀ t ∈ Ioo (-1.5 : ℝ) 1.5, HasDerivAt g (F (g t) v) t := by
      intro t ht
      have ht_abs : |t| ≤ 1.5 := (abs_lt.mpr ⟨ht.1, ht.2⟩).le
      let u_bd : ℕ → ℝ := fun k => if k = 0 then 0 else A * r_g * (1 / 4 : ℝ) ^ (k - 1)
      have hu_sum : Summable u_bd := by
        rw [← summable_nat_add_iff 1]
        have h1 : (fun i : ℕ => u_bd (i + 1)) = fun i => (A * r_g) * (1 / 4 : ℝ) ^ i := by
          ext i; simp [u_bd]
        rw [h1]
        exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      have hg_hasDeriv : HasDerivAt g (∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • cSer P k (fun _ => v)) t := by
        change HasDerivAt (fun s : ℝ => ∑' k : ℕ, (s ^ k) • cSer P k (fun _ => v))
          (∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • cSer P k (fun _ => v)) t
        refine hasDerivAt_tsum_of_isPreconnected
          (g := fun k s => (s ^ k) • cSer P k (fun _ => v))
          (g' := fun k s => ((k : ℝ) * s ^ (k - 1)) • cSer P k (fun _ => v))
          (y₀ := (0 : ℝ))
          hu_sum isOpen_Ioo isPreconnected_Ioo ?_ ?_
          (show (0 : ℝ) ∈ Ioo (-1.5 : ℝ) 1.5 by norm_num) ?_ ht
        · intro k s _
          cases k with
          | zero => simp [cSer_zero]; exact hasDerivAt_const s (0 : E n × E n)
          | succ k' =>
            simpa using (hasDerivAt_pow (k' + 1) s).smul_const (cSer P (k' + 1) (fun _ => v))
        · intro k s hs
          cases k with
          | zero => simp [cSer_zero, u_bd]
          | succ k' =>
            simpa [u_bd] using (hterm_bd (k' + 1) (Nat.succ_pos k') s (abs_lt.mpr ⟨hs.1, hs.2⟩).le).2
        · refine Summable.of_norm ?_
          have h0 : (fun k : ℕ => ‖((0 : ℝ) ^ k) • cSer P k (fun _ => v)‖) = fun _ => 0 := by
            ext k; cases k with
            | zero => simp [cSer_zero]
            | succ k' => simp [zero_pow (Nat.succ_ne_zero k')]
          rw [h0]; exact summable_zero
      -- Show g t ∈ closedBall 0 (R / 2) ⊆ ball 0 R
      have hsum_gt : Summable (fun i : ℕ => ‖cSer P (i + 1) (fun _ => v)‖ * |t| ^ (i + 1)) := by
        have hgeom : Summable (fun i : ℕ => A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i) :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => ?_) hgeom
        have := (hterm_bd (i + 1) (Nat.succ_pos i) t ht_abs).1
        simpa [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm] using this
      have hgt_norm : ‖g t‖ ≤ R / 2 := by
        have hgt_eq : g t = ∑' i : ℕ, (t ^ (i + 1)) • cSer P (i + 1) (fun _ => v) := by
          have hs_all : Summable (fun k : ℕ => (t ^ k) • cSer P k (fun _ => v)) := by
            rw [← summable_nat_add_iff 1]
            exact Summable.of_norm (hsum_gt.congr fun i => by
              rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm])
          rw [show g t = ∑' k : ℕ, (t ^ k) • cSer P k (fun _ => v) from rfl, tsum_nat_zero_add hs_all]
          simp [cSer_zero]
        rw [hgt_eq]
        have hgeom : Summable (fun i : ℕ => A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i) :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        have hle1 : ‖∑' i : ℕ, (t ^ (i + 1)) • cSer P (i + 1) (fun _ => v)‖ ≤
            ∑' i : ℕ, A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i := by
          calc _ ≤ ∑' i : ℕ, ‖(t ^ (i + 1)) • cSer P (i + 1) (fun _ => v)‖ :=
                norm_tsum_le_tsum_norm (hsum_gt.congr fun i => by
                  rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm])
            _ ≤ ∑' i : ℕ, A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i :=
                Summable.tsum_le_tsum (fun i => (hterm_bd (i + 1) (Nat.succ_pos i) t ht_abs).1)
                  (hsum_gt.congr fun i => by rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]) hgeom
        have hgeval : ∑' i : ℕ, A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i = A * (1.5 * r_g) * (4 / 3) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
        rw [hgeval] at hle1
        nlinarith
      -- Show F (g t) v = ∑' k, (k * t^(k-1)) • c_k(v) via P-expansion and compList Cauchy product
      have hF_eq_deriv : F (g t) v = ∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • cSer P k (fun _ => v) := by
        have hgt_eball : g t ∈ Metric.eball (0 : E n × E n) r_P := by
          rw [Metric.mem_eball, edist_dist, dist_zero_right]
          exact (ENNReal.ofReal_lt_ofReal_iff hR_pos |>.mpr (by linarith)).trans hR_lt_rP
        have hF_hasSum : HasSum (fun m : ℕ => P m (fun _ => g t) v) (F (g t) v) := by
          have h1 := hP.hasSum (by simpa using hgt_eball)
          have h1' : HasSum (fun m : ℕ => P m (fun _ => g t)) (F (g t)) := by
            rwa [show ((0 : E n), (0 : E n)) + g t = g t from zero_add _] at h1
          exact (ContinuousLinearMap.apply ℝ (E n × E n) v).hasSum h1'
        have hgt_shift : g t = ∑' i : ℕ, (t ^ (i + 1)) • cSer P (i + 1) (fun _ => v) := by
          have hs_all : Summable (fun k : ℕ => (t ^ k) • cSer P k (fun _ => v)) := by
            rw [← summable_nat_add_iff 1]
            exact Summable.of_norm (hsum_gt.congr fun i => by
              rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm])
          rw [show g t = ∑' k : ℕ, (t ^ k) • cSer P k (fun _ => v) from rfl, tsum_nat_zero_add hs_all]
          simp [cSer_zero]
        have hinner : ∀ m : ℕ, HasSum
            (fun k : ℕ => (t ^ k) • (sumEvalList (P m) (fun j => cSer P j (fun _ => v)) k v))
            (P m (fun _ => g t) v) := by
          intro m
          have h1 := hasSum_sumEvalList (a := fun j => cSer P j (fun _ => v)) hsum_gt (P m)
          rw [← hgt_shift] at h1
          have h2 := (ContinuousLinearMap.apply ℝ (E n × E n) v).hasSum h1
          simpa using h2
        -- Double summability over (m, k)
        let term : ℕ × ℕ → E n × E n := fun p =>
          (t ^ p.2) • (sumEvalList (P p.1) (fun j => cSer P j (fun _ => v)) p.2 v)
        have hdouble : Summable term := by
          refine Summable.of_norm ?_
          let b : ℕ → ℝ := fun j => ‖cSer P j (fun _ => v)‖ * |t| ^ j
          have hb_nn : ∀ j, 0 ≤ b j := fun j => by positivity
          have hS_b_le : ∑' i : ℕ, b (i + 1) ≤ R / 2 := by
            have hgeom : Summable (fun i : ℕ => A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i) :=
              (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
            have hle1 : ∑' i : ℕ, b (i + 1) ≤ ∑' i : ℕ, A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i :=
              Summable.tsum_le_tsum (fun i => by
                have := (hterm_bd (i + 1) (Nat.succ_pos i) t ht_abs).1
                simpa [b, norm_smul, Real.norm_eq_abs, abs_pow, mul_comm] using this) hsum_gt hgeom
            rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hle1
            nlinarith
          have hbound_prod : Summable (fun p : ℕ × ℕ =>
              (M * R⁻¹ ^ p.1 * ‖v‖) * ((compList p.1 p.2).map (fun l => (l.map b).prod)).sum) :=
            summable_compList_prod_bound hb_nn hsum_gt (by positivity) hR_pos (norm_nonneg v) hS_b_le
          refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hbound_prod
          have h1 : ‖term p‖ ≤ |t| ^ p.2 * (‖sumEvalList (P p.1) (fun j => cSer P j (fun _ => v)) p.2‖ * ‖v‖) := by
            simp only [term, norm_smul, Real.norm_eq_abs, abs_pow]
            exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity)
          have h2 := norm_sumEvalList_le (P p.1) (fun j => cSer P j (fun _ => v)) p.2
          have hprod_eq : |t| ^ p.2 * ((compList p.1 p.2).map (fun l => (l.map (fun j => ‖cSer P j (fun _ => v)‖)).prod)).sum =
              ((compList p.1 p.2).map (fun l => (l.map b).prod)).sum := by
            rw [← list_sum_map_mul_left]
            congr 1; apply List.map_congr_left; intro l hl
            have hsum_l : l.sum = p.2 := (mem_compList.mp hl).2.1
            rw [← hsum_l]; clear hsum_l hl
            induction l with
            | nil => simp
            | cons j ls ih => simp only [List.sum_cons, List.map_cons, List.prod_cons, pow_add, b]; rw [mul_assoc, ← ih]; ring
          calc ‖term p‖
              ≤ |t| ^ p.2 * ((‖P p.1‖ * ((compList p.1 p.2).map (fun l => (l.map (fun j => ‖cSer P j (fun _ => v)‖)).prod)).sum) * ‖v‖) :=
                h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg v)) (by positivity))
            _ ≤ |t| ^ p.2 * (((M * R⁻¹ ^ p.1) * ((compList p.1 p.2).map (fun l => (l.map (fun j => ‖cSer P j (fun _ => v)‖)).prod)).sum) * ‖v‖) := by
                have hnn : 0 ≤ ((compList p.1 p.2).map (fun l => (l.map (fun j => ‖cSer P j (fun _ => v)‖)).prod)).sum :=
                  List.sum_nonneg fun _ hx => by
                    rcases List.mem_map.mp hx with ⟨l, _, rfl⟩
                    exact List.prod_nonneg fun _ hy => by rcases List.mem_map.mp hy with ⟨j, _, rfl⟩; exact norm_nonneg _
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hP_bd p.1) hnn) (norm_nonneg v)) (by positivity)
            _ = (M * R⁻¹ ^ p.1 * ‖v‖) * (|t| ^ p.2 * ((compList p.1 p.2).map (fun l => (l.map (fun j => ‖cSer P j (fun _ => v)‖)).prod)).sum) := by ring
            _ = (M * R⁻¹ ^ p.1 * ‖v‖) * ((compList p.1 p.2).map (fun l => (l.map b).prod)).sum := by rw [hprod_eq]
        -- Swap double sum via Summable.tsum_comm
        have hswap : ∑' m : ℕ, ∑' k : ℕ, term (m, k) = ∑' k : ℕ, ∑' m : ℕ, term (m, k) :=
          (Summable.tsum_comm (f := fun m k => term (m, k)) hdouble).symm
        have hLHS : F (g t) v = ∑' m : ℕ, ∑' k : ℕ, term (m, k) := by
          rw [← hF_hasSum.tsum_eq]
          congr 1; funext m; exact (hinner m).tsum_eq.symm
        rw [hLHS, hswap]
        -- Reindex RHS from k to k + 1 (k = 0 term is 0)
        have hderiv_sum : Summable (fun k : ℕ => ((k : ℝ) * t ^ (k - 1)) • cSer P k (fun _ => v)) := by
          rw [← summable_nat_add_iff 1]
          exact Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun i => (hterm_bd (i + 1) (Nat.succ_pos i) t ht_abs).2)
            ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _))
        rw [tsum_nat_zero_add hderiv_sum]
        simp only [Nat.cast_zero, zero_mul, zero_smul, zero_add]
        congr 1; funext k
        cases k with
        | zero =>
          rw [tsum_eq_single 0]
          · simp [term, sumEvalList, compList, evalList, cSer_one_diag]
          · intro m hm
            simp [term, sumEvalList_eq_zero_of_nil _ _ _ (compList_zero_of_pos (Nat.pos_of_ne_zero hm))]
        | succ k' =>
          rw [tsum_eq_sum (s := Finset.Icc 1 (k' + 1))]
          · dsimp only [term]
            rw [← Finset.smul_sum, ← cSer_succ_succ_diag P k' v, smul_smul]
            congr 1; push_cast; ring
          · intro m hm
            simp only [Finset.mem_Icc, not_and_or, not_le] at hm
            rcases hm with hm0 | hmbig
            · have hm_eq : m = 0 := by omega
              subst hm_eq
              have hnil : compList 0 (k' + 1) = [] := by unfold compList; simp
              simp [term, sumEvalList_eq_zero_of_nil _ _ _ hnil]
            · have hempty : compList m (k' + 1) = [] := by
                rw [List.eq_nil_iff_forall_not_mem]
                intro l hl
                have hlen := (mem_compList.mp hl).1
                have hsuml := (mem_compList.mp hl).2.1
                have hposl := (mem_compList.mp hl).2.2
                have hge : l.length ≤ l.sum := by
                  clear hlen hsuml hl
                  induction l with
                  | nil => simp
                  | cons a t iht =>
                    have ha := hposl a (List.mem_cons_self ..)
                    have ht := iht (fun r hr => hposl r (List.mem_cons_of_mem _ hr))
                    simp; omega
                omega
              simp [term, sumEvalList_eq_zero_of_nil _ _ _ hempty]
      rwa [← hF_eq_deriv] at hg_hasDeriv
    -- Apply Gronwall uniqueness ODE_solution_unique_of_mem_Icc on [-0.5, 1.1]
    have hgt_in : ∀ t ∈ Ioo (-0.5 : ℝ) 1.1, g t ∈ closedBall (0 : E n × E n) (R / 2) := by
      intro t ht
      rw [Metric.mem_closedBall, dist_zero_right]
      have ht_abs : |t| ≤ 1.5 := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have hsum_gt : Summable (fun i : ℕ => ‖cSer P (i + 1) (fun _ => v)‖ * |t| ^ (i + 1)) := by
        have hgeom : Summable (fun i : ℕ => A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i) :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => ?_) hgeom
        have := (hterm_bd (i + 1) (Nat.succ_pos i) t ht_abs).1
        simpa [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm] using this
      have hgt_eq : g t = ∑' i : ℕ, (t ^ (i + 1)) • cSer P (i + 1) (fun _ => v) := by
        have hs_all : Summable (fun k : ℕ => (t ^ k) • cSer P k (fun _ => v)) := by
          rw [← summable_nat_add_iff 1]
          exact Summable.of_norm (hsum_gt.congr fun i => by
            rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm])
        rw [show g t = ∑' k : ℕ, (t ^ k) • cSer P k (fun _ => v) from rfl, tsum_nat_zero_add hs_all]
        simp [cSer_zero]
      rw [hgt_eq]
      have hgeom : Summable (fun i : ℕ => A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      have hle1 : ‖∑' i : ℕ, (t ^ (i + 1)) • cSer P (i + 1) (fun _ => v)‖ ≤
          ∑' i : ℕ, A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i :=
        (norm_tsum_le_tsum_norm (hsum_gt.congr fun i => by
          rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm])).trans
          (Summable.tsum_le_tsum (fun i => (hterm_bd (i + 1) (Nat.succ_pos i) t ht_abs).1)
            (hsum_gt.congr fun i => by rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]) hgeom)
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hle1
      nlinarith
    have hv_lip : ∀ t ∈ Ioo (-0.5 : ℝ) 1.1,
        LipschitzOnWith (K_F * ‖v‖₊) (fun z => F z v) (closedBall (0 : E n × E n) (R / 2)) := by
      intro _ _ z₁ hz₁ z₂ hz₂
      have h1 := hF_lip hz₁ hz₂
      rw [edist_dist, edist_dist] at h1 ⊢
      rw [dist_eq_norm, dist_eq_norm, ← sub_apply]
      have h2 : ‖(F z₁ - F z₂) v‖ ≤ ‖F z₁ - F z₂‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      have h1' : dist (F z₁) (F z₂) ≤ (K_F : ℝ) * dist z₁ z₂ := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg K_F)] at h1
        exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg K_F) dist_nonneg)).mp h1
      rw [dist_eq_norm] at h1'
      have h3 : ‖(F z₁ - F z₂) v‖ ≤ ((K_F * ‖v‖₊ : ℝ≥0) : ℝ) * dist z₁ z₂ := by
        push_cast; rw [mul_right_comm]; exact h2.trans (mul_le_mul_of_nonneg_right h1' (norm_nonneg v))
      calc ENNReal.ofReal ‖(F z₁ - F z₂) v‖
          ≤ ENNReal.ofReal (((K_F * ‖v‖₊ : ℝ≥0) : ℝ) * dist z₁ z₂) := ENNReal.ofReal_le_ofReal h3
        _ = (K_F * ‖v‖₊ : ℝ≥0∞) * ENNReal.ofReal (dist z₁ z₂) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]
    have huniq := ODE_solution_unique_of_mem_Icc
      (a := -0.5) (b := 1.1) (t₀ := 0) (K := K_F * ‖v‖₊)
      (v := fun _ z => F z v) (s := fun _ => closedBall 0 (R / 2))
      (f := fun s => z_fn (s • v)) (g := g)
      hv_lip (by norm_num)
      (by
        refine hz_cont.comp (continuousOn_id.smul continuousOn_const) (fun t ht => ?_)
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
        have ht_abs : |t| ≤ 1.1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        have hv_nn : 0 ≤ ‖v‖ := norm_nonneg v
        nlinarith)
      (fun t ht => hode v (Metric.ball_subset_ball hrg_rv.le hv) t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (fun t ht => by
        apply hbr_z
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
        have ht_abs : |t| ≤ 1.5 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hv_nn : 0 ≤ ‖v‖ := norm_nonneg v
        nlinarith)
      (by
        intro t ht
        exact (hg_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt)
      (fun t ht => hg_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      hgt_in
      (by
        simp only [zero_smul, hz0, g]
        symm
        have hzero : (fun k : ℕ => ((0 : ℝ) ^ k) • cSer P k (fun _ => v)) = fun _ => 0 := by
          funext k; cases k with
          | zero => simp [cSer_zero]
          | succ k' => simp [zero_pow (Nat.succ_ne_zero k')]
        rw [hzero, tsum_zero]; rfl)
    have h1eq := huniq (by norm_num : (1 : ℝ) ∈ Icc (-0.5 : ℝ) 1.1)
    simp only [one_smul, g, one_pow, one_smul] at h1eq
    rw [h1eq]
    refine Summable.hasSum (Summable.of_norm ?_)
    rw [← summable_nat_add_iff 1]
    have hgeom : Summable (fun i : ℕ => A * (1.5 * r_g) * (1 / 4 : ℝ) ^ i) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hgeom
    have := (hterm_bd (i + 1) (Nat.succ_pos i) 1 (by norm_num)).1
    simpa using this
  -- Assemble HasFPowerSeriesOnBall z_fn (cSer P) 0 (ENNReal.ofReal r_g)
  have hrad : ENNReal.ofReal r_g ≤ (cSer P).radius := by
    rw [ENNReal.ofReal_eq_coe_nnreal hr_g.le]
    refine FormalMultilinearSeries.le_radius_of_bound (cSer P) (r := ⟨r_g, hr_g.le⟩) (A * r_g) (fun k => ?_)
    cases k with
    | zero => simp [cSer_zero]; positivity
    | succ k' =>
      have hk := hc_bd (k' + 1) (Nat.succ_pos k')
      have hpow : r_g ^ (k' + 1) = r_g * r_g ^ k' := pow_succ' r_g k'
      have hrgB : B * r_g ≤ 1 := by linarith
      have hk1 : (1 : ℝ) ≤ ((k' + 1 : ℕ) : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ ((k' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k'
        nlinarith
      have hdiv : A * B ^ k' / ((k' + 1 : ℕ) : ℝ) ^ 2 ≤ A * B ^ k' / 1 :=
        div_le_div_of_nonneg_left (by positivity) zero_lt_one hk1
      calc ‖cSer P (k' + 1)‖ * r_g ^ (k' + 1)
          ≤ (A * B ^ k' / ((k' + 1 : ℕ) : ℝ) ^ 2) * (r_g * r_g ^ k') := by
            rw [hpow]; exact mul_le_mul_of_nonneg_right hk (by positivity)
        _ ≤ (A * B ^ k' / 1) * (r_g * r_g ^ k') :=
            mul_le_mul_of_nonneg_right hdiv (by positivity)
        _ = (A * r_g) * (B * r_g) ^ k' := by rw [mul_pow]; ring
        _ ≤ (A * r_g) * 1 ^ k' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrgB k') (by positivity)
        _ = A * r_g := by simp
  have hfps : HasFPowerSeriesOnBall z_fn (cSer P) 0 (ENNReal.ofReal r_g) :=
    { r_le := hrad
      r_pos := ENNReal.ofReal_pos.mpr hr_g
      hasSum := fun {y} hy => by
        have hy_ball : y ∈ ball 0 r_g := by
          rw [Metric.mem_eball, edist_dist] at hy
          rw [Metric.mem_ball]
          exact (ENNReal.ofReal_lt_ofReal_iff hr_g).mp hy
        simpa using hmain_eq y hy_ball }
  exact hfps.analyticAt

private lemma analyticAt_local_hom {n : ℕ} (G : LocalAnalyticGroupHom n) :
    AnalyticAt ℝ G.f 0 := by
  obtain ⟨A, hA⟩ := hasFDerivAt_zero_of_local_hom G
  obtain ⟨F, r_v, hr_v, _, hF_an, hf_cont, hode⟩ := hasDerivAt_radial_ode G hA
  have hz_an : AnalyticAt ℝ (fun v : E n => (v, G.f v)) 0 :=
    analyticAt_of_radial_ode hr_v hF_an (by simp [G.hf_zero])
      (continuousOn_id.prodMk hf_cont) hode
  exact AnalyticAt.comp
    (g := ContinuousLinearMap.snd ℝ (E n) (E n)) (f := fun v : E n => (v, G.f v))
    ((ContinuousLinearMap.snd ℝ (E n) (E n)).analyticAt (0, G.f 0)) hz_an

/- ### Part 4: Lie group chart reduction and main theorem -/

private lemma contMDiffAt_one_of_continuous_hom (n : ℕ) (L : Type) [Group L]
    [TopologicalSpace L] [T2Space L] [ChartedSpace (E n) L]
    [LieGroup (𝓡 n) ω L] (α : L →* L) (hα : Continuous α) :
    ContMDiffAt (𝓡 n) (𝓡 n) ω α 1 := by
  have : IsTopologicalGroup L := topologicalGroup_of_lieGroup (𝓡 n) ω
  let e : OpenPartialHomeomorph L (E n) := chartAt (E n) (1 : L)
  let c : E n := e 1
  let toC : L → E n := fun x => e x - c
  let fromC : E n → L := fun v => e.symm (v + c)
  have h1_src : (1 : L) ∈ e.source := mem_chart_source (E n) (1 : L)
  have hc_tgt : c ∈ e.target := e.map_source h1_src
  have hfrom0 : fromC 0 = 1 := by simp [fromC, c, e.left_inv h1_src]
  have hto1 : toC 1 = 0 := by simp [toC, c]
  have hfrom_contAt : ContinuousAt fromC 0 := by
    have h1 : ContinuousAt e.symm ((fun v : E n => v + c) 0) := by
      simpa using e.continuousOn_invFun.continuousAt (e.open_target.mem_nhds hc_tgt)
    have h2 : ContinuousAt (fun v : E n => v + c) 0 := continuousAt_id.add continuousAt_const
    exact ContinuousAt.comp (g := e.symm) (f := fun v : E n => v + c) h1 h2
  have hto_contAt : ContinuousAt toC 1 := by
    have h1 : ContinuousAt e 1 := e.continuousOn_toFun.continuousAt (e.open_source.mem_nhds h1_src)
    exact h1.sub continuousAt_const
  let μ : E n × E n → E n := fun p => toC (fromC p.1 * fromC p.2)
  let ι : E n → E n := fun v => toC (fromC v)⁻¹
  let f : E n → E n := fun v => toC (α (fromC v))
  have hμ_an : AnalyticAt ℝ μ (0, 0) := by
    have hmul : ContMDiffAt ((𝓡 n).prod (𝓡 n)) (𝓡 n) ω (fun p : L × L => p.1 * p.2) (1, 1) :=
      (contMDiff_mul (𝓡 n) ω).contMDiffAt
    rw [contMDiffAt_iff] at hmul
    have hcd : ContDiffAt ℝ ω (fun p : E n × E n => e (e.symm p.1 * e.symm p.2)) (c, c) := by
      have h2 := hmul.2
      have hrange : range ((𝓡 n).prod (𝓡 n)) = Set.univ := by simp [modelWithCornersSelf_coe]
      rw [hrange, contDiffWithinAt_univ] at h2
      have hfn : (↑(extChartAt (𝓡 n) ((1 : L) * 1)) ∘ (fun p : L × L => p.1 * p.2) ∘
          ↑(extChartAt ((𝓡 n).prod (𝓡 n)) ((1 : L), (1 : L))).symm) =
          fun p : E n × E n => e (e.symm p.1 * e.symm p.2) := by
        ext p
        simp only [mul_one, Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm,
          PartialEquiv.prod_coe, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
          modelWithCornersSelf_coe_symm, id_eq, e]
      have hpt : extChartAt ((𝓡 n).prod (𝓡 n)) ((1 : L), (1 : L)) (1, 1) = (c, c) := by
        simp [e, c]
      rw [hfn, hpt] at h2
      exact h2
    have han : AnalyticAt ℝ (fun p : E n × E n => e (e.symm p.1 * e.symm p.2)) (c, c) := by
      rw [← analyticWithinAt_univ, ← contDiffWithinAt_omega_iff_analyticWithinAt, contDiffWithinAt_univ]
      exact hcd
    have hshift : AnalyticAt ℝ (fun p : E n × E n => (p.1 + c, p.2 + c)) (0, 0) :=
      (analyticAt_fst.add analyticAt_const).prod (analyticAt_snd.add analyticAt_const)
    have han' : AnalyticAt ℝ (fun p : E n × E n => e (e.symm p.1 * e.symm p.2))
        ((fun p : E n × E n => (p.1 + c, p.2 + c)) (0, 0)) := by simpa using han
    have hcomp := AnalyticAt.comp (g := fun p : E n × E n => e (e.symm p.1 * e.symm p.2))
      (f := fun p : E n × E n => (p.1 + c, p.2 + c)) han' hshift
    exact hcomp.sub analyticAt_const
  have hι_an : AnalyticAt ℝ ι 0 := by
    have hinv : ContMDiffAt (𝓡 n) (𝓡 n) ω (fun x : L => x⁻¹) 1 :=
      (contMDiff_inv (𝓡 n) ω).contMDiffAt
    rw [contMDiffAt_iff] at hinv
    have hcd : ContDiffAt ℝ ω (fun v : E n => e (e.symm v)⁻¹) c := by
      have h2 := hinv.2
      rw [show range (𝓡 n) = Set.univ by simp [modelWithCornersSelf_coe], contDiffWithinAt_univ] at h2
      have hfn : (↑(extChartAt (𝓡 n) (1 : L)⁻¹) ∘ (fun x : L => x⁻¹) ∘ ↑(extChartAt (𝓡 n) (1 : L)).symm) =
          fun v : E n => e (e.symm v)⁻¹ := by
        ext v
        simp only [inv_one, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
          modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq, e]
      have hpt : extChartAt (𝓡 n) (1 : L) 1 = c := by
        simp [e, c]
      rw [hfn, hpt] at h2
      exact h2
    have han : AnalyticAt ℝ (fun v : E n => e (e.symm v)⁻¹) c := by
      rw [← analyticWithinAt_univ, ← contDiffWithinAt_omega_iff_analyticWithinAt, contDiffWithinAt_univ]
      exact hcd
    have han' : AnalyticAt ℝ (fun v : E n => e (e.symm v)⁻¹) ((fun v : E n => v + c) 0) := by simpa using han
    have hsh : AnalyticAt ℝ (fun v : E n => v + c) 0 := analyticAt_id.add analyticAt_const
    exact (AnalyticAt.comp (g := fun v : E n => e (e.symm v)⁻¹)
      (f := fun v : E n => v + c) han' hsh).sub analyticAt_const
  -- Find a small radius ρ > 0 so all local operations stay in e.source / e.target
  have hsmall : ∀ᶠ v in 𝓝 (0 : E n),
      v + c ∈ e.target ∧ fromC v ∈ e.source ∧ (fromC v)⁻¹ ∈ e.source ∧ α (fromC v) ∈ e.source := by
    have h1 : ∀ᶠ v in 𝓝 (0 : E n), v + c ∈ e.target :=
      (continuousAt_id.add continuousAt_const).eventually (by simpa using e.open_target.mem_nhds hc_tgt)
    have h2 : ∀ᶠ v in 𝓝 (0 : E n), fromC v ∈ e.source :=
      hfrom_contAt.eventually (by rw [hfrom0]; exact e.open_source.mem_nhds h1_src)
    have h3 : ∀ᶠ v in 𝓝 (0 : E n), (fromC v)⁻¹ ∈ e.source :=
      (hfrom_contAt.inv).eventually
        (by simp [hfrom0]; exact e.open_source.mem_nhds h1_src)
    have h4 : ∀ᶠ v in 𝓝 (0 : E n), α (fromC v) ∈ e.source :=
      (ContinuousAt.comp (g := α) (f := fromC) hα.continuousAt hfrom_contAt).eventually
        (by simp [hfrom0]; exact e.open_source.mem_nhds h1_src)
    filter_upwards [h1, h2, h3, h4] with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hmul_small : ∀ᶠ p in 𝓝 ((0 : E n), (0 : E n)),
      fromC p.1 * fromC p.2 ∈ e.source ∧
      (fromC p.1)⁻¹ * fromC p.2 ∈ e.source := by
    have hfc1 : ContinuousAt (fun p : E n × E n => fromC p.1) (0, 0) :=
      ContinuousAt.comp (g := fromC) (f := Prod.fst) hfrom_contAt continuousAt_fst
    have hfc2 : ContinuousAt (fun p : E n × E n => fromC p.2) (0, 0) :=
      ContinuousAt.comp (g := fromC) (f := Prod.snd) hfrom_contAt continuousAt_snd
    have hcont1 : ContinuousAt (fun p : E n × E n => fromC p.1 * fromC p.2) (0, 0) :=
      hfc1.mul hfc2
    have hcont2 : ContinuousAt (fun p : E n × E n => (fromC p.1)⁻¹ * fromC p.2) (0, 0) :=
      hfc1.inv.mul hfc2
    have h1 : ∀ᶠ p in 𝓝 ((0 : E n), (0 : E n)), fromC p.1 * fromC p.2 ∈ e.source :=
      hcont1.eventually (by simp [hfrom0]; exact e.open_source.mem_nhds h1_src)
    have h2 : ∀ᶠ p in 𝓝 ((0 : E n), (0 : E n)), (fromC p.1)⁻¹ * fromC p.2 ∈ e.source :=
      hcont2.eventually (by simp [hfrom0]; exact e.open_source.mem_nhds h1_src)
    filter_upwards [h1, h2] with p h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨r₁, hr₁, hbr₁⟩ := Metric.mem_nhds_iff.mp hsmall
  obtain ⟨r₂, hr₂, hbr₂⟩ := Metric.mem_nhds_iff.mp hmul_small
  set ρ : ℝ := min r₁ r₂
  have hρ : 0 < ρ := by positivity
  have hfrom_to : ∀ x ∈ e.source, fromC (toC x) = x := by
    intro x hx; simp only [fromC, toC, sub_add_cancel]; exact e.left_inv hx
  have hto_from : ∀ v ∈ ball 0 ρ, toC (fromC v) = v := by
    intro v hv
    have hvt : v + c ∈ e.target := (hbr₁ (Metric.ball_subset_ball (min_le_left _ _) hv)).1
    simp only [toC, fromC, e.right_inv hvt, add_sub_cancel_right]
  have hmul_src : ∀ x ∈ ball 0 ρ, ∀ y ∈ ball 0 ρ, fromC x * fromC y ∈ e.source := by
    intro x hx y hy
    have hp : (x, y) ∈ ball ((0 : E n), (0 : E n)) r₂ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) hx),
             Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) hy)⟩
    exact (hbr₂ hp).1
  let G : LocalAnalyticGroupHom n :=
    { μ := μ, ι := ι, f := f, ρ := ρ, hρ := hρ
      hμ_an := hμ_an, hι_an := hι_an
      hf_cont := by
        intro v hv
        have h1 : ContinuousAt fromC v := by
          have hvt : v + c ∈ e.target := (hbr₁ (Metric.ball_subset_ball (min_le_left _ _) hv)).1
          exact ContinuousAt.comp (g := e.symm) (f := fun w : E n => w + c)
            (e.continuousOn_invFun.continuousAt (e.open_target.mem_nhds hvt))
            (continuousAt_id.add continuousAt_const)
        have h2 : ContinuousAt (fun w => α (fromC w)) v :=
          ContinuousAt.comp (g := α) (f := fromC) hα.continuousAt h1
        have h3 : ContinuousAt toC (α (fromC v)) :=
          (e.continuousOn_toFun.continuousAt
            (e.open_source.mem_nhds (hbr₁ (Metric.ball_subset_ball (min_le_left _ _) hv)).2.2.2)).sub
            continuousAt_const
        exact (ContinuousAt.comp (g := toC) (f := fun w => α (fromC w)) h3 h2).continuousWithinAt
      hf_zero := by simp [f, hfrom0, hto1]
      hι_zero := by simp [ι, hfrom0, hto1]
      hμ_left_id := fun y hy => by simp only [μ, hfrom0, one_mul]; exact hto_from y hy
      hμ_right_id := fun x hx => by simp only [μ, hfrom0, mul_one]; exact hto_from x hx
      hμ_assoc := fun x hx y hy z hz => by
        simp only [μ]
        rw [hfrom_to _ (hmul_src y hy z hz), hfrom_to _ (hmul_src x hx y hy), mul_assoc]
      hμ_inv_left := fun x hx y hy => by
        simp only [μ, ι]
        rw [hfrom_to _ (hbr₁ (Metric.ball_subset_ball (min_le_left _ _) hx)).2.2.1,
            hfrom_to _ (hmul_src x hx y hy), inv_mul_cancel_left]
        exact hto_from y hy
      hμ_inv_right := fun x hx z hz => by
        simp only [μ, ι]
        rw [hfrom_to _ (hbr₁ (Metric.ball_subset_ball (min_le_left _ _) hx)).2.2.1]
        have hsrc : (fromC x)⁻¹ * fromC z ∈ e.source := by
          have hp : (x, z) ∈ ball ((0 : E n), (0 : E n)) r₂ := by
            rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
            exact ⟨Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) hx),
                   Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) hz)⟩
          exact (hbr₂ hp).2
        rw [hfrom_to _ hsrc, mul_inv_cancel_left]
        exact hto_from z hz
      hf_hom := fun x hx y hy => by
        simp only [f, μ]
        rw [hfrom_to _ (hmul_src x hx y hy), map_mul,
            hfrom_to _ (hbr₁ (Metric.ball_subset_ball (min_le_left _ _) hx)).2.2.2,
            hfrom_to _ (hbr₁ (Metric.ball_subset_ball (min_le_left _ _) hy)).2.2.2] }
  have hf_an : AnalyticAt ℝ f 0 := analyticAt_local_hom G
  rw [contMDiffAt_iff]
  refine ⟨hα.continuousAt, ?_⟩
  rw [show range (𝓡 n) = Set.univ by simp [modelWithCornersSelf_coe], contDiffWithinAt_univ,
      ← contDiffWithinAt_univ, contDiffWithinAt_omega_iff_analyticWithinAt, analyticWithinAt_univ]
  have hchart_eq : (extChartAt (𝓡 n) (α 1) ∘ α ∘ (extChartAt (𝓡 n) (1 : L)).symm) =
      fun v : E n => f (v - c) + c := by
    ext v
    simp only [Function.comp_apply, map_one, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq, f, toC, fromC, e, c, sub_add_cancel]
  have hpt : extChartAt (𝓡 n) (1 : L) 1 = c := by
    simp [extChartAt, OpenPartialHomeomorph.extend, e, c]
  rw [hchart_eq, hpt]
  have hf_an' : AnalyticAt ℝ f ((fun v : E n => v - c) c) := by simpa using hf_an
  have hsub_c : AnalyticAt ℝ (fun v : E n => v - c) c := analyticAt_id.sub analyticAt_const
  exact (AnalyticAt.comp (g := f) (f := fun v : E n => v - c) hf_an' hsub_c).add analyticAt_const

end Hilbert5R1H3

open scoped Manifold ContDiff in
theorem OMA.solution : OMA.R_Hilbert5_hilbert_fifth_problem_R1.H3 := by
  intro n L _ _ _ _ _ _ α hα g
  have h1 : ContMDiffAt (𝓡 n) (𝓡 n) ω α 1 :=
    Hilbert5R1H3.contMDiffAt_one_of_continuous_hom n L α hα
  have hcomp : ContMDiffAt (𝓡 n) (𝓡 n) ω ((fun y : L => α g * y) ∘ α ∘ (fun x : L => g⁻¹ * x)) g := by
    have hL : ContMDiffAt (𝓡 n) (𝓡 n) ω (fun x : L => g⁻¹ * x) g := contMDiff_mul_left.contMDiffAt
    have hR : ContMDiffAt (𝓡 n) (𝓡 n) ω (fun y : L => α g * y) (α (g⁻¹ * g)) := contMDiff_mul_left.contMDiffAt
    have hmid : ContMDiffAt (𝓡 n) (𝓡 n) ω α (g⁻¹ * g) := by simpa using h1
    exact hR.comp g (hmid.comp g hL)
  have heq : ((fun y : L => α g * y) ∘ α ∘ (fun x : L => g⁻¹ * x)) = α := by
    ext x
    simp only [Function.comp_apply, map_mul, map_inv, mul_inv_cancel_left]
  rwa [heq] at hcomp

