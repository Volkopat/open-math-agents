import FormalConjectures.Arxiv.«2607.05349».MicroscopicWeighting

/-!
# Proof of Theorem 3.8 (`hasMicroscopicWeighting_iff_of_isUnit`)

When `D = distanceMatrix X` is invertible, set `v = D⁻¹ *ᵥ 1` and `s = ∑ i, v i`.
1. `HasFiniteConcentration D ↔ s ≠ 0` (the unique candidate gauging is `s⁻¹ • v`).
2. `t ↦ det (similarityMatrix X t)` is real-analytic on `ℝ` and tends to `1` as `t → ∞`, so by
   the identity theorem `similarityMatrix X t` is invertible eventually as `t → 0⁺`.
3. Writing `similarityMatrix X t = J - t • A t` with `A t → D` as `t → 0⁺`:
   - If `s ≠ 0`, `u t = (A t)⁻¹ *ᵥ 1 → v` satisfies `Z t *ᵥ u t = (∑ u t - t) • 1`, so
     `weighting X t = (∑ u t - t)⁻¹ • u t → s⁻¹ • v`.
   - If `weighting X t → w` and `s = 0`, then `Z t *ᵥ weighting X t = 1` gives `∑ w = 1` in the
     limit, while dotting with `v` yields `v ⬝ᵥ (A t *ᵥ weighting X t) = 0`, hence
     `∑ w = v ⬝ᵥ (D *ᵥ w) = 0`, a contradiction.
-/

-- Original formalization by @TheWaler, PR #367.
-- Determinant-limit argument adapted from @luciusacarr’s forward implication,
-- PR #636. Continuity helpers simplified using Mathlib’s matrix inverse,
-- matrix-vector multiplication, dot-product continuity, and right-slope APIs.

namespace MicroscopicWeightingProof

open Arxiv.«2607.05349» Filter Matrix
open scoped Topology

private def onesMat (X : Type*) : Matrix X X ℝ :=
  Matrix.of fun _ _ => 1

private noncomputable def scaledDiffMat (X : Type*) [MetricSpace X] (t : ℝ) : Matrix X X ℝ :=
  Matrix.of fun i j => (1 - Real.exp (-t * dist i j)) / t

private lemma distanceMatrix_isSymm (X : Type*) [Fintype X] [MetricSpace X] :
    (distanceMatrix X).IsSymm := by
  ext i j
  exact dist_comm j i

private lemma onesMat_mulVec {X : Type*} [Fintype X] (u : X → ℝ) :
    onesMat X *ᵥ u = (∑ j, u j) • (1 : X → ℝ) := by
  ext i
  simp [onesMat, Matrix.mulVec, dotProduct]

private lemma similarityMatrix_eq_sub {X : Type*} [Fintype X] [MetricSpace X]
    {t : ℝ} (ht : t ≠ 0) :
    similarityMatrix X t = onesMat X - t • scaledDiffMat X t := by
  ext i j
  simp [similarityMatrix, onesMat, scaledDiffMat, mul_div_cancel₀ _ ht]

private lemma hasFiniteConcentration_iff_sum_ne_zero
    {X : Type*} [Fintype X] [DecidableEq X] [MetricSpace X]
    (h : IsUnit (distanceMatrix X).det) :
    HasFiniteConcentration (distanceMatrix X) ↔ ∑ i, ((distanceMatrix X)⁻¹ *ᵥ 1) i ≠ 0 := by
  set D := distanceMatrix X
  set v := D⁻¹ *ᵥ (1 : X → ℝ)
  constructor
  · rintro ⟨g, c, hsum, hDg⟩ hs
    have hconst : Function.const X c = c • (1 : X → ℝ) := by
      ext i
      simp
    have hg : g = c • v := by
      calc
        g = (D⁻¹ * D) *ᵥ g := by rw [Matrix.nonsing_inv_mul D h, Matrix.one_mulVec]
        _ = D⁻¹ *ᵥ (D *ᵥ g) := by rw [Matrix.mulVec_mulVec]
        _ = D⁻¹ *ᵥ (c • (1 : X → ℝ)) := by rw [hDg, hconst]
        _ = c • v := by rw [Matrix.mulVec_smul]
    rw [hg] at hsum
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hs, mul_zero] at hsum
    norm_num at hsum
  · intro hs
    refine ⟨(∑ i, v i)⁻¹ • v, (∑ i, v i)⁻¹, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hs]
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv D h, Matrix.one_mulVec]
      ext i
      simp

private lemma eventually_isUnit_det_similarityMatrix
    {X : Type*} [Fintype X] [DecidableEq X] [MetricSpace X] :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), IsUnit (similarityMatrix X t).det := by
  suffices hz : ∀ᶠ t in 𝓝[>] (0 : ℝ), (similarityMatrix X t).det ≠ 0 by
    exact hz.mono fun _ ht => isUnit_iff_ne_zero.mpr ht
  classical
  let f := fun t => (similarityMatrix X t).det
  have ha : AnalyticOnNhd ℝ f Set.univ := by
    intro t _
    unfold f
    rw [show (fun t => (similarityMatrix X t).det) =
        fun t => ∑ σ : Equiv.Perm X, (Equiv.Perm.sign σ : ℝ) *
          ∏ i, Real.exp (-t * dist (σ i) i) by
      ext t
      simp [Matrix.det_apply, similarityMatrix, Units.smul_def]]
    fun_prop
  have hmat : Tendsto (fun (t : ℝ) (i j : X) => Real.exp (-t * dist i j))
      atTop (𝓝 (fun i j => (1 : Matrix X X ℝ) i j)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · have hdist : 0 < dist i j := dist_pos.mpr hij
      have hneg : Tendsto (fun t : ℝ => -t * dist i j) atTop atBot :=
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hdist)).congr
          fun t => by simp; ring
      simpa [Function.comp_def, Matrix.one_apply, hij] using Real.tendsto_exp_atBot.comp hneg
  have hlim : Tendsto f atTop (𝓝 1) := by
    have hc : Continuous (fun M : Matrix X X ℝ => M.det) := continuous_id.matrix_det
    have hmat' : Tendsto (similarityMatrix X) atTop (𝓝 (1 : Matrix X X ℝ)) := hmat
    simpa [f, Function.comp_def] using
      (hc.continuousAt (x := (1 : Matrix X X ℝ))).tendsto.comp hmat'
  have hnzero : ¬ Set.EqOn f 0 Set.univ := by
    intro h
    have hzero : Tendsto f atTop (𝓝 0) :=
      tendsto_const_nhds.congr fun t => (h (Set.mem_univ t)).symm
    exact one_ne_zero (tendsto_nhds_unique hlim hzero)
  rcases (ha 0 (Set.mem_univ 0)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact False.elim (hnzero (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) h))
  · exact h.filter_mono (nhdsGT_le_nhdsNE 0)

private lemma tendsto_scaledDiffMat {X : Type*} [Fintype X] [MetricSpace X] :
    Tendsto (scaledDiffMat X) (𝓝[>] (0 : ℝ)) (𝓝 (distanceMatrix X)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  set d : ℝ := dist i j
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-t * d)) (-d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -t * d) (-d) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).neg.mul_const d
    simpa [Real.exp_zero] using h1.exp
  simpa [scaledDiffMat, distanceMatrix, Pi.neg_apply, sub_eq_add_neg,
    div_eq_mul_inv, smul_eq_mul, mul_comm, add_comm] using hd.neg.tendsto_slope_zero_right

private lemma tendsto_similarityMatrix {X : Type*} [Fintype X] [MetricSpace X] :
    Tendsto (similarityMatrix X) (𝓝[>] (0 : ℝ)) (𝓝 (onesMat X)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hcont : Continuous (fun t : ℝ => Real.exp (-t * dist i j)) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => Real.exp (-t * dist i j)) (𝓝 (0 : ℝ)) (𝓝 1) := by
    simpa using hcont.tendsto 0
  exact hlim.mono_left nhdsWithin_le_nhds

private lemma tendsto_scaledDiffMat_inv {X : Type*} [Fintype X] [DecidableEq X] [MetricSpace X]
    (h : IsUnit (distanceMatrix X).det) :
    Tendsto (fun t => (scaledDiffMat X t)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (distanceMatrix X)⁻¹) := by
  exact (continuousAt_matrix_inv _ (by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ h.ne_zero)).tendsto.comp
      (tendsto_scaledDiffMat (X := X))

private lemma tendsto_mulVec {X : Type*} [Fintype X] {l : Filter ℝ}
    {M : ℝ → Matrix X X ℝ} {M0 : Matrix X X ℝ} {u : ℝ → X → ℝ} {u0 : X → ℝ}
    (hM : Tendsto M l (𝓝 M0)) (hu : Tendsto u l (𝓝 u0)) :
    Tendsto (fun t => M t *ᵥ u t) l (𝓝 (M0 *ᵥ u0)) := by
  exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (hM.prodMk_nhds hu)

end MicroscopicWeightingProof

open Arxiv.«2607.05349» Filter Matrix MicroscopicWeightingProof
open scoped Topology

theorem OMA.solution : type_of% @Arxiv.«2607.05349».hasMicroscopicWeighting_iff_of_isUnit := by
  intro X _ _ _ _ h
  rw [hasFiniteConcentration_iff_sum_ne_zero h]
  set D := distanceMatrix X
  set v := D⁻¹ *ᵥ (1 : X → ℝ)
  set s := ∑ i, v i
  have hZ_unit : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsUnit (similarityMatrix X t).det :=
    eventually_isUnit_det_similarityMatrix
  have hA_lim : Tendsto (scaledDiffMat X) (𝓝[>] (0 : ℝ)) (𝓝 D) := tendsto_scaledDiffMat
  have hA_inv_lim : Tendsto (fun t => (scaledDiffMat X t)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 D⁻¹) :=
    tendsto_scaledDiffMat_inv h
  have hA_unit : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsUnit (scaledDiffMat X t).det := by
    have hdet : Tendsto (fun t => (scaledDiffMat X t).det) (𝓝[>] (0 : ℝ)) (𝓝 D.det) :=
      (continuous_id.matrix_det.tendsto D).comp hA_lim
    exact (hdet.eventually_ne h.ne_zero).mono fun _ ht => isUnit_iff_ne_zero.mpr ht
  constructor
  · rintro ⟨w, hw⟩ hs
    have hZw_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), similarityMatrix X t *ᵥ weighting X t = 1 := by
      filter_upwards [hZ_unit] with t ht
      simp only [weighting, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ht, Matrix.one_mulVec]
    have hJw : onesMat X *ᵥ w = 1 :=
      tendsto_nhds_unique (tendsto_mulVec tendsto_similarityMatrix hw)
        (tendsto_const_nhds.congr' (hZw_ev.mono fun _ ht => ht.symm))
    have hsum_w_one : ∑ j, w j = 1 := by
      obtain ⟨i0⟩ := ‹Nonempty X›
      have hi0 := congr_fun hJw i0
      simpa [onesMat_mulVec] using hi0
    have hdot_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), v ⬝ᵥ (scaledDiffMat X t *ᵥ weighting X t) = 0 := by
      filter_upwards [hZw_ev, self_mem_nhdsWithin] with t ht ht_pos
      have ht_ne : t ≠ 0 := ne_of_gt ht_pos
      have heq : onesMat X *ᵥ weighting X t - t • (scaledDiffMat X t *ᵥ weighting X t) = 1 := by
        rw [← Matrix.smul_mulVec, ← Matrix.sub_mulVec, ← similarityMatrix_eq_sub ht_ne]
        exact ht
      have hdot := congr_arg (fun y => v ⬝ᵥ y) heq
      have hv1 : v ⬝ᵥ (1 : X → ℝ) = 0 := by simpa [dotProduct, s] using hs
      have hvJ : v ⬝ᵥ (onesMat X *ᵥ weighting X t) = 0 := by
        rw [onesMat_mulVec, dotProduct_smul, smul_eq_mul, hv1, mul_zero]
      rw [dotProduct_sub, hvJ, zero_sub, dotProduct_smul, smul_eq_mul, hv1] at hdot
      have hmul : t * (v ⬝ᵥ (scaledDiffMat X t *ᵥ weighting X t)) = 0 := by linarith
      exact (mul_eq_zero.mp hmul).resolve_left ht_ne
    have hdot_lim : Tendsto (fun t => v ⬝ᵥ (scaledDiffMat X t *ᵥ weighting X t))
        (𝓝[>] (0 : ℝ)) (𝓝 (v ⬝ᵥ (D *ᵥ w))) := by
      exact (continuous_const.dotProduct continuous_id).tendsto _ |>.comp
        (tendsto_mulVec hA_lim hw)
    have hdot_zero : v ⬝ᵥ (D *ᵥ w) = 0 :=
      tendsto_nhds_unique hdot_lim (tendsto_const_nhds.congr' (hdot_ev.mono fun _ ht => ht.symm))
    have hdot_eq_sum : v ⬝ᵥ (D *ᵥ w) = ∑ j, w j := by
      rw [dotProduct_mulVec, ← mulVec_transpose, (distanceMatrix_isSymm X).eq]
      have hDv : D *ᵥ v = 1 := by
        simp only [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv D h, Matrix.one_mulVec]
      rw [hDv]
      simp [dotProduct]
    linarith
  · intro hs
    let u : ℝ → X → ℝ := fun t => (scaledDiffMat X t)⁻¹ *ᵥ (1 : X → ℝ)
    let sf : ℝ → ℝ := fun t => ∑ i, u t i
    have hu_lim : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 v) :=
      tendsto_mulVec hA_inv_lim tendsto_const_nhds
    have hsf_lim : Tendsto sf (𝓝[>] (0 : ℝ)) (𝓝 s) :=
      tendsto_finsetSum Finset.univ fun i _ => (tendsto_pi_nhds.mp hu_lim) i
    have hdenom_lim : Tendsto (fun t => sf t - t) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
      simpa using hsf_lim.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    have hdenom_ne : ∀ᶠ t in 𝓝[>] (0 : ℝ), sf t - t ≠ 0 := hdenom_lim.eventually_ne hs
    have hw_eq : ∀ᶠ t in 𝓝[>] (0 : ℝ), weighting X t = (sf t - t)⁻¹ • u t := by
      filter_upwards [hZ_unit, hA_unit, hdenom_ne, self_mem_nhdsWithin] with t hZt hAt hd ht_pos
      have hZu : similarityMatrix X t *ᵥ u t = (sf t - t) • (1 : X → ℝ) := by
        rw [similarityMatrix_eq_sub (ne_of_gt ht_pos), Matrix.sub_mulVec, onesMat_mulVec,
          Matrix.smul_mulVec]
        have hAu : scaledDiffMat X t *ᵥ u t = 1 := by
          simp only [u, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAt, Matrix.one_mulVec]
        rw [hAu, sub_smul]
      have hinv : u t = (sf t - t) • weighting X t := by
        calc
          u t = ((similarityMatrix X t)⁻¹ * similarityMatrix X t) *ᵥ u t := by
            rw [Matrix.nonsing_inv_mul _ hZt, Matrix.one_mulVec]
          _ = (similarityMatrix X t)⁻¹ *ᵥ (similarityMatrix X t *ᵥ u t) :=
            (Matrix.mulVec_mulVec (u t) (similarityMatrix X t)⁻¹ (similarityMatrix X t)).symm
          _ = (similarityMatrix X t)⁻¹ *ᵥ ((sf t - t) • (1 : X → ℝ)) := by rw [hZu]
          _ = (sf t - t) • weighting X t := by rw [Matrix.mulVec_smul]; rfl
      rw [hinv, smul_smul, inv_mul_cancel₀ hd, one_smul]
    refine ⟨s⁻¹ • v, ?_⟩
    exact ((hdenom_lim.inv₀ hs).smul hu_lim).congr' (hw_eq.mono fun _ ht => ht.symm)
