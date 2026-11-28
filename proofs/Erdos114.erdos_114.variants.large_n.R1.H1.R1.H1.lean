import OMAReductions.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Upper semicontinuity of lemniscate length (Erdos 114 H1). -/

open Set Topology Polynomial Metric Filter Erdos114 MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Erdos114H1Aux

lemma unit_circle_re_sub {u₁ u₂ : ℂ} (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1) :
    2 * ((starRingEnd ℂ u₁) * (u₁ - u₂)).re = ‖u₁ - u₂‖ ^ 2 := by
  have n₁ : u₁.re * u₁.re + u₁.im * u₁.im = 1 := by
    have := congrArg (· ^ 2) h₁
    simpa [Complex.sq_norm, Complex.normSq_apply] using this
  have n₂ : u₂.re * u₂.re + u₂.im * u₂.im = 1 := by
    have := congrArg (· ^ 2) h₂
    simpa [Complex.sq_norm, Complex.normSq_apply] using this
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  linear_combination n₁ - n₂

lemma norm_le_two_abs_re_of_im_bound (h : ℂ) (him : |h.im| ≤ |h.re| + (1 / 4 : ℝ) * ‖h‖) :
    ‖h‖ ≤ 2 * |h.re| := by
  by_contra! hlt
  have hpos : 0 < ‖h‖ := lt_of_le_of_lt (by positivity) hlt
  have hre : |h.re| < (1 / 2 : ℝ) * ‖h‖ := by linarith
  have him' : |h.im| < (3 / 4 : ℝ) * ‖h‖ := by linarith
  have hsq : ‖h‖ ^ 2 = |h.re| ^ 2 + |h.im| ^ 2 := by
    rw [sq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre_sq : |h.re| ^ 2 < (1 / 4 : ℝ) * ‖h‖ ^ 2 := by nlinarith [abs_nonneg h.re]
  have him_sq : |h.im| ^ 2 < (9 / 16 : ℝ) * ‖h‖ ^ 2 := by nlinarith [abs_nonneg h.im]
  nlinarith [hpos]

lemma local_re_antilipschitz (p : ℂ[X]) {z₀ : ℂ} (hz₀ : z₀ ∈ lemniscate p)
    (hw_le : |(starRingEnd ℂ (p.eval z₀) * p.derivative.eval z₀).re| ≤
      |(starRingEnd ℂ (p.eval z₀) * p.derivative.eval z₀).im|)
    (hw_ne : (starRingEnd ℂ (p.eval z₀) * p.derivative.eval z₀).im ≠ 0) :
    ∃ δ > 0, ∀ z₁ ∈ lemniscate p ∩ closedBall z₀ δ, ∀ z₂ ∈ lemniscate p ∩ closedBall z₀ δ,
      ‖z₁ - z₂‖ ≤ 2 * |(z₁ - z₂).re| := by
  let w₀ := p.eval z₀
  let d₀ := p.derivative.eval z₀
  let w := starRingEnd ℂ w₀ * d₀
  have hw₀_norm : ‖w₀‖ = 1 := hz₀
  have hwm_pos : 0 < |w.im| := abs_pos.mpr hw_ne
  have hd_pos : 0 < ‖d₀‖ := by
    have : 0 < ‖w‖ := lt_of_lt_of_le hwm_pos (Complex.abs_im_le_norm w)
    simpa [w, norm_mul, hw₀_norm] using this
  let ε := |w.im| / 8
  have hε : 0 < ε := by positivity
  have hderiv := (p.hasStrictDerivAt z₀).isLittleO.bound hε
  rw [Metric.eventually_nhds_iff] at hderiv
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hderiv
  let η := |w.im| / (16 * (‖d₀‖ + ε))
  have hη : 0 < η := by positivity
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp p.continuous.continuousAt η hη
  refine ⟨min δ₁ δ₂ / 2, by positivity, ?_⟩
  intro z₁ ⟨hz₁L, hz₁B⟩ z₂ ⟨hz₂L, hz₂B⟩
  have hz₁_d₁ : dist z₁ z₀ < δ₁ :=
    lt_of_le_of_lt (mem_closedBall.mp hz₁B) (by linarith [min_le_left δ₁ δ₂])
  have hz₂_d₁ : dist z₂ z₀ < δ₁ :=
    lt_of_le_of_lt (mem_closedBall.mp hz₂B) (by linarith [min_le_left δ₁ δ₂])
  have hz₁_d₂ : dist z₁ z₀ < δ₂ :=
    lt_of_le_of_lt (mem_closedBall.mp hz₁B) (by linarith [min_le_right δ₁ δ₂])
  have hpair : dist (z₁, z₂) (z₀, z₀) < δ₁ := by
    rw [Prod.dist_eq, max_lt_iff]; exact ⟨hz₁_d₁, hz₂_d₁⟩
  have hlin : ‖p.eval z₁ - p.eval z₂ - d₀ * (z₁ - z₂)‖ ≤ ε * ‖z₁ - z₂‖ := by
    simpa [d₀, mul_comm] using hδ₁ hpair
  let u₁ := p.eval z₁
  let u₂ := p.eval z₂
  let h := z₁ - z₂
  have hu_diff : ‖u₁ - u₂‖ ≤ (‖d₀‖ + ε) * ‖h‖ := by
    calc ‖u₁ - u₂‖ = ‖(u₁ - u₂ - d₀ * h) + d₀ * h‖ := by ring_nf
      _ ≤ ‖u₁ - u₂ - d₀ * h‖ + ‖d₀ * h‖ := norm_add_le _ _
      _ ≤ ε * ‖h‖ + ‖d₀‖ * ‖h‖ := by rw [norm_mul]; linarith
      _ = (‖d₀‖ + ε) * ‖h‖ := by ring
  have hu₁_near : ‖u₁ - w₀‖ < η := by simpa [u₁, w₀, dist_eq_norm] using hδ₂ hz₁_d₂
  have hu₂_near : ‖u₂ - w₀‖ < η := by
    have hz₂_d₂ : dist z₂ z₀ < δ₂ :=
      lt_of_le_of_lt (mem_closedBall.mp hz₂B) (by linarith [min_le_right δ₁ δ₂])
    simpa [u₂, w₀, dist_eq_norm] using hδ₂ hz₂_d₂
  have hu₁₂_small : ‖u₁ - u₂‖ ≤ 2 * η := by
    calc ‖u₁ - u₂‖ = ‖(u₁ - w₀) - (u₂ - w₀)‖ := by ring_nf
      _ ≤ ‖u₁ - w₀‖ + ‖u₂ - w₀‖ := norm_sub_le _ _
      _ ≤ 2 * η := by linarith
  have hcircle : 2 * ((starRingEnd ℂ u₁) * (u₁ - u₂)).re = ‖u₁ - u₂‖ ^ 2 :=
    unit_circle_re_sub hz₁L hz₂L
  have hre_u : |((starRingEnd ℂ w₀) * (u₁ - u₂)).re| ≤ (|w.im| / 8) * ‖h‖ := by
    have hsplit : ((starRingEnd ℂ w₀) * (u₁ - u₂)).re =
        ((starRingEnd ℂ u₁) * (u₁ - u₂)).re + ((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re := by
      rw [← Complex.add_re, ← add_mul, ← map_add]; congr 3; ring
    have h1 : |((starRingEnd ℂ u₁) * (u₁ - u₂)).re| ≤ η * ‖u₁ - u₂‖ := by
      have hnonneg : 0 ≤ ((starRingEnd ℂ u₁) * (u₁ - u₂)).re := by linarith [sq_nonneg ‖u₁ - u₂‖]
      rw [abs_of_nonneg hnonneg]; nlinarith [norm_nonneg (u₁ - u₂)]
    have h2 : |((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re| ≤ η * ‖u₁ - u₂‖ := by
      calc |((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re|
          ≤ ‖(starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)‖ := Complex.abs_re_le_norm _
        _ = ‖u₁ - w₀‖ * ‖u₁ - u₂‖ := by rw [norm_mul, RCLike.norm_conj, norm_sub_rev]
        _ ≤ η * ‖u₁ - u₂‖ := mul_le_mul_of_nonneg_right hu₁_near.le (norm_nonneg _)
    have h3 : |((starRingEnd ℂ w₀) * (u₁ - u₂)).re| ≤ 2 * η * ‖u₁ - u₂‖ := by
      rw [hsplit]
      linarith [abs_add_le ((starRingEnd ℂ u₁) * (u₁ - u₂)).re
        ((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re]
    have h4 : 2 * η * ‖u₁ - u₂‖ ≤ 2 * η * ((‖d₀‖ + ε) * ‖h‖) :=
      mul_le_mul_of_nonneg_left hu_diff (by positivity)
    have h5 : 2 * η * (‖d₀‖ + ε) = |w.im| / 8 := by
      dsimp [η]; field_simp [ne_of_gt (add_pos hd_pos hε)]; ring
    calc |((starRingEnd ℂ w₀) * (u₁ - u₂)).re|
        ≤ 2 * η * ‖u₁ - u₂‖ := h3
      _ ≤ 2 * η * ((‖d₀‖ + ε) * ‖h‖) := h4
      _ = (2 * η * (‖d₀‖ + ε)) * ‖h‖ := by ring
      _ = (|w.im| / 8) * ‖h‖ := by rw [h5]
  have hre_err : |((starRingEnd ℂ w₀) * (u₁ - u₂ - d₀ * h)).re| ≤ (|w.im| / 8) * ‖h‖ := by
    calc |((starRingEnd ℂ w₀) * (u₁ - u₂ - d₀ * h)).re|
        ≤ ‖(starRingEnd ℂ w₀) * (u₁ - u₂ - d₀ * h)‖ := Complex.abs_re_le_norm _
      _ = ‖w₀‖ * ‖u₁ - u₂ - d₀ * h‖ := by rw [norm_mul, RCLike.norm_conj]
      _ ≤ 1 * (ε * ‖h‖) := by rw [hw₀_norm]; linarith
      _ = (|w.im| / 8) * ‖h‖ := by dsimp [ε]; ring
  have hre_wh : |(w * h).re| ≤ (|w.im| / 4) * ‖h‖ := by
    have hid : (w * h).re = ((starRingEnd ℂ w₀) * (u₁ - u₂)).re -
        ((starRingEnd ℂ w₀) * (u₁ - u₂ - d₀ * h)).re := by
      dsimp [w]; rw [← Complex.sub_re]; congr 1; ring
    rw [hid]
    linarith [abs_sub ((starRingEnd ℂ w₀) * (u₁ - u₂)).re
      ((starRingEnd ℂ w₀) * (u₁ - u₂ - d₀ * h)).re]
  have him_bd : |h.im| ≤ |h.re| + (1 / 4 : ℝ) * ‖h‖ := by
    have hexp : (w * h).re = w.re * h.re - w.im * h.im := Complex.mul_re w h
    have htri : |w.im| * |h.im| ≤ |w.re| * |h.re| + |(w * h).re| := by
      calc |w.im| * |h.im| = |w.im * h.im| := (abs_mul _ _).symm
        _ = |w.re * h.re - (w * h).re| := by rw [hexp]; ring_nf
        _ ≤ |w.re * h.re| + |(w * h).re| := abs_sub _ _
        _ = |w.re| * |h.re| + |(w * h).re| := by rw [abs_mul]
    have htri2 : |w.im| * |h.im| ≤ |w.im| * |h.re| + (|w.im| / 4) * ‖h‖ := by
      nlinarith [abs_nonneg h.re]
    nlinarith [hwm_pos]
  exact norm_le_two_abs_re_of_im_bound h him_bd

lemma measurableSet_re_sdiff_compact {C D : Set ℂ} (hC : IsCompact C) (hD : IsCompact D) :
    MeasurableSet (Complex.re '' (C \ D)) := by
  by_cases hne : D.Nonempty
  · have hEq : C \ D = ⋃ m : ℕ, (C ∩ {z : ℂ | (1 : ℝ) / (m + 1) ≤ infDist z D}) := by
      ext z
      simp only [Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hzC, hzD⟩
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt ((hD.isClosed.notMem_iff_infDist_pos hne).mp hzD)
        exact ⟨m, hzC, hm.le⟩
      · rintro ⟨m, hzC, hm⟩
        exact ⟨hzC, (hD.isClosed.notMem_iff_infDist_pos hne).mpr (lt_of_lt_of_le (by positivity) hm)⟩
    rw [hEq, image_iUnion]
    refine MeasurableSet.iUnion fun m => ?_
    have hKm : IsCompact (C ∩ {z : ℂ | (1 : ℝ) / (m + 1) ≤ infDist z D}) :=
      hC.inter_right (isClosed_le continuous_const (continuous_infDist_pt D))
    exact (hKm.image Complex.continuous_re).isClosed.measurableSet
  · rw [not_nonempty_iff_eq_empty.mp hne, sdiff_empty]
    exact (hC.image Complex.continuous_re).isClosed.measurableSet

lemma hausdorff_le_two_volume_re {A : Set ℂ}
    (hA : ∀ z₁ ∈ A, ∀ z₂ ∈ A, ‖z₁ - z₂‖ ≤ 2 * |(z₁ - z₂).re|) :
    μH[1] A ≤ 2 * volume (Complex.re '' A) := by
  let f : A → ℝ := fun z => (z : ℂ).re
  have hf : AntilipschitzWith 2 f := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    change dist (x : ℂ) (y : ℂ) ≤ (2 : ℝ) * dist ((x : ℂ).re) ((y : ℂ).re)
    rw [dist_eq_norm, Real.dist_eq, ← Complex.sub_re]
    exact hA x.1 x.2 y.1 y.2
  have hiso : Isometry (Subtype.val : A → ℂ) := isometry_subtype_coe
  have h1 : μH[1] A = μH[1] (univ : Set A) := by
    simpa using hiso.hausdorffMeasure_image (Or.inl (zero_le_one' ℝ)) (univ : Set A)
  have h2 := hf.le_hausdorffMeasure_image (d := 1) zero_le_one (univ : Set A)
  have h3 : f '' (univ : Set A) = Complex.re '' A := by ext x; simp [f]
  rw [h1]
  simpa [h3, hausdorffMeasure_real] using h2

lemma finite_line_intersections {p : ℂ[X]} (hp : 0 < p.natDegree) (a b : ℂ) (hb : b ≠ 0) :
    {t : ℝ | ‖p.eval (a + (t : ℂ) * b)‖ = 1}.Finite := by
  let q := p.comp (C b * X + C a)
  let c := starRingEnd ℂ
  let f := q * q.map c - 1
  have hq : q.natDegree = p.natDegree := by simp [q, natDegree_comp, natDegree_C_mul_X _ hb]
  have hq' : (q.map c).natDegree = q.natDegree := natDegree_map_eq_of_injective c.injective q
  have hq₀ : q ≠ 0 := fun h => by rw [h, natDegree_zero] at hq; omega
  have hqc₀ : q.map c ≠ 0 := fun h => by rw [h, natDegree_zero, hq] at hq'; omega
  have hf : f.natDegree = 2 * p.natDegree := by
    dsimp [f]; rw [← C_1, natDegree_sub_C, natDegree_mul hq₀ hqc₀, hq', hq]; omega
  have hf₀ : f ≠ 0 := fun he => by rw [he, natDegree_zero] at hf; omega
  refine Set.Finite.of_finite_image (f := fun t : ℝ => (t : ℂ)) ?_ Complex.ofReal_injective.injOn
  refine f.roots.toFinset.finite_toSet.subset ?_
  rintro _ ⟨t, ht, rfl⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hf₀]
  have htEval : q.eval (t : ℂ) = p.eval (a + (t : ℂ) * b) := by
    simp [q, eval_comp, mul_comm b, add_comm a]
  have hc : c (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hqEval : (q.map c).eval (t : ℂ) = c (q.eval (t : ℂ)) := by
    simpa only [hc] using eval_map_apply (p := q) (f := c) (t : ℂ)
  change ‖p.eval (a + (t : ℂ) * b)‖ = 1 at ht
  dsimp only [f]
  rw [IsRoot, eval_sub, eval_mul, eval_one, hqEval]
  change q.eval (t : ℂ) * (starRingEnd ℂ) (q.eval (t : ℂ)) - 1 = 0
  rw [Complex.mul_conj, ← Complex.sq_norm, htEval, ht]
  norm_num

lemma disk_bound {p : ℂ[X]} (hp : 0 < p.natDegree) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    μH[1] (lemniscate p ∩ closedBall a r) ≤ ENNReal.ofReal (16 * p.natDegree * r) := by
  have hline : ∀ a' b' : ℂ, b' ≠ 0 →
      {t : ℝ | ‖p.eval (a' + (t : ℂ) * b')‖ = 1}.ncard ≤ 2 * p.natDegree :=
    fun _ _ hb' => OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1.ncard_level_line hp hb'
  have hSx_gen : ∀ (q : ℂ[X]), 0 < q.natDegree →
      (∀ a' b' : ℂ, b' ≠ 0 → {t : ℝ | ‖q.eval (a' + (t : ℂ) * b')‖ = 1}.ncard ≤ 2 * q.natDegree) →
      ∀ c₀ : ℂ, μH[1] {z ∈ lemniscate q ∩ closedBall c₀ r |
        |(starRingEnd ℂ (q.eval z) * q.derivative.eval z).re| ≤
          |(starRingEnd ℂ (q.eval z) * q.derivative.eval z).im| ∧
        (starRingEnd ℂ (q.eval z) * q.derivative.eval z).im ≠ 0} ≤
          ENNReal.ofReal (8 * q.natDegree * r) := by
    intro q hq hqline c₀
    classical
    let w : ℂ → ℂ := fun z => starRingEnd ℂ (q.eval z) * q.derivative.eval z
    have hw_cont : Continuous w := (continuous_star.comp q.continuous).mul q.derivative.continuous
    let K : ℕ → Set ℂ := fun m =>
      {z ∈ lemniscate q ∩ closedBall c₀ r |
        (1 : ℝ) / (m + 1) ≤ |(w z).im| ∧ |(w z).re| ≤ |(w z).im|}
    have hmono : Monotone K := by
      intro m₁ m₂ hm z ⟨hzS, hz1, hz2⟩
      exact ⟨hzS, le_trans (by gcongr) hz1, hz2⟩
    have hunion : {z ∈ lemniscate q ∩ closedBall c₀ r | |(w z).re| ≤ |(w z).im| ∧ (w z).im ≠ 0} =
        ⋃ m : ℕ, K m := by
      ext z; simp only [K, mem_ofPred_eq, mem_iUnion]
      refine ⟨fun ⟨hzS, hle, hne⟩ => ?_, fun ⟨m, hzS, hm, hle⟩ =>
        ⟨hzS, hle, abs_pos.mp (lt_of_lt_of_le (by positivity) hm)⟩⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hne)
      exact ⟨m, hzS, hm.le, hle⟩
    rw [hunion, hmono.measure_iUnion]
    refine iSup_le fun m => ?_
    have hKm_compact : IsCompact (K m) := by
      refine ((isCompact_closedBall c₀ r).inter_left (isClosed_eq q.continuous.norm continuous_const)).inter_right ?_
      exact (isClosed_le continuous_const (continuous_abs.comp (Complex.continuous_im.comp hw_cont))).inter
        (isClosed_le (continuous_abs.comp (Complex.continuous_re.comp hw_cont))
          (continuous_abs.comp (Complex.continuous_im.comp hw_cont)))
    have hloc : ∀ z : ℂ, ∃ δ : ℝ, 0 < δ ∧
        (z ∈ K m → ∀ z₁ ∈ lemniscate q ∩ closedBall z δ, ∀ z₂ ∈ lemniscate q ∩ closedBall z δ,
          ‖z₁ - z₂‖ ≤ 2 * |(z₁ - z₂).re|) := by
      intro z
      by_cases hz : z ∈ K m
      · obtain ⟨hzS, hm', hle⟩ := hz
        obtain ⟨δ, hδ, hlip⟩ := local_re_antilipschitz q hzS.1 hle
          (abs_pos.mp (lt_of_lt_of_le (by positivity) hm'))
        exact ⟨δ, hδ, fun _ => hlip⟩
      · exact ⟨1, zero_lt_one, fun h => (hz h).elim⟩
    choose δ hδ_pos hδ_lip using hloc
    obtain ⟨t, ht_cov⟩ := hKm_compact.elim_finite_subcover
      (fun x : K m => ball (x : ℂ) (δ x)) (fun _ => isOpen_ball)
      (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hδ_pos z)⟩)
    let N := Fintype.card t
    let e : Fin N ≃ t := (Fintype.equivFin t).symm
    let C : Fin N → Set ℂ := fun i => K m ∩ closedBall ((e i).1 : ℂ) (δ ((e i).1 : ℂ))
    have hC_compact : ∀ i, IsCompact (C i) := fun i => hKm_compact.inter_right isClosed_closedBall
    let D : Fin N → Set ℂ := fun i => ⋃ j ∈ Finset.univ.filter (· < i), C j
    have hD_compact : ∀ i, IsCompact (D i) := fun i =>
      (Finset.univ.filter (· < i)).isCompact_biUnion (fun j _ => hC_compact j)
    let A : Fin N → Set ℂ := fun i => C i \ D i
    have hKm_sub : K m ⊆ ⋃ i : Fin N, A i := by
      intro z hz
      obtain ⟨w₀, hw₀⟩ := mem_iUnion.mp (ht_cov hz)
      obtain ⟨hw₀_t, hz_ball⟩ := mem_iUnion.mp hw₀
      let i₁ : Fin N := e.symm ⟨w₀, hw₀_t⟩
      have hzi₁ : z ∈ C i₁ := ⟨hz, by
        have heq : (e i₁).1 = w₀ := congrArg Subtype.val (e.apply_symm_apply ⟨w₀, hw₀_t⟩)
        rw [heq]; exact ball_subset_closedBall hz_ball⟩
      let S_idx := Finset.univ.filter (fun i : Fin N => z ∈ C i)
      have hSne : S_idx.Nonempty := ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi₁⟩⟩
      let i₀ := S_idx.min' hSne
      refine mem_iUnion.mpr ⟨i₀, (Finset.mem_filter.mp (Finset.min'_mem S_idx hSne)).2, ?_⟩
      intro hzD
      obtain ⟨j, hjF, hzj⟩ := mem_iUnion₂.mp hzD
      exact not_lt_of_ge (Finset.min'_le S_idx j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj⟩))
        (Finset.mem_filter.mp hjF).2
    have hA_disj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact Set.disjoint_left.mpr fun z hzi hzj =>
          hzj.2 (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hzi.1⟩)
      · exact Set.disjoint_left.mpr fun z hzi hzj =>
          hzi.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, hzj.1⟩)
    have hA_meas : ∀ i, MeasurableSet (Complex.re '' A i) := fun i =>
      measurableSet_re_sdiff_compact (hC_compact i) (hD_compact i)
    let J : Set ℝ := Icc (c₀.re - r) (c₀.re + r)
    have hsum_vol : (∑ i : Fin N, volume (Complex.re '' A i)) ≤ ENNReal.ofReal (4 * q.natDegree * r) := by
      have hpt : ∀ x : ℝ,
          (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
            (2 * q.natDegree : ℝ≥0∞) * J.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        intro x
        let F := Finset.univ.filter (fun i : Fin N => x ∈ Complex.re '' A i)
        have hsumF : (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x) = F.card := by
          calc (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x)
              = ∑ i : Fin N, if x ∈ Complex.re '' A i then (1 : ℝ≥0∞) else 0 :=
                Finset.sum_congr rfl fun i _ => by by_cases hx : x ∈ Complex.re '' A i <;> simp [hx]
            _ = F.card := by simp [F]
        rw [hsumF]
        by_cases hF : F.Nonempty
        · obtain ⟨i₀, hi₀⟩ := hF
          obtain ⟨z₀, hz₀A, hz₀x⟩ := (Finset.mem_filter.mp hi₀).2
          have hz₀B : z₀ ∈ closedBall c₀ r := hz₀A.1.1.1.2
          have hxJ : x ∈ J := by
            have habs : |x - c₀.re| ≤ r := by
              calc |x - c₀.re| = |(z₀ - c₀).re| := by rw [← hz₀x, Complex.sub_re]
                _ ≤ ‖z₀ - c₀‖ := Complex.abs_re_le_norm _
                _ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hz₀B
            exact ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩
          rw [indicator_of_mem hxJ, mul_one]
          let T : Set ℝ := {t : ℝ | ‖q.eval ((x : ℂ) + (t : ℂ) * Complex.I)‖ = 1}
          have hTfin : T.Finite := finite_line_intersections hq (x : ℂ) Complex.I Complex.I_ne_zero
          let g : Fin N → ℝ := fun i =>
            if hi : i ∈ F then ((Finset.mem_filter.mp hi).2.choose).im else 0
          have hg_maps : MapsTo g (F : Set (Fin N)) T := by
            intro i hi
            have hi' : i ∈ F := hi
            dsimp [g]; rw [dif_pos hi']
            let w₀ := (Finset.mem_filter.mp hi').2.choose
            have hz : w₀ ∈ A i ∧ w₀.re = x := (Finset.mem_filter.mp hi').2.choose_spec
            have hL : ‖q.eval w₀‖ = 1 := hz.1.1.1.1.1
            have hdecomp : (x : ℂ) + (w₀.im : ℂ) * Complex.I = w₀ :=
              Complex.ext (by simp [hz.2]) (by simp)
            change ‖q.eval ((x : ℂ) + (w₀.im : ℂ) * Complex.I)‖ = 1
            rwa [hdecomp]
          have hg_inj : InjOn g (F : Set (Fin N)) := by
            intro i hi j hj hij
            have hi' : i ∈ F := hi
            have hj' : j ∈ F := hj
            dsimp [g] at hij; rw [dif_pos hi', dif_pos hj'] at hij
            have hzi := (Finset.mem_filter.mp hi').2.choose_spec
            have hzj := (Finset.mem_filter.mp hj').2.choose_spec
            have heq := Complex.ext (hzi.2.trans hzj.2.symm) hij
            by_contra hne
            exact Set.disjoint_left.mp (hA_disj hne) hzi.1 (heq ▸ hzj.1)
          have hcard : F.card ≤ 2 * q.natDegree := by
            calc F.card = (F : Set (Fin N)).ncard := (ncard_coe_finset F).symm
              _ ≤ T.ncard := ncard_le_ncard_of_injOn g hg_maps hg_inj hTfin
              _ ≤ 2 * q.natDegree := hqline (x : ℂ) Complex.I Complex.I_ne_zero
          exact_mod_cast hcard
        · rw [Finset.not_nonempty_iff_eq_empty.mp hF]; simp
      calc (∑ i : Fin N, volume (Complex.re '' A i))
          = ∫⁻ x, (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ∂volume := by
            rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hA_meas i))]
            exact Finset.sum_congr rfl fun i _ => (lintegral_indicator_one (hA_meas i)).symm
        _ ≤ ∫⁻ x, (2 * q.natDegree : ℝ≥0∞) * J.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume :=
            lintegral_mono hpt
        _ = (2 * q.natDegree : ℝ≥0∞) * volume J := by
            rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Icc)]
            erw [lintegral_indicator_one measurableSet_Icc]
        _ = ENNReal.ofReal (4 * q.natDegree * r) := by
            rw [Real.volume_Icc, show c₀.re + r - (c₀.re - r) = 2 * r by ring]
            have hcast : (2 * q.natDegree : ℝ≥0∞) = ENNReal.ofReal (2 * q.natDegree : ℝ) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
            rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
    calc μH[1] (K m)
        ≤ μH[1] (⋃ i : Fin N, A i) := measure_mono hKm_sub
      _ ≤ ∑ i : Fin N, μH[1] (A i) := measure_iUnion_fintype_le (μH[1]) A
      _ ≤ ∑ i : Fin N, 2 * volume (Complex.re '' A i) := Finset.sum_le_sum fun i _ =>
          hausdorff_le_two_volume_re fun z₁ hz₁ z₂ hz₂ =>
            hδ_lip ((e i).1 : ℂ) (e i).1.2 z₁ ⟨hz₁.1.1.1.1, hz₁.1.2⟩ z₂ ⟨hz₂.1.1.1.1, hz₂.1.2⟩
      _ = 2 * ∑ i : Fin N, volume (Complex.re '' A i) := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ENNReal.ofReal (4 * q.natDegree * r) :=
          mul_le_mul_of_nonneg_left hsum_vol (by positivity)
      _ = ENNReal.ofReal (8 * q.natDegree * r) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  let Sx_set := {z ∈ lemniscate p ∩ closedBall a r |
    |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).re| ≤
      |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).im| ∧
    (starRingEnd ℂ (p.eval z) * p.derivative.eval z).im ≠ 0}
  let Sy_set := {z ∈ lemniscate p ∩ closedBall a r |
    |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).im| ≤
      |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).re| ∧
    (starRingEnd ℂ (p.eval z) * p.derivative.eval z).re ≠ 0}
  have hSy : μH[1] Sy_set ≤ ENNReal.ofReal (8 * p.natDegree * r) := by
    let q : ℂ[X] := p.comp (C Complex.I * X)
    have hq_deg : q.natDegree = p.natDegree := by
      simp [q, natDegree_comp, natDegree_C_mul_X _ Complex.I_ne_zero]
    have hq_pos : 0 < q.natDegree := hq_deg.symm ▸ hp
    have hq_line : ∀ a' b' : ℂ, b' ≠ 0 →
        {t : ℝ | ‖q.eval (a' + (t : ℂ) * b')‖ = 1}.ncard ≤ 2 * q.natDegree :=
      fun _ _ hb' => OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1.ncard_level_line hq_pos hb'
    let rot : ℂ ≃ᵢ ℂ :=
      ⟨Equiv.mulLeft₀ Complex.I Complex.I_ne_zero, Isometry.of_dist_eq fun x y => by
        change dist (Complex.I * x) (Complex.I * y) = dist x y
        rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_I, one_mul]⟩
    have hpre : rot ⁻¹' Sy_set = {z ∈ lemniscate q ∩ closedBall (-Complex.I * a) r |
        |(starRingEnd ℂ (q.eval z) * q.derivative.eval z).re| ≤
          |(starRingEnd ℂ (q.eval z) * q.derivative.eval z).im| ∧
        (starRingEnd ℂ (q.eval z) * q.derivative.eval z).im ≠ 0} := by
      ext u
      have hq_eval : q.eval u = p.eval (Complex.I * u) := by simp [q, eval_comp]
      have hq_deriv : q.derivative.eval u = Complex.I * p.derivative.eval (Complex.I * u) := by
        have hd : q.derivative = p.derivative.comp (C Complex.I * X) * C Complex.I := by
          dsimp [q]; rw [derivative_comp]; simp; ring
        rw [hd, eval_mul, eval_comp]
        simp only [eval_mul, eval_C, eval_X]
        rw [mul_comm]
      let wp := starRingEnd ℂ (p.eval (Complex.I * u)) * p.derivative.eval (Complex.I * u)
      have hwq : starRingEnd ℂ (q.eval u) * q.derivative.eval u = Complex.I * wp := by
        rw [hq_eval, hq_deriv]; dsimp [wp]; ring
      have hball : Complex.I * u ∈ closedBall a r ↔ u ∈ closedBall (-Complex.I * a) r := by
        simp only [mem_closedBall, dist_eq_norm]
        have hid : Complex.I * u - a = Complex.I * (u - (-Complex.I * a)) := by
          calc Complex.I * u - a = Complex.I * u - (Complex.I * (-Complex.I)) * a := by simp
            _ = Complex.I * (u - (-Complex.I * a)) := by ring
        rw [hid, norm_mul, Complex.norm_I, one_mul]
      change (Complex.I * u ∈ Sy_set) ↔ _
      have hL_iff : Complex.I * u ∈ lemniscate p ↔ u ∈ lemniscate q := by
        change ‖p.eval (Complex.I * u)‖ = 1 ↔ ‖q.eval u‖ = 1
        rw [hq_eval]
      have hre_rot : (Complex.I * wp).re = -wp.im := by simp
      have him_rot : (Complex.I * wp).im = wp.re := by simp
      simp only [Sy_set, mem_ofPred_eq, mem_inter_iff, hL_iff, hball]
      change (_ ∧ |wp.im| ≤ |wp.re| ∧ wp.re ≠ 0) ↔
        (_ ∧ |(starRingEnd ℂ (q.eval u) * q.derivative.eval u).re| ≤
              |(starRingEnd ℂ (q.eval u) * q.derivative.eval u).im| ∧
            (starRingEnd ℂ (q.eval u) * q.derivative.eval u).im ≠ 0)
      rw [hwq, hre_rot, him_rot, abs_neg]
    have hm := rot.hausdorffMeasure_preimage 1 Sy_set
    rw [hpre] at hm
    rw [← hm, ← hq_deg]
    exact hSx_gen q hq_pos hq_line (-Complex.I * a)
  have hScrit : μH[1] {z : ℂ | p.derivative.eval z = 0} = 0 := by
    have hp_ne : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hp; omega
    have hderiv_ne : p.derivative ≠ 0 := by
      intro hd
      have hc := congrArg (fun f : ℂ[X] => f.coeff (p.natDegree - 1)) hd
      rw [coeff_zero, coeff_derivative, Nat.sub_add_cancel hp] at hc
      have hcast : ((p.natDegree - 1 : ℕ) : ℂ) + 1 = (p.natDegree : ℂ) := by
        exact_mod_cast Nat.sub_add_cancel hp
      rw [hcast] at hc
      exact mul_ne_zero (p.leadingCoeff_ne_zero.mpr hp_ne)
        (Nat.cast_ne_zero.mpr hp.ne') hc
    have hfin : {z : ℂ | p.derivative.eval z = 0}.Finite :=
      p.derivative.roots.toFinset.finite_toSet.subset fun z hz => by
        rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hderiv_ne]; exact hz
    have := MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ (zero_lt_one' ℝ)
    exact hfin.measure_zero (μH[1])
  have hcov : lemniscate p ∩ closedBall a r ⊆
      {z : ℂ | p.derivative.eval z = 0} ∪ (Sx_set ∪ Sy_set) := by
    intro z hz
    by_cases hc : p.derivative.eval z = 0
    · exact Or.inl hc
    · right
      let w := starRingEnd ℂ (p.eval z) * p.derivative.eval z
      have hw_ne : w ≠ 0 := by
        have hpz : p.eval z ≠ 0 := fun h0 => by have : ‖p.eval z‖ = 1 := hz.1; simp [h0] at this
        exact mul_ne_zero (by simp [hpz]) hc
      rcases le_total |w.re| |w.im| with hxy | hyx
      · refine Or.inl ⟨hz, hxy, fun him0 => ?_⟩
        have hre0 : w.re = 0 := abs_nonpos_iff.mp (by rw [him0, abs_zero] at hxy; exact hxy)
        exact hw_ne (Complex.ext hre0 him0)
      · refine Or.inr ⟨hz, hyx, fun hre0 => ?_⟩
        have him0 : w.im = 0 := abs_nonpos_iff.mp (by rw [hre0, abs_zero] at hyx; exact hyx)
        exact hw_ne (Complex.ext hre0 him0)
  calc μH[1] (lemniscate p ∩ closedBall a r)
      ≤ μH[1] ({z : ℂ | p.derivative.eval z = 0} ∪ (Sx_set ∪ Sy_set)) := measure_mono hcov
    _ ≤ μH[1] {z : ℂ | p.derivative.eval z = 0} + (μH[1] Sx_set + μH[1] Sy_set) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ 0 + (ENNReal.ofReal (8 * p.natDegree * r) + ENNReal.ofReal (8 * p.natDegree * r)) := by
        rw [hScrit]
        exact add_le_add le_rfl (add_le_add (hSx_gen p hp hline a) hSy)
    _ = ENNReal.ofReal (16 * p.natDegree * r) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

noncomputable def polyOfRoots {n : ℕ} (z : Fin n → ℂ) : ℂ[X] :=
  ∏ i : Fin n, (X - C (z i))

lemma natDegree_polyOfRoots {n : ℕ} (z : Fin n → ℂ) :
    (polyOfRoots z).natDegree = n := by
  unfold polyOfRoots
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

lemma eval_polyOfRoots {n : ℕ} (z : Fin n → ℂ) (ζ : ℂ) :
    (polyOfRoots z).eval ζ = ∏ i : Fin n, (ζ - z i) := by
  simp [polyOfRoots, eval_prod]

lemma eval_derivative_polyOfRoots {n : ℕ} (z : Fin n → ℂ) (ζ : ℂ) :
    (polyOfRoots z).derivative.eval ζ =
      ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (ζ - z j) := by
  unfold polyOfRoots
  rw [derivative_prod_finset]
  simp [eval_finsetSum, eval_prod]

lemma lemniscate_subset_closedBall {n : ℕ} (hn : 0 < n) (z₀ z : Fin n → ℂ)
    (hz : dist z z₀ < 1) :
    lemniscate (polyOfRoots z) ⊆ closedBall (0 : ℂ) (2 + ∑ i : Fin n, ‖z₀ i‖) := by
  intro ζ hζ
  rw [mem_closedBall, dist_zero_right]
  by_contra! hgt
  have hfac : ∀ i : Fin n, 1 < ‖ζ - z i‖ := by
    intro i
    have hzi : ‖z i - z₀ i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) i) (by simpa [dist_eq_norm] using hz)
    have hz₀i : ‖z₀ i‖ ≤ ∑ j : Fin n, ‖z₀ j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (z₀ j)) (Finset.mem_univ i)
    have htri1 : ‖z i‖ ≤ ‖z₀ i‖ + ‖z i - z₀ i‖ := by
      calc ‖z i‖ = ‖z₀ i + (z i - z₀ i)‖ := by ring_nf
        _ ≤ ‖z₀ i‖ + ‖z i - z₀ i‖ := norm_add_le _ _
    have htri2 : ‖ζ‖ - ‖z i‖ ≤ ‖ζ - z i‖ := norm_sub_norm_le ζ (z i)
    linarith
  let i₀ : Fin n := ⟨0, hn⟩
  have herase : 1 ≤ ∏ j ∈ Finset.univ.erase i₀, ‖ζ - z j‖ :=
    Finset.prod_induction _ (fun x => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun j _ => (hfac j).le)
  have hprod_gt : 1 < ∏ i : Fin n, ‖ζ - z i‖ := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ < ‖ζ - z i₀‖ * 1 := by linarith [hfac i₀]
      _ ≤ ‖ζ - z i₀‖ * ∏ j ∈ Finset.univ.erase i₀, ‖ζ - z j‖ :=
        mul_le_mul_of_nonneg_left herase (norm_nonneg _)
  have heq1 : (∏ i : Fin n, ‖ζ - z i‖) = 1 := by
    have : ‖(polyOfRoots z).eval ζ‖ = 1 := hζ
    simpa [eval_polyOfRoots, norm_prod] using this
  linarith

lemma uniform_close_of_continuous {n : ℕ} {G : (Fin n → ℂ) × ℂ → ℂ} (hG : Continuous G)
    (z₀ : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ z : Fin n → ℂ, dist z z₀ < δ → ∀ ζ ∈ closedBall (0 : ℂ) R,
      ‖G (z, ζ) - G (z₀, ζ)‖ < η := by
  classical
  let K : Set ℂ := closedBall (0 : ℂ) R
  have hK : IsCompact K := isCompact_closedBall 0 R
  have hloc : ∀ ζ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ p : (Fin n → ℂ) × ℂ,
      dist p (z₀, ζ) < r → ‖G p - G (z₀, ζ)‖ < η / 2 := by
    intro ζ
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hG.continuousAt (η / 2) (by positivity)
    exact ⟨r, hr, fun p hp => by simpa [dist_eq_norm] using hball hp⟩
  choose r hr_pos hr_bd using hloc
  obtain ⟨t, ht_cov⟩ := hK.elim_finite_subcover
    (fun x : K => ball (x : ℂ) (r x)) (fun _ => isOpen_ball)
    (fun ζ hζ => mem_iUnion.mpr ⟨⟨ζ, hζ⟩, mem_ball_self (hr_pos ζ)⟩)
  have ht_ne : t.Nonempty := by
    have h0K : (0 : ℂ) ∈ K := mem_closedBall_self hR
    obtain ⟨x, hx⟩ := mem_iUnion.mp (ht_cov h0K)
    obtain ⟨hxt, _⟩ := mem_iUnion.mp hx
    exact ⟨x, hxt⟩
  let s_rad := t.image (fun x : K => r (x : ℂ))
  let δ := s_rad.min' (ht_ne.image _)
  have hδ_pos : 0 < δ := by
    obtain ⟨x, _, hxeq⟩ := Finset.mem_image.mp (Finset.min'_mem s_rad (ht_ne.image _))
    dsimp [δ]; rw [← hxeq]; exact hr_pos x
  refine ⟨δ, hδ_pos, fun z hz ζ hζ => ?_⟩
  obtain ⟨x, hx⟩ := mem_iUnion.mp (ht_cov hζ)
  obtain ⟨hxt, hζx⟩ := mem_iUnion.mp hx
  have hδ_le : δ ≤ r (x : ℂ) :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)
  have hp1 : dist (z, ζ) (z₀, (x : ℂ)) < r (x : ℂ) := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_lt_of_le hz hδ_le, hζx⟩
  have hp2 : dist (z₀, ζ) (z₀, (x : ℂ)) < r (x : ℂ) := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by simp [hr_pos (x : ℂ)], hζx⟩
  calc ‖G (z, ζ) - G (z₀, ζ)‖
      = ‖(G (z, ζ) - G (z₀, (x : ℂ))) - (G (z₀, ζ) - G (z₀, (x : ℂ)))‖ := by ring_nf
    _ ≤ ‖G (z, ζ) - G (z₀, (x : ℂ))‖ + ‖G (z₀, ζ) - G (z₀, (x : ℂ))‖ := norm_sub_le _ _
    _ < η / 2 + η / 2 := add_lt_add (hr_bd _ _ hp1) (hr_bd _ _ hp2)
    _ = η := by ring

lemma uniform_close_polyOfRoots {n : ℕ} (z₀ : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ z : Fin n → ℂ, dist z z₀ < δ →
      (∀ ζ ∈ closedBall (0 : ℂ) R, ‖(polyOfRoots z).eval ζ - (polyOfRoots z₀).eval ζ‖ < η) ∧
      (∀ ζ ∈ closedBall (0 : ℂ) R,
        ‖(polyOfRoots z).derivative.eval ζ - (polyOfRoots z₀).derivative.eval ζ‖ < η) := by
  have hcont1 : Continuous (fun p : (Fin n → ℂ) × ℂ => (polyOfRoots p.1).eval p.2) := by
    simp only [eval_polyOfRoots]; fun_prop
  have hcont2 : Continuous (fun p : (Fin n → ℂ) × ℂ => (polyOfRoots p.1).derivative.eval p.2) := by
    simp only [eval_derivative_polyOfRoots]; fun_prop
  obtain ⟨δ₁, hδ₁, hb₁⟩ := uniform_close_of_continuous hcont1 z₀ hR hη
  obtain ⟨δ₂, hδ₂, hb₂⟩ := uniform_close_of_continuous hcont2 z₀ hR hη
  exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz =>
    ⟨hb₁ z (lt_of_lt_of_le hz (min_le_left _ _)), hb₂ z (lt_of_lt_of_le hz (min_le_right _ _))⟩⟩

lemma local_chart_data (P₀ : ℂ[X]) (w : ℂ) (hd : P₀.derivative.eval w ≠ 0)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ (g : ℂ → ℂ) (ρ r_u : ℝ),
      0 < ρ ∧ ρ ≤ 1 / 4 ∧ 0 < r_u ∧
      (∀ u ∈ ball (P₀.eval w) r_u, P₀.eval (g u) = u) ∧
      (∀ u₁ ∈ ball (P₀.eval w) r_u, ∀ u₂ ∈ ball (P₀.eval w) r_u,
        ‖g u₁ - g u₂ - (P₀.derivative.eval w)⁻¹ * (u₁ - u₂)‖ ≤
          (θ / (4 * ‖P₀.derivative.eval w‖)) * ‖u₁ - u₂‖) ∧
      (∀ ζ ∈ ball w (4 * ρ), g (P₀.eval ζ) = ζ) ∧
      (∀ ζ ∈ ball w (4 * ρ), P₀.eval ζ ∈ ball (P₀.eval w) (r_u / 2)) ∧
      (∀ ζ₁ ∈ ball w (4 * ρ), ∀ ζ₂ ∈ ball w (4 * ρ),
        ‖P₀.eval ζ₁ - P₀.eval ζ₂ - P₀.derivative.eval w * (ζ₁ - ζ₂)‖ ≤
          (θ * ‖P₀.derivative.eval w‖ / 4) * ‖ζ₁ - ζ₂‖) := by
  let f₀ : ℂ → ℂ := fun ζ => P₀.eval ζ
  have hf : HasStrictDerivAt f₀ (P₀.derivative.eval w) w := P₀.hasStrictDerivAt w
  let g : ℂ → ℂ := hf.localInverse f₀ (P₀.derivative.eval w) w hd
  have hd_pos : 0 < ‖P₀.derivative.eval w‖ := norm_pos_iff.mpr hd
  obtain ⟨r₁, hr₁_pos, hr₁⟩ := Metric.eventually_nhds_iff.mp (hf.eventually_right_inverse hd)
  have hg_deriv := (hf.to_localInverse hd).isLittleO.bound
    (show 0 < θ / (4 * ‖P₀.derivative.eval w‖) by positivity)
  obtain ⟨r₂, hr₂_pos, hr₂⟩ := Metric.eventually_nhds_iff.mp hg_deriv
  let r_u := min r₁ r₂
  have hru_pos : 0 < r_u := lt_min hr₁_pos hr₂_pos
  obtain ⟨s₁, hs₁_pos, hs₁⟩ := Metric.eventually_nhds_iff.mp (hf.eventually_left_inverse hd)
  obtain ⟨s₂, hs₂_pos, hs₂⟩ := Metric.continuousAt_iff.mp P₀.continuous.continuousAt (r_u / 2) (by positivity)
  obtain ⟨s₃, hs₃_pos, hs₃⟩ := Metric.eventually_nhds_iff.mp
    (hf.isLittleO.bound (show 0 < θ * ‖P₀.derivative.eval w‖ / 4 by positivity))
  let s := min 1 (min s₁ (min s₂ s₃))
  have hs_pos : 0 < s := lt_min zero_lt_one (lt_min hs₁_pos (lt_min hs₂_pos hs₃_pos))
  refine ⟨g, s / 8, r_u, by positivity, ?_, hru_pos, ?_, ?_, ?_, ?_, ?_⟩
  · have : s ≤ 1 := min_le_left _ _; linarith
  · intro u hu
    exact hr₁ (lt_of_lt_of_le (mem_ball.mp hu) (min_le_left _ _))
  · intro u₁ hu₁ u₂ hu₂
    have hp : dist (u₁, u₂) (f₀ w, f₀ w) < r₂ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨lt_of_lt_of_le (mem_ball.mp hu₁) (min_le_right _ _),
        lt_of_lt_of_le (mem_ball.mp hu₂) (min_le_right _ _)⟩
    simpa [g, mul_comm] using hr₂ hp
  · intro ζ hζ
    have hs_le : s ≤ s₁ := (min_le_right _ _).trans (min_le_left _ _)
    exact hs₁ (lt_of_lt_of_le (mem_ball.mp hζ) (by linarith))
  · intro ζ hζ
    have hs_le : s ≤ s₂ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    exact hs₂ (lt_of_lt_of_le (mem_ball.mp hζ) (by linarith))
  · intro ζ₁ hζ₁ ζ₂ hζ₂
    have hs_le : s ≤ s₃ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    have hp : dist (ζ₁, ζ₂) (w, w) < s₃ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨lt_of_lt_of_le (mem_ball.mp hζ₁) (by linarith),
        lt_of_lt_of_le (mem_ball.mp hζ₂) (by linarith)⟩
    simpa [f₀, mul_comm] using hs₃ hp

lemma eval_diff_lip_on_closedBall (P₀ Pz : ℂ[X]) {R η : ℝ}
    (hder_bd : ∀ w ∈ closedBall (0 : ℂ) R, ‖Pz.derivative.eval w - P₀.derivative.eval w‖ ≤ η) :
    ∀ ζ₁ ∈ closedBall (0 : ℂ) R, ∀ ζ₂ ∈ closedBall (0 : ℂ) R,
      ‖(Pz.eval ζ₁ - P₀.eval ζ₁) - (Pz.eval ζ₂ - P₀.eval ζ₂)‖ ≤ η * ‖ζ₁ - ζ₂‖ := by
  intro ζ₁ hζ₁ ζ₂ hζ₂
  let Qz : ℂ[X] := Pz - P₀
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) R,
      HasDerivWithinAt (fun w => Qz.eval w) (Qz.derivative.eval w) (closedBall (0 : ℂ) R) w :=
    fun w _ => Qz.hasDerivWithinAt w _
  have hbd : ∀ w ∈ closedBall (0 : ℂ) R, ‖Qz.derivative.eval w‖ ≤ η := by
    intro w hw
    have : Qz.derivative.eval w = Pz.derivative.eval w - P₀.derivative.eval w := by
      dsimp only [Qz]; rw [derivative_sub, eval_sub]
    rw [this]
    exact hder_bd w hw
  have hmv := (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    hdiff hbd hζ₂ hζ₁
  dsimp only [Qz] at hmv
  rw [eval_sub, eval_sub] at hmv
  exact hmv

lemma phi_antilipschitz (P₀ Pz : ℂ[X]) {K₀ Az : Set ℂ} {R₀ δ θ ρ_min d_min η_der : ℝ}
    (hδ_pos : 0 < δ) (hθ_pos : 0 < θ) (hθ_lt_one : θ < 1) (hθ_inv : (1 + δ) * (1 - θ) = 1)
    {M : ℕ} (wi : Fin M → ℂ) (g_w : ℂ → ℂ → ℂ) (ρ_w ru_w : ℂ → ℝ)
    (hwi_K₀ : ∀ i, wi i ∈ K₀) (hK₀_deriv : ∀ w ∈ K₀, P₀.derivative.eval w ≠ 0)
    (hρ_pos : ∀ w, 0 < ρ_w w) (hρmin_le : ∀ i, ρ_min ≤ ρ_w (wi i))
    (hdmin_le : ∀ i, d_min ≤ ‖P₀.derivative.eval (wi i)‖)
    (hηder_le : η_der ≤ θ * d_min / 8)
    (hchart_spec : ∀ w ∈ K₀,
      (∀ u ∈ ball (P₀.eval w) (ru_w w), P₀.eval (g_w w u) = u) ∧
      (∀ u₁ ∈ ball (P₀.eval w) (ru_w w), ∀ u₂ ∈ ball (P₀.eval w) (ru_w w),
        ‖g_w w u₁ - g_w w u₂ - (P₀.derivative.eval w)⁻¹ * (u₁ - u₂)‖ ≤
          (θ / (4 * ‖P₀.derivative.eval w‖)) * ‖u₁ - u₂‖) ∧
      (∀ ζ ∈ ball w (4 * ρ_w w), g_w w (P₀.eval ζ) = ζ) ∧
      (∀ ζ ∈ ball w (4 * ρ_w w), P₀.eval ζ ∈ ball (P₀.eval w) (ru_w w / 2)) ∧
      (∀ ζ₁ ∈ ball w (4 * ρ_w w), ∀ ζ₂ ∈ ball w (4 * ρ_w w),
        ‖P₀.eval ζ₁ - P₀.eval ζ₂ - P₀.derivative.eval w * (ζ₁ - ζ₂)‖ ≤
          (θ * ‖P₀.derivative.eval w‖ / 4) * ‖ζ₁ - ζ₂‖))
    (hball_R1 : ∀ (i : Fin M) {ζ : ℂ}, ζ ∈ ball (wi i) (4 * ρ_w (wi i)) →
      ζ ∈ closedBall (0 : ℂ) (R₀ + 1))
    (hlocal_eval_in_ru : ∀ (i : Fin M) {ζ : ℂ}, ζ ∈ ball (wi i) (4 * ρ_w (wi i)) →
      Pz.eval ζ ∈ ball (P₀.eval (wi i)) (ru_w (wi i)))
    (hlocal_disp : ∀ (i : Fin M) {ζ : ℂ}, ζ ∈ ball (wi i) (2 * ρ_w (wi i)) →
      ‖g_w (wi i) (Pz.eval ζ) - ζ‖ < min (ρ_min / 2) (θ * ρ_min / 2))
    (hQz_lip : ∀ ζ₁ ∈ closedBall (0 : ℂ) (R₀ + 1), ∀ ζ₂ ∈ closedBall (0 : ℂ) (R₀ + 1),
      ‖(Pz.eval ζ₁ - P₀.eval ζ₁) - (Pz.eval ζ₂ - P₀.eval ζ₂)‖ ≤ η_der * ‖ζ₁ - ζ₂‖)
    (idx : ∀ ζ ∈ Az, Fin M)
    (hidx : ∀ ζ (hζ : ζ ∈ Az), ζ ∈ ball (wi (idx ζ hζ)) (ρ_w (wi (idx ζ hζ)))) :
    AntilipschitzWith ⟨1 + δ, by positivity⟩
      (fun x : Az => g_w (wi (idx x.1 x.2)) (Pz.eval x.1)) := by
  let Φ : Az → ℂ := fun x => g_w (wi (idx x.1 x.2)) (Pz.eval x.1)
  refine AntilipschitzWith.of_le_mul_dist fun x₁ x₂ => ?_
  change dist x₁.1 x₂.1 ≤ (1 + δ) * dist (Φ x₁) (Φ x₂)
  rw [dist_eq_norm, dist_eq_norm]
  suffices h1 : (1 - θ) * ‖x₁.1 - x₂.1‖ ≤ ‖Φ x₁ - Φ x₂‖ by
    have hm := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + δ by positivity)
    rwa [← mul_assoc, hθ_inv, one_mul] at hm
  by_cases hfar : ρ_min ≤ ‖x₁.1 - x₂.1‖
  · have hd1 : ‖Φ x₁ - x₁.1‖ < θ * ρ_min / 2 := by
      have := hlocal_disp (idx x₁.1 x₁.2)
        (ball_subset_ball (by linarith [hρ_pos (wi (idx x₁.1 x₁.2))]) (hidx x₁.1 x₁.2))
      exact (lt_min_iff.mp this).2
    have hd2 : ‖Φ x₂ - x₂.1‖ < θ * ρ_min / 2 := by
      have := hlocal_disp (idx x₂.1 x₂.2)
        (ball_subset_ball (by linarith [hρ_pos (wi (idx x₂.1 x₂.2))]) (hidx x₂.1 x₂.2))
      exact (lt_min_iff.mp this).2
    have htri : ‖x₁.1 - x₂.1‖ ≤ ‖Φ x₁ - Φ x₂‖ + ‖Φ x₁ - x₁.1‖ + ‖Φ x₂ - x₂.1‖ := by
      calc ‖x₁.1 - x₂.1‖ = ‖(Φ x₁ - Φ x₂) - (Φ x₁ - x₁.1) + (Φ x₂ - x₂.1)‖ := by ring_nf
        _ ≤ ‖(Φ x₁ - Φ x₂) - (Φ x₁ - x₁.1)‖ + ‖Φ x₂ - x₂.1‖ := norm_add_le _ _
        _ ≤ ‖Φ x₁ - Φ x₂‖ + ‖Φ x₁ - x₁.1‖ + ‖Φ x₂ - x₂.1‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
    have hθ_mul : θ * ρ_min ≤ θ * ‖x₁.1 - x₂.1‖ := mul_le_mul_of_nonneg_left hfar hθ_pos.le
    linarith
  · push Not at hfar
    let i := idx x₁.1 x₁.2
    have hρmin_i : ρ_min ≤ ρ_w (wi i) := hρmin_le i
    have hx₁_1 : x₁.1 ∈ ball (wi i) (ρ_w (wi i)) := hidx x₁.1 x₁.2
    have hx₂_2 : x₂.1 ∈ ball (wi i) (2 * ρ_w (wi i)) := by
      rw [mem_ball, dist_eq_norm] at hx₁_1 ⊢
      calc ‖x₂.1 - wi i‖ = ‖(x₁.1 - wi i) - (x₁.1 - x₂.1)‖ := by ring_nf
        _ ≤ ‖x₁.1 - wi i‖ + ‖x₁.1 - x₂.1‖ := norm_sub_le _ _
        _ < ρ_w (wi i) + ρ_min := add_lt_add hx₁_1 hfar
        _ ≤ 2 * ρ_w (wi i) := by linarith
    have hΦ₂_eq : Φ x₂ = g_w (wi i) (Pz.eval x₂.1) := by
      let j := idx x₂.1 x₂.2
      have hd_a : ‖Φ x₂ - x₂.1‖ < ρ_min / 2 :=
        (lt_min_iff.mp (hlocal_disp j
          (ball_subset_ball (by linarith [hρ_pos (wi j)]) (hidx x₂.1 x₂.2)))).1
      have hd_b : ‖g_w (wi i) (Pz.eval x₂.1) - x₂.1‖ < ρ_min / 2 :=
        (lt_min_iff.mp (hlocal_disp i hx₂_2)).1
      have ha_4 : Φ x₂ ∈ ball (wi i) (4 * ρ_w (wi i)) := by
        rw [mem_ball, dist_eq_norm] at hx₂_2 ⊢
        calc ‖Φ x₂ - wi i‖ = ‖(Φ x₂ - x₂.1) + (x₂.1 - wi i)‖ := by ring_nf
          _ ≤ ‖Φ x₂ - x₂.1‖ + ‖x₂.1 - wi i‖ := norm_add_le _ _
          _ < ρ_min / 2 + 2 * ρ_w (wi i) := add_lt_add hd_a hx₂_2
          _ ≤ 4 * ρ_w (wi i) := by linarith [hρ_pos (wi i)]
      have hb_4 : g_w (wi i) (Pz.eval x₂.1) ∈ ball (wi i) (4 * ρ_w (wi i)) := by
        rw [mem_ball, dist_eq_norm] at hx₂_2 ⊢
        calc ‖g_w (wi i) (Pz.eval x₂.1) - wi i‖ =
            ‖(g_w (wi i) (Pz.eval x₂.1) - x₂.1) + (x₂.1 - wi i)‖ := by ring_nf
          _ ≤ ‖g_w (wi i) (Pz.eval x₂.1) - x₂.1‖ + ‖x₂.1 - wi i‖ := norm_add_le _ _
          _ < ρ_min / 2 + 2 * ρ_w (wi i) := add_lt_add hd_b hx₂_2
          _ ≤ 4 * ρ_w (wi i) := by linarith [hρ_pos (wi i)]
      have hx₂_4 : x₂.1 ∈ ball (wi i) (4 * ρ_w (wi i)) :=
        ball_subset_ball (by linarith [hρ_pos (wi i)]) hx₂_2
      have hx₂_4j : x₂.1 ∈ ball (wi j) (4 * ρ_w (wi j)) :=
        ball_subset_ball (by linarith [hρ_pos (wi j)]) (hidx x₂.1 x₂.2)
      have hP₀_a : P₀.eval (Φ x₂) = Pz.eval x₂.1 :=
        (hchart_spec (wi j) (hwi_K₀ j)).1 (Pz.eval x₂.1) (hlocal_eval_in_ru j hx₂_4j)
      have hP₀_b : P₀.eval (g_w (wi i) (Pz.eval x₂.1)) = Pz.eval x₂.1 :=
        (hchart_spec (wi i) (hwi_K₀ i)).1 (Pz.eval x₂.1) (hlocal_eval_in_ru i hx₂_4)
      have hleft := (hchart_spec (wi i) (hwi_K₀ i)).2.2.1
      calc Φ x₂ = g_w (wi i) (P₀.eval (Φ x₂)) := (hleft (Φ x₂) ha_4).symm
        _ = g_w (wi i) (P₀.eval (g_w (wi i) (Pz.eval x₂.1))) := by rw [hP₀_a, hP₀_b]
        _ = g_w (wi i) (Pz.eval x₂.1) := hleft _ hb_4
    have hx₁_4 : x₁.1 ∈ ball (wi i) (4 * ρ_w (wi i)) :=
      ball_subset_ball (by linarith [hρ_pos (wi i)]) hx₁_1
    have hx₂_4 : x₂.1 ∈ ball (wi i) (4 * ρ_w (wi i)) :=
      ball_subset_ball (by linarith [hρ_pos (wi i)]) hx₂_2
    have hsp := hchart_spec (wi i) (hwi_K₀ i)
    let di := P₀.derivative.eval (wi i)
    have hdi_ne : di ≠ 0 := hK₀_deriv (wi i) (hwi_K₀ i)
    have hdi_pos' : 0 < ‖di‖ := norm_pos_iff.mpr hdi_ne
    have hdmin_le_i : d_min ≤ ‖di‖ := hdmin_le i
    let u₁ := Pz.eval x₁.1
    let u₂ := Pz.eval x₂.1
    let h := x₁.1 - x₂.1
    have hu₁_ru : u₁ ∈ ball (P₀.eval (wi i)) (ru_w (wi i)) := hlocal_eval_in_ru i hx₁_4
    have hu₂_ru : u₂ ∈ ball (P₀.eval (wi i)) (ru_w (wi i)) := hlocal_eval_in_ru i hx₂_4
    have herr_g : ‖g_w (wi i) u₁ - g_w (wi i) u₂ - di⁻¹ * (u₁ - u₂)‖ ≤
        (θ / (4 * ‖di‖)) * ‖u₁ - u₂‖ := hsp.2.1 u₁ hu₁_ru u₂ hu₂_ru
    have herr_P₀ : ‖P₀.eval x₁.1 - P₀.eval x₂.1 - di * h‖ ≤ (θ * ‖di‖ / 4) * ‖h‖ :=
      hsp.2.2.2.2 x₁.1 hx₁_4 x₂.1 hx₂_4
    have herr_Q : ‖(u₁ - P₀.eval x₁.1) - (u₂ - P₀.eval x₂.1)‖ ≤ (θ * ‖di‖ / 8) * ‖h‖ := by
      have h1 := hQz_lip x₁.1 (hball_R1 i hx₁_4) x₂.1 (hball_R1 i hx₂_4)
      have h2 : η_der ≤ θ * ‖di‖ / 8 :=
        hηder_le.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdmin_le_i hθ_pos.le) (by positivity))
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg h))
    have herr_u : ‖u₁ - u₂ - di * h‖ ≤ (3 * θ * ‖di‖ / 8) * ‖h‖ := by
      calc ‖u₁ - u₂ - di * h‖
          = ‖(P₀.eval x₁.1 - P₀.eval x₂.1 - di * h) +
              ((u₁ - P₀.eval x₁.1) - (u₂ - P₀.eval x₂.1))‖ := by ring_nf
        _ ≤ ‖P₀.eval x₁.1 - P₀.eval x₂.1 - di * h‖ +
              ‖(u₁ - P₀.eval x₁.1) - (u₂ - P₀.eval x₂.1)‖ := norm_add_le _ _
        _ ≤ (θ * ‖di‖ / 4) * ‖h‖ + (θ * ‖di‖ / 8) * ‖h‖ := add_le_add herr_P₀ herr_Q
        _ = (3 * θ * ‖di‖ / 8) * ‖h‖ := by ring
    have hu_norm : ‖u₁ - u₂‖ ≤ 2 * ‖di‖ * ‖h‖ := by
      have hcoef : 3 * θ / 8 + 1 ≤ 2 := by linarith [hθ_lt_one]
      calc ‖u₁ - u₂‖ = ‖(u₁ - u₂ - di * h) + di * h‖ := by ring_nf
        _ ≤ ‖u₁ - u₂ - di * h‖ + ‖di * h‖ := norm_add_le _ _
        _ ≤ (3 * θ * ‖di‖ / 8) * ‖h‖ + ‖di‖ * ‖h‖ := by rw [norm_mul]; linarith
        _ = (3 * θ / 8 + 1) * (‖di‖ * ‖h‖) := by ring
        _ ≤ 2 * (‖di‖ * ‖h‖) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg hdi_pos'.le (norm_nonneg h))
        _ = 2 * ‖di‖ * ‖h‖ := by ring
    have herr_dinv : ‖di⁻¹ * (u₁ - u₂) - h‖ ≤ (3 * θ / 8) * ‖h‖ := by
      have hid : di⁻¹ * (u₁ - u₂) - h = di⁻¹ * (u₁ - u₂ - di * h) := by
        calc di⁻¹ * (u₁ - u₂) - h = di⁻¹ * (u₁ - u₂) - (di⁻¹ * di) * h := by
              rw [inv_mul_cancel₀ hdi_ne, one_mul]
          _ = di⁻¹ * (u₁ - u₂ - di * h) := by ring
      rw [hid, norm_mul, norm_inv]
      calc ‖di‖⁻¹ * ‖u₁ - u₂ - di * h‖
          ≤ ‖di‖⁻¹ * ((3 * θ * ‖di‖ / 8) * ‖h‖) :=
            mul_le_mul_of_nonneg_left herr_u (by positivity)
        _ = (3 * θ / 8) * ‖h‖ := by
            calc ‖di‖⁻¹ * ((3 * θ * ‖di‖ / 8) * ‖h‖)
                = (3 * θ / 8) * ‖h‖ * (‖di‖⁻¹ * ‖di‖) := by ring
              _ = (3 * θ / 8) * ‖h‖ := by rw [inv_mul_cancel₀ hdi_pos'.ne', mul_one]
    have herr_g' : ‖g_w (wi i) u₁ - g_w (wi i) u₂ - di⁻¹ * (u₁ - u₂)‖ ≤ (θ / 2) * ‖h‖ := by
      calc ‖g_w (wi i) u₁ - g_w (wi i) u₂ - di⁻¹ * (u₁ - u₂)‖
          ≤ (θ / (4 * ‖di‖)) * ‖u₁ - u₂‖ := herr_g
        _ ≤ (θ / (4 * ‖di‖)) * (2 * ‖di‖ * ‖h‖) :=
            mul_le_mul_of_nonneg_left hu_norm (by positivity)
        _ = (θ / 2) * ‖h‖ := by
            calc (θ / (4 * ‖di‖)) * (2 * ‖di‖ * ‖h‖)
                = (θ / 2) * ‖h‖ * (‖di‖ / ‖di‖) := by ring
              _ = (θ / 2) * ‖h‖ := by rw [div_self hdi_pos'.ne', mul_one]
    have htot : ‖(Φ x₁ - Φ x₂) - h‖ ≤ θ * ‖h‖ := by
      have hΦ₁_eq : Φ x₁ = g_w (wi i) u₁ := rfl
      rw [hΦ₁_eq, hΦ₂_eq]
      calc ‖(g_w (wi i) u₁ - g_w (wi i) u₂) - h‖
          = ‖(g_w (wi i) u₁ - g_w (wi i) u₂ - di⁻¹ * (u₁ - u₂)) +
              (di⁻¹ * (u₁ - u₂) - h)‖ := by ring_nf
        _ ≤ ‖g_w (wi i) u₁ - g_w (wi i) u₂ - di⁻¹ * (u₁ - u₂)‖ +
              ‖di⁻¹ * (u₁ - u₂) - h‖ := norm_add_le _ _
        _ ≤ (θ / 2) * ‖h‖ + (3 * θ / 8) * ‖h‖ := add_le_add herr_g' herr_dinv
        _ = (7 / 8 : ℝ) * (θ * ‖h‖) := by ring
        _ ≤ 1 * (θ * ‖h‖) :=
            mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hθ_pos.le (norm_nonneg h))
        _ = θ * ‖h‖ := one_mul _
    have hrev : ‖h‖ - ‖(Φ x₁ - Φ x₂) - h‖ ≤ ‖Φ x₁ - Φ x₂‖ := by
      have h1 := norm_sub_norm_le h (h - (Φ x₁ - Φ x₂))
      rw [norm_sub_rev h (Φ x₁ - Φ x₂), sub_sub_cancel] at h1
      exact h1
    linarith

lemma nonempty_branch_bound {n : ℕ} (hn : 0 < n) (z₀ : Fin n → ℂ) (P₀ : ℂ[X])
    (hP₀_def : P₀ = polyOfRoots z₀) {R₀ L₀ ε δ θ m_far : ℝ}
    (hR₀_pos : 0 < R₀) (hR₀_eq : R₀ = 2 + ∑ i : Fin n, ‖z₀ i‖)
    (hL₀_nonneg : 0 ≤ L₀) (hL₀_ofReal : ENNReal.ofReal L₀ = lemniscateLength P₀)
    (hL₀_sub : lemniscate P₀ ⊆ closedBall (0 : ℂ) R₀)
    (hε_pos : 0 < ε) (hδ_pos : 0 < δ) (hδ_eq : δ = ε / (4 * (L₀ + 1)))
    (hθ_pos : 0 < θ) (hθ_lt_one : θ < 1) (hθ_inv : (1 + δ) * (1 - θ) = 1)
    (hmfar_pos : 0 < m_far)
    {K₀ V_crit B_crit : Set ℂ}
    (hK₀_lem : K₀ ⊆ lemniscate P₀)
    (hK₀_deriv : ∀ w ∈ K₀, P₀.derivative.eval w ≠ 0)
    (hB_crit_bound : ∀ z : Fin n → ℂ, μH[1] (lemniscate (polyOfRoots z) ∩ B_crit) ≤ ENNReal.ofReal (ε / 2))
    (hVB : V_crit ⊆ B_crit)
    {g_w : ℂ → ℂ → ℂ} {ρ_w ru_w : ℂ → ℝ}
    (hρ_pos : ∀ w, 0 < ρ_w w) (hρ_le : ∀ w, ρ_w w ≤ 1 / 4) (hru_pos : ∀ w, 0 < ru_w w)
    (hchart_spec : ∀ w ∈ K₀,
      (∀ u ∈ ball (P₀.eval w) (ru_w w), P₀.eval (g_w w u) = u) ∧
      (∀ u₁ ∈ ball (P₀.eval w) (ru_w w), ∀ u₂ ∈ ball (P₀.eval w) (ru_w w),
        ‖g_w w u₁ - g_w w u₂ - (P₀.derivative.eval w)⁻¹ * (u₁ - u₂)‖ ≤
          (θ / (4 * ‖P₀.derivative.eval w‖)) * ‖u₁ - u₂‖) ∧
      (∀ ζ ∈ ball w (4 * ρ_w w), g_w w (P₀.eval ζ) = ζ) ∧
      (∀ ζ ∈ ball w (4 * ρ_w w), P₀.eval ζ ∈ ball (P₀.eval w) (ru_w w / 2)) ∧
      (∀ ζ₁ ∈ ball w (4 * ρ_w w), ∀ ζ₂ ∈ ball w (4 * ρ_w w),
        ‖P₀.eval ζ₁ - P₀.eval ζ₂ - P₀.derivative.eval w * (ζ₁ - ζ₂)‖ ≤
          (θ * ‖P₀.derivative.eval w‖ / 4) * ‖ζ₁ - ζ₂‖))
    {M : ℕ} (hM : Nonempty (Fin M)) (wi : Fin M → ℂ) (hwi_K₀ : ∀ i, wi i ∈ K₀)
    (hmfar_bd_W : ∀ ζ ∈ closedBall (0 : ℂ) R₀, ζ ∉ V_crit →
      (∀ i : Fin M, ζ ∉ ball (wi i) (ρ_w (wi i))) → m_far ≤ |‖P₀.eval ζ‖ - 1|) :
    ∀ᶠ z in 𝓝 z₀, lemniscateLength (polyOfRoots z) ≤ ENNReal.ofReal (L₀ + ε) := by
  classical
  have hUniv_ne : (Finset.univ : Finset (Fin M)).Nonempty := Finset.univ_nonempty
  have hwi_ball : ∀ i, wi i ∈ closedBall (0 : ℂ) R₀ := fun i => hL₀_sub (hK₀_lem (hwi_K₀ i))
  have hdi_pos : ∀ i, 0 < ‖P₀.derivative.eval (wi i)‖ :=
    fun i => norm_pos_iff.mpr (hK₀_deriv (wi i) (hwi_K₀ i))
  have hex_bounds : ∃ ρ_min ru_min d_min L_max : ℝ,
      0 < ρ_min ∧ 0 < ru_min ∧ 0 < d_min ∧ 0 < L_max ∧
      (∀ i : Fin M, ρ_min ≤ ρ_w (wi i)) ∧
      (∀ i : Fin M, ru_min ≤ ru_w (wi i) / 2) ∧
      (∀ i : Fin M, d_min ≤ ‖P₀.derivative.eval (wi i)‖) ∧
      (∀ i : Fin M, 2 * ‖(P₀.derivative.eval (wi i))⁻¹‖ + 1 ≤ L_max) := by
    let s_ρ := Finset.univ.image (fun i : Fin M => ρ_w (wi i))
    let ρ_min : ℝ := s_ρ.min' (hUniv_ne.image _)
    have hρmin_pos : 0 < ρ_min := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem s_ρ (hUniv_ne.image _))
      dsimp [ρ_min]; rw [← hi]; exact hρ_pos (wi i)
    let s_ru := Finset.univ.image (fun i : Fin M => ru_w (wi i) / 2)
    let ru_min : ℝ := s_ru.min' (hUniv_ne.image _)
    have hrumin_pos : 0 < ru_min := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem s_ru (hUniv_ne.image _))
      dsimp [ru_min]; rw [← hi]; have := hru_pos (wi i); positivity
    let s_d := Finset.univ.image (fun i : Fin M => ‖P₀.derivative.eval (wi i)‖)
    let d_min : ℝ := s_d.min' (hUniv_ne.image _)
    have hdmin_pos : 0 < d_min := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem s_d (hUniv_ne.image _))
      dsimp [d_min]; rw [← hi]; exact hdi_pos i
    let s_L := Finset.univ.image (fun i : Fin M => 2 * ‖(P₀.derivative.eval (wi i))⁻¹‖ + 1)
    let L_max' : ℝ := s_L.max' (hUniv_ne.image _)
    have hLmax_pos : 0 < L_max' := by
      have hle : 2 * ‖(P₀.derivative.eval (wi hM.some))⁻¹‖ + 1 ≤ L_max' :=
        Finset.le_max' s_L _ (Finset.mem_image.mpr ⟨hM.some, Finset.mem_univ _, rfl⟩)
      have : 0 ≤ 2 * ‖(P₀.derivative.eval (wi hM.some))⁻¹‖ := by positivity
      linarith
    refine ⟨ρ_min, ru_min, d_min, L_max', hρmin_pos, hrumin_pos, hdmin_pos, hLmax_pos, ?_, ?_, ?_, ?_⟩
    · intro i; exact Finset.min'_le s_ρ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · intro i; exact Finset.min'_le s_ru _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · intro i; exact Finset.min'_le s_d _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · intro i; exact Finset.le_max' s_L _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  obtain ⟨ρ_min, ru_min, d_min, L_max, hρmin_pos, hrumin_pos, hdmin_pos, hLmax_pos,
    hρmin_le, hrumin_le, hdmin_le, hLmax_le⟩ := hex_bounds
  let η_val : ℝ := min m_far (min ru_min (min (ρ_min / (2 * L_max)) ((θ * ρ_min) / (2 * L_max))))
  have hηval_pos : 0 < η_val :=
    lt_min hmfar_pos (lt_min hrumin_pos (lt_min (by positivity) (by positivity)))
  let η_der : ℝ := θ * d_min / 8
  have hηder_pos : 0 < η_der := by positivity
  let η_all : ℝ := min η_val η_der
  have hηall_pos : 0 < η_all := lt_min hηval_pos hηder_pos
  obtain ⟨δ_u, hδu_pos, hδu⟩ :=
    uniform_close_polyOfRoots z₀ (show 0 ≤ R₀ + 1 by positivity) hηall_pos
  refine Metric.eventually_nhds_iff.mpr ⟨min (1 / 2) δ_u, lt_min (by positivity) hδu_pos, ?_⟩
  intro z hz
  have hz_half : dist z z₀ < 1 := lt_of_lt_of_le hz (by linarith [min_le_left (1 / 2 : ℝ) δ_u])
  have hz_u : dist z z₀ < δ_u := lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨hval_bd', hder_bd'⟩ := hδu z hz_u
  have hval_bd : ∀ ζ ∈ closedBall (0 : ℂ) (R₀ + 1), ‖(polyOfRoots z).eval ζ - P₀.eval ζ‖ < η_all := by
    rw [hP₀_def]; exact hval_bd'
  have hder_bd : ∀ ζ ∈ closedBall (0 : ℂ) (R₀ + 1),
      ‖(polyOfRoots z).derivative.eval ζ - P₀.derivative.eval ζ‖ < η_all := by
    rw [hP₀_def]; exact hder_bd'
  let Pz := polyOfRoots z
  let Az : Set ℂ := lemniscate Pz \ B_crit
  have hPz_sub : lemniscate Pz ⊆ closedBall (0 : ℂ) R₀ := by
    rw [hR₀_eq]
    exact lemniscate_subset_closedBall hn z₀ z hz_half
  have hAz_W : ∀ ζ ∈ Az, ∃ i : Fin M, ζ ∈ ball (wi i) (ρ_w (wi i)) := by
    intro ζ ⟨hζL, hζB⟩
    have hζR₀ : ζ ∈ closedBall (0 : ℂ) R₀ := hPz_sub hζL
    have hζR1 : ζ ∈ closedBall (0 : ℂ) (R₀ + 1) :=
      closedBall_subset_closedBall (by linarith) hζR₀
    have hζ_not_V : ζ ∉ V_crit := fun hV => hζB (hVB hV)
    by_contra hnotW
    push Not at hnotW
    have h1 := hmfar_bd_W ζ hζR₀ hζ_not_V hnotW
    have h2 : |‖P₀.eval ζ‖ - 1| ≤ ‖Pz.eval ζ - P₀.eval ζ‖ := by
      have hn1 : ‖Pz.eval ζ‖ = 1 := hζL
      calc |‖P₀.eval ζ‖ - 1| = |‖P₀.eval ζ‖ - ‖Pz.eval ζ‖| := by rw [hn1]
        _ ≤ ‖P₀.eval ζ - Pz.eval ζ‖ := abs_norm_sub_norm_le _ _
        _ = ‖Pz.eval ζ - P₀.eval ζ‖ := norm_sub_rev _ _
    have h3 : ‖Pz.eval ζ - P₀.eval ζ‖ < m_far :=
      lt_of_lt_of_le (hval_bd ζ hζR1) ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  choose idx hidx using hAz_W
  let Φ : Az → ℂ := fun x => g_w (wi (idx x.1 x.2)) (Pz.eval x.1)
  have hball_R1 : ∀ (i : Fin M) {ζ : ℂ}, ζ ∈ ball (wi i) (4 * ρ_w (wi i)) →
      ζ ∈ closedBall (0 : ℂ) (R₀ + 1) := by
    intro i ζ hζ
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖ζ - wi i‖ < 4 * ρ_w (wi i) := mem_ball_iff_norm.mp hζ
    have h2 : ρ_w (wi i) ≤ 1 / 4 := hρ_le (wi i)
    have h3 : ‖wi i‖ ≤ R₀ := by simpa [mem_closedBall, dist_zero_right] using hwi_ball i
    have h4 : ‖ζ‖ ≤ ‖wi i‖ + ‖ζ - wi i‖ := by
      calc ‖ζ‖ = ‖wi i + (ζ - wi i)‖ := by ring_nf
        _ ≤ ‖wi i‖ + ‖ζ - wi i‖ := norm_add_le _ _
    linarith
  have hlocal_eval_in_ru : ∀ (i : Fin M) {ζ : ℂ}, ζ ∈ ball (wi i) (4 * ρ_w (wi i)) →
      Pz.eval ζ ∈ ball (P₀.eval (wi i)) (ru_w (wi i)) := by
    intro i ζ hζ
    have hsp := hchart_spec (wi i) (hwi_K₀ i)
    have hP₀_in : P₀.eval ζ ∈ ball (P₀.eval (wi i)) (ru_w (wi i) / 2) := hsp.2.2.2.1 ζ hζ
    have hdiff : ‖Pz.eval ζ - P₀.eval ζ‖ < ru_w (wi i) / 2 := by
      have h1 := hval_bd ζ (hball_R1 i hζ)
      have h2 : η_all ≤ ru_min :=
        (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have h3 : ru_min ≤ ru_w (wi i) / 2 := hrumin_le i
      linarith
    rw [mem_ball, dist_eq_norm] at hP₀_in ⊢
    calc ‖Pz.eval ζ - P₀.eval (wi i)‖
        = ‖(Pz.eval ζ - P₀.eval ζ) + (P₀.eval ζ - P₀.eval (wi i))‖ := by ring_nf
      _ ≤ ‖Pz.eval ζ - P₀.eval ζ‖ + ‖P₀.eval ζ - P₀.eval (wi i)‖ := norm_add_le _ _
      _ < ru_w (wi i) / 2 + ru_w (wi i) / 2 := add_lt_add hdiff hP₀_in
      _ = ru_w (wi i) := by ring
  have hlocal_disp : ∀ (i : Fin M) {ζ : ℂ}, ζ ∈ ball (wi i) (2 * ρ_w (wi i)) →
      ‖g_w (wi i) (Pz.eval ζ) - ζ‖ < min (ρ_min / 2) (θ * ρ_min / 2) := by
    intro i ζ hζ2
    have hζ4 : ζ ∈ ball (wi i) (4 * ρ_w (wi i)) :=
      ball_subset_ball (by linarith [hρ_pos (wi i)]) hζ2
    have hsp := hchart_spec (wi i) (hwi_K₀ i)
    have hu₁ : Pz.eval ζ ∈ ball (P₀.eval (wi i)) (ru_w (wi i)) := hlocal_eval_in_ru i hζ4
    have hu₂ : P₀.eval ζ ∈ ball (P₀.eval (wi i)) (ru_w (wi i)) :=
      ball_subset_ball (by linarith [hru_pos (wi i)]) (hsp.2.2.2.1 ζ hζ4)
    have hg_id : g_w (wi i) (P₀.eval ζ) = ζ := hsp.2.2.1 ζ hζ4
    have hg_lin := hsp.2.1 (Pz.eval ζ) hu₁ (P₀.eval ζ) hu₂
    rw [hg_id] at hg_lin
    let di := P₀.derivative.eval (wi i)
    have hlip_g : ‖g_w (wi i) (Pz.eval ζ) - ζ‖ ≤ L_max * ‖Pz.eval ζ - P₀.eval ζ‖ := by
      have htri : ‖g_w (wi i) (Pz.eval ζ) - ζ‖ ≤
          ‖g_w (wi i) (Pz.eval ζ) - ζ - di⁻¹ * (Pz.eval ζ - P₀.eval ζ)‖ +
            ‖di⁻¹ * (Pz.eval ζ - P₀.eval ζ)‖ := by
        calc ‖g_w (wi i) (Pz.eval ζ) - ζ‖ =
            ‖(g_w (wi i) (Pz.eval ζ) - ζ - di⁻¹ * (Pz.eval ζ - P₀.eval ζ)) +
              di⁻¹ * (Pz.eval ζ - P₀.eval ζ)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [norm_mul] at htri
      have hcoef : θ / (4 * ‖di‖) + ‖di⁻¹‖ ≤ L_max := by
        have hinv : (‖di‖)⁻¹ = ‖di⁻¹‖ := (norm_inv di).symm
        have h1 : θ / (4 * ‖di‖) = (θ / 4) * ‖di⁻¹‖ := by rw [← hinv]; ring
        have h2_mul : (θ / 4) * ‖di⁻¹‖ ≤ 1 * ‖di⁻¹‖ :=
          mul_le_mul_of_nonneg_right (by linarith [hθ_lt_one]) (norm_nonneg _)
        have h3 : 2 * ‖di⁻¹‖ + 1 ≤ L_max := hLmax_le i
        linarith
      calc ‖g_w (wi i) (Pz.eval ζ) - ζ‖
          ≤ ‖g_w (wi i) (Pz.eval ζ) - ζ - di⁻¹ * (Pz.eval ζ - P₀.eval ζ)‖ +
              ‖di⁻¹‖ * ‖Pz.eval ζ - P₀.eval ζ‖ := htri
        _ ≤ (θ / (4 * ‖di‖)) * ‖Pz.eval ζ - P₀.eval ζ‖ + ‖di⁻¹‖ * ‖Pz.eval ζ - P₀.eval ζ‖ :=
            add_le_add hg_lin le_rfl
        _ = (θ / (4 * ‖di‖) + ‖di⁻¹‖) * ‖Pz.eval ζ - P₀.eval ζ‖ := by ring
        _ ≤ L_max * ‖Pz.eval ζ - P₀.eval ζ‖ :=
            mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    have hval_lt : ‖Pz.eval ζ - P₀.eval ζ‖ <
        min (ρ_min / (2 * L_max)) ((θ * ρ_min) / (2 * L_max)) :=
      lt_of_lt_of_le (hval_bd ζ (hball_R1 i hζ4))
        ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [lt_min_iff] at hval_lt ⊢
    constructor
    · have h1 : L_max * (ρ_min / (2 * L_max)) = ρ_min / 2 := by
        calc L_max * (ρ_min / (2 * L_max)) = (ρ_min / 2) * (L_max / L_max) := by ring
          _ = ρ_min / 2 := by rw [div_self hLmax_pos.ne', mul_one]
      calc ‖g_w (wi i) (Pz.eval ζ) - ζ‖
          ≤ L_max * ‖Pz.eval ζ - P₀.eval ζ‖ := hlip_g
        _ < L_max * (ρ_min / (2 * L_max)) := mul_lt_mul_of_pos_left hval_lt.1 hLmax_pos
        _ = ρ_min / 2 := h1
    · have h1 : L_max * ((θ * ρ_min) / (2 * L_max)) = θ * ρ_min / 2 := by
        calc L_max * ((θ * ρ_min) / (2 * L_max)) = (θ * ρ_min / 2) * (L_max / L_max) := by ring
          _ = θ * ρ_min / 2 := by rw [div_self hLmax_pos.ne', mul_one]
      calc ‖g_w (wi i) (Pz.eval ζ) - ζ‖
          ≤ L_max * ‖Pz.eval ζ - P₀.eval ζ‖ := hlip_g
        _ < L_max * ((θ * ρ_min) / (2 * L_max)) := mul_lt_mul_of_pos_left hval_lt.2 hLmax_pos
        _ = θ * ρ_min / 2 := h1
  have hΦ_lem : ∀ x : Az, Φ x ∈ lemniscate P₀ := by
    intro x
    let i := idx x.1 x.2
    have hx4 : x.1 ∈ ball (wi i) (4 * ρ_w (wi i)) :=
      ball_subset_ball (by linarith [hρ_pos (wi i)]) (hidx x.1 x.2)
    have heval : P₀.eval (Φ x) = Pz.eval x.1 :=
      (hchart_spec (wi i) (hwi_K₀ i)).1 (Pz.eval x.1) (hlocal_eval_in_ru i hx4)
    change ‖P₀.eval (Φ x)‖ = 1
    rw [heval]
    exact x.2.1
  have hQz_lip : ∀ ζ₁ ∈ closedBall (0 : ℂ) (R₀ + 1), ∀ ζ₂ ∈ closedBall (0 : ℂ) (R₀ + 1),
      ‖(Pz.eval ζ₁ - P₀.eval ζ₁) - (Pz.eval ζ₂ - P₀.eval ζ₂)‖ ≤ η_der * ‖ζ₁ - ζ₂‖ :=
    eval_diff_lip_on_closedBall P₀ Pz fun w hw =>
      (lt_of_lt_of_le (hder_bd w hw) (min_le_right _ _)).le
  have hΦ_anti := phi_antilipschitz P₀ Pz hδ_pos hθ_pos hθ_lt_one hθ_inv wi g_w ρ_w ru_w
    hwi_K₀ hK₀_deriv hρ_pos hρmin_le hdmin_le le_rfl hchart_spec hball_R1 hlocal_eval_in_ru
    hlocal_disp hQz_lip idx hidx
  have hAz_meas : μH[1] Az ≤ ENNReal.ofReal (L₀ + ε / 2) := by
    have hiso : Isometry (Subtype.val : Az → ℂ) := isometry_subtype_coe
    have h1 : μH[1] Az = μH[1] (univ : Set Az) := by
      simpa only [Set.image_univ, Subtype.range_coe] using
        hiso.hausdorffMeasure_image (Or.inl (zero_le_one' ℝ)) (univ : Set Az)
    have h2 := hΦ_anti.le_hausdorffMeasure_image (d := 1) zero_le_one (univ : Set Az)
    have h3 : Φ '' (univ : Set Az) ⊆ lemniscate P₀ := by
      rintro _ ⟨x, _, rfl⟩; exact hΦ_lem x
    let c_lip : ℝ≥0 := ⟨1 + δ, by positivity⟩
    have h2' : μH[1] (univ : Set Az) ≤ (c_lip : ℝ≥0∞) ^ (1 : ℝ) * μH[1] (Φ '' (univ : Set Az)) := h2
    have h4 : (c_lip : ℝ≥0∞) ^ (1 : ℝ) = ENNReal.ofReal (1 + δ) := by
      rw [ENNReal.rpow_one, ENNReal.coe_nnreal_eq c_lip]
      rfl
    calc μH[1] Az
        ≤ ENNReal.ofReal (1 + δ) * μH[1] (Φ '' (univ : Set Az)) := by rw [h1, ← h4]; exact h2'
      _ ≤ ENNReal.ofReal (1 + δ) * lemniscateLength P₀ :=
          mul_le_mul_of_nonneg_left (measure_mono h3) (by positivity)
      _ = ENNReal.ofReal ((1 + δ) * L₀) := by
          rw [← hL₀_ofReal, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (L₀ + ε / 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hδL : δ * (L₀ + 1) = ε / 4 := by
            have hL1 : L₀ + 1 ≠ 0 := by positivity
            rw [hδ_eq]
            calc (ε / (4 * (L₀ + 1))) * (L₀ + 1)
                = (ε / 4) / (L₀ + 1) * (L₀ + 1) := by rw [div_mul_eq_div_div]
              _ = ε / 4 := div_mul_cancel₀ _ hL1
          have hδL₀ : δ * L₀ ≤ δ * (L₀ + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ_pos.le
          linarith [hδL, hε_pos]
  have hsplit : lemniscate Pz ⊆ Az ∪ (lemniscate Pz ∩ B_crit) := by
    intro ζ hζ
    by_cases hB : ζ ∈ B_crit
    · exact Or.inr ⟨hζ, hB⟩
    · exact Or.inl ⟨hζ, hB⟩
  calc lemniscateLength Pz
      ≤ μH[1] (Az ∪ (lemniscate Pz ∩ B_crit)) := measure_mono hsplit
    _ ≤ μH[1] Az + μH[1] (lemniscate Pz ∩ B_crit) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (L₀ + ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add hAz_meas (hB_crit_bound z)
    _ = ENNReal.ofReal (L₀ + ε) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end Erdos114H1Aux

theorem OMA.solution : OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1.H1 := by
  classical
  intro n hn z₀ y hy
  let P₀ := Erdos114H1Aux.polyOfRoots z₀
  have hP₀_deg : P₀.natDegree = n := Erdos114H1Aux.natDegree_polyOfRoots z₀
  have hP₀_pos : 0 < P₀.natDegree := hP₀_deg.symm ▸ hn
  let R₀ : ℝ := 2 + ∑ i : Fin n, ‖z₀ i‖
  have hR₀_pos : 0 < R₀ := by
    have : 0 ≤ ∑ i : Fin n, ‖z₀ i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  have hL₀_sub : lemniscate P₀ ⊆ closedBall (0 : ℂ) R₀ :=
    Erdos114H1Aux.lemniscate_subset_closedBall hn z₀ z₀ (by simp)
  have hL₀_top : lemniscateLength P₀ < ⊤ := by
    have heq : lemniscate P₀ = lemniscate P₀ ∩ closedBall (0 : ℂ) R₀ :=
      (inter_eq_left.mpr hL₀_sub).symm
    calc lemniscateLength P₀ = μH[1] (lemniscate P₀ ∩ closedBall (0 : ℂ) R₀) := by
          rw [lemniscateLength, ← heq]
      _ ≤ ENNReal.ofReal (16 * P₀.natDegree * R₀) := Erdos114H1Aux.disk_bound hP₀_pos 0 hR₀_pos
      _ < ⊤ := ENNReal.ofReal_lt_top
  let L₀ : ℝ := (lemniscateLength P₀).toReal
  have hL₀_nonneg : 0 ≤ L₀ := ENNReal.toReal_nonneg
  have hL₀_ofReal : ENNReal.ofReal L₀ = lemniscateLength P₀ := ENNReal.ofReal_toReal hL₀_top.ne
  have hex_ε : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal (L₀ + ε) < y := by
    by_cases hy_top : y = ⊤
    · exact ⟨1, zero_lt_one, hy_top ▸ ENNReal.ofReal_lt_top⟩
    · have hlt : L₀ < y.toReal :=
        (ENNReal.toReal_lt_toReal hL₀_top.ne hy_top).mpr hy
      have hε_sub : 0 < (y.toReal - L₀) / 2 := by linarith
      refine ⟨(y.toReal - L₀) / 2, hε_sub, ?_⟩
      calc ENNReal.ofReal (L₀ + (y.toReal - L₀) / 2)
          < ENNReal.ofReal y.toReal :=
            (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hL₀_nonneg hlt)).mpr (by linarith)
        _ = y := ENNReal.ofReal_toReal hy_top
  obtain ⟨ε, hε_pos, hε_lt⟩ := hex_ε
  have hP₀_ne : P₀ ≠ 0 := fun h => by rw [h, natDegree_zero] at hP₀_pos; omega
  have hderiv_ne : P₀.derivative ≠ 0 := by
    intro hd
    have hc := congrArg (fun f : ℂ[X] => f.coeff (P₀.natDegree - 1)) hd
    rw [coeff_zero, coeff_derivative, Nat.sub_add_cancel hP₀_pos] at hc
    have hcast : ((P₀.natDegree - 1 : ℕ) : ℂ) + 1 = (P₀.natDegree : ℂ) := by
      exact_mod_cast Nat.sub_add_cancel hP₀_pos
    rw [hcast] at hc
    exact mul_ne_zero (P₀.leadingCoeff_ne_zero.mpr hP₀_ne)
      (Nat.cast_ne_zero.mpr hP₀_pos.ne') hc
  obtain ⟨Crit₀, hCrit₀⟩ : ∃ Crit₀ : Finset ℂ, Crit₀ = P₀.derivative.roots.toFinset := ⟨_, rfl⟩
  obtain ⟨r_c, hr_c⟩ : ∃ r_c : ℝ, r_c = ε / (64 * (n : ℝ) * (Crit₀.card + 1 : ℝ)) := ⟨_, rfl⟩
  have hn_pos_R : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrc_pos : 0 < r_c := by rw [hr_c]; positivity
  let U_crit : Set ℂ := ⋃ c ∈ Crit₀, ball c r_c
  let V_crit : Set ℂ := ⋃ c ∈ Crit₀, ball c (2 * r_c)
  let B_crit : Set ℂ := ⋃ c ∈ Crit₀, closedBall c (2 * r_c)
  have hU_open : IsOpen U_crit := isOpen_biUnion fun _ _ => isOpen_ball
  have hV_open : IsOpen V_crit := isOpen_biUnion fun _ _ => isOpen_ball
  have hB_crit_bound : ∀ z : Fin n → ℂ,
      μH[1] (lemniscate (Erdos114H1Aux.polyOfRoots z) ∩ B_crit) ≤ ENNReal.ofReal (ε / 2) := by
    intro z
    let Pz := Erdos114H1Aux.polyOfRoots z
    have hPz_deg : Pz.natDegree = n := Erdos114H1Aux.natDegree_polyOfRoots z
    have hPz_pos : 0 < Pz.natDegree := hPz_deg.symm ▸ hn
    have hsub : lemniscate Pz ∩ B_crit ⊆ ⋃ c ∈ Crit₀, (lemniscate Pz ∩ closedBall c (2 * r_c)) := by
      intro ζ ⟨hζL, hζB⟩
      obtain ⟨c, hc, hζc⟩ := mem_iUnion₂.mp hζB
      exact mem_iUnion₂.mpr ⟨c, hc, hζL, hζc⟩
    calc μH[1] (lemniscate Pz ∩ B_crit)
        ≤ μH[1] (⋃ c ∈ Crit₀, (lemniscate Pz ∩ closedBall c (2 * r_c))) := measure_mono hsub
      _ ≤ ∑ c ∈ Crit₀, μH[1] (lemniscate Pz ∩ closedBall c (2 * r_c)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _ ∈ Crit₀, ENNReal.ofReal (16 * Pz.natDegree * (2 * r_c)) :=
          Finset.sum_le_sum fun c _ => Erdos114H1Aux.disk_bound hPz_pos c (by positivity)
      _ = ENNReal.ofReal ((Crit₀.card : ℝ) * (32 * (n : ℝ) * r_c)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, hPz_deg,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (ε / 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hcard_le : (Crit₀.card : ℝ) ≤ (Crit₀.card + 1 : ℝ) := by linarith
          have h1 : (Crit₀.card + 1 : ℝ) * (32 * (n : ℝ) * r_c) = ε / 2 := by
            rw [hr_c]
            calc (Crit₀.card + 1 : ℝ) * (32 * (n : ℝ) * (ε / (64 * (n : ℝ) * (Crit₀.card + 1 : ℝ))))
                = (ε / 2) * ((64 * (n : ℝ) * (Crit₀.card + 1 : ℝ)) /
                    (64 * (n : ℝ) * (Crit₀.card + 1 : ℝ))) := by ring
              _ = ε / 2 := by rw [div_self (by positivity), mul_one]
          nlinarith
  obtain ⟨δ, hδ_eq⟩ : ∃ δ : ℝ, δ = ε / (4 * (L₀ + 1)) := ⟨_, rfl⟩
  have hδ_pos : 0 < δ := by rw [hδ_eq]; positivity
  obtain ⟨θ, hθ_eq⟩ : ∃ θ : ℝ, θ = δ / (1 + δ) := ⟨_, rfl⟩
  have hθ_pos : 0 < θ := by rw [hθ_eq]; positivity
  have hθ_lt_one : θ < 1 := by
    rw [hθ_eq, div_lt_one (by positivity)]; linarith
  have hθ_inv : (1 + δ) * (1 - θ) = 1 := by
    have h1d : (1 + δ) ≠ 0 := by positivity
    calc (1 + δ) * (1 - θ) = (1 + δ) - ((1 + δ) / (1 + δ)) * δ := by rw [hθ_eq]; ring
      _ = 1 := by rw [div_self h1d]; ring
  let K₀ : Set ℂ := lemniscate P₀ \ U_crit
  have hK₀_compact : IsCompact K₀ :=
    ((isCompact_closedBall (0 : ℂ) R₀).of_isClosed_subset
      (isClosed_eq P₀.continuous.norm continuous_const) hL₀_sub).diff hU_open
  have hK₀_deriv : ∀ w ∈ K₀, P₀.derivative.eval w ≠ 0 := by
    intro w ⟨_, hwU⟩ hd0
    have hwC : w ∈ Crit₀ := by
      rw [hCrit₀, Multiset.mem_toFinset, mem_roots hderiv_ne]; exact hd0
    exact hwU (mem_iUnion₂.mpr ⟨w, hwC, mem_ball_self hrc_pos⟩)
  have hchart : ∀ w : ℂ, ∃ (g : ℂ → ℂ) (ρ r_u : ℝ),
      0 < ρ ∧ ρ ≤ 1 / 4 ∧ 0 < r_u ∧
      (w ∈ K₀ →
        (∀ u ∈ ball (P₀.eval w) r_u, P₀.eval (g u) = u) ∧
        (∀ u₁ ∈ ball (P₀.eval w) r_u, ∀ u₂ ∈ ball (P₀.eval w) r_u,
          ‖g u₁ - g u₂ - (P₀.derivative.eval w)⁻¹ * (u₁ - u₂)‖ ≤
            (θ / (4 * ‖P₀.derivative.eval w‖)) * ‖u₁ - u₂‖) ∧
        (∀ ζ ∈ ball w (4 * ρ), g (P₀.eval ζ) = ζ) ∧
        (∀ ζ ∈ ball w (4 * ρ), P₀.eval ζ ∈ ball (P₀.eval w) (r_u / 2)) ∧
        (∀ ζ₁ ∈ ball w (4 * ρ), ∀ ζ₂ ∈ ball w (4 * ρ),
          ‖P₀.eval ζ₁ - P₀.eval ζ₂ - P₀.derivative.eval w * (ζ₁ - ζ₂)‖ ≤
            (θ * ‖P₀.derivative.eval w‖ / 4) * ‖ζ₁ - ζ₂‖)) := by
    intro w
    by_cases hw : w ∈ K₀
    · obtain ⟨g, ρ, r_u, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        Erdos114H1Aux.local_chart_data P₀ w (hK₀_deriv w hw) hθ_pos
      exact ⟨g, ρ, r_u, h1, h2, h3, fun _ => ⟨h4, h5, h6, h7, h8⟩⟩
    · exact ⟨id, 1 / 4, 1, by positivity, le_rfl, zero_lt_one, fun h => (hw h).elim⟩
  choose g_w ρ_w ru_w hρ_pos hρ_le hru_pos hchart_spec using hchart
  obtain ⟨t, ht_cov⟩ := hK₀_compact.elim_finite_subcover
    (fun x : K₀ => ball (x : ℂ) (ρ_w x)) (fun _ => isOpen_ball)
    (fun w hw => mem_iUnion.mpr ⟨⟨w, hw⟩, mem_ball_self (hρ_pos w)⟩)
  let M := Fintype.card t
  let e : Fin M ≃ t := (Fintype.equivFin t).symm
  let W_open : Set ℂ := ⋃ i : Fin M, ball ((e i).1 : ℂ) (ρ_w ((e i).1 : ℂ))
  have hW_open : IsOpen W_open := isOpen_iUnion fun _ => isOpen_ball
  let E_far : Set ℂ := closedBall (0 : ℂ) R₀ \ (V_crit ∪ W_open)
  have hE_compact : IsCompact E_far := (isCompact_closedBall 0 R₀).diff (hV_open.union hW_open)
  have hE_disj : ∀ ζ ∈ E_far, 0 < |‖P₀.eval ζ‖ - 1| := by
    intro ζ ⟨hζB, hζVW⟩
    rw [abs_pos, sub_ne_zero]
    intro hnorm1
    have hζU : ζ ∉ U_crit := by
      intro hU
      obtain ⟨c, hc, hζc⟩ := mem_iUnion₂.mp hU
      exact hζVW (Or.inl (mem_iUnion₂.mpr ⟨c, hc, ball_subset_ball (by linarith [hrc_pos]) hζc⟩))
    have hζK₀ : ζ ∈ K₀ := ⟨hnorm1, hζU⟩
    obtain ⟨x, hx⟩ := mem_iUnion.mp (ht_cov hζK₀)
    obtain ⟨hxt, hζx⟩ := mem_iUnion.mp hx
    let i₀ : Fin M := e.symm ⟨x, hxt⟩
    have heq : (e i₀).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxt⟩)
    exact hζVW (Or.inr (mem_iUnion.mpr ⟨i₀, by simpa [heq] using hζx⟩))
  have hex_mfar : ∃ m_far : ℝ, 0 < m_far ∧ ∀ ζ ∈ E_far, m_far ≤ |‖P₀.eval ζ‖ - 1| := by
    by_cases hE_ne : E_far.Nonempty
    · obtain ⟨ζ₀, hζ₀, hmin⟩ := hE_compact.exists_isMinOn hE_ne
        (continuous_abs.comp (P₀.continuous.norm.sub continuous_const)).continuousOn
      exact ⟨|‖P₀.eval ζ₀‖ - 1|, hE_disj ζ₀ hζ₀, fun ζ hζ => hmin hζ⟩
    · exact ⟨1, zero_lt_one, fun ζ hζ => (hE_ne ⟨ζ, hζ⟩).elim⟩
  obtain ⟨m_far, hmfar_pos, hmfar_bd⟩ := hex_mfar
  by_cases hM : Nonempty (Fin M)
  · let wi : Fin M → ℂ := fun i => ((e i).1 : ℂ)
    have hwi_K₀ : ∀ i, wi i ∈ K₀ := fun i => (e i).1.2
    have hVB : V_crit ⊆ B_crit := by
      intro ζ hV
      obtain ⟨c, hc, hζc⟩ := mem_iUnion₂.mp hV
      exact mem_iUnion₂.mpr ⟨c, hc, ball_subset_closedBall hζc⟩
    have hmfar_bd_W : ∀ ζ ∈ closedBall (0 : ℂ) R₀, ζ ∉ V_crit →
        (∀ i : Fin M, ζ ∉ ball (wi i) (ρ_w (wi i))) → m_far ≤ |‖P₀.eval ζ‖ - 1| := by
      intro ζ hζR₀ hζV hζW
      apply hmfar_bd ζ
      refine ⟨hζR₀, fun h => h.elim hζV (fun hW => ?_)⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hW
      exact hζW i hi
    have hev := Erdos114H1Aux.nonempty_branch_bound hn z₀ P₀ rfl hR₀_pos rfl hL₀_nonneg hL₀_ofReal
      hL₀_sub hε_pos hδ_pos hδ_eq hθ_pos hθ_lt_one hθ_inv hmfar_pos Set.sdiff_subset hK₀_deriv
      hB_crit_bound hVB hρ_pos hρ_le hru_pos hchart_spec hM wi hwi_K₀ hmfar_bd_W
    exact hev.mono fun z hz => lt_of_le_of_lt hz hε_lt
  · have : IsEmpty (Fin M) := not_nonempty_iff.mp hM
    have hW_empty : W_open = ∅ := by simp [W_open]
    obtain ⟨δ_u, hδu_pos, hδu⟩ :=
      Erdos114H1Aux.uniform_close_polyOfRoots z₀ (show 0 ≤ R₀ by positivity) hmfar_pos
    refine Metric.eventually_nhds_iff.mpr ⟨min (1 / 2) δ_u, lt_min (by positivity) hδu_pos, ?_⟩
    intro z hz
    let Pz := Erdos114H1Aux.polyOfRoots z
    have hPz_sub : lemniscate Pz ⊆ closedBall (0 : ℂ) R₀ :=
      Erdos114H1Aux.lemniscate_subset_closedBall hn z₀ z
        (lt_of_lt_of_le hz (by linarith [min_le_left (1 / 2 : ℝ) δ_u]))
    obtain ⟨hval_bd, _⟩ := hδu z (lt_of_lt_of_le hz (min_le_right _ _))
    have hPz_B : lemniscate Pz ⊆ lemniscate Pz ∩ B_crit := by
      intro ζ hζL
      refine ⟨hζL, ?_⟩
      by_contra hζB
      have hζV : ζ ∉ V_crit := by
        intro hV
        obtain ⟨c, hc, hζc⟩ := mem_iUnion₂.mp hV
        exact hζB (mem_iUnion₂.mpr ⟨c, hc, ball_subset_closedBall hζc⟩)
      have hζE : ζ ∈ E_far := ⟨hPz_sub hζL, by
        simp only [mem_union, hW_empty, mem_empty_iff_false, or_false]; exact hζV⟩
      have h1 := hmfar_bd ζ hζE
      have h2 : |‖P₀.eval ζ‖ - 1| ≤ ‖Pz.eval ζ - P₀.eval ζ‖ := by
        have hn1 : ‖Pz.eval ζ‖ = 1 := hζL
        calc |‖P₀.eval ζ‖ - 1| = |‖P₀.eval ζ‖ - ‖Pz.eval ζ‖| := by rw [hn1]
          _ ≤ ‖P₀.eval ζ - Pz.eval ζ‖ := abs_norm_sub_norm_le _ _
          _ = ‖Pz.eval ζ - P₀.eval ζ‖ := norm_sub_rev _ _
      have h3 := hval_bd ζ (hPz_sub hζL)
      linarith
    calc lemniscateLength Pz
        ≤ μH[1] (lemniscate Pz ∩ B_crit) := measure_mono hPz_B
      _ ≤ ENNReal.ofReal (ε / 2) := hB_crit_bound z
      _ ≤ ENNReal.ofReal (L₀ + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ < y := hε_lt
