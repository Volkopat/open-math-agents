import OMAReductions.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Proof of Erdős 114 H2. -/

open Set Topology Polynomial Metric Filter Erdos114 MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Erdos114H2Proof

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
  linarith [sq_nonneg ‖h‖]

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
  have hcont : ContinuousAt (fun z => p.eval z) z₀ := p.continuous.continuousAt
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcont η hη
  refine ⟨min δ₁ δ₂ / 2, by positivity, ?_⟩
  intro z₁ ⟨hz₁L, hz₁B⟩ z₂ ⟨hz₂L, hz₂B⟩
  have hz₁_d₁ : dist z₁ z₀ < δ₁ :=
    lt_of_le_of_lt (mem_closedBall.mp hz₁B) (by linarith [min_le_left δ₁ δ₂])
  have hz₂_d₁ : dist z₂ z₀ < δ₁ :=
    lt_of_le_of_lt (mem_closedBall.mp hz₂B) (by linarith [min_le_left δ₁ δ₂])
  have hz₁_d₂ : dist z₁ z₀ < δ₂ :=
    lt_of_le_of_lt (mem_closedBall.mp hz₁B) (by linarith [min_le_right δ₁ δ₂])
  have hz₂_d₂ : dist z₂ z₀ < δ₂ :=
    lt_of_le_of_lt (mem_closedBall.mp hz₂B) (by linarith [min_le_right δ₁ δ₂])
  have hpair : dist (z₁, z₂) (z₀, z₀) < δ₁ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hz₁_d₁, hz₂_d₁⟩
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
  have hu₂_near : ‖u₂ - w₀‖ < η := by simpa [u₂, w₀, dist_eq_norm] using hδ₂ hz₂_d₂
  have hu₁₂_small : ‖u₁ - u₂‖ ≤ 2 * η := by
    calc ‖u₁ - u₂‖ = ‖(u₁ - w₀) - (u₂ - w₀)‖ := by ring_nf
      _ ≤ ‖u₁ - w₀‖ + ‖u₂ - w₀‖ := norm_sub_le _ _
      _ ≤ η + η := by linarith
      _ = 2 * η := by ring
  have hcircle : 2 * ((starRingEnd ℂ u₁) * (u₁ - u₂)).re = ‖u₁ - u₂‖ ^ 2 :=
    unit_circle_re_sub hz₁L hz₂L
  have hre_u : |((starRingEnd ℂ w₀) * (u₁ - u₂)).re| ≤ (|w.im| / 8) * ‖h‖ := by
    have hsplit : ((starRingEnd ℂ w₀) * (u₁ - u₂)).re =
        ((starRingEnd ℂ u₁) * (u₁ - u₂)).re + ((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re := by
      rw [← Complex.add_re, ← add_mul, ← map_add]
      congr 2
      ring
    have h1 : |((starRingEnd ℂ u₁) * (u₁ - u₂)).re| ≤ η * ‖u₁ - u₂‖ := by
      have hnonneg : 0 ≤ ((starRingEnd ℂ u₁) * (u₁ - u₂)).re := by linarith [sq_nonneg ‖u₁ - u₂‖]
      rw [abs_of_nonneg hnonneg]
      nlinarith [norm_nonneg (u₁ - u₂)]
    have h2 : |((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re| ≤ η * ‖u₁ - u₂‖ := by
      calc |((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re|
          ≤ ‖(starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)‖ := Complex.abs_re_le_norm _
        _ = ‖u₁ - w₀‖ * ‖u₁ - u₂‖ := by rw [norm_mul, RCLike.norm_conj, norm_sub_rev]
        _ ≤ η * ‖u₁ - u₂‖ := mul_le_mul_of_nonneg_right hu₁_near.le (norm_nonneg _)
    have h3 : |((starRingEnd ℂ w₀) * (u₁ - u₂)).re| ≤ 2 * η * ‖u₁ - u₂‖ := by
      rw [hsplit]
      linarith [abs_add_le ((starRingEnd ℂ u₁) * (u₁ - u₂)).re
        ((starRingEnd ℂ (w₀ - u₁)) * (u₁ - u₂)).re]
    have h5 : 2 * η * (‖d₀‖ + ε) = |w.im| / 8 := by
      dsimp [η]
      field_simp [ne_of_gt (add_pos hd_pos hε)]
      ring
    calc |((starRingEnd ℂ w₀) * (u₁ - u₂)).re|
        ≤ 2 * η * ‖u₁ - u₂‖ := h3
      _ ≤ 2 * η * ((‖d₀‖ + ε) * ‖h‖) := mul_le_mul_of_nonneg_left hu_diff (by positivity)
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
      dsimp [w]
      rw [← Complex.sub_re]
      congr 1
      ring
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

end Erdos114H2Proof

namespace Erdos114H2Proof

lemma measurableSet_re_sdiff_compact {C D : Set ℂ} (hC : IsCompact C) (hD : IsCompact D) :
    MeasurableSet (Complex.re '' (C \ D)) := by
  by_cases hne : D.Nonempty
  · have hEq : C \ D = ⋃ m : ℕ, (C ∩ {z : ℂ | (1 : ℝ) / (m + 1) ≤ infDist z D}) := by
      ext z
      simp only [Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hzC, hzD⟩
        have hpos : 0 < infDist z D := (hD.isClosed.notMem_iff_infDist_pos hne).mp hzD
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
        exact ⟨m, hzC, hm.le⟩
      · rintro ⟨m, hzC, hm⟩
        refine ⟨hzC, (hD.isClosed.notMem_iff_infDist_pos hne).mpr ?_⟩
        exact lt_of_lt_of_le (by positivity) hm
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
  have h3 : f '' (univ : Set A) = Complex.re '' A := by
    ext x
    simp [f]
  rw [h1]
  simpa [h3, hausdorffMeasure_real] using h2

lemma finite_line_intersections {p : ℂ[X]} (hp : 0 < p.natDegree) (a b : ℂ) (hb : b ≠ 0) :
    {t : ℝ | ‖p.eval (a + (t : ℂ) * b)‖ = 1}.Finite := by
  let q := p.comp (C b * X + C a)
  let c := starRingEnd ℂ
  let f := q * q.map c - 1
  have hq : q.natDegree = p.natDegree := by
    simp [q, natDegree_comp, natDegree_C_mul_X _ hb]
  have hq' : (q.map c).natDegree = q.natDegree :=
    natDegree_map_eq_of_injective c.injective q
  have hq₀ : q ≠ 0 := fun h => by rw [h, natDegree_zero] at hq; omega
  have hqc₀ : q.map c ≠ 0 := fun h => by rw [h, natDegree_zero, hq] at hq'; omega
  have hf : f.natDegree = 2 * p.natDegree := by
    dsimp [f]
    rw [← C_1, natDegree_sub_C, natDegree_mul hq₀ hqc₀, hq', hq]
    omega
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

lemma sum_volume_re_le {p : ℂ[X]} (hp : 0 < p.natDegree)
    (hline : ∀ a b : ℂ, b ≠ 0 →
      {t : ℝ | ‖p.eval (a + (t : ℂ) * b)‖ = 1}.ncard ≤ 2 * p.natDegree)
    (a : ℂ) {r : ℝ} (_hr : 0 < r) {N : ℕ} (A : Fin N → Set ℂ)
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hsub : ∀ i, A i ⊆ lemniscate p ∩ closedBall a r)
    (hmeas : ∀ i, MeasurableSet (Complex.re '' A i)) :
    (∑ i : Fin N, volume (Complex.re '' A i)) ≤ ENNReal.ofReal (4 * p.natDegree * r) := by
  classical
  let J : Set ℝ := Icc (a.re - r) (a.re + r)
  have hpt : ∀ x : ℝ,
      (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
        (2 * p.natDegree : ℝ≥0∞) * J.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    let F := Finset.univ.filter (fun i : Fin N => x ∈ Complex.re '' A i)
    have hsumF : (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x) = F.card := by
      calc (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x)
          = ∑ i : Fin N, if x ∈ Complex.re '' A i then (1 : ℝ≥0∞) else 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hx : x ∈ Complex.re '' A i <;> simp [hx]
        _ = F.card := by simp [F]
    rw [hsumF]
    by_cases hF : F.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hF
      obtain ⟨z₀, hz₀A, hz₀x⟩ := (Finset.mem_filter.mp hi₀).2
      have hz₀B : z₀ ∈ closedBall a r := (hsub i₀ hz₀A).2
      have hxJ : x ∈ J := by
        have habs : |x - a.re| ≤ r := by
          calc |x - a.re| = |(z₀ - a).re| := by rw [← hz₀x, Complex.sub_re]
            _ ≤ ‖z₀ - a‖ := Complex.abs_re_le_norm _
            _ ≤ r := dist_eq_norm z₀ a ▸ mem_closedBall.mp hz₀B
        exact ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩
      rw [indicator_of_mem hxJ, mul_one]
      let T : Set ℝ := {t : ℝ | ‖p.eval ((x : ℂ) + (t : ℂ) * Complex.I)‖ = 1}
      have hTfin : T.Finite := finite_line_intersections hp (x : ℂ) Complex.I Complex.I_ne_zero
      let g : Fin N → ℝ := fun i =>
        if hi : i ∈ F then ((Finset.mem_filter.mp hi).2.choose).im else 0
      have hg_maps : MapsTo g (F : Set (Fin N)) T := by
        intro i hi
        have hi' : i ∈ F := hi
        dsimp [g]
        rw [dif_pos hi']
        have hz := (Finset.mem_filter.mp hi').2.choose_spec
        have hL : ‖p.eval ((Finset.mem_filter.mp hi').2.choose)‖ = 1 := (hsub i hz.1).1
        have hdecomp : (x : ℂ) + (((Finset.mem_filter.mp hi').2.choose).im : ℂ) * Complex.I =
            (Finset.mem_filter.mp hi').2.choose := by
          apply Complex.ext
          · simp [hz.2]
          · simp
        change ‖p.eval ((x : ℂ) + (((Finset.mem_filter.mp hi').2.choose).im : ℂ) * Complex.I)‖ = 1
        rwa [hdecomp]
      have hg_inj : InjOn g (F : Set (Fin N)) := by
        intro i hi j hj hij
        have hi' : i ∈ F := hi
        have hj' : j ∈ F := hj
        dsimp [g] at hij
        rw [dif_pos hi', dif_pos hj'] at hij
        have hzi := (Finset.mem_filter.mp hi').2.choose_spec
        have hzj := (Finset.mem_filter.mp hj').2.choose_spec
        have heq : (Finset.mem_filter.mp hi').2.choose = (Finset.mem_filter.mp hj').2.choose :=
          Complex.ext (hzi.2.trans hzj.2.symm) hij
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hne) hzi.1 (heq ▸ hzj.1)
      have hcard : F.card ≤ 2 * p.natDegree := by
        calc F.card = (F : Set (Fin N)).ncard := (ncard_coe_finset F).symm
          _ ≤ T.ncard := ncard_le_ncard_of_injOn g hg_maps hg_inj hTfin
          _ ≤ 2 * p.natDegree := hline (x : ℂ) Complex.I Complex.I_ne_zero
      exact_mod_cast hcard
    · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
      simp
  have h1 : (∑ i : Fin N, volume (Complex.re '' A i)) =
      ∫⁻ x, (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ∂volume := by
    rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hmeas i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 from rfl, lintegral_indicator_one (hmeas i)]
  rw [h1]
  calc ∫⁻ x, (∑ i : Fin N, (Complex.re '' A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ∂volume
      ≤ ∫⁻ x, (2 * p.natDegree : ℝ≥0∞) * J.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume :=
        lintegral_mono hpt
    _ = (2 * p.natDegree : ℝ≥0∞) * ∫⁻ x, J.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume :=
        lintegral_const_mul _ (measurable_const.indicator measurableSet_Icc)
    _ = (2 * p.natDegree : ℝ≥0∞) * volume J := by
        rw [show (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 from rfl, lintegral_indicator_one measurableSet_Icc]
    _ = ENNReal.ofReal (4 * p.natDegree * r) := by
        rw [Real.volume_Icc]
        have hlen : a.re + r - (a.re - r) = 2 * r := by ring
        rw [hlen]
        have hcast : (2 * p.natDegree : ℝ≥0∞) = ENNReal.ofReal (2 * p.natDegree : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
        rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

def Sx (p : ℂ[X]) (a : ℂ) (r : ℝ) : Set ℂ :=
  {z ∈ lemniscate p ∩ closedBall a r |
    |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).re| ≤
      |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).im| ∧
    (starRingEnd ℂ (p.eval z) * p.derivative.eval z).im ≠ 0}

lemma measure_Sx_le {p : ℂ[X]} (hp : 0 < p.natDegree)
    (hline : ∀ a b : ℂ, b ≠ 0 →
      {t : ℝ | ‖p.eval (a + (t : ℂ) * b)‖ = 1}.ncard ≤ 2 * p.natDegree)
    (a : ℂ) {r : ℝ} (hr : 0 < r) :
    μH[1] (Sx p a r) ≤ ENNReal.ofReal (8 * p.natDegree * r) := by
  classical
  let w : ℂ → ℂ := fun z => starRingEnd ℂ (p.eval z) * p.derivative.eval z
  have hw_cont : Continuous w :=
    (continuous_star.comp p.continuous).mul p.derivative.continuous
  let K : ℕ → Set ℂ := fun m =>
    {z ∈ lemniscate p ∩ closedBall a r |
      (1 : ℝ) / (m + 1) ≤ |(w z).im| ∧ |(w z).re| ≤ |(w z).im|}
  have hmono : Monotone K := by
    intro m₁ m₂ hm z ⟨hzS, hz1, hz2⟩
    refine ⟨hzS, le_trans ?_ hz1, hz2⟩
    gcongr
  have hunion : Sx p a r = ⋃ m : ℕ, K m := by
    ext z
    simp only [Sx, K, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hzS, hle, hne⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hne)
      exact ⟨m, hzS, hm.le, hle⟩
    · rintro ⟨m, hzS, hm, hle⟩
      exact ⟨hzS, hle, abs_pos.mp (lt_of_lt_of_le (by positivity) hm)⟩
  rw [hunion, hmono.measure_iUnion]
  refine iSup_le fun m => ?_
  have hS_closed : IsClosed (lemniscate p) := isClosed_eq p.continuous.norm continuous_const
  have hKm_compact : IsCompact (K m) := by
    refine ((isCompact_closedBall a r).inter_left hS_closed).inter_right ?_
    exact (isClosed_le continuous_const (continuous_abs.comp (Complex.continuous_im.comp hw_cont))).inter
      (isClosed_le (continuous_abs.comp (Complex.continuous_re.comp hw_cont))
        (continuous_abs.comp (Complex.continuous_im.comp hw_cont)))
  have hloc : ∀ z : ℂ, ∃ δ : ℝ, 0 < δ ∧
      (z ∈ K m → ∀ z₁ ∈ lemniscate p ∩ closedBall z δ, ∀ z₂ ∈ lemniscate p ∩ closedBall z δ,
        ‖z₁ - z₂‖ ≤ 2 * |(z₁ - z₂).re|) := by
    intro z
    by_cases hz : z ∈ K m
    · obtain ⟨hzS, hm', hle⟩ := hz
      have hne : (w z).im ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hm')
      obtain ⟨δ, hδ, hlip⟩ := local_re_antilipschitz p hzS.1 hle hne
      exact ⟨δ, hδ, fun _ => hlip⟩
    · exact ⟨1, zero_lt_one, fun h => (hz h).elim⟩
  choose δ hδ_pos hδ_lip using hloc
  obtain ⟨t, ht_cov⟩ := hKm_compact.elim_finite_subcover
    (fun x : K m => ball (x : ℂ) (δ x)) (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hδ_pos z)⟩)
  let N := Fintype.card t
  let e : Fin N ≃ t := (Fintype.equivFin t).symm
  let C : Fin N → Set ℂ := fun i => K m ∩ closedBall ((e i).1 : ℂ) (δ ((e i).1 : ℂ))
  have hC_compact : ∀ i, IsCompact (C i) := fun i =>
    hKm_compact.inter_right isClosed_closedBall
  let D : Fin N → Set ℂ := fun i => ⋃ j ∈ Finset.univ.filter (· < i), C j
  have hD_compact : ∀ i, IsCompact (D i) := fun i =>
    (Finset.univ.filter (· < i)).isCompact_biUnion (fun j _ => hC_compact j)
  let A : Fin N → Set ℂ := fun i => C i \ D i
  have hKm_sub : K m ⊆ ⋃ i : Fin N, A i := by
    intro z hz
    obtain ⟨w₀, hw₀⟩ := mem_iUnion.mp (ht_cov hz)
    obtain ⟨hw₀_t, hz_ball⟩ := mem_iUnion.mp hw₀
    let i₁ : Fin N := e.symm ⟨w₀, hw₀_t⟩
    have hzi₁ : z ∈ C i₁ := by
      refine ⟨hz, ?_⟩
      have heq : (e i₁).1 = w₀ := congrArg Subtype.val (e.apply_symm_apply ⟨w₀, hw₀_t⟩)
      rw [heq]
      exact ball_subset_closedBall hz_ball
    let S_idx := Finset.univ.filter (fun i : Fin N => z ∈ C i)
    have hSne : S_idx.Nonempty := ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi₁⟩⟩
    let i₀ := S_idx.min' hSne
    refine mem_iUnion.mpr ⟨i₀, (Finset.mem_filter.mp (Finset.min'_mem S_idx hSne)).2, ?_⟩
    intro hzD
    obtain ⟨j, hjF, hzj⟩ := mem_iUnion₂.mp hzD
    have hj_lt : j < i₀ := (Finset.mem_filter.mp hjF).2
    have hj_mem : j ∈ S_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj⟩
    exact not_le_of_gt hj_lt (Finset.min'_le S_idx j hj_mem)
  have hA_disj : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine Set.disjoint_left.mpr fun z hzi hzj => hzj.2 ?_
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hzi.1⟩
    · refine Set.disjoint_left.mpr fun z hzi hzj => hzi.2 ?_
      exact mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, hzj.1⟩
  have hA_sub : ∀ i, A i ⊆ lemniscate p ∩ closedBall a r := by
    intro i z hz
    exact hz.1.1.1
  have hA_meas : ∀ i, MeasurableSet (Complex.re '' A i) := fun i =>
    measurableSet_re_sdiff_compact (hC_compact i) (hD_compact i)
  have hA_haus : ∀ i, μH[1] (A i) ≤ 2 * volume (Complex.re '' A i) := by
    intro i
    refine hausdorff_le_two_volume_re fun z₁ hz₁ z₂ hz₂ => ?_
    exact hδ_lip ((e i).1 : ℂ) (e i).1.2 z₁ ⟨hz₁.1.1.1.1, hz₁.1.2⟩ z₂ ⟨hz₂.1.1.1.1, hz₂.1.2⟩
  calc μH[1] (K m)
      ≤ μH[1] (⋃ i : Fin N, A i) := measure_mono hKm_sub
    _ ≤ ∑ i : Fin N, μH[1] (A i) := measure_iUnion_fintype_le (μH[1]) A
    _ ≤ ∑ i : Fin N, 2 * volume (Complex.re '' A i) := Finset.sum_le_sum fun i _ => hA_haus i
    _ = 2 * ∑ i : Fin N, volume (Complex.re '' A i) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ENNReal.ofReal (4 * p.natDegree * r) :=
        mul_le_mul_of_nonneg_left (sum_volume_re_le hp hline a hr A hA_disj hA_sub hA_meas) (by positivity)
    _ = ENNReal.ofReal (8 * p.natDegree * r) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

def Sy (p : ℂ[X]) (a : ℂ) (r : ℝ) : Set ℂ :=
  {z ∈ lemniscate p ∩ closedBall a r |
    |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).im| ≤
      |(starRingEnd ℂ (p.eval z) * p.derivative.eval z).re| ∧
    (starRingEnd ℂ (p.eval z) * p.derivative.eval z).re ≠ 0}

lemma measure_Sy_le {p : ℂ[X]} (hp : 0 < p.natDegree)
    (hline : ∀ a b : ℂ, b ≠ 0 →
      {t : ℝ | ‖p.eval (a + (t : ℂ) * b)‖ = 1}.ncard ≤ 2 * p.natDegree)
    (a : ℂ) {r : ℝ} (hr : 0 < r) :
    μH[1] (Sy p a r) ≤ ENNReal.ofReal (8 * p.natDegree * r) := by
  let q : ℂ[X] := p.comp (C Complex.I * X)
  have hq_deg : q.natDegree = p.natDegree := by
    simp [q, natDegree_comp, natDegree_C_mul_X _ Complex.I_ne_zero]
  have hq_pos : 0 < q.natDegree := hq_deg.symm ▸ hp
  have hq_line : ∀ a' b' : ℂ, b' ≠ 0 →
      {t : ℝ | ‖q.eval (a' + (t : ℂ) * b')‖ = 1}.ncard ≤ 2 * q.natDegree := by
    intro a' b' hb'
    have hset : {t : ℝ | ‖q.eval (a' + (t : ℂ) * b')‖ = 1} =
        {t : ℝ | ‖p.eval (Complex.I * a' + (t : ℂ) * (Complex.I * b'))‖ = 1} := by
      ext t
      simp only [q, eval_comp, eval_mul, eval_C, eval_X, mem_ofPred_eq]
      congr 2
      ring
    rw [hset, hq_deg]
    exact hline (Complex.I * a') (Complex.I * b') (mul_ne_zero Complex.I_ne_zero hb')
  let rot : ℂ ≃ᵢ ℂ :=
    ⟨Equiv.mulLeft₀ Complex.I Complex.I_ne_zero, Isometry.of_dist_eq fun x y => by
      change dist (Complex.I * x) (Complex.I * y) = dist x y
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_I, one_mul]⟩
  have hpre : rot ⁻¹' (Sy p a r) = Sx q (-Complex.I * a) r := by
    ext u
    have hq_eval : q.eval u = p.eval (Complex.I * u) := by simp [q, eval_comp]
    have hq_deriv : q.derivative.eval u = Complex.I * p.derivative.eval (Complex.I * u) := by
      have hd : q.derivative = p.derivative.comp (C Complex.I * X) * C Complex.I := by
        simp [q, derivative_comp]; ring
      simp only [hd, eval_mul, eval_comp, eval_C, eval_X, mul_comm]
    let wp := starRingEnd ℂ (p.eval (Complex.I * u)) * p.derivative.eval (Complex.I * u)
    have hwq : starRingEnd ℂ (q.eval u) * q.derivative.eval u = Complex.I * wp := by
      rw [hq_eval, hq_deriv]
      dsimp [wp]
      ring
    have hre : (Complex.I * wp).re = -wp.im := by simp
    have him : (Complex.I * wp).im = wp.re := by simp
    have hball : Complex.I * u ∈ closedBall a r ↔ u ∈ closedBall (-Complex.I * a) r := by
      simp only [mem_closedBall, dist_eq_norm]
      have hid : Complex.I * u - a = Complex.I * (u - (-Complex.I * a)) := by
        calc Complex.I * u - a = Complex.I * u - (Complex.I * (-Complex.I)) * a := by simp
          _ = Complex.I * (u - (-Complex.I * a)) := by ring
      rw [hid, norm_mul, Complex.norm_I, one_mul]
    change (Complex.I * u ∈ Sy p a r) ↔ (u ∈ Sx q (-Complex.I * a) r)
    simp only [Sy, Sx, mem_inter_iff, mem_ofPred_eq, lemniscate, hball]
    rw [hwq, hq_eval, hre, him, abs_neg]
  have hm := rot.hausdorffMeasure_preimage 1 (Sy p a r)
  rw [hpre] at hm
  rw [← hm, ← hq_deg]
  exact measure_Sx_le hq_pos hq_line (-Complex.I * a) hr

lemma measure_crit_zero {p : ℂ[X]} (hp : 0 < p.natDegree) :
    μH[1] {z : ℂ | p.derivative.eval z = 0} = 0 := by
  have hp_ne : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hp; omega
  have hderiv_ne : p.derivative ≠ 0 := by
    intro hd
    have hc := congrArg (fun f : ℂ[X] => f.coeff (p.natDegree - 1)) hd
    simp only [coeff_zero, coeff_derivative] at hc
    have hsub : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel hp
    have hcast : ((p.natDegree - 1 : ℕ) : ℂ) + 1 = (p.natDegree : ℂ) := by exact_mod_cast hsub
    rw [hsub, hcast] at hc
    have hlead : p.coeff p.natDegree ≠ 0 := p.leadingCoeff_ne_zero.mpr hp_ne
    have hdeg_ne : ((p.natDegree : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    exact mul_ne_zero hlead hdeg_ne hc
  have hfin : {z : ℂ | p.derivative.eval z = 0}.Finite := by
    refine p.derivative.roots.toFinset.finite_toSet.subset fun z hz => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hderiv_ne]
    exact hz
  have := MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ (zero_lt_one' ℝ)
  exact hfin.measure_zero (μH[1])

end Erdos114H2Proof

theorem OMA.solution : OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1.H2 := by
  intro p hp hline a r hr
  let Scrit : Set ℂ := {z : ℂ | p.derivative.eval z = 0}
  have hcov : lemniscate p ∩ closedBall a r ⊆
      Scrit ∪ (Erdos114H2Proof.Sx p a r ∪ Erdos114H2Proof.Sy p a r) := by
    intro z hz
    by_cases hc : p.derivative.eval z = 0
    · exact Or.inl hc
    · right
      let w := starRingEnd ℂ (p.eval z) * p.derivative.eval z
      have hw_ne : w ≠ 0 := by
        have hpz : p.eval z ≠ 0 := by
          intro h0
          have : ‖p.eval z‖ = 1 := hz.1
          simp [h0] at this
        have hconj : starRingEnd ℂ (p.eval z) ≠ 0 :=
          fun h => hpz (by simpa using congrArg (starRingEnd ℂ) h)
        exact mul_ne_zero hconj hc
      rcases le_total |w.re| |w.im| with hxy | hyx
      · refine Or.inl ⟨hz, hxy, ?_⟩
        intro him0
        have him0' : w.im = 0 := him0
        have hre0 : w.re = 0 := abs_nonpos_iff.mp (hxy.trans (by simp [him0']))
        exact hw_ne (Complex.ext hre0 him0')
      · refine Or.inr ⟨hz, hyx, ?_⟩
        intro hre0
        have hre0' : w.re = 0 := hre0
        have him0 : w.im = 0 := abs_nonpos_iff.mp (hyx.trans (by simp [hre0']))
        exact hw_ne (Complex.ext hre0' him0)
  calc μH[1] (lemniscate p ∩ closedBall a r)
      ≤ μH[1] (Scrit ∪ (Erdos114H2Proof.Sx p a r ∪ Erdos114H2Proof.Sy p a r)) :=
        measure_mono hcov
    _ ≤ μH[1] Scrit + μH[1] (Erdos114H2Proof.Sx p a r ∪ Erdos114H2Proof.Sy p a r) :=
        measure_union_le _ _
    _ ≤ μH[1] Scrit + (μH[1] (Erdos114H2Proof.Sx p a r) + μH[1] (Erdos114H2Proof.Sy p a r)) :=
        add_le_add_right (measure_union_le _ _) _
    _ ≤ 0 + (ENNReal.ofReal (8 * p.natDegree * r) + ENNReal.ofReal (8 * p.natDegree * r)) := by
        rw [Erdos114H2Proof.measure_crit_zero hp]
        exact add_le_add_right (add_le_add
          (Erdos114H2Proof.measure_Sx_le hp hline a hr)
          (Erdos114H2Proof.measure_Sy_le hp hline a hr)) _
    _ = ENNReal.ofReal (16 * p.natDegree * r) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
