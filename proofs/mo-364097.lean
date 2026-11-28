import OMAStatements.S_mo_364097

/-!
Adapted from @connoranderson’s earlier complete proof, pin
 ec801973a3a28064e31a0dade2ef1fcf61bb99cc, linked by statement #27108.
The standard compact closed-thickening measure limit replaces its manual
outer-regularity argument for upper semicontinuity. The ball-slicing and finite-net
construction is retained. Standard null-set congruence replaces its manual
finite-union measure bound. @Solfanbtc’s merged proof #30699 was also read.
Source: Redeldio, https://mathoverflow.net/questions/364097 (CC BY-SA 4.0);
original observations credited to Ville Salo and Pierre PC.
-/

namespace OMA.S_mo_364097
open Set MeasureTheory Metric Filter Topology

private lemma upper {n : ℕ} (K : Set (E n)) (hc : IsCompact K) (hn : K.Nonempty)
    (ε : ℝ) (hε : 0<ε) : ∃ δ>0, ∀ H : Set (E n), IsCompact H → H.Nonempty →
      hausdorffDist K H<δ → vol H < vol K+ε := by
  have ht := (ENNReal.tendsto_toReal hc.measure_lt_top.ne).comp
    (tendsto_measure_cthickening_of_isCompact (μ := volume) hc)
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), vol (cthickening r K) < vol K + ε :=
    (ht.mono_left inf_le_left) (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨δ,hv,hδ⟩ := (he.and self_mem_nhdsWithin).exists
  refine ⟨δ,hδ,fun H hC hN hD => ?_⟩
  have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded hN hn hC.isBounded hc.isBounded
  apply lt_of_le_of_lt (measureReal_mono (μ := volume) ?_
    hc.isBounded.cthickening.measure_lt_top.ne) hv
  intro x hx
  rw [mem_cthickening_iff]
  apply (infEDist_le_hausdorffEDist_of_mem hx).trans
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (by simpa [hausdorffDist, hausdorffEDist_comm] using hD.le)

private lemma slice {n : ℕ} (K : Set (E n)) (hc : IsCompact K)
    (m : ℝ) (hm : m∈Icc 0 (vol K)) : ∃ J⊆K, IsCompact J ∧ vol J=m := by
  let B (r : ℝ) := closedBall (0:E n) r
  let f (r : ℝ) := vol (K ∩ B r)
  let g (r : ℝ) := r^(Module.finrank ℝ (E n))*volume.real (ball (0:E n) 1)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hB (r : ℝ) (hr : 0≤r) : vol (B r)=g r := Measure.addHaar_real_closedBall volume 0 hr
  have bound (a b : ℝ) (ha : 0≤a) (hab : a≤b) : dist (f a) (f b) ≤ dist (g a) (g b) := by
    have hinc : B a⊆B b := closedBall_subset_closedBall hab
    have hsub : (K ∩ B b) \ (K ∩ B a) ⊆ B b \ B a := by rintro x ⟨⟨hx,hxb⟩,hx'⟩; exact ⟨hxb,fun hxa => hx' ⟨hx,hxa⟩⟩
    have hf : volume (B b) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hf' : volume (K ∩ B b) ≠ ⊤ := measure_ne_top_of_subset inter_subset_right hf
    have he := measureReal_mono (μ:=volume) hsub (measure_ne_top_of_subset sdiff_subset hf)
    rw [measureReal_sdiff (μ:=volume) (inter_subset_inter_right K hinc) (hc.measurableSet.inter measurableSet_closedBall) hf',
      measureReal_sdiff (μ:=volume) hinc measurableSet_closedBall hf] at he
    have ha' : f a≤f b := measureReal_mono (inter_subset_inter_right K hinc) hf'
    have hb' : vol (B a)≤vol (B b) := measureReal_mono hinc hf
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr ha'),Real.dist_eq,←hB a ha,←hB b (ha.trans hab),
      abs_of_nonpos (sub_nonpos.mpr hb')]
    change -(vol (K∩B a)-vol (K∩B b)) ≤ _
    change vol (K∩B b)-vol (K∩B a) ≤ vol (B b)-vol (B a) at he
    linarith
  obtain ⟨R0,hR0⟩ := hc.isBounded.subset_closedBall (0:E n)
  let R := max 0 R0
  have hR : 0≤R := le_max_left _ _
  have hcov : K ⊆ B R := hR0.trans (closedBall_subset_closedBall (le_max_right _ _))
  have hcon : ContinuousOn f (Icc 0 R) := by
    rw [Metric.continuousOn_iff]
    intro a ha ε hε
    obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x:=a)) ε hε
    refine ⟨δ,hδ,?_⟩
    intro b hb hh
    have hbd : dist (f b) (f a) ≤ dist (g b) (g a) := by
      rcases le_total b a with h|h
      · exact bound _ _ hb.1 h
      · simpa [dist_comm] using bound _ _ ha.1 h
    exact hbd.trans_lt (hd hh)
  have h0 : f 0=0 := by
    simp only [f,vol,measureReal_def]
    rw [measure_inter_null_of_null_right K (by simp [B]), ENNReal.toReal_zero]
  have hend : f R=vol K := by simp [f,inter_eq_left.mpr hcov]
  obtain ⟨r,_,hr⟩ := intermediate_value_Icc hR hcon (show m∈Icc (f 0) (f R) by simpa [h0,hend] using hm)
  exact ⟨K∩B r,inter_subset_left,hc.inter_right isClosed_closedBall,hr⟩

private lemma attain {n : ℕ} (K : Set (E n)) (hc : IsCompact K) (hn : K.Nonempty)
    (m : ℝ) (hm : m∈Icc 0 (vol K)) (δ : ℝ) (hδ : 0<δ) : ∃ H : Set (E n),
      IsCompact H ∧ H.Nonempty ∧ hausdorffDist K H<δ ∧ vol H=m := by
  obtain ⟨J,hJK,hJ,hv⟩ := slice K hc m hm
  obtain ⟨N,hN,hf,hcov⟩ := hc.finite_cover_balls (half_pos hδ)
  have hnear (x : E n) (hx : x∈K) : ∃ y∈N, dist x y<δ/2 := by
    simpa only [mem_iUnion,exists_prop,mem_ball] using hcov hx
  obtain ⟨x,hx⟩ := hn
  obtain ⟨y,hy,-⟩ := hnear x hx
  refine ⟨J∪N,hJ.union hf.isCompact,⟨y,Or.inr hy⟩,?_,?_⟩
  · apply lt_of_le_of_lt _ (half_lt_self hδ)
    apply hausdorffDist_le_of_mem_dist (half_pos hδ).le
    · intro z hz
      obtain ⟨w,hw,hzw⟩ := hnear z hz
      exact ⟨w,Or.inr hw,hzw.le⟩
    · intro z hz
      exact ⟨z,union_subset hJK hN hz,by rw [dist_self]; positivity⟩
  · exact (measureReal_congr (union_ae_eq_left_of_ae_eq_empty
      (ae_eq_empty.mpr (hf.measure_zero volume)))).trans hv

end OMA.S_mo_364097

theorem OMA.solution : type_of% @OMA.S_mo_364097.main := by
  open OMA.S_mo_364097 Set MeasureTheory Metric in
  intro n K hc hn
  have up := upper K hc hn
  have atn := attain K hc hn
  refine ⟨up,?_,?_⟩
  · intro m
    refine ⟨atn m,fun h => ?_⟩
    obtain ⟨H,_,_,_,hH⟩ := h 1 zero_lt_one
    refine ⟨hH ▸ (measureReal_nonneg : 0≤vol H),?_⟩
    by_contra! hlt
    obtain ⟨δ,hδ,hb⟩ := up (m-vol K) (sub_pos.mpr hlt)
    obtain ⟨L,hL,hnL,hd,hv⟩ := h δ hδ
    linarith [hb L hL hnL hd]
  · constructor
    · intro h
      by_contra hne
      have hv : 0<vol K := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
      obtain ⟨δ,hδ,hb⟩ := h (vol K) hv
      obtain ⟨L,hL,hnL,hd,hvL⟩ := atn 0 ⟨le_rfl,hv.le⟩ δ hδ
      have hh := hb L hL hnL hd
      simp [hvL,abs_of_pos hv] at hh
    · intro hv ε hε
      obtain ⟨δ,hδ,hb⟩ := up ε hε
      refine ⟨δ,hδ,?_⟩
      intro H hC hN hd
      have hnH : 0≤vol H := measureReal_nonneg
      rw [hv,sub_zero,abs_of_nonneg hnH]
      simpa [hv] using hb H hC hN hd
