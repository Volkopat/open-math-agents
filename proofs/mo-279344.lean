import OMAStatements.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory Finset Set Metric Filter
open scoped Topology
private instance samples_prob {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (samples μ n) := by unfold samples; infer_instance
private noncomputable def nearest {X : Type*} [MetricSpace X] (o : X) {n : ℕ} [NeZero n] (R : ℝ) (x : Fin n → X) :=
  min R (Finset.univ.inf' Finset.univ_nonempty (fun i => dist (x i) o))
private lemma nearest_le {X : Type*} [MetricSpace X] (o : X) {n : ℕ} [NeZero n]
    (R : ℝ) (x : Fin n → X) (i : Fin n) : nearest o R x ≤ dist (x i) o :=
  (min_le_right ..).trans (Finset.inf'_le _ (mem_univ i))
private lemma nearest_eq_of_far {X : Type*} [MetricSpace X] (o : X) {n : ℕ} [NeZero n]
    (R : ℝ) (x : Fin n → X) (hx : ∀ i,R ≤ dist (x i) o) : nearest o R x=R :=
  min_eq_left (Finset.le_inf' _ _ (fun i _ => hx i))
private lemma nearest_bound {X : Type*} [MetricSpace X] (o : X) {n : ℕ} [NeZero n]
    {R : ℝ} (hR : 0 ≤ R) (x : Fin n → X) : 0 ≤ nearest o R x ∧ nearest o R x ≤ R :=
  ⟨le_min hR (Finset.le_inf' _ _ fun _ _ => dist_nonneg),min_le_left ..⟩
private lemma nearest_symm {X : Type*} [MetricSpace X] (o : X) {n : ℕ} [NeZero n] (R : ℝ) :
    symmetric (nearest o (n := n) R) := by
  intro π x
  unfold nearest
  congr 1
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using Finset.inf'_le (fun i => dist ((x ∘ π) i) o) (mem_univ (π.symm i))
  · apply Finset.le_inf'
    intro i _
    exact Finset.inf'_le _ (mem_univ (π i))
private lemma nearest_lipschitz {X : Type*} [MetricSpace X] (o : X) {n : ℕ} [NeZero n] (R : ℝ) :
    LipschitzWith 1 (nearest o (n := n) R) := by
  have le_add (x y : Fin n → X) : nearest o R x ≤ nearest o R y + dist x y := by
    obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => dist (y i) o)
    unfold nearest
    rw [hj,←min_add_add_right]
    apply le_min
    · linarith [min_le_left R (Finset.univ.inf' Finset.univ_nonempty (fun i => dist (x i) o)),dist_nonneg (x := x) (y := y)]
    · have h := nearest_le o R x j
      change min R _ ≤ _ at h
      linarith [dist_triangle (x j) (y j) o,dist_le_pi_dist x y j]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,abs_le]
  constructor
  · linarith [le_add y x,dist_comm y x]
  · linarith [le_add x y]
private lemma coord_mass {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (i : Fin n) {S : Set X} (hS : MeasurableSet S) :
    (samples μ n).real {x | x i ∈ S} = μ.real S :=
  congrArg ENNReal.toReal ((measurePreserving_eval (fun _ : Fin n => μ) i).measure_preimage hS.nullMeasurableSet)
private lemma nearest_tail {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (o : X) {n : ℕ} [NeZero n] {R : ℝ} (hR : 0 < R)
    (hn : n*μ.real (ball o R) ≤ 1/2) :
    μ.real (ball o (R/4)) ≤ tail μ (nearest o (n := n) R) (R/8) := by
  classical
  let ρ := samples μ n
  let f := nearest o (n := n) R
  let H : Set (Fin n → X) := ⋃ i : Fin n, {x | x i ∈ ball o R}
  have hH : MeasurableSet H := MeasurableSet.iUnion (fun i => measurableSet_ball.preimage (measurable_pi_apply i))
  have hprob : ρ.real H ≤ 1/2 := calc
    _ ≤ ∑ i : Fin n, ρ.real {x | x i ∈ ball o R} := measureReal_iUnion_fintype_le _
    _ = n*μ.real (ball o R) := by
      simp only [ρ,coord_mass μ _ measurableSet_ball,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ ≤ _ := hn
  have hcomp : 1/2 ≤ ρ.real Hᶜ := by rw [measureReal_compl hH,probReal_univ]; linarith
  have hfm : Measurable f := by
    apply measurable_const.min
    have hl : Measurable (Finset.univ.inf' Finset.univ_nonempty (fun (i : Fin n) (x : Fin n → X) => dist (x i) o)) :=
      Finset.inf'_induction _ _ (fun _ hm _ hm' => hm.inf hm') (fun i _ => ((continuous_id.dist (continuous_const (y := o))).measurable.comp (measurable_pi_apply i)))
    convert! hl using 1
    ext x
    simp
  have hfi : Integrable f ρ := .of_bound hfm.aestronglyMeasurable R
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (nearest_bound o hR.le x).1]; exact (nearest_bound o hR.le x).2)
  have hmean : R/2 ≤ ∫ x,f x ∂ρ := calc
    _ ≤ ρ.real Hᶜ*R := by nlinarith [mul_le_mul_of_nonneg_right hcomp hR.le]
    _ = ∫ x,Hᶜ.indicator (fun _ => R) x ∂ρ := by rw [integral_indicator hH.compl,setIntegral_const,smul_eq_mul]
    _ ≤ _ := by
      apply integral_mono ((integrable_const R).indicator hH.compl) hfi
      intro x
      by_cases hx : x∈Hᶜ
      · rw [indicator_of_mem hx]
        apply le_of_eq
        symm
        apply nearest_eq_of_far
        intro i
        apply le_of_not_gt
        exact fun h => hx (mem_iUnion.mpr ⟨i,h⟩)
      · rw [indicator_of_notMem hx]
        exact (nearest_bound o hR.le x).1
  rw [←coord_mass μ (n := n) 0 measurableSet_ball]
  refine measureReal_mono ?_
  intro x hx
  have hx' : dist (x 0) o < R/4 := hx
  have hs := nearest_le o R x 0
  change R/8 < |f x-∫ z,f z ∂ρ|
  change f x ≤ _ at hs
  exact lt_of_lt_of_le (by linarith : R/8 < -(f x-∫ z,f z ∂ρ)) (neg_le_abs _)
end OMA.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory Filter Metric
open scoped Topology
private lemma obstruction {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (o : X) (D : ℕ) (A B : ℝ) (hA : 0<A) (hB : 0<B)
    (hcap : ∀ r : ℝ, 0<r → r ≤ 1 → A*r^D ≤ μ.real (ball o r) ∧ μ.real (ball o r) ≤ B*r^3) :
    violations μ := by
  intro c hc N
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*D:ℕ):ℝ) (c/64)
    (by positivity)).comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ k : ℕ in atTop, (k:ℝ)^(2*D)*Real.exp (-(c/64)*k) < A/(2*4^D) := by
    simpa only [Function.comp_apply,Real.rpow_natCast] using ht.eventually_lt_const (show 0<A/(2*4^D) by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt (2*B)
  obtain ⟨k,hk⟩ := (he.and ((eventually_ge_atTop K).and ((eventually_ge_atTop N).and (eventually_ge_atTop 1)))).exists
  obtain ⟨hexp,hKk,hNk,h1k⟩ := hk
  have hk1 : 1 ≤ (k:ℝ) := by exact_mod_cast h1k
  have hkpos : 0<(k:ℝ) := by linarith
  have hB' : 2*B ≤ (k:ℝ) := hK.le.trans (by exact_mod_cast hKk)
  let R := 1/(k:ℝ)^2
  have hR : 0<R := by dsimp [R]; positivity
  have hR1 : R≤1 := by dsimp [R]; rw [div_le_one (by positivity)]; nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hN : N ≤ k^5 := hNk.trans (Nat.le_self_pow (by decide : 5≠0) k)
  let := NeZero.mk (pow_ne_zero 5 (show k ≠ 0 by omega))
  refine ⟨k^5,hN,nearest o (n := k^5) R,nearest_symm o R,nearest_lipschitz o R,R/8,by positivity,?_⟩
  have hmass : (k^5:ℕ)*μ.real (ball o R) ≤ 1/2 := by
    push_cast
    calc _ ≤ (k:ℝ)^5*(B*R^3) := mul_le_mul_of_nonneg_left (hcap R hR hR1).2 (by positivity)
         _ = B/k := by dsimp [R]; field_simp
         _ ≤ _ := by rw [div_le_div_iff₀ hkpos (by norm_num)]; linarith
  apply lt_of_lt_of_le _ (nearest_tail μ o hR hmass)
  apply lt_of_lt_of_le _ (hcap (R/4) (by positivity) (by linarith)).1
  have scale : -c*(k^5:ℕ)*(R/8)^2 = -(c/64)*k := by push_cast; dsimp [R]; field_simp; ring
  rw [scale]
  have hr : A*(R/4)^D = (A/4^D)/(k:ℝ)^(2*D) := by
    dsimp [R]; rw [div_pow,one_div_pow,←pow_mul]; ring
  rw [hr,lt_div_iff₀ (by positivity)]
  rw [lt_div_iff₀ (by positivity)] at hexp
  rw [lt_div_iff₀ (by positivity)]
  nlinarith only [hexp]
end OMA.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory Set Metric Finset
open scoped Pointwise ENNReal NNReal
private noncomputable def pole (d : ℕ) : Sphere d :=
  ⟨PiLp.single 2 0 1,by simp⟩
private noncomputable def ballVol (d : ℕ) : ℝ := (volume : Measure (Ambient d)).real (ball 0 1)
private lemma vol_pos (d : ℕ) : 0 < ballVol d := by
  exact lt_of_le_of_ne measureReal_nonneg (Ne.symm ((measureReal_ne_zero_iff (measure_ball_lt_top.ne)).mpr
    (isOpen_ball.measure_ne_zero _ (nonempty_ball.mpr zero_lt_one))))
private lemma surface_norm (d : ℕ) (s : Set (Sphere d)) :
    (surface d).real s = (volume : Measure (Ambient d)).toSphere.real s / ((d+1:ℝ)*ballVol d) := by
  rw [surface,Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hu := (volume : Measure (Ambient d)).toSphere_real_apply_univ
  simp only [finrank_euclideanSpace_fin,Nat.cast_add,Nat.cast_one] at hu
  rw [←Measure.real,hu]
  change _ = (volume.toSphere s).toReal / ((d+1:ℝ)*volume.real (ball (0:Ambient d) 1))
  ring
private instance surface_prob (d : ℕ) : IsProbabilityMeasure (surface d) := by
  apply isProbabilityMeasure_iff_real.mpr
  rw [surface_norm,Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin,Nat.cast_add,Nat.cast_one]
  have h := vol_pos d
  change ((d+1:ℝ)*ballVol d)/_ = 1
  exact div_self (by positivity)
private lemma lower_cap (d : ℕ) (r : ℝ) (hr : 0 < r) (h1 : r ≤ 1) :
    (1/4:ℝ)^(d+1)*r^(d+1) ≤ (surface d).real (ball (pole d) r) := by
  have hb := (volume : Measure (Ambient d)).toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball hr (pole d)
  have hv := vol_pos d
  rw [surface_norm,le_div_iff₀ (by positivity)]
  simp only [finrank_euclideanSpace_fin] at hb
  unfold Measure.toSphereBallBound at hb
  rw [if_pos ⟨by omega,hr⟩,min_eq_left (show r.toNNReal ≤ 2 by
    exact_mod_cast (show (r.toNNReal:ℝ) ≤ (2:ℝ) by rw [Real.coe_toNNReal _ hr.le]; linarith))] at hb
  simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,Real.coe_toNNReal _ hr.le,
    Nat.cast_add,Nat.cast_one] at hb
  change (1/4:ℝ)^(d+1)*r^(d+1)*((d+1:ℝ)*ballVol d) ≤ _
  convert hb using 1
  unfold ballVol
  push_cast
  simp only [div_pow,one_pow]
  ring
private def slab {d : ℕ} (r : ℝ) (i : Fin (d+1)) : Set ℝ :=
  if i=0 then Icc (-1) 1 else Icc (-r) r
private lemma coord_box {d : ℕ} (r : ℝ) :
    Ioo (0:ℝ) 1 • (Subtype.val '' ball (pole d) r) ⊆
      (WithLp.ofLp ⁻¹' (Set.univ.pi (slab (d := d) r))) := by
  rintro x ⟨q,hq,_,⟨v,hv,rfl⟩,rfl⟩
  intro i _
  have vn : ‖v.val‖ = 1 := by simp
  have hcoord := (PiLp.norm_apply_le v.val i).trans_eq vn
  have hm : |q*v.val i| ≤ |v.val i| := by
    rw [abs_mul,abs_of_pos hq.1]
    nlinarith [mul_nonneg (abs_nonneg (v.val i)) (sub_nonneg.mpr hq.2.le)]
  change q*v.val i ∈ slab r i
  by_cases hi : i=0
  · rw [slab,if_pos hi]
    exact abs_le.mp (hm.trans hcoord)
  · rw [slab,if_neg hi]
    have hg := PiLp.dist_apply_le v.val (pole d).val i
    have hd : dist v.val (pole d).val < r := hv
    have hp : (pole d).val i = 0 := PiLp.single_eq_of_ne _ hi _
    rw [hp,dist_zero_right] at hg
    exact abs_le.mp (hm.trans (hg.trans hd.le))
private lemma box_volume (d : ℕ) (r : ℝ) (hr : 0 < r) :
    (volume : Measure (Ambient d)).real (WithLp.ofLp ⁻¹' (Set.univ.pi (slab (d := d) r))) =
      2*(2*r)^d := by
  have hs : MeasurableSet (Set.univ.pi (slab (d := d) r)) :=
    MeasurableSet.univ_pi fun i => by unfold slab; split <;> measurability
  rw [Measure.real,(PiLp.volume_preserving_ofLp (Fin (d+1))).measure_preimage hs.nullMeasurableSet,
    volume_pi_pi,ENNReal.toReal_prod,←Finset.mul_prod_erase _ _ (mem_univ (0 : Fin (d+1)))]
  have hf (i : Fin (d+1)) (hi : i ≠ 0) : (volume (slab r i)).toReal = 2*r := by
    rw [slab,if_neg hi,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith)]; ring
  rw [show (volume (slab r (0 : Fin (d+1)))).toReal = 2 by simp [slab,Real.volume_Icc]; norm_num]
  congr 1
  calc _ = ∏ _ ∈ (Finset.univ.erase (0 : Fin (d+1))), (2*r) :=
          Finset.prod_congr rfl (fun i hi => hf i (Finset.mem_erase.mp hi).1)
       _ = _ := by simp
private lemma upper_cap (d : ℕ) (hd : 3 ≤ d) (r : ℝ) (hr : 0<r) (h1 : r ≤ 1) :
    (surface d).real (ball (pole d) r) ≤ (2^(d+1)/ballVol d)*r^3 := by
  have hb : 0 < (volume : Measure (Ambient d)).real (WithLp.ofLp ⁻¹' Set.univ.pi (slab (d := d) r)) := by
    rw [box_volume d r hr]; positivity
  have h := measureReal_mono (μ := (volume : Measure (Ambient d))) (coord_box (d := d) r)
    (ENNReal.toReal_pos_iff.mp hb).2.ne
  have hv := vol_pos d
  rw [surface_norm,Measure.real,Measure.toSphere_apply' _ measurableSet_ball,ENNReal.toReal_mul,
    finrank_euclideanSpace_fin,ENNReal.toReal_natCast,Nat.cast_add,Nat.cast_one,←Measure.real]
  rw [box_volume d r hr] at h
  rw [div_le_iff₀ (by positivity)]
  have hp := pow_le_pow_of_le_one hr.le h1 hd
  have hA : (2:ℝ)^(d+1)*r^d ≤ 2^(d+1)*r^3 := by gcongr
  calc _ ≤ (d+1:ℝ)*(2*(2*r)^d) := mul_le_mul_of_nonneg_left h (by positivity)
       _ = (d+1:ℝ)*(2^(d+1)*r^d) := by rw [mul_pow,pow_succ];ring
       _ ≤ (d+1:ℝ)*(2^(d+1)*r^3) := by gcongr
       _ = _ := by field_simp
end OMA.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory Finset Set Metric
private noncomputable def freq {X : Type*} {n : ℕ} (x : Fin n → X) (S : Set X) : ℝ := by
  classical exact ((Finset.univ.filter (fun i => x i ∈ S)).card:ℝ)/n
private def near {X : Type*} [MetricSpace X] (S : Finset X) (a : ℝ) : Set X :=
  ⋃ i : S, ball (i:X) a
private lemma open_near {X : Type*} [MetricSpace X] (S : Finset X) (a : ℝ) : IsOpen (near S a) :=
  isOpen_iUnion fun _ => isOpen_ball
private lemma closure_near {X : Type*} [MetricSpace X] (S : Finset X) {a : ℝ} (ha : 0<a) :
    closure (near S a) ⊆ near S (2*a) := by
  unfold near
  rw [closure_iUnion_of_finite]
  apply Set.iUnion_mono
  intro i
  exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
private lemma connected_margin {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [ConnectedSpace X] (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {U V : Set X} (hV : IsOpen V) (hN : U.Nonempty)
    (hUV : closure U ⊆ V) (hfull : V ≠ Set.univ) : μ.real U < μ.real V := by
  have hw : (V \ closure U).Nonempty := by
    by_contra! h
    have he : V=closure U := Set.Subset.antisymm (fun v hv => by by_contra hnc; exact (Set.notMem_empty v) (h ▸ (show v ∈ V \ closure U from ⟨hv,hnc⟩))) hUV
    have hc : IsClopen V := ⟨he ▸ isClosed_closure,hV⟩
    rcases isClopen_iff.mp hc with hm|hm
    · exact (hN.mono (subset_closure.trans hUV)).ne_empty hm
    · exact hfull hm
  have hwo : IsOpen (V \ closure U) := hV.sdiff isClosed_closure
  have hpos : 0 < μ.real (V \ closure U) := lt_of_le_of_ne measureReal_nonneg
    (Ne.symm ((measureReal_ne_zero_iff (measure_ne_top _ _)).mpr (hwo.measure_ne_zero μ hw)))
  have hd : Disjoint U (V \ closure U) := Set.disjoint_left.mpr (fun _ h₁ h₂ => h₂.2 (subset_closure h₁))
  have hl : μ.real (U ∪ (V \ closure U)) ≤ μ.real V := measureReal_mono (μ := μ) (Set.union_subset (subset_closure.trans hUV) Set.sdiff_subset)
  rw [measureReal_union hd hwo.measurableSet] at hl
  linarith
private lemma test_sets {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [ConnectedSpace X] (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (a : ℝ) (ha : 0<a) : ∃ (tests : Finset (Set X)) (η : ℝ),
      0<η ∧ (∀ s ∈ tests, MeasurableSet s) ∧ ∀ n : ℕ, 0<n → ∀ x y : Fin n → X,
      (∀ s ∈ tests, |freq x s-μ.real s|<η) → (∀ s ∈ tests, |freq y s-μ.real s|<η) →
      ∃ π : Equiv.Perm (Fin n), dist x (y ∘ π) ≤ 3*a := by
  classical
  obtain ⟨T,_,hfin,hcov⟩ := finite_cover_balls_of_compact (X := X) isCompact_univ ha
  let t := hfin.toFinset
  have cover (x : X) : ∃ v ∈ t, dist x v < a := by
    obtain ⟨v,hv⟩ := mem_iUnion.mp (hcov (Set.mem_univ x))
    obtain ⟨hvT,hx⟩ := mem_iUnion.mp hv
    exact ⟨v,hfin.mem_toFinset.mpr hvT,hx⟩
  choose site hs hdist using cover
  let gaps (s : Finset X) : ℝ :=
    if s.Nonempty ∧ near s (2*a) ≠ Set.univ then (μ.real (near s (2*a))-μ.real (near s a))/3 else 1
  have hg (s : Finset X) : 0<gaps s := by
    unfold gaps
    split_ifs with h
    · obtain ⟨v,hv⟩ := h.1
      have hm : (near s a).Nonempty := ⟨v,mem_iUnion.mpr ⟨⟨v,hv⟩,mem_ball_self ha⟩⟩
      have := connected_margin μ (open_near _ _) hm (closure_near s ha) h.2
      positivity
    · norm_num
  have hp : t.powerset.Nonempty := ⟨∅,by simp⟩
  let η := t.powerset.inf' hp gaps
  let tests := t.powerset.image (fun s => near s a) ∪ t.powerset.image (fun s => near s (2*a))
  have hpos : 0<η := (Finset.lt_inf'_iff hp).mpr (fun s _ => hg s)
  refine ⟨tests,η,hpos,?_,?_⟩
  · intro s h
    rcases Finset.mem_union.mp h with h|h <;> obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp h <;> exact (open_near _ _).measurableSet
  · intro n hn x y hx hy
    let rel (i j : Fin n) := dist (x i) (y j) < 3*a
    have hall (A : Finset (Fin n)) : A.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ A, rel i j)).card := by
      by_cases hnA : A.Nonempty
      · let S := A.image (fun i => site (x i))
        have hS : S ⊆ t := by
          intro v hv; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv; exact hs _
        have hS' : S ∈ t.powerset := Finset.mem_powerset.mpr hS
        have hU : near S a ∈ tests := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨S,hS',rfl⟩)
        have hV : near S (2*a) ∈ tests := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S,hS',rfl⟩)
        have hAC : A ⊆ Finset.univ.filter (fun i => x i ∈ near S a) := by
          intro i hi
          exact Finset.mem_filter.mpr ⟨mem_univ _,mem_iUnion.mpr ⟨⟨_,Finset.mem_image_of_mem _ hi⟩,hdist _⟩⟩
        have hBN : (Finset.univ.filter (fun j => y j ∈ near S (2*a))) ⊆
            Finset.univ.filter (fun j => ∃ i ∈ A, rel i j) := by
          intro j hj
          obtain ⟨⟨v,hv⟩,hd⟩ := mem_iUnion.mp (Finset.mem_filter.mp hj).2
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
          change dist (y j) (site (x i)) < 2*a at hd
          refine Finset.mem_filter.mpr ⟨mem_univ _,i,hi,?_⟩
          change dist (x i) (y j) < 3*a
          linarith [dist_triangle_right (x i) (y j) (site (x i)),hdist (x i)]
        apply le_trans _ (Finset.card_le_card hBN)
        by_cases hfull : near S (2*a)=Set.univ
        · simpa [hfull] using Finset.card_le_univ A
        · apply (Finset.card_le_card hAC).trans
          have hη : η ≤ gaps S := Finset.inf'_le _ hS'
          dsimp only [gaps] at hη
          rw [if_pos ⟨hnA.image _,hfull⟩] at hη
          have hu := (abs_lt.mp (hx _ hU)).2
          have hv := (abs_lt.mp (hy _ hV)).1
          have hf : freq x (near S a) ≤ freq y (near S (2*a)) := by linarith
          unfold freq at hf
          have hnr : 0<(n:ℝ) := by exact_mod_cast hn
          exact_mod_cast (div_le_div_iff_of_pos_right hnr).mp hf
      · simp [Finset.not_nonempty_iff_eq_empty.mp hnA]
    obtain ⟨g,hg,hrel⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp (fun A => by
      convert! hall A using 1
      congr 1
      ext j
      simp)
    let π := Equiv.ofBijective g ((Finite.injective_iff_bijective).mp hg)
    refine ⟨π,(dist_pi_le_iff (by positivity)).mpr (fun i => (hrel i).le)⟩
end OMA.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal
private lemma freq_sum {X : Type*} {n : ℕ} (x : Fin n → X) (S : Set X) :
    freq x S = (∑ i, S.indicator (fun _ => (1:ℝ)) (x i))/n := by
  classical
  simp only [freq,Set.indicator,Finset.sum_boole]
private lemma freq_meas {X : Type*} [MeasurableSpace X] (n : ℕ) {S : Set X} (hS : MeasurableSet S) :
    Measurable (fun x : Fin n → X => freq x S) := by
  simp_rw [freq_sum]
  exact (Finset.measurable_fun_sum _ fun i _ => (measurable_const.indicator hS).comp (measurable_pi_apply i)).div_const _
private lemma freq_tail {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0<n) (S : Set X) (hS : MeasurableSet S) (a : ℝ) (ha : 0<a) :
    (samples μ n).real {x | a ≤ |freq x S-μ.real S|} ≤ 2*Real.exp (-(2*a^2)*n) := by
  classical
  let W := S.indicator (fun _ => (1:ℝ))
  let Z (i : Fin n) (x : Fin n → X) := W (x i)-μ.real S
  let ρ := samples μ n
  have hm : Measurable W := measurable_const.indicator hS
  have hv (i : Fin n) : (∫ x : Fin n → X, W (x i) ∂ρ)=μ.real S :=
    (integral_comp_eval hm.aestronglyMeasurable).trans (integral_indicator_one hS)
  have hsg (i : Fin n) : HasSubgaussianMGF (Z i) ((1:ℝ≥0)/4) ρ := by
    have hmem : ∀ᵐ x : Fin n → X ∂ρ, W (x i) ∈ Icc (0:ℝ) 1 := ae_of_all _ fun x => by
      by_cases h : x i ∈ S <;> simp [W,h]
    have hb := hasSubgaussianMGF_of_mem_Icc ((hm.comp (measurable_pi_apply i)).aemeasurable) hmem
    simp only [Function.comp_apply,hv] at hb
    convert! hb using 1
    norm_num
  have hi : iIndepFun Z ρ := iIndepFun_pi (X := fun _ : Fin n => fun z : X => W z-μ.real S)
    (fun _ => (hm.sub measurable_const).aemeasurable)
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hi (s := univ) (fun i _ => hsg i)
  let g (x : Fin n → X) := ∑ i,Z i x
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hident (x : Fin n → X) : g x=n*(freq x S-μ.real S) := by
    rw [freq_sum]
    simp only [g,Z,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,W]
    field_simp
  have hu := hs.measure_ge_le (show 0 ≤ n*a by positivity)
  have hl := hs.neg.measure_ge_le (show 0 ≤ n*a by positivity)
  have hsub : {x : Fin n → X | a ≤ |freq x S-μ.real S|} ⊆
      {x | n*a ≤ g x} ∪ {x | n*a ≤ -g x} := by
    intro x hx
    change a ≤ |freq x S-μ.real S| at hx
    rcases le_abs.mp hx with h|h
    · exact Or.inl ((mul_le_mul_of_nonneg_left h hn'.le).trans_eq (hident x).symm)
    · right
      change n*a ≤ -g x
      rw [hident]
      nlinarith [mul_le_mul_of_nonneg_left h hn'.le]
  have hp : -(n*a)^2/(2*((∑ _ : Fin n, (1:ℝ≥0)/4):ℝ≥0)) = -(2*a^2)*n := by
    simp [nsmul_eq_mul]
    field_simp
    ring
  rw [hp] at hu hl
  calc _ ≤ _ := measureReal_mono hsub
       _ ≤ _ := measureReal_union_le _ _
       _ ≤ _ := by
        change ρ.real {x | n*a ≤ g x}+ρ.real {x | n*a ≤ -g x} ≤ _
        change ρ.real {x | n*a ≤ g x} ≤ _ at hu
        change ρ.real {x | n*a ≤ -g x} ≤ _ at hl
        linarith
private def good {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ)
    (tests : Finset (Set X)) (a : ℝ) : Set (Fin n → X) :=
  {x | ∀ s ∈ tests, |freq x s-μ.real s| < a}
private lemma good_meas {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ)
    {tests : Finset (Set X)} (h : ∀ s ∈ tests, MeasurableSet s) (a : ℝ) : MeasurableSet (good μ n tests a) := by
  have he : good μ n tests a = ⋂ i : tests, {x | |freq x i.val-μ.real i.val| < a} := by
    ext x; simp [good]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_lt ((freq_meas n (h i i.property)).sub measurable_const).abs measurable_const)
private lemma good_prob {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0<n) {tests : Finset (Set X)} (h : ∀ s ∈ tests, MeasurableSet s) (a : ℝ) (ha : 0<a) :
    (samples μ n).real (good μ n tests a)ᶜ ≤ (2*tests.card)*Real.exp (-(2*a^2)*n) := by
  classical
  have he : (good μ n tests a)ᶜ = ⋃ s ∈ tests, {x | a ≤ |freq x s-μ.real s|} := by ext x; simp [good]
  rw [he]
  calc _ ≤ _ := measureReal_biUnion_finset_le tests _
       _ ≤ ∑ _ ∈ tests, 2*Real.exp (-(2*a^2)*n) := Finset.sum_le_sum fun s hs => freq_tail μ n hn s (h s hs) a ha
       _ = _ := by simp [nsmul_eq_mul]; ring
end OMA.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory Set Finset Metric Filter
open scoped Topology
private lemma exp_vanish (K c : ℝ) (hc : 0 < c) : Tendsto (fun n : ℕ => K*Real.exp (-c*n)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds (x := K)).mul h
private lemma compact_concentrates {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [ConnectedSpace X] (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] :
    concentrates μ := by
  classical
  intro r hr
  let a := r/8
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨tests,η,hη,hm,hmatches⟩ := test_sets μ a ha
  let K : ℝ := 2*(tests.card+1)
  let c := 2*η^2
  let D := Metric.diam (Set.univ : Set X)+1
  have hc : 0<c := by dsimp [c]; positivity
  have hD : 0<D := by dsimp [D]; linarith [Metric.diam_nonneg (s := (Set.univ : Set X))]
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,c,hK,hc,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ),(exp_vanish K c hc).eventually_lt_const
    (show 0 < min 1 (a/D) by positivity)] with n hn hsmall
  intro f hsym hLip
  let G := good μ n tests η
  let ρ := samples μ n
  have hmG : MeasurableSet G := good_meas μ n hm η
  have hbad : ρ.real Gᶜ ≤ K*Real.exp (-c*n) := by
    apply (good_prob μ n hn hm η hη).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp [K]; linarith
  have hGn : G.Nonempty := by
    by_contra! he
    have h1 : ρ.real Gᶜ = 1 := by simp [he]
    linarith [hsmall.trans_le (min_le_left ..)]
  obtain ⟨b,hb⟩ := hGn
  have hgood (x : Fin n → X) (hx : x ∈ G) : |f x-f b| ≤ 3*a := by
    obtain ⟨π,hπ⟩ := hmatches n hn x b hx hb
    have hl := hLip.dist_le_mul x (b ∘ π)
    simpa [Real.dist_eq,hsym π b] using hl.trans (show (1:ℝ)*dist x (b ∘ π) ≤ 3*a by simpa using hπ)
  have hosc (x : Fin n → X) : |f x-f b| ≤ D := by
    have hxy : dist x b ≤ D := (dist_pi_le_iff hD.le).mpr fun i =>
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ (x i)) (mem_univ (b i))).trans (by dsimp [D]; linarith)
    simpa [Real.dist_eq] using (hLip.dist_le_mul x b).trans (show (1:ℝ)*dist x b ≤ D by simpa using hxy)
  have hfi : Integrable f ρ := .of_bound hLip.continuous.aestronglyMeasurable (D+|f b|)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; linarith [abs_sub_abs_le_abs_sub (f x) (f b),hosc x])
  have hrhs : Integrable (fun x : Fin n → X => (3*a)+Gᶜ.indicator (fun _ => D) x) ρ :=
    (integrable_const _).add ((integrable_const _).indicator hmG.compl)
  have hmean : |(∫ x,f x ∂ρ)-f b| ≤ 3*a+D*ρ.real Gᶜ := calc
    _ = |∫ x,f x-f b ∂ρ| := by rw [integral_sub hfi (integrable_const _)]; simp
    _ ≤ ∫ x,|f x-f b| ∂ρ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ρ) (fun x => f x-f b)
    _ ≤ ∫ x,3*a+Gᶜ.indicator (fun _ => D) x ∂ρ := by
      refine integral_mono ((hfi.sub (integrable_const _)).abs) hrhs (fun x => ?_)
      by_cases hx : x∈G
      · rw [indicator_of_notMem (show x∉Gᶜ from fun h => h hx),add_zero]
        exact hgood x hx
      · rw [indicator_of_mem (show x∈Gᶜ from hx)]
        linarith [hosc x]
    _ = _ := by rw [integral_add (integrable_const _) ((integrable_const _).indicator hmG.compl),integral_indicator hmG.compl,setIntegral_const]; simp [smul_eq_mul,mul_comm]
  apply le_trans _ hbad
  refine measureReal_mono ?_
  intro x hx hg
  have ht : r < |f x-(∫ z,f z ∂ρ)| := hx
  have hp : D*ρ.real Gᶜ < a := by
    have := (lt_div_iff₀ hD).mp (hbad.trans_lt (hsmall.trans_le (min_le_right ..)))
    linarith
  have htri := abs_sub_le (f x) (f b) (∫ z,f z ∂ρ)
  rw [abs_sub_comm (f b)] at htri
  have hxg := hgood x hg
  dsimp [a] at *
  linarith
end OMA.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory Set Metric Finset Filter
open scoped Topology ENNReal NNReal
private lemma connected_of_concentrates {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] (h : concentrates μ) :
    ConnectedSpace X := by
  classical
  refine connectedSpace_iff_clopen.mpr ⟨nonempty_of_isProbabilityMeasure μ,?_⟩
  intro U hU
  by_contra! hn
  have h₁ : 0 < μ.real U := lt_of_le_of_ne measureReal_nonneg <| Ne.symm <|
    (measureReal_ne_zero_iff (measure_ne_top _ _)).mpr (hU.isOpen.measure_ne_zero _ hn.1)
  have h₂ : 0 < μ.real Uᶜ := lt_of_le_of_ne measureReal_nonneg <| Ne.symm <|
    (measureReal_ne_zero_iff (measure_ne_top _ _)).mpr (hU.compl.isOpen.measure_ne_zero _ (Set.nonempty_compl.mpr hn.2))
  rw [measureReal_compl hU.isOpen.measurableSet,probReal_univ] at h₂
  obtain ⟨s,hs,hsep⟩ := Metric.exists_pos_forall_lt_edist hU.isClosed.isCompact hU.compl.isClosed disjoint_compl_right
  let d : ℝ := s
  have hd : 0<d := hs
  have hsep' (x : X) (hx : x∈U) (y : X) (hy : y∉U) : d < dist x y := by
    change (s:ℝ) < ↑(nndist x y)
    have he := hsep x hx y hy
    rw [edist_nndist, ENNReal.coe_lt_coe] at he
    exact_mod_cast he
  let χ (x : X) : ℝ := if x ∈ U then 1 else -1
  let F (n : ℕ) (x : Fin n → X) := (d/2)*∏ i,χ (x i)
  have hc₀ (x : X) : |χ x|=1 := by by_cases hx : x∈U <;> simp [χ,hx]
  have hF_abs (n : ℕ) (x : Fin n → X) : |F n x|=d/2 := by
    simp [F,abs_mul,Finset.abs_prod,hc₀,abs_of_nonneg (show 0≤d/2 by positivity)]
  have hF_sym (n : ℕ) : symmetric (F n) := by
    intro π x
    unfold F
    congr 1
    exact Equiv.prod_comp π (fun i => χ (x i))
  have hF_lip (n : ℕ) : LipschitzWith 1 (F n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul,Real.dist_eq]
    by_cases hm : dist x y < d
    · have hm' (i : Fin n) : χ (x i)=χ (y i) := by
        have ht := (dist_le_pi_dist x y i).trans_lt hm
        by_cases hx : x i ∈ U <;> by_cases hy : y i ∈ U
        · simp [χ,hx,hy]
        · linarith [hsep' _ hx _ hy]
        · linarith [hsep' _ hy _ hx,dist_comm (x i) (y i)]
        · simp [χ,hx,hy]
      have he : F n x=F n y := by unfold F; simp only [hm']
      rw [he,sub_self,abs_zero]; exact dist_nonneg
    · have ht := abs_sub (F n x) (F n y)
      rw [hF_abs,hF_abs] at ht
      linarith
  have hw : (∫ x,χ x ∂μ)=2*μ.real U-1 := by
    have he : χ = fun x => 2*(U.indicator (fun _ => (1:ℝ)) x)-1 := by
      funext x; by_cases hx : x ∈ U <;> norm_num [χ,hx]
    rw [he,integral_sub (((integrable_const _).indicator hU.isOpen.measurableSet).const_mul 2) (integrable_const _),
      integral_const_mul]
    change 2*(∫ x,U.indicator (1:X → ℝ) x ∂μ) - _ = _
    rw [integral_indicator_one hU.isOpen.measurableSet]
    simp
  let b := 2*μ.real U-1
  have hb : |b|<1 := abs_lt.mpr ⟨by dsimp [b]; linarith,by dsimp [b]; linarith⟩
  have hex (n : ℕ) : (∫ x,F n x ∂samples μ n) = d/2*b^n := by
    simp only [F,integral_const_mul,samples,integral_fintype_prod_eq_pow,Fintype.card_fin,hw,b]
  obtain ⟨K,c,_,hc,hcon⟩ := h (d/8) (by positivity)
  have hpow := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hb).abs
  obtain ⟨n,hn,hp,hK⟩ := (hcon.and ((hpow.eventually_lt_const (show |(0:ℝ)|<1/2 by norm_num)).and
    ((exp_vanish K c hc).eventually_lt_const zero_lt_one))).exists
  have htail := hn (F n) (hF_sym n) (hF_lip n)
  have hall : {x : Fin n → X | d/8 < |F n x-∫ z,F n z ∂samples μ n|} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change d/8 < |F n x-∫ z,F n z ∂samples μ n|
    rw [hex]
    have hh := abs_sub_abs_le_abs_sub (F n x) (d/2*b^n)
    rw [hF_abs,abs_mul,abs_of_pos (show 0<d/2 by positivity)] at hh
    change |b^n|<1/2 at hp
    nlinarith [mul_lt_mul_of_pos_left hp hd]
  rw [tail,hall,probReal_univ] at htail
  exact (not_lt_of_ge htail) hK
end OMA.S_mo_279344
namespace OMA.S_mo_279344
open MeasureTheory Set Metric
private instance surface_open_pos (d : ℕ) : (surface d).IsOpenPosMeasure where
  open_pos U hU hn := by
    simp only [surface,Measure.smul_apply,smul_eq_mul]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hU.measure_ne_zero _ hn)
private lemma sphere_conc (d : ℕ) (hd : 1 ≤ d) : concentrates (surface d) := by
  have hr : 1 < Module.rank ℝ (Ambient d) := Module.one_lt_rank_of_one_lt_finrank (by
    rw [finrank_euclideanSpace_fin]; omega)
  let := isConnected_iff_connectedSpace.mp (isConnected_sphere hr (0:Ambient d) zero_le_one)
  exact compact_concentrates _
private lemma sphere_bad (d : ℕ) (hd : 3 ≤ d) : violations (surface d) := by
  apply obstruction (surface d) (pole d) (d+1) ((1/4:ℝ)^(d+1)) (2^(d+1)/ballVol d) (by positivity)
    (div_pos (by positivity) (vol_pos d))
  exact fun r hr h1 => ⟨lower_cap d r hr h1,upper_cap d hd r hr h1⟩
end OMA.S_mo_279344
open OMA.S_mo_279344
theorem OMA.solution : type_of% @OMA.S_mo_279344.main := by
  refine ⟨sphere_bad,fun _ _ _ _ => obstruction,?_,sphere_conc⟩
  intro X _ _ _ _ μ _ _
  exact ⟨connected_of_concentrates μ,fun _ => compact_concentrates μ⟩
