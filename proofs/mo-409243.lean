import OMAStatements.S_mo_409243

namespace OMA.S_mo_409243
open MeasureTheory Set Finset
private instance : IsProbabilityMeasure U := ⟨by simp [U,Measure.restrict_apply,Real.volume_Ioo]⟩
private instance : NullSingletonClass U := by unfold U; infer_instance
private instance (s : ℕ) : IsProbabilityMeasure (law s) := by unfold law; infer_instance
private lemma u_io {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : U.real (Iio x)=x := by
  rw [U,measureReal_restrict_apply measurableSet_Iio,Iio_inter_Ioo,min_eq_left hx.2,Real.volume_real_Ioo]
  simp [hx.1]
private lemma u_hi {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : U.real (Ici x)=1-x := by
  simpa [u_io hx] using (measureReal_compl (μ := U) measurableSet_Iio (s := Iio x))
private lemma u_oi {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : U.real (Ioi x)=1-x := by
  have he : Ioi x =ᵐ[U] Ici x := Ioi_ae_eq_Ici
  exact (congrArg ENNReal.toReal (measure_congr he)).trans (u_hi hx)
private lemma u_support : ∀ᵐ x ∂U, x ∈ Icc (0:ℝ) 1 :=
  (ae_restrict_mem measurableSet_Ioo).mono (fun _ hx => ⟨hx.1.le,hx.2.le⟩)
private lemma u_integral (f : ℝ → ℝ) : (∫ x,f x ∂U) = ∫ x in (0:ℝ)..1,f x := by
  rw [U,intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_congr_set Ioo_ae_eq_Ioc
private lemma fub {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure ν] (S : Set (α × β)) (h : MeasurableSet S) :
    (μ.prod ν).real S = ∫ x,ν.real ((Prod.mk x) ⁻¹' S) ∂μ := by
  rw [measureReal_def,Measure.prod_apply h]
  exact (integral_toReal (measurable_measure_prodMk_left h).aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)).symm
private def spare (s : ℕ) (t : ℝ) : Set (Fin s → ℝ×ℝ) := {r | ∀ i,min (r i).1 (r i).2 < t}
private lemma spare_prob (s : ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    (Measure.pi fun _ : Fin s => U.prod U).real (spare s x)=(1-(1-x)^2)^s := by
  let M := {w : ℝ×ℝ | min w.1 w.2 < x}
  have hM : M = (Ici x ×ˢ Ici x)ᶜ := by
    ext p
    change min p.1 p.2 < x ↔ ¬(x ≤ p.1 ∧ x ≤ p.2)
    rw [←le_min_iff,not_le]
  have hval : (U.prod U).real M=1-(1-x)^2 := by
    rw [hM,measureReal_compl (measurableSet_Ici.prod measurableSet_Ici),measureReal_prod_prod,u_hi hx]
    simp [pow_two]
  have hs : spare s x = Set.univ.pi (fun _ : Fin s => M) := by ext y; simp [spare,M]
  rw [hs]
  simp [measureReal_def,Measure.pi_pi] at hval ⊢
  simpa [ENNReal.toReal_pow] using congrArg (fun r : ℝ => r^s) hval
private lemma measurable_miss {α : Type*} [MeasurableSpace α] {s : ℕ} (g : α → Sample s)
    (t : α → ℝ) (hg : Measurable g) (ht : Measurable t) : MeasurableSet {a | miss (g a) (t a)} := by
  unfold miss
  refine (measurableSet_lt (by fun_prop) ht).inter ((measurableSet_lt (by fun_prop) ht).inter ?_)
  rw [show (fun a => ∀ i, min ((g a).2.2 i).1 ((g a).2.2 i).2 < t a) = (⋂ i, {a | min ((g a).2.2 i).1 ((g a).2.2 i).2 < t a} : Set α) by
    ext a
    change (∀ i, min ((g a).2.2 i).1 ((g a).2.2 i).2 < t a) ↔ a ∈ ⋂ i, {a | min ((g a).2.2 i).1 ((g a).2.2 i).2 < t a}
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]]
  exact MeasurableSet.iInter (fun i : Fin s => measurableSet_lt (show Measurable (fun a => min ((g a).2.2 i).1 ((g a).2.2 i).2) by fun_prop) ht)
end OMA.S_mo_409243

namespace OMA.S_mo_409243
open MeasureTheory Set
private abbrev Rest (s : ℕ) := (ℝ×ℝ) × (Fin s → ℝ×ℝ)
private noncomputable def rest (s : ℕ) : Measure (Rest s) :=
  (U.prod U).prod (Measure.pi fun _ : Fin s => U.prod U)
private instance (s) : IsProbabilityMeasure (rest s) := by unfold rest; infer_instance
private def flip {s : ℕ} (w : Sample s) : Sample s :=
  ((w.1.2,w.1.1),((w.2.1.2,w.2.1.1),w.2.2))
private lemma flip_pres (s : ℕ) : MeasurePreserving (@flip s) (law s) (law s) :=
  (Measure.measurePreserving_swap (μ := U) (ν := U)).prod ((Measure.measurePreserving_swap (μ := U) (ν := U)).prod
    (MeasurePreserving.id _))
private lemma flip_miss {s} (w : Sample s) (t : ℝ) : miss (flip w) t ↔ miss w t := by
  simp [flip,miss,and_left_comm]
private def failL (s : ℕ) : Set (Sample s) := {w | miss w w.1.1}
private def failR (s : ℕ) : Set (Sample s) := {w | miss w w.1.2}
private lemma mL (s) : MeasurableSet (failL s) := measurable_miss id _ measurable_id (by fun_prop)
private lemma mR (s) : MeasurableSet (failR s) := measurable_miss id _ measurable_id (by fun_prop)
private lemma fail_swap (s) : (law s).real (failR s)=(law s).real (failL s) := by
  have h : failR s=flip ⁻¹' failL s := by ext w; exact (flip_miss w w.1.2).symm
  exact congrArg ENNReal.toReal (h ▸ (flip_pres s).measure_preimage (mL s).nullMeasurableSet)
private lemma iter (s : ℕ) (S : Set (Sample s)) (hS : MeasurableSet S) :
    (law s).real S=∫ x,∫ y,(rest s).real ((Prod.mk (x,y)) ⁻¹' S) ∂U ∂U := by
  change ((U.prod U).prod (rest s)).real S=_
  rw [fub _ _ _ hS]
  apply integral_prod
  apply (integrable_const (μ := U.prod U) (1:ℝ)).mono
  · exact (measurable_measure_prodMk_left hS).ennreal_toReal.aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg,abs_one]
      exact measureReal_le_one
private lemma one_fail (s : ℕ) : (law s).real (failL s) =
    ∫ x in (0:ℝ)..1, x*(1-(1-x)^2)^(s+1) := by
  rw [iter _ _ (mL _),←u_integral]
  apply integral_congr_ae
  filter_upwards [u_support] with x hx
  let G := (1-(1-x)^2)^s
  have hsection (y : ℝ) : (rest s).real (Prod.mk (x,y) ⁻¹' failL s) =
      if y<x then x*G else x*x*G := by
    by_cases hy : y<x
    · have h : Prod.mk (x,y) ⁻¹' failL s = (Iio x ×ˢ Set.univ) ×ˢ spare s x := by
        ext w; simp [failL,miss,hy,spare]
      simp [rest,h,hy,u_io hx,spare_prob s hx,G]
    · have h : Prod.mk (x,y) ⁻¹' failL s = (Iio x ×ˢ Iio x) ×ˢ spare s x := by
        ext w; simp [failL,miss,hy,spare,and_assoc]
      simp [rest,h,hy,u_io hx,spare_prob s hx,G]
  simp_rw [hsection]
  change (∫ y,(Iio x).piecewise (fun _ => x*G) (fun _ => x*x*G) y ∂U) = _
  rw [integral_piecewise measurableSet_Iio (integrable_const _).integrableOn (integrable_const _).integrableOn]
  simp [u_io hx,u_hi hx,G,pow_succ]
  ring
private def tri (s : ℕ) (strict : Bool) : Set (Sample s) :=
  (failL s ∩ failR s) ∩ {w | if strict then w.1.1<w.1.2 else w.1.1 ≤ w.1.2}
private lemma mtri (s : ℕ) (b : Bool) : MeasurableSet (tri s b) := by
  refine ((mL s).inter (mR s)).inter ?_
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
private lemma tri_prob (s : ℕ) (b : Bool) : (law s).real (tri s b) =
    ∫ x in (0:ℝ)..1, (1-x)*x^2*(1-(1-x)^2)^s := by
  rw [iter _ _ (mtri _ _),←u_integral]
  apply integral_congr_ae
  filter_upwards [u_support] with x hx
  let T := if b then Ioi x else Ici x
  let G := x*x*(1-(1-x)^2)^s
  have mT : MeasurableSet T := by dsimp [T]; split <;> measurability
  have ht : U.real T=1-x := by cases b <;> simp [T,u_oi hx,u_hi hx]
  have hsection (y : ℝ) : (rest s).real (Prod.mk (x,y) ⁻¹' tri s b) =
      T.indicator (fun _ => G) y := by
    have hyiff : y ∈ T ↔ (if b then x<y else x ≤ y) := by cases b <;> rfl
    by_cases hy : y∈T
    · have hxy : x ≤ y := by cases b <;> simp [T] at hy <;> linarith
      have hm (w : Rest s) : miss ((x,y),w) x → miss ((x,y),w) y :=
        fun h => ⟨h.1.trans_le hxy,h.2.1.trans_le hxy,fun i => (h.2.2 i).trans_le hxy⟩
      have h : Prod.mk (x,y) ⁻¹' tri s b = (Iio x ×ˢ Iio x) ×ˢ spare s x := by
        ext w
        change ((miss ((x,y),w) x ∧ miss ((x,y),w) y) ∧ (if b then x<y else x ≤ y)) ↔ _
        rw [←hyiff,and_iff_left hy,and_iff_left_of_imp (hm w)]
        simp [miss,not_lt.mpr hxy,spare,and_assoc]
      simp [h,hy,G,rest,u_io hx,spare_prob s hx]
    · have h : Prod.mk (x,y) ⁻¹' tri s b = ∅ := by
        ext w
        change ((_ ∧ _) ∧ (if b then x<y else x ≤ y)) ↔ False
        rw [←hyiff]; simp [hy]
      simp [h,hy]
  simp_rw [hsection]
  rw [integral_indicator_const G mT,ht]
  simp [G,pow_two,mul_assoc]
private lemma two_fail (s : ℕ) : (law s).real (failL s ∩ failR s) =
    2*∫ x in (0:ℝ)..1, (1-x)*x^2*(1-(1-x)^2)^s := by
  let a := tri s false
  let b := flip ⁻¹' tri s true
  have hu : failL s ∩ failR s=a ∪ b := by
    ext w
    change (_ ∧ _) ↔ ((_ ∧ _) ∧ _) ∨ ((_ ∧ _) ∧ _)
    simp [failL,failR,flip,miss]
    grind [le_total (w.1.1) (w.1.2)]
  have hd : Disjoint a b := by
    rw [Set.disjoint_left]
    intro w ha hb
    exact (not_lt_of_ge (show w.1.1 ≤ w.1.2 from ha.2)) (show w.1.2<w.1.1 from hb.2)
  have hb : (law s).real b=(law s).real (tri s true) :=
    congrArg ENNReal.toReal ((flip_pres s).measure_preimage (mtri _ _).nullMeasurableSet)
  rw [hu,measureReal_union hd ((flip_pres s).measurable (mtri s true)),hb]
  change (law s).real (tri s false)+_=_
  rw [tri_prob,tri_prob]
  ring
end OMA.S_mo_409243

namespace OMA.S_mo_409243
open MeasureTheory Set
private lemma int₁ : (∫ x in (0:ℝ)..1,x*(1-(1-x)^2)^(2+1))=93/280 := by
  have h (x : ℝ) : x*(1-(1-x)^2)^(2+1)=8*x^4-12*x^5+6*x^6-x^7 := by ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num [intervalIntegral.integral_const_mul,integral_pow]
private lemma int₂ : 2*(∫ x in (0:ℝ)..1,(1-x)*x^2*(1-(1-x)^2)^2)=47/420 := by
  have h (x : ℝ) : (1-x)*x^2*(1-(1-x)^2)^2=4*x^4-8*x^5+5*x^6-x^7 := by ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num [intervalIntegral.integral_const_mul,integral_pow]
end OMA.S_mo_409243
open OMA.S_mo_409243 MeasureTheory Set in
theorem OMA.solution : type_of% @OMA.S_mo_409243.main := by
  refine ⟨by decide +kernel,by decide +kernel,fun s => ?_,fun s => ?_,?_⟩
  · change (law s).real (failL s)ᶜᶜ=_
    rw [compl_compl]; exact one_fail s
  · change (law s).real ((failL s)ᶜᶜ ∩ (failR s)ᶜᶜ)=_
    rw [compl_compl,compl_compl]; exact two_fail s
  · dsimp only
    change (law 2).real (failL 2)ᶜ=_ ∧ (law 2).real (failR 2)ᶜ=_ ∧
      (law 2).real ((failL 2)ᶜ ∩ (failR 2)ᶜ)=_ ∧ _ < _
    have hL := (one_fail 2).trans int₁
    have hR := (fail_swap 2).trans hL
    have hI := (two_fail 2).trans int₂
    have hU := measureReal_union_add_inter (μ := law 2) (s := failL 2) (mR 2)
    have hBoth : (law 2).real ((failL 2)ᶜ ∩ (failR 2)ᶜ)=47/105 := by
      rw [←compl_union,measureReal_compl ((mL _).union (mR _)),show (law 2).real univ=1 by simp]
      linarith
    have hA : (law 2).real (failL 2)ᶜ=187/280 := by rw [measureReal_compl (mL _),hL]; norm_num
    have hB : (law 2).real (failR 2)ᶜ=187/280 := by rw [measureReal_compl (mR _),hR]; norm_num
    refine ⟨hA,hB,hBoth,?_⟩
    change (law 2).real (failL 2)ᶜ*(law 2).real (failR 2)ᶜ < (law 2).real ((failL 2)ᶜ ∩ (failR 2)ᶜ)
    rw [hA,hB,hBoth]; norm_num
