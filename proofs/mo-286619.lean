import OMAStatements.S_mo_286619

/-! Homothetic subdomains give the lower bound for the negative part.
The translated Minkowski gauge realizes equality by its sublevel volumes. -/

namespace OMA.S_mo_286619
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

noncomputable def hom {n : ℕ} (a : E n) (r : ℝ) (x : E n) : E n :=
  (1-r) • a + r • x

private noncomputable def homEquiv {n : ℕ} (a : E n) (r : ℝ) (hr : 0 < r) : E n ≃ₜ E n :=
  (Homeomorph.smul (Units.mk0 r hr.ne')).trans (Homeomorph.addLeft ((1-r) • a))

lemma hom_isOpen_image {n : ℕ} {P : Set (E n)} (hP : IsOpen P) (a : E n) (r : ℝ) (hr : 0 < r) :
    IsOpen (hom a r '' P) := (homEquiv a r hr).isOpenMap _ hP

lemma hom_measurableSet_image {n : ℕ} {P : Set (E n)} (hP : IsOpen P) (a : E n) (r : ℝ) (hr : 0 < r) :
    MeasurableSet (hom a r '' P) := (hom_isOpen_image hP a r hr).measurableSet

private lemma hom_map {n : ℕ} (a : E n) (r : ℝ) (hr : 0 < r) :
    Measure.map (hom a r) volume = ENNReal.ofReal ((r^n)⁻¹) • volume := by
  change Measure.map ((fun y : E n => (1-r) • a+y) ∘ (fun x : E n => r • x)) volume=_
  have h₁ : Measurable (fun x : E n => r • x) := by fun_prop
  have h₂ : Measurable (fun y : E n => (1-r) • a+y) := by fun_prop
  rw [←Measure.map_map h₂ h₁,
    map_addHaar_smul _ hr.ne',Measure.map_smul,map_add_left_eq_self]
  simp [E,abs_of_pos (inv_pos.mpr (pow_pos hr _))]

private lemma hom_restrict {n : ℕ} (P : Set (E n)) (a : E n) (r : ℝ) (hr : 0 < r) :
    Measure.map (hom a r) (volume.restrict P) =
      ENNReal.ofReal ((r^n)⁻¹) • volume.restrict (hom a r '' P) := by
  let e := (homEquiv a r hr).toMeasurableEquiv
  have h := e.restrict_map volume (e '' P)
  rw [Set.preimage_image_eq _ e.injective] at h
  change (Measure.map (hom a r) volume).restrict (hom a r '' P) = Measure.map (hom a r) (volume.restrict P) at h
  rw [←h,hom_map a r hr,Measure.restrict_smul]

lemma hom_integral {n : ℕ} (P : Set (E n)) (a : E n) (r : ℝ) (hr : 0 < r) (F : E n → ℝ) :
    (∫ x in hom a r '' P, F x) = r^n * ∫ x in P, F (hom a r x) := by
  have h := integral_map_equiv (μ:=volume.restrict P) (homEquiv a r hr).toMeasurableEquiv F
  change (∫ x, F x ∂Measure.map (hom a r) (volume.restrict P)) = ∫ x in P, F (hom a r x) at h
  rw [hom_restrict P a r hr,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),smul_eq_mul] at h
  rw [←h,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),one_mul]

lemma hom_integrable_iff {n : ℕ} (P : Set (E n)) (a : E n) (r : ℝ) (hr : 0 < r) (F : E n → ℝ) :
    IntegrableOn F (hom a r '' P) ↔ IntegrableOn (F ∘ hom a r) P := by
  have h := integrable_map_equiv (μ:=volume.restrict P) (homEquiv a r hr).toMeasurableEquiv F
  change Integrable F (Measure.map (hom a r) (volume.restrict P)) ↔ Integrable (F ∘ hom a r) (volume.restrict P) at h
  rwa [hom_restrict P a r hr,integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top] at h

end OMA.S_mo_286619

namespace OMA.S_mo_286619

lemma gauge_model {n : ℕ} (P : Set (E n)) (ho : IsOpen P) (hc : Convex ℝ P)
    (_hb : Bornology.IsBounded P) (a : E n) (ha : a ∈ P) :
    ∃ G : E n → ℝ, Continuous G ∧ ConvexOn ℝ P G ∧ G a=0 ∧
      (∀ x, 0≤G x) ∧ (∀ x∈P, G x<1) ∧
      (∀ r : ℝ, 0<r → r≤1 → {x | x∈P ∧ G x<r} = hom a r '' P) := by
  let S : Set (E n) := {x | x+a ∈ P}
  have hS : IsOpen S := ho.preimage (continuous_id.add continuous_const)
  have hzero : (0:E n) ∈ S := by simpa [S] using ha
  have hconv : Convex ℝ S := by
    intro x hx y hy u v hu hv huv
    have h := hc (show x+a ∈ P from hx) (show y+a ∈ P from hy) hu hv huv
    have he : u • (x+a)+v • (y+a) = u • x+v • y+a := by
      calc
        _ = u • x+v • y+(u • a+v • a) := by simp only [smul_add]; abel
        _ = _ := by rw [← add_smul,huv,one_smul]
    rwa [he] at h
  have hmem (x : E n) : gauge S (x-a)<1 ↔ x∈P := by
    change x-a ∈ {y | gauge S y<1} ↔ _
    rw [setOfPred_gauge_lt_one_eq_self_of_isOpen hconv hzero hS]
    simp [S]
  refine ⟨fun x => gauge S (x-a), (continuous_gauge hconv (hS.mem_nhds hzero)).comp
    (continuous_id.sub continuous_const), ⟨hc,?_⟩, by simp, fun _ => gauge_nonneg _,
    fun x hx => (hmem x).mpr hx, ?_⟩
  · intro x hx y hy u v hu hv huv
    have he : (u • x + v • y)-a = u • (x-a)+v • (y-a) := by
      rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,huv,one_smul]
    simp only [he]
    simpa only [gauge_smul_of_nonneg hu, gauge_smul_of_nonneg hv] using
      gauge_add_le hconv (absorbent_nhds_zero (hS.mem_nhds hzero)) (u • (x-a)) (v • (y-a))
  · intro r hr hr1
    have diff (y : E n) : hom a r y - a = r • (y-a) := by
      simp only [hom,sub_smul,one_smul,smul_sub]
      abel
    ext x
    constructor
    · rintro ⟨_,hx⟩
      let y := r⁻¹ • (x-a) + a
      have hy : y-a = r⁻¹ • (x-a) := add_sub_cancel_right _ _
      refine ⟨y,(hmem y).mp ?_,?_⟩
      · rw [hy,gauge_smul_of_nonneg (inv_nonneg.mpr hr.le),smul_eq_mul,
          inv_mul_lt_iff₀ hr,mul_one]
        exact hx
      · have he : hom a r y - a = x-a := by rw [diff,hy,smul_inv_smul₀ hr.ne']
        exact sub_left_injective (b := a) he
    · rintro ⟨y,hy,rfl⟩
      refine ⟨hc ha hy (sub_nonneg.mpr hr1) hr.le (by ring),?_⟩
      change gauge S (hom a r y-a) < r
      rw [diff,gauge_smul_of_nonneg hr.le,smul_eq_mul]
      simpa using (mul_lt_mul_of_pos_left ((hmem y).mpr hy) hr)

end OMA.S_mo_286619

namespace OMA.S_mo_286619

open MeasureTheory Set

lemma gauge_deficit {n : ℕ} (P : Set (E n)) (ho : IsOpen P) (hb : Bornology.IsBounded P)
    (G : E n → ℝ) (hcont : Continuous G) (hnn : ∀ x, 0 ≤ G x)
    (hsub : ∀ t : ℝ, 0 < t → t ≤ 1 → volume.real {x | x ∈ P ∧ G x < t} =
      t^n*volume.real P) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    (∫ x in P, max (r-G x) 0) = r^(n+1)/(n+1:ℝ)*volume.real P := by
  let f := fun x => max (r-G x) 0
  have hf : Continuous f := (continuous_const.sub hcont).max continuous_const
  have hi : IntegrableOn f P := 
    (hf.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  change (∫ x in P, f x) = _
  rw [hi.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun x => le_max_right _ _)]
  let g := fun t : ℝ => (r-t)^n * volume.real P
  calc
    _ = ∫ t in Ioi (0:ℝ), (Ioo 0 r).indicator g t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      change (volume.restrict P).real {a | t < f a} = _
      rw [measureReal_restrict_apply' ho.measurableSet]
      by_cases htr : t < r
      · rw [indicator_of_mem (show t ∈ Ioo 0 r from ⟨ht,htr⟩)]
        have eqs : {a | t < f a} ∩ P = {x | x ∈ P ∧ G x < r-t} := by
          ext x
          simp only [mem_inter_iff,mem_ofPred_eq,f,lt_max_iff,not_lt.mpr ht.le,or_false]
          constructor <;> rintro ⟨h,h'⟩
          · exact ⟨h',by linarith⟩
          · exact ⟨by linarith,h⟩
        rw [eqs]
        exact hsub (r-t) (sub_pos.mpr htr) (by linarith)
      · rw [indicator_of_notMem (show t ∉ Ioo 0 r from fun h => htr h.2)]
        have eqs : {a | t < f a} ∩ P = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact (not_lt.mpr (max_le (by linarith [hnn x]) ht.le)) hx.1
        simp [eqs]
    _ = ∫ t in Ioo 0 r, g t := by
      rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr Ioo_subset_Ioi_self]
    _ = ∫ t in (0:ℝ)..r, g t := by
      rw [intervalIntegral.integral_of_le hr.le,integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      dsimp only [g]
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n)]
      simp

end OMA.S_mo_286619

namespace OMA.S_mo_286619

open MeasureTheory Set Filter

private lemma bound_at {n : ℕ} (P : Set (E n)) (ho : IsOpen P) (hb : Bornology.IsBounded P)
    (f : E n → ℝ) (hc : ConvexOn ℝ P f) (hf : IntegrableOn f P) (hz : (∫ x in P, f x)=0)
    (a : E n) (ha : a ∈ P) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1) :
    -(2*r^n*(1-r)*volume.real P)*f a ≤ ∫ x in P, |f x| := by
  let F := fun x => max (-f x) 0
  have hF : IntegrableOn F P := Integrable.sup hf.neg (integrable_zero _ _ _)
  let S := hom a r '' P
  have hSP : S ⊆ P := by
    rintro _ ⟨x,hx,rfl⟩
    exact hc.1 ha hx (sub_nonneg.mpr hr') hr.le (by ring)
  have hsub : (∫ x in S, F x) ≤ ∫ x in P, F x :=
    setIntegral_mono_set hF (Eventually.of_forall (fun x => le_max_right _ _))
      (Eventually.of_forall hSP)
  have hcomp : IntegrableOn (F ∘ hom a r) P :=
    (hom_integrable_iff P a r hr F).mp (hF.mono_set hSP)
  have hconst : IntegrableOn (fun _ : E n => -(1-r)*f a) P :=
    integrableOn_const hb.measure_lt_top.ne
  have hle : (∫ x in P, (-(1-r)*f a) - r*f x) ≤ ∫ x in P, F (hom a r x) := by
    apply setIntegral_mono_on (hconst.sub (hf.const_mul r)) hcomp ho.measurableSet
    intro x hx
    have h := hc.2 ha hx (sub_nonneg.mpr hr') hr.le (by ring : (1-r)+r=1)
    simp only [smul_eq_mul] at h
    change -(1-r)*f a - r*f x ≤ max (-(f ((1-r) • a + r • x))) 0
    apply le_trans _ (le_max_left _ _)
    linarith
  rw [integral_sub hconst (hf.const_mul r),setIntegral_const,smul_eq_mul,integral_const_mul,hz,
    mul_zero,sub_zero] at hle
  have hj := hom_integral P a r hr F
  change (∫ x in S, F x)=_ at hj
  rw [hj] at hsub
  have habs := integral_abs_eq_two_mul_integral_negPart_add_integral hf
  rw [hz,add_zero] at habs
  change (∫ x in P, |f x|)=2*(∫ x in P, F x) at habs
  rw [habs]
  linarith [mul_le_mul_of_nonneg_left hle (pow_nonneg hr.le n)]

private lemma optimal_lower {n : ℕ} (hn : 0 < n) (P : Set (E n)) (hne : P.Nonempty)
    (ho : IsOpen P) (hb : Bornology.IsBounded P) (f : E n → ℝ)
    (hc : ConvexOn ℝ P f) (hf : IntegrableOn f P) (hz : (∫ x in P, f x)=0)
    (hg : IsGLB (f '' P) (-1)) : best n P ≤ ∫ x in P, |f x| := by
  let r : ℝ := n/(n+1)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; positivity
  have hr' : r < 1 := by dsimp [r]; apply (div_lt_one (by positivity)).mpr; linarith
  have hv : 0 < volume.real P :=
    ENNReal.toReal_pos (ho.measure_pos volume hne).ne' hb.measure_lt_top.ne
  let c := 2*r^n*(1-r)*volume.real P
  have hc' : 0 < c := by dsimp [c]; positivity
  have hlow : -(∫ x in P, |f x|)/c ∈ lowerBounds (f '' P) := by
    rintro _ ⟨a,ha,rfl⟩
    apply (div_le_iff₀ hc').mpr
    have h := bound_at P ho hb f hc hf hz a ha r hr hr'.le
    change -c*f a ≤ _ at h
    linarith
  have h := (div_le_iff₀ hc').mp (hg.2 hlow)
  have he : best n P=c := by
    unfold best c r
    field_simp
    ring
  rw [he]
  linarith

end OMA.S_mo_286619

namespace OMA.S_mo_286619

open MeasureTheory Set

private lemma attained {n : ℕ} (hn : 0 < n) (P : Set (E n)) (hne : P.Nonempty)
    (ho : IsOpen P) (hc : Convex ℝ P) (hb : Bornology.IsBounded P) :
    ∃ f : E n → ℝ, ConvexOn ℝ P f ∧ IntegrableOn f P ∧ (∫ x in P, f x)=0 ∧
      IsGLB (f '' P) (-1) ∧ best n P = ∫ x in P, |f x| := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨G,hG,hconv,hGa,hnn,hlt,hsub⟩ := gauge_model P ho hc hb a ha
  have hvol (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      volume.real {x | x∈P ∧ G x < t}=t^n*volume.real P := by
    rw [hsub t ht ht1]
    simpa [setIntegral_const] using hom_integral P a t ht (fun _ => 1)
  let r : ℝ := n/(n+1)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; apply (div_le_one (by positivity)).mpr; linarith
  let f (x : E n) := r⁻¹ * G x - 1
  have hgint : IntegrableOn G P :=
    (hG.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have h1 : IntegrableOn (fun _ : E n => (1:ℝ)) P := integrableOn_const hb.measure_lt_top.ne
  have hfi : IntegrableOn f P := (hgint.const_mul _).sub h1
  have hmeanG : (∫ x in P, G x)=r*volume.real P := by
    have hdef := gauge_deficit P ho hb G hG hnn hvol 1 zero_lt_one le_rfl
    have he : (∫ x in P, max (1-G x) 0) = ∫ x in P, 1-G x := by
      apply setIntegral_congr_fun ho.measurableSet
      intro x hx
      exact max_eq_left (sub_nonneg.mpr (hlt x hx).le)
    rw [he,integral_sub h1 hgint,setIntegral_const,smul_eq_mul,mul_one,one_pow] at hdef
    dsimp [r]
    field_simp at hdef ⊢
    linarith
  have hzero : (∫ x in P, f x)=0 := by
    dsimp only [f]
    rw [integral_sub (hgint.const_mul _) h1,integral_const_mul,hmeanG,setIntegral_const,smul_eq_mul]
    field_simp
    ring
  refine ⟨f,?_,hfi,hzero,?_,?_⟩
  · simpa only [f,Pi.add_def,smul_eq_mul,sub_eq_add_neg] using (hconv.smul (inv_nonneg.mpr hr.le)).add_const (-1)
  · apply IsLeast.isGLB
    refine ⟨⟨a,ha,by simp [f,hGa]⟩,?_⟩
    rintro _ ⟨x,_,rfl⟩
    dsimp [f]
    linarith [mul_nonneg (inv_nonneg.mpr hr.le) (hnn x)]
  · have he (x : E n) : (f x)⁻ = r⁻¹ * max (r-G x) 0 := by
      change max (-(r⁻¹*G x-1)) 0 = _
      rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hr.le),mul_zero]
      congr 1
      field_simp
      ring
    rw [integral_abs_eq_two_mul_integral_negPart_add_integral hfi,hzero,add_zero]
    simp_rw [he]
    rw [integral_const_mul,gauge_deficit P ho hb G hG hnn hvol r hr hr1,pow_succ]
    unfold best
    change 2*r^n/(n+1)*volume.real P=_
    field_simp

end OMA.S_mo_286619

theorem OMA.solution : type_of% @OMA.S_mo_286619.main := by
  intro n hn P hne ho hc hb
  refine ⟨OMA.S_mo_286619.attained hn P hne ho hc hb,?_⟩
  rintro _ ⟨f,hconv,hint,hzero,hglb,rfl⟩
  exact OMA.S_mo_286619.optimal_lower hn P hne ho hb f hconv hint hzero hglb
