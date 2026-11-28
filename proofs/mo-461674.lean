import OMAStatements.S_mo_461674

namespace OMA.S_mo_461674
open MeasureTheory Set Filter
open scoped Topology Interval

private lemma ac_max {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => max (f x) (g x)) a b := by
  apply squeeze_zero (fun E => ?_) (fun E => ?_) (by simpa using Tendsto.add hf hg)
  · exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    let x := (E.2 i).1
    let y := (E.2 i).2
    have h := lipschitzWith_max.dist_le_mul (f x,g x) (f y,g y)
    simp only [NNReal.coe_one,one_mul,Prod.dist_eq] at h
    exact h.trans (max_le (le_add_of_nonneg_right dist_nonneg) (le_add_of_nonneg_left dist_nonneg))

private lemma primitive_support (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1)
    (hm : MonotoneOn f (Ioo 0 1)) {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    (∫ t in (0:ℝ)..x, f t) + (y-x)*f x ≤ ∫ t in (0:ℝ)..y, f t := by
  have hsub {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
      IntervalIntegrable f volume a b :=
    hf.mono_set (uIcc_subset_uIcc (by simpa using ha) (by simpa using hb))
  have h0 : (0:ℝ) ∈ Icc 0 1 := by simp
  have hx' := Ioo_subset_Icc_self hx
  have hy' := Ioo_subset_Icc_self hy
  rw [← le_sub_iff_add_le', intervalIntegral.integral_interval_sub_left (hsub h0 hy') (hsub h0 hx')]
  rcases le_total x y with hxy | hyx
  · have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hxy intervalIntegrable_const
        (hsub hx' hy') (f := fun _ => f x) (fun z hz => hm hx ⟨hx.1.trans hz.1,hz.2.trans hy.2⟩ hz.1.le)
    simpa [smul_eq_mul] using h
  · have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hyx (hsub hy' hx')
        intervalIntegrable_const (g := fun _ => f x)
        (fun z hz => hm ⟨hy.1.trans hz.1,hz.2.trans hx.2⟩ hx hz.2.le)
    rw [intervalIntegral.integral_symm]
    simp only [intervalIntegral.integral_const,smul_eq_mul] at h
    linarith

private lemma deriv_at_contact {f H : ℝ → ℝ} {x d : ℝ} (hx : H x=f x)
    (h : ∀ y, f y ≤ H y) (hf : HasDerivAt f d x) (hH : DifferentiableAt ℝ H x) :
    deriv H x=d := by
  have hmin : IsLocalMin (fun y => H y-f y) x :=
    Eventually.of_forall fun y => by change H x-f x ≤ H y-f y;rw [hx,sub_self]; exact sub_nonneg.mpr (h y)
  exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (hH.hasDerivAt.sub hf))

lemma lower_pair (f g : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (mf : MonotoneOn f (Ioo 0 1))
    (mg : MonotoneOn g (Ioo 0 1)) :
    ∃ l : ℝ → ℝ, MonotoneOn l (Ioo 0 1) ∧ IntervalIntegrable l volume 0 1 ∧
      (∀ t, l t=f t ∨ l t=g t) ∧ ∀ t ∈ Icc (0:ℝ) 1,
        (∫ x in (0:ℝ)..t, l x) = max (∫ x in (0:ℝ)..t, f x) (∫ x in (0:ℝ)..t, g x) := by
  let F (x : ℝ) := ∫ t in (0:ℝ)..x, f t
  let G (x : ℝ) := ∫ t in (0:ℝ)..x, g t
  let H (x : ℝ) := max (F x) (G x)
  let l (x : ℝ) := if G x ≤ F x then f x else g x
  have hH : AbsolutelyContinuousOnInterval H 0 1 :=
    ac_max (hf.absolutelyContinuousOnInterval_intervalIntegral (by simp))
      (hg.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hs {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) : H x+(y-x)*l x ≤ H y := by
    by_cases h : G x ≤ F x
    · simp only [l,if_pos h,H,max_eq_left h]
      exact (primitive_support f hf mf hx hy).trans (le_max_left ..)
    · simp only [l,if_neg h,H,max_eq_right (le_of_not_ge h)]
      exact (primitive_support g hg mg hx hy).trans (le_max_right ..)
  have he : ∀ᵐ x : ℝ, x ∈ uIcc (0:ℝ) 1 → deriv H x=l x := by
    filter_upwards [hH.ae_differentiableAt,hf.ae_hasDerivAt_integral,hg.ae_hasDerivAt_integral]
      with x hdiff df dg
    intro hx
    by_cases h : G x ≤ F x
    · rw [show l x=f x from if_pos h]
      exact deriv_at_contact (max_eq_left h) (fun y => le_max_left (F y) (G y))
        (df hx 0 (by simp)) (hdiff hx)
    · rw [show l x=g x from if_neg h]
      exact deriv_at_contact (max_eq_right (le_of_not_ge h)) (fun y => le_max_right (F y) (G y))
        (dg hx 0 (by simp)) (hdiff hx)
  refine ⟨l,?_,?_,?_,?_⟩
  · intro x hx y hy hxy
    rcases hxy.eq_or_lt with rfl | hlt
    · rfl
    · have h1 := hs hx hy
      have h2 := hs hy hx
      apply le_of_mul_le_mul_left (a := y-x) _ (sub_pos.mpr hlt)
      linarith
  · apply hH.intervalIntegrable_deriv.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [he] with x hx using fun h => hx (uIoc_subset_uIcc h)
  · intro t;dsimp [l];split_ifs <;> simp
  · intro t ht
    have hsub : uIcc (0:ℝ) t ⊆ uIcc 0 1 := uIcc_subset_uIcc (by simp) (by simpa using ht)
    calc
      _ = ∫ x in (0:ℝ)..t, deriv H x := intervalIntegral.integral_congr_ae (by
        filter_upwards [he] with x hx using fun h => (hx (hsub (uIoc_subset_uIcc h))).symm)
      _ = H t-H 0 := (hH.mono hsub).integral_deriv_eq_sub
      _ = _ := by simp [H,F,G]
end OMA.S_mo_461674

namespace OMA.S_mo_461674
open Set MeasureTheory
open scoped Interval

lemma subinterval {f : ℝ → ℝ} (h : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a≤b) (hb : b≤1) : IntervalIntegrable f volume a b := by
  apply h.mono_set
  rw [uIcc_of_le hab,uIcc_of_le zero_le_one]
  exact Icc_subset_Icc ha hb

private lemma put_integrable {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable f volume a b) (c : ℝ) :
    IntervalIntegrable (fun x => max (c-f x) 0) volume a b := by
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume a b := intervalIntegrable_const
  exact ⟨(hc.sub h).1.pos_part,(hc.sub h).2.pos_part⟩

private lemma prefix_le_put {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (c : ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    t*c - (∫ x in (0:ℝ)..t, f x) ≤ (∫ x in (0:ℝ)..1, max (c-f x) 0) := by
  have h0 := subinterval hf (a:=0) le_rfl ht.1 ht.2
  have h1 := subinterval hf ht.1 ht.2 (b:=1) le_rfl
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume 0 t := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on ht.1 (hc.sub h0) (put_integrable h0 c)
    (fun x _ => le_max_left (c-f x) 0)
  change (∫ x in (0:ℝ)..t, c-f x) ≤ _ at h
  rw [intervalIntegral.integral_sub hc h0,intervalIntegral.integral_const] at h
  simp only [sub_zero,smul_eq_mul] at h
  have hp := intervalIntegral.integral_nonneg_of_forall (μ:=volume) ht.2 (fun x => le_max_right (c-f x) 0)
  have hs := intervalIntegral.integral_add_adjacent_intervals (put_integrable h0 c) (put_integrable h1 c)
  linarith

private lemma put_at_prefix {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (mf : MonotoneOn f (Ioo 0 1)) (c : ℝ) :
    ∃ t ∈ Icc (0:ℝ) 1, (∫ x in (0:ℝ)..1, max (c-f x) 0) =
      t*c - (∫ x in (0:ℝ)..t, f x) := by
  let S := insert (0:ℝ) {x | x∈Ioo (0:ℝ) 1 ∧ f x≤c}
  have h0S : (0:ℝ)∈S := mem_insert _ _
  have hb : ∀ x∈S, x ≤ 1 := by
    intro x hx
    rcases hx with h|h
    · simp [h]
    · exact h.1.2.le
  let t := sSup S
  have ht0 : 0≤t := le_csSup ⟨1,hb⟩ h0S
  have ht1 : t≤1 := csSup_le ⟨_,h0S⟩ hb
  have hl (x : ℝ) (hx : x∈Ioo (0:ℝ) t) : f x≤c := by
    obtain ⟨y,hy,hxy⟩ := exists_lt_of_lt_csSup (s:=S) ⟨_,h0S⟩ hx.2
    rcases hy with hy|hy
    · linarith [hx.1]
    · exact (mf ⟨hx.1,hx.2.trans_le ht1⟩ hy.1 hxy.le).trans hy.2
  have hr (x : ℝ) (hx : x∈Ioo t 1) : c≤f x := by
    by_contra! hh
    have hxS : x∈S := Or.inr ⟨⟨ht0.trans_lt hx.1,hx.2⟩,hh.le⟩
    exact (le_csSup ⟨1,hb⟩ hxS).not_gt hx.1
  have h0 := subinterval hf (a:=0) le_rfl ht0 ht1
  have h1 := subinterval hf ht0 ht1 (b:=1) le_rfl
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume 0 t := intervalIntegrable_const
  refine ⟨t,⟨ht0,ht1⟩,?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (put_integrable h0 c) (put_integrable h1 c)]
  rw [intervalIntegral.integral_congr_Ioo_of_le ht0 (g:=fun x => c-f x)
    (fun x hx => max_eq_left (sub_nonneg.mpr (hl x hx)))]
  rw [intervalIntegral.integral_congr_Ioo_of_le ht1 (g:=fun _ => 0)
    (fun x hx => max_eq_right (sub_nonpos.mpr (hr x hx)))]
  rw [intervalIntegral.integral_sub hc h0]
  simp

lemma put_compare {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (mf : MonotoneOn f (Ioo 0 1))
    (hp : ∀ t ∈ Icc (0:ℝ) 1, (∫ x in (0:ℝ)..t, g x) ≤ (∫ x in (0:ℝ)..t, f x))
    (c : ℝ) : (∫ x in (0:ℝ)..1, max (c-f x) 0) ≤ (∫ x in (0:ℝ)..1, max (c-g x) 0) := by
  obtain ⟨t,ht,he⟩ := put_at_prefix hf mf c
  rw [he]
  exact (sub_le_sub_left (hp t ht) _).trans (prefix_le_put hg c ht)

end OMA.S_mo_461674

namespace OMA.S_mo_461674
open Set MeasureTheory
open scoped Interval

private lemma selected_moment {p : ℝ} {f g z : ℝ → ℝ} (hf : Moment p f) (hg : Moment p g)
    (hz : IntervalIntegrable z volume 0 1) (h : ∀ x, z x=f x ∨ z x=g x) : Moment p z := by
  refine ⟨hz,(hf.2.add hg.2).mono_fun' ?_ ?_⟩
  · exact (hz.aestronglyMeasurable_restrict_uIoc.aemeasurable.abs.pow_const p).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    change ‖|z x| ^ p‖ ≤ |f x|^p + |g x|^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rcases h x with hx|hx
    · rw [hx]; exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    · rw [hx]; exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)

lemma brackets (p : ℝ) (f g : ℝ → ℝ) (mf : MonotoneOn f (Ioo 0 1))
    (mg : MonotoneOn g (Ioo 0 1)) (hf : Moment p f) (hg : Moment p g)
    (hmean : (∫ t in (0:ℝ)..1, f t) = (∫ t in (0:ℝ)..1, g t)) :
    ∃ l r : ℝ → ℝ, Moment p l ∧ Moment p r ∧ below l f ∧ below l g ∧ below f r ∧ below g r ∧
      (∫ t in (0:ℝ)..1, |l t-r t|^p) = (∫ t in (0:ℝ)..1, |f t-g t|^p) := by
  obtain ⟨l,ml,hl,hs,hprefix⟩ := lower_pair f g hf.1 hg.1 mf mg
  let r (x : ℝ) := f x + g x - l x
  have hr : IntervalIntegrable r volume 0 1 := (hf.1.add hg.1).sub hl
  have hrs (x : ℝ) : r x=f x ∨ r x=g x := by
    rcases hs x with hx|hx
    · exact Or.inr (by simp [r,hx])
    · exact Or.inl (by simp [r,hx])
  have hlow := hprefix 1 (show (1:ℝ) ∈ Icc 0 1 by simp)
  rw [hmean,max_self] at hlow
  have hupper (t : ℝ) (ht : t ∈ Icc 0 1) :
      (∫ x in (0:ℝ)..t, r x) = min (∫ x in (0:ℝ)..t, f x) (∫ x in (0:ℝ)..t, g x) := by
    have hft := subinterval hf.1 (a:=0) le_rfl ht.1 ht.2
    have hgt := subinterval hg.1 (a:=0) le_rfl ht.1 ht.2
    have hlt := subinterval hl (a:=0) le_rfl ht.1 ht.2
    rw [show (∫ x in (0:ℝ)..t, r x) = _ from intervalIntegral.integral_sub (hft.add hgt) hlt,
      intervalIntegral.integral_add hft hgt,hprefix t ht]
    rcases le_total (∫ x in (0:ℝ)..t, f x) (∫ x in (0:ℝ)..t, g x) with h|h
    · simp [max_eq_right h,min_eq_left h]
    · simp [max_eq_left h,min_eq_right h]
  have hup := hupper 1 (show (1:ℝ) ∈ Icc 0 1 by simp)
  rw [hmean,min_self] at hup
  refine ⟨l,r,selected_moment hf hg hl hs,selected_moment hf hg hr hrs,
    ⟨hlow.trans hmean.symm,put_compare hl hf.1 ml (fun t ht => (hprefix t ht) ▸ le_max_left _ _)⟩,
    ⟨hlow,put_compare hl hg.1 ml (fun t ht => (hprefix t ht) ▸ le_max_right _ _)⟩,
    ⟨hmean.trans hup.symm,put_compare hf.1 hr mf (fun t ht => (hupper t ht) ▸ min_le_left _ _)⟩,
    ⟨hup.symm,put_compare hg.1 hr mg (fun t ht => (hupper t ht) ▸ min_le_right _ _)⟩,?_⟩
  apply intervalIntegral.integral_congr
  intro x _
  rcases hs x with h|h
  · simp [r,h]
  · simp [r,h,abs_sub_comm (g x) (f x)]

end OMA.S_mo_461674

theorem OMA.solution : type_of% @OMA.S_mo_461674.main := by
  intro p _ f g
  exact OMA.S_mo_461674.brackets p f g
