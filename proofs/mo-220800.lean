import OMAStatements.S_mo_220800

namespace OMA.S_mo_220800
open MeasureTheory Finset Set
open scoped ENNReal NNReal
private instance sample_prob {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (sample n μ) := by unfold sample; infer_instance
private lemma max_witness {n} (x : Arr n) : ∃ i, ‖x‖=|x i| := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (s := Finset.univ) Finset.univ_nonempty (fun i => ‖x i‖₊)
  exact ⟨i,congrArg (fun r : ℝ≥0 => (r:ℝ)) hi⟩
private lemma second_tail (μ : Measure ℝ) (hμ : standard μ) {t : ℝ} (ht : 0<t) :
    μ.real {z | t ≤ |z|} ≤ 1/t^2 := by
  let := hμ.1
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun x : ℝ => sq_nonneg x) hμ.2.2.1 (t^2)
  rw [hμ.2.2.2.2] at h
  have he : {z : ℝ | t≤|z|} = {z | t^2 ≤ z^2} := by
    ext z
    simp only [mem_ofPred_eq,←sq_abs z]
    exact (sq_le_sq₀ ht.le (abs_nonneg z)).symm
  rwa [he,mul_comm]
private lemma coord_tail {n} (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin (n+1)) (t : ℝ) :
    (sample n μ).real {x | t ≤ |x i|} = μ.real {z | t ≤ |z|} := by
  exact congrArg ENNReal.toReal ((measurePreserving_eval (fun _ : Fin (n+1) => μ) i).measure_preimage
    (measurableSet_le measurable_const measurable_abs).nullMeasurableSet)
private lemma max_tail {n} (μ : Measure ℝ) (hμ : standard μ) {t : ℝ} (ht : 0<t) :
    (sample n μ).real {x | t ≤ ‖x‖} ≤ min 1 ((n+1:ℝ)/t^2) := by
  let := hμ.1
  refine le_min (measureReal_le_one) ?_
  have hs : {x : Arr n | t ≤ ‖x‖} ⊆ ⋃ i : Fin (n+1), {x | t ≤ |x i|} := by
    intro x hx
    obtain ⟨i,hi⟩ := max_witness x
    exact mem_iUnion.mpr ⟨i, (show t ≤ ‖x‖ from hx).trans_eq hi⟩
  calc _ ≤ _ := measureReal_mono hs
       _ ≤ _ := measureReal_iUnion_fintype_le _
       _ ≤ ∑ _ : Fin (n+1), 1/t^2 := by
        apply sum_le_sum
        intro i _
        rw [coord_tail]
        exact second_tail μ hμ ht
       _ = _ := by simp [div_eq_mul_inv]
private lemma upper (n : ℕ) (t : ℝ) (ht : 1 ≤ t) (μ ν : Measure ℝ) (hμ : standard μ) (hν : standard ν) :
    dropProb μ ν n t ≤ 2*rate n t := by
  classical
  let := hμ.1
  let := hν.1
  let E : Set (Arr n × Arr n) := {v | ‖v.1+v.2‖+t ≤ ‖v.1‖}
  let D : Set (Arr n) := {x | t ≤ ‖x‖}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) (by fun_prop)
  have hD : MeasurableSet D := measurableSet_le measurable_const measurable_norm
  have ht' : 0<t := by linarith
  let f (x : Arr n) := (sample n ν).real (Prod.mk x ⁻¹' E)
  have hfm : Measurable f := (measurable_measure_prodMk_left hE).ennreal_toReal
  have hf : Integrable f (sample n μ) := .of_bound hfm.aestronglyMeasurable 1 <|
    ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hfd (x : Arr n) : f x ≤ D.indicator (fun _ => 1/t^2) x := by
    by_cases hx : x ∈ D
    · rw [indicator_of_mem hx]
      obtain ⟨i,hi⟩ := max_witness x
      have hsub : Prod.mk x ⁻¹' E ⊆ {y | t ≤ |y i|} := by
        intro y hy
        change ‖x+y‖+t ≤ ‖x‖ at hy
        have hcoord := norm_le_pi_norm (x+y) i
        rw [Real.norm_eq_abs,Pi.add_apply] at hcoord
        have htri := abs_sub (x i+y i) (y i)
        rw [add_sub_cancel_right] at htri
        change t ≤ |y i|
        rw [hi] at hy
        linarith
      exact (measureReal_mono hsub).trans ((coord_tail ν i t).le.trans (second_tail ν hν ht'))
    · rw [indicator_of_notMem hx]
      have hno : Prod.mk x ⁻¹' E = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        change ‖x+y‖+t ≤ ‖x‖ at hy
        exact hx (show t ≤ ‖x‖ by linarith [norm_nonneg (x+y)])
      simp [f,hno]
  have heq : dropProb μ ν n t = ∫ x,f x ∂sample n μ := by
    change (((sample n μ).prod (sample n ν)) E).toReal = _
    rw [Measure.prod_apply hE]
    exact (integral_toReal (measurable_measure_prodMk_left hE).aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)).symm
  rw [heq]
  calc _ ≤ ∫ x,D.indicator (fun _ => 1/t^2) x ∂sample n μ :=
          integral_mono hf ((integrable_const _).indicator hD) hfd
       _ = (sample n μ).real D * (1/t^2) := by rw [integral_indicator hD,setIntegral_const,smul_eq_mul]
       _ ≤ (min 1 ((n+1:ℝ)/t^2))*(1/t^2) := by
         gcongr
         exact max_tail μ hμ ht'
       _ ≤ _ := by
         unfold rate
         calc _ ≤ min 1 ((n+1:ℝ)/t^2)*(2/(1+t^2)) := by
                apply mul_le_mul_of_nonneg_left _ (le_min zero_le_one (by positivity))
                rw [div_le_div_iff₀ (sq_pos_of_pos ht') (by positivity)]
                nlinarith
              _ = _ := by ring
end OMA.S_mo_220800

namespace OMA.S_mo_220800
open MeasureTheory Set
open scoped ENNReal Classical
private noncomputable def rare (a : ℝ) := 1/(1+a^2)
private noncomputable def two (a : ℝ) : Measure ℝ :=
  ENNReal.ofReal (rare a) • Measure.dirac a + ENNReal.ofReal (1-rare a) • Measure.dirac (-1/a)
private lemma rare_pos (a : ℝ) : 0<rare a := by unfold rare; positivity
private lemma rare_le (a : ℝ) : rare a ≤ 1 := by
  unfold rare; rw [div_le_one (by positivity)]; linarith [sq_nonneg a]
private lemma two_apply (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (two a).real s = (if a ∈ s then rare a else 0) + (if -1/a ∈ s then 1-rare a else 0) := by
  classical
  simp only [two,Measure.real,Measure.add_apply,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hs,
    indicator,Pi.one_apply]
  split_ifs <;> simp [ENNReal.toReal_add,ENNReal.toReal_ofReal (rare_pos a).le,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (rare_le a))]
private lemma two_standard (a : ℝ) (ha : a≠0) : standard (two a) := by
  have hp := (rare_pos a).le
  have hq := sub_nonneg.mpr (rare_le a)
  have hi (f : ℝ → ℝ) : Integrable f (two a) :=
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  have hw (f : ℝ → ℝ) : (∫ x,f x ∂two a) = rare a*f a+(1-rare a)*f (-1/a) := by
    unfold two
    rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
       ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
    simp [integral_smul_measure,ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal hq,smul_eq_mul]
  refine ⟨isProbabilityMeasure_iff_real.mpr ?_,hi _,hi _,?_,?_⟩
  · simp [two_apply]
  · rw [hw]; unfold rare; field_simp; ring
  · rw [hw]; unfold rare; field_simp; ring
private lemma exceptional {a : ℝ} (ha : a≠0) : (-1/a)≠a := by
  intro h; have he := (div_eq_iff ha).mp h; nlinarith [sq_nonneg a]
private lemma two_single {a : ℝ} (ha : a≠0) : (two a).real {a}=rare a := by
  simp [two_apply,exceptional ha]
private lemma two_other {a : ℝ} (ha : a≠0) : (two a).real {-1/a}=1-rare a := by
  simp [two_apply,Ne.symm (exceptional ha)]
private lemma two_support (a : ℝ) : (two a).real {a,-1/a}=1 := by simp [two_apply]
private lemma printed : ∃ μ : Measure ℝ, standard μ ∧ ∀ c : ℝ, 0<c →
      Real.exp (-c) < (μ.prod μ).real {v | |v.1| ≤ |v.1+v.2|+1} := by
  have hs := two_standard 1 (by norm_num)
  let _ := hs.1
  refine ⟨two 1,hs,fun c hc => ?_⟩
  calc Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
       _ = ((two 1).prod (two 1)).real ({1,-1/(1:ℝ)} ×ˢ univ) := by
         rw [measureReal_prod_prod,two_support]; simp
       _ ≤ _ := by
        refine measureReal_mono ?_
        rintro ⟨x,y⟩ ⟨hx,_⟩
        rcases hx with h|h
        · change x=1 at h; subst x; simp
        · change x=(-1/(1:ℝ)) at h; subst x; simp
end OMA.S_mo_220800

namespace OMA.S_mo_220800
open MeasureTheory Set Finset
open scoped ENNReal Function
private noncomputable def pattern {n : ℕ} (a : ℝ) (j : Fin (n+1)) : Arr n := fun i => if i=j then a else -1/a
private def choices {n : ℕ} (t : ℝ) (j i : Fin (n+1)) : Set ℝ :=
  if i=j then {-t} else {-t,-1/(-t)}
private def rect {n : ℕ} (a t : ℝ) (j : Fin (n+1)) : Set (Arr n × Arr n) :=
  {pattern a j} ×ˢ Set.univ.pi (choices t j)
private lemma rect_meas {n} (a t : ℝ) (j : Fin (n+1)) : MeasurableSet (rect a t j) := by
  apply (measurableSet_singleton _).prod
  apply MeasurableSet.univ_pi
  intro i
  unfold choices; split <;> measurability
private lemma rect_disjoint {n} (a t : ℝ) (ha : a≠0) :
    Pairwise (Disjoint on (rect (n := n) a t)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ⟨x,y⟩ h₁ h₂
  have h : pattern a i = pattern a j := (mem_singleton_iff.mp h₁.1).symm.trans (mem_singleton_iff.mp h₂.1)
  have hx := congrFun h i
  simp [pattern,hij,Ne.symm (exceptional ha)] at hx
private lemma rect_sub {n} (a t : ℝ) (ht : 1 ≤ t) (ha : 3*t ≤ a) (j : Fin (n+1)) :
    rect a t j ⊆ {v | ‖v.1+v.2‖+t ≤ ‖v.1‖} := by
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0<a := by linarith
  have ht0 : 0<t := by linarith
  have hai : 1/a ≤ 1 := (div_le_one ha0).mpr ha1
  have hti : 1/t ≤ 1 := (div_le_one ht0).mpr ht
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  obtain rfl := mem_singleton_iff.mp hx
  have lo := norm_le_pi_norm (pattern a j) j
  simp [pattern,Real.norm_eq_abs,abs_of_pos ha0] at lo
  have hu : ‖pattern a j+y‖ ≤ a-t := by
    apply (pi_norm_le_iff_of_nonneg (by linarith)).2
    intro i
    have hyi := hy i (Set.mem_univ i)
    rw [Real.norm_eq_abs,Pi.add_apply]
    by_cases he : i=j
    · subst i
      have h : y j= -t := by simpa [choices] using hyi
      rw [h]; simp [pattern,←sub_eq_add_neg,abs_of_nonneg (show 0 ≤ a-t by linarith)]
    · have h : y i= -t ∨ y i= -1/(-t) := by simpa [choices,he] using hyi
      have hb : |y i| ≤ t := by
        rcases h with h|h <;> rw [h] <;> simp [abs_of_pos ht0]
        simpa [one_div] using hti.trans ht
      rw [show pattern a j i = -1/a by simp [pattern,he]]
      calc _ ≤ |(-1/a)|+|y i| := abs_add_le _ _
           _ ≤ 1/a+t := by rw [abs_div,abs_of_pos ha0]; norm_num; linarith
           _ ≤ _ := by linarith
  change ‖pattern a j+y‖+t ≤ ‖pattern a j‖
  linarith
private lemma rect_mass {n} (a t : ℝ) (ha : a≠0) (ht : t≠0) (j : Fin (n+1)) :
    ((sample n (two a)).prod (sample n (two (-t)))).real (rect a t j) =
      (rare a*(1-rare a)^n)*rare (-t) := by
  classical
  let := (two_standard a ha).1
  let := (two_standard (-t) (neg_ne_zero.mpr ht)).1
  rw [rect,measureReal_prod_prod]
  congr 1
  · change ((Measure.pi (fun _ : Fin (n+1) => two a)) {pattern a j}).toReal = _
    rw [Measure.pi_singleton,ENNReal.toReal_prod]
    change ∏ i, (two a).real {pattern a j i} = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    rw [show pattern a j j=a by simp [pattern],two_single ha]
    congr 1
    calc _ = ∏ _ ∈ (Finset.univ.erase j), (1-rare a) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [show pattern a j i = -1/a by simp [pattern,(Finset.mem_erase.mp hi).1],two_other ha]
         _ = _ := by simp
  · change ((Measure.pi (fun _ : Fin (n+1) => two (-t))) (univ.pi (choices t j))).toReal = _
    rw [Measure.pi_pi,ENNReal.toReal_prod]
    change ∏ i, (two (-t)).real (choices t j i) = _
    convert Fintype.prod_ite_eq' j (fun _ => rare (-t)) using 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i=j
    · rw [choices,if_pos hi,if_pos hi,two_single (neg_ne_zero.mpr ht)]
    · rw [choices,if_neg hi,if_neg hi,two_support]
private lemma mass_bound (n : ℕ) (a t : ℝ) (ht : 1 ≤ t) (ha : 3*t ≤ a) :
    (n+1:ℝ)*rare a*(1-rare a)^n*rare (-t) ≤ dropProb (two a) (two (-t)) n t := by
  classical
  have ha0 : a≠0 := by linarith
  have ht0 : t≠0 := by linarith
  let := (two_standard a ha0).1
  let := (two_standard (-t) (neg_ne_zero.mpr ht0)).1
  let ρ := (sample n (two a)).prod (sample n (two (-t)))
  calc _ = ∑ j : Fin (n+1), ρ.real (rect a t j) := by
          simp [ρ,rect_mass a t ha0 ht0]; ring
       _ = ρ.real (⋃ j : Fin (n+1), rect a t j) :=
         (measureReal_iUnion_fintype (rect_disjoint a t ha0) (rect_meas a t)).symm
       _ ≤ _ := measureReal_mono (Set.iUnion_subset (rect_sub a t ht ha))
private lemma lower (n : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    ∃ μ ν : Measure ℝ, standard μ ∧ standard ν ∧ rate n t/24 ≤ dropProb μ ν n t := by
  let N : ℝ := n+1
  let a := max (3*t) (Real.sqrt (2*N))
  have hn : 1 ≤ N := by dsimp [N]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hs := Real.sq_sqrt (show 0 ≤ 2*N by positivity)
  have ha : 3*t ≤ a := le_max_left _ _
  have ht0 : 0<t := by linarith
  have hA : 0<a := by linarith
  have h2 : 2*N ≤ a^2 := by
    have := sq_le_sq₀ (Real.sqrt_nonneg (2*N)) hA.le
    exact hs ▸ this.mpr (le_max_right _ _)
  have hhalf : N*rare a ≤ 1/2 := by
    unfold rare; rw [mul_one_div,div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hB : 1/2 ≤ (1-rare a)^n := by
    have hh := one_add_mul_le_pow (a := -rare a) (by linarith [rare_le a]) n
    dsimp [N] at hhalf
    rw [sub_eq_add_neg]
    nlinarith [rare_pos a]
  have hlow : min 1 (N/t^2) ≤ 12*(N*rare a) := by
    have huu : 1+a^2 ≤ 12*max N (t^2) := by
      have h1 := le_max_left N (t^2)
      have h2' := le_max_right N (t^2)
      unfold a
      rcases le_total (3*t) (Real.sqrt (2*N)) with h|h
      · rw [max_eq_right h,hs]; linarith
      · rw [max_eq_left h]; nlinarith [sq_nonneg (t-1)]
    unfold rare
    rw [mul_one_div,←mul_div_assoc,le_div_iff₀ (by positivity)]
    rcases le_total N (t^2) with h|h
    · rw [max_eq_right h] at huu
      rw [min_eq_right ((div_le_one (sq_pos_of_pos ht0)).mpr h)]
      calc _ ≤ N/t^2 * (12*t^2) := mul_le_mul_of_nonneg_left huu (by positivity)
           _ = _ := by field_simp
    · rw [max_eq_left h] at huu
      rw [min_eq_left ((one_le_div (sq_pos_of_pos ht0)).mpr h),one_mul]
      exact huu
  refine ⟨two a,two (-t),two_standard a hA.ne',two_standard _ (neg_ne_zero.mpr ht0.ne'),?_⟩
  apply le_trans _ (mass_bound n a t ht ha)
  change min 1 (N/t^2)/(1+t^2)/24 ≤ N*rare a*(1-rare a)^n*rare (-t)
  have hr : rare (-t) = 1/(1+t^2) := by simp [rare]
  rw [hr]
  calc _ ≤ (12*(N*rare a))/(1+t^2)/24 := by gcongr
       _ = N*rare a*(1/2)*(1/(1+t^2)) := by ring
       _ ≤ _ := by gcongr; exact mul_nonneg (by linarith) (rare_pos a).le
end OMA.S_mo_220800

namespace OMA.S_mo_220800
open MeasureTheory Set
open scoped ENNReal
private noncomputable def weight (k : ℕ) : ℝ := (1/4)*(1/8)^k
private noncomputable def branch (s : ℝ) : Measure ℝ :=
  Measure.sum (fun k => ENNReal.ofReal (weight k) • Measure.dirac (s*2^k))
private noncomputable def heavy : Measure ℝ :=
  (ENNReal.ofReal (3/7) • Measure.dirac 0) + branch 1 + branch (-1)
private lemma wm (k p : ℕ) (s : ℝ) :
    weight k*(s*2^k)^p = (s^p/4)*(((2:ℝ)^p)/8)^k := by
  simp only [weight,mul_pow,div_pow,one_pow,←pow_mul,Nat.mul_comm k p]
  ring
private lemma branch_moment (s : ℝ) (p : ℕ) (hp : (2:ℝ)^p/8<1) :
    Integrable (fun x : ℝ => x^p) (branch s) ∧
      (∫ x,x^p ∂branch s) = (s^p/4)/(1-(2:ℝ)^p/8) := by
  have hg := hasSum_geometric_of_norm_lt_one (show ‖(2:ℝ)^p/8‖<1 by rwa [Real.norm_eq_abs,abs_of_pos (by positivity)])
  have hW : HasSum (fun k => weight k*(s*2^k)^p) ((s^p/4)/(1-(2:ℝ)^p/8)) := by
    simp only [wm,div_eq_mul_inv] at *
    exact hg.mul_left _
  have hn (k : ℕ) : 0 ≤ weight k := by unfold weight; positivity
  have hw (k : ℕ) := ENNReal.toReal_ofReal (hn k)
  constructor
  · apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
    apply hW.summable.abs.congr
    intro k
    simp only [hw,abs_mul,abs_of_nonneg (hn k),Real.norm_eq_abs]
  · unfold branch
    rw [integral_sum_dirac (by simp)]
    simpa [hw,smul_eq_mul] using hW.tsum_eq
private lemma heavy_all (p : ℕ) (hp : (2:ℝ)^p/8<1) :
    Integrable (fun x : ℝ => x^p) heavy ∧ (∫ x,x^p ∂heavy) =
      (3/7)*(0:ℝ)^p + ((1:ℝ)^p/4)/(1-2^p/8) + ((-1:ℝ)^p/4)/(1-2^p/8) := by
  have h := branch_moment 1 p hp
  have g := branch_moment (-1) p hp
  have h0 : Integrable (fun x : ℝ => x^p) (ENNReal.ofReal (3/7) • Measure.dirac 0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  refine ⟨(h0.add_measure h.1).add_measure g.1,?_⟩
  rw [heavy,integral_add_measure (h0.add_measure h.1) g.1,integral_add_measure h0 h.1,
    integral_smul_measure,integral_dirac,h.2,g.2]
  norm_num [smul_eq_mul]
private lemma heavy_standard : standard heavy := by
  have h₀ := (heavy_all 0 (by norm_num)).2
  have h₁ := heavy_all 1 (by norm_num)
  have h₂ := heavy_all 2 (by norm_num)
  norm_num at h₀ h₁ h₂
  exact ⟨isProbabilityMeasure_iff_real.mpr h₀,h₁.1,h₂.1,h₁.2,h₂.2⟩
private lemma heavy_symmetric : heavy.map Neg.neg = heavy := by
  have hb (s : ℝ) : (branch s).map Neg.neg = branch (-s) := by
    unfold branch
    rw [Measure.map_sum measurable_neg.aemeasurable]
    simp [Measure.map_smul,Measure.map_dirac' measurable_neg]
  simp only [heavy,Measure.map_add _ _ measurable_neg,Measure.map_smul,Measure.map_dirac' measurable_neg,
    neg_zero,hb,neg_neg]
  abel
private lemma mass_at (s : ℝ) (k : ℕ) : ENNReal.ofReal (weight k) ≤ branch s {s*2^k} := by
  have h := Measure.le_sum (fun j => ENNReal.ofReal (weight j) • Measure.dirac (s*2^j)) k {s*2^k}
  simpa [branch] using h
private lemma heavy_cancel (k : ℕ) : 1/(16*((2:ℝ)^k)^6) ≤ oneDrop heavy (2^k) := by
  let := heavy_standard.1
  let x : ℝ := 2^k
  have w : 0 ≤ weight k := by unfold weight; positivity
  have a : weight k ≤ heavy.real {x} := by
    rw [←ENNReal.toReal_ofReal w]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    calc _ ≤ branch 1 {x} := by simpa [x] using mass_at 1 k
         _ ≤ _ := by unfold heavy; simp only [Measure.add_apply]; exact le_trans (le_add_self) le_self_add
  have b : weight k ≤ heavy.real {-x} := by
    rw [←ENNReal.toReal_ofReal w]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    calc _ ≤ branch (-1) {-x} := by simpa [x] using mass_at (-1) k
         _ ≤ _ := by unfold heavy; simp only [Measure.add_apply]; exact le_add_self
  calc _ = weight k*weight k := by
          unfold weight
          have h8 : (8:ℝ)^k = (2^k)^3 := by
            rw [show (8:ℝ)=2^3 by norm_num,←pow_mul,←pow_mul,Nat.mul_comm]
          rw [one_div_pow,h8]
          ring
       _ ≤ heavy.real {x}*heavy.real {-x} := mul_le_mul a b w measureReal_nonneg
       _ = (heavy.prod heavy).real ({x} ×ˢ {-x}) := (measureReal_prod_prod _ _).symm
       _ ≤ _ := by
        refine measureReal_mono ?_
        rintro ⟨u,v⟩ ⟨hu,hv⟩
        obtain rfl := mem_singleton_iff.mp hu
        obtain rfl := mem_singleton_iff.mp hv
        change |x + -x|+2^k ≤ |x|
        simp [x]
private lemma slow (c : ℝ) (hc : 0<c) : ∃ t : ℝ, 1 ≤ t ∧ Real.exp (-c*t^2) < oneDrop heavy t := by
  obtain ⟨k,hk⟩ := exists_nat_gt ((Real.log 16+6*Real.log 2)/c+1)
  have h16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk1 : 1 ≤ (k:ℝ) := by linarith [show 0 ≤ (Real.log 16+6*Real.log 2)/c by positivity]
  have hkc : Real.log 16+6*Real.log 2 < k*c := (div_lt_iff₀ hc).mp (by linarith)
  have hkpow : 1+(k:ℝ) ≤ (2:ℝ)^k := by simpa only [mul_one,show (1:ℝ)+1=2 by norm_num] using one_add_mul_le_pow (a:=(1:ℝ)) (by norm_num) k
  refine ⟨2^k,by linarith,lt_of_lt_of_le ?_ (heavy_cancel k)⟩
  apply (Real.log_lt_log_iff (Real.exp_pos _) (by positivity)).mp
  rw [Real.log_exp,Real.log_div one_ne_zero (by positivity),Real.log_one,Real.log_mul (by norm_num) (by positivity),
    Real.log_pow,Real.log_pow]
  have hcmp := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by linarith : 0 ≤ (k:ℝ))
    (by positivity)).mpr (show (k:ℝ) ≤ 2^k by linarith)) hc.le
  have hr := mul_lt_mul_of_pos_right hkc (show 0 < (k:ℝ) by linarith)
  have hfin : Real.log 16+6*((k:ℝ)*Real.log 2) < c*(2^k)^2 := calc
    _ ≤ (Real.log 16+6*Real.log 2)*(k:ℝ) := by nlinarith only [mul_nonneg (sub_nonneg.mpr hk1) h16]
    _ < (k:ℝ)*c*k := hr
    _ ≤ _ := by nlinarith only [hcmp]
  push_cast
  linarith only [hfin]
end OMA.S_mo_220800

open OMA.S_mo_220800
theorem OMA.solution : type_of% @OMA.S_mo_220800.main := by
  exact ⟨printed,fun n t ht => ⟨upper n t ht,lower n t ht⟩,heavy,heavy_standard,heavy_symmetric,heavy_cancel,slow⟩
