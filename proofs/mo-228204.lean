import OMAStatements.S_mo_228204

namespace OMA.S_mo_228204
open scoped RealInnerProductSpace
private lemma scalar_bound (r a b d A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : d^2 ≤ r^2*A*B) : (r*a*b+d)^2 ≤ r^2*(a^2+A)*(b^2+B) := by
  have hD : |d| ≤ |r| * (Real.sqrt A * Real.sqrt B) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [sq_abs,mul_pow,sq_abs,mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB]
    linarith
  have ht : |r*a*b+d| ≤ |r| *(|a| *|b|+Real.sqrt A*Real.sqrt B) := by
    calc _ ≤ |r*a*b| + |d| := abs_add_le _ _
         _ ≤ |r*a*b| + |r| * (Real.sqrt A*Real.sqrt B) := add_le_add le_rfl hD
         _ = _ := by rw [abs_mul,abs_mul]; ring
  have hc : (|a| *|b|+Real.sqrt A*Real.sqrt B)^2 ≤ (a^2+A)*(b^2+B) := by
    calc _ ≤ (|a|^2+(Real.sqrt A)^2)*(|b|^2+(Real.sqrt B)^2) := by
               nlinarith [sq_nonneg (|a| *Real.sqrt B-|b| *Real.sqrt A)]
         _ = _ := by rw [sq_abs,sq_abs,Real.sq_sqrt hA,Real.sq_sqrt hB]
  have hs := mul_self_le_mul_self (abs_nonneg _) ht
  rw [←sq,←sq,sq_abs,mul_pow,sq_abs] at hs
  exact hs.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hc (sq_nonneg r))
private lemma tangent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {U V : Submodule ℝ H} {x y : H} (hx : x∈U) (hy : y∈V) (hx1 : ⟪x,x⟫=1)
    (hy1 : ⟪y,y⟫=1) (h : bounded U V ⟪x,y⟫) {u : H} (hu : u∈U) (hu0 : ⟪u,x⟫=0) :
    ⟪u,y⟫=0 := by
  have hx0 : ⟪x,u⟫=0 := (real_inner_comm _ _).trans hu0
  let r := ⟪x,y⟫
  let a := ⟪u,y⟫
  let b := ⟪u,u⟫
  have hb : 0≤b := real_inner_self_nonneg
  have hh := h _ (U.add_mem (U.smul_mem (r*b) hx) (U.smul_mem a hu)) _ hy
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,hx0,hu0,hx1,hy1] at hh
  change (r*b*r+a*a)^2 ≤ r^2*(r*b*(r*b*1)+r*b*(a*0)+(a*(r*b*0)+a*(a*b)))*1 at hh
  by_contra ha
  have hp : 0<a^2 := sq_pos_of_ne_zero ha
  have hp2 : 0<a^2*(r^2*b+a^2) := mul_pos hp (by positivity)
  nlinarith
private lemma criterion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U V : Submodule ℝ H) (x y : H) (hx : x∈U) (hy : y∈V) (hx1 : ⟪x,x⟫=1)
    (hy1 : ⟪y,y⟫=1) :
    bounded U V ⟪x,y⟫ ↔
      (∀ u ∈ U, ⟪u,x⟫=0 → ⟪u,y⟫=0) ∧ (∀ v ∈ V, ⟪v,y⟫=0 → ⟪x,v⟫=0) ∧
      ∀ u ∈ U, ∀ v ∈ V, ⟪u,x⟫=0 → ⟪v,y⟫=0 →
        ⟪u,v⟫^2 ≤ ⟪x,y⟫^2 * ⟪u,u⟫ * ⟪v,v⟫ := by
  constructor
  · intro h
    refine ⟨fun _ => tangent hx hy hx1 hy1 h, ?_, fun u hu v hv _ _ => h u hu v hv⟩
    intro v hv hv0
    have ht : bounded V U ⟪y,x⟫ := by
      intro v hv u hu
      simpa only [real_inner_comm v u,real_inner_comm y x,mul_right_comm] using h u hu v hv
    rw [real_inner_comm v x]
    exact tangent hy hx hy1 hx1 ht hv hv0
  · rintro ⟨hU,hV,hR⟩ u hu v hv
    let a := ⟪u,x⟫
    let b := ⟪v,y⟫
    let U' := u-a • x
    let V' := v-b • y
    have hu' : U'∈U := U.sub_mem hu (U.smul_mem a hx)
    have hv' : V'∈V := V.sub_mem hv (V.smul_mem b hy)
    have hux : ⟪U',x⟫=0 := by simp only [U',a,inner_sub_left,real_inner_smul_left,hx1,mul_one,sub_self]
    have hvy : ⟪V',y⟫=0 := by simp only [V',b,inner_sub_left,real_inner_smul_left,hy1,mul_one,sub_self]
    have huy := hU U' hu' hux
    have hxv := hV V' hv' hvy
    have hxu := (real_inner_comm U' x).trans hux
    have hyv := (real_inner_comm V' y).trans hvy
    have h := scalar_bound ⟪x,y⟫ a b ⟪U',V'⟫ ⟪U',U'⟫ ⟪V',V'⟫
      real_inner_self_nonneg real_inner_self_nonneg (hR U' hu' V' hv' hux hvy)
    rw [show u=U'+a • x by simp [U'],show v=V'+b • y by simp [V']]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      hux,hvy,hxu,hyv,huy,hxv,hx1,hy1]
    linarith only [h]
end OMA.S_mo_228204

namespace OMA.S_mo_228204
open MeasureTheory ProbabilityTheory
open scoped ENNReal
private noncomputable abbrev D := γ.prod γ
private def S (p : ℝ×ℝ) := p.1+p.2
private lemma sum_map : D.map S = ν := by
  change Measure.conv γ γ = ν
  rw [gaussianReal_conv_gaussianReal]
  norm_num [ν]
private lemma twice_map : γ.map (2*·) = gaussianReal 0 4 := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  norm_num
private lemma cfst (s : ℝ) : (coupled s).map Prod.fst = γ.map (s*·) := by
  rw [coupled,Measure.map_map measurable_fst (by fun_prop)]
  change D.map ((s*·) ∘ Prod.fst) = _
  rw [←Measure.map_map (by fun_prop) measurable_fst]
  simp [D]
private lemma csnd (s : ℝ) : (coupled s).map Prod.snd = ν := by
  rw [coupled,Measure.map_map measurable_snd (by fun_prop)]
  exact sum_map
private lemma ratio_enn : ((1:ℝ≥0∞)/4)+1/4=1/2 ∧ (1:ℝ≥0∞)/2+1/2=1 := by
  constructor <;> apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;> norm_num [ENNReal.toReal_add]
private lemma marginals : joint.map Prod.fst = μX ∧ joint.map Prod.snd = ν := by
  constructor
  · simp only [joint,Measure.map_add _ _ measurable_fst,Measure.map_smul,cfst,one_mul,Measure.map_id',
      Measure.map_fst_prod,measure_univ,one_smul,twice_map,μX]
    rw [add_right_comm,←add_smul,ratio_enn.1]
  · simp only [joint,Measure.map_add _ _ measurable_snd,Measure.map_smul,csnd,
      Measure.map_snd_prod,measure_univ,one_smul]
    rw [add_right_comm,←add_smul,ratio_enn.1,←add_smul,ratio_enn.2,one_smul]
private lemma prob_joint : IsProbabilityMeasure joint := by
  constructor
  have h := congrArg (fun σ : Measure ℝ => σ Set.univ) marginals.2
  simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using h
private lemma coupled_ac (s : ℝ) (hs : γ.map (s*·) ≪ volume) : coupled s ≪ volume := by
  let h : ℝ×ℝ → ℝ×ℝ := fun p => (p.1,p.1+p.2)
  let k := Prod.map (s*·) (id : ℝ→ℝ)
  have hh : Measurable h := by dsimp [h]; fun_prop
  have hk : Measurable k := (by fun_prop : Measurable (fun x : ℝ => s*x)).prodMap measurable_id
  have hm : D.map h ≪ γ.prod volume := by
    have h1 := (Measure.AbsolutelyContinuous.rfl (μ := γ)).prod (gaussianReal_absolutelyContinuous 0 (v := 1) one_ne_zero)
    have he : (γ.prod volume).map h = γ.prod volume := (measurePreserving_prod_add γ volume).map_eq
    simpa only [he] using h1.map hh
  have h2 := hm.map hk
  rw [Measure.map_map hk hh,←Measure.map_prod_map _ _ (by fun_prop) measurable_id] at h2
  exact h2.trans (by rw [Measure.volume_eq_prod]; simpa [Measure.map_id] using hs.prod (Measure.AbsolutelyContinuous.rfl (μ := (volume : Measure ℝ))))
private lemma joint_ac : joint ≪ volume := by
  have h1 := gaussianReal_absolutelyContinuous 0 (v := 1) one_ne_zero
  have h2 := gaussianReal_absolutelyContinuous 0 (v := 2) (by norm_num)
  have h4 := gaussianReal_absolutelyContinuous 0 (v := 4) (by norm_num)
  exact (((coupled_ac 1 (by simpa only [one_mul,Measure.map_id'] using h1)).smul_left _).add_left
    ((coupled_ac 2 (twice_map ▸ h4)).smul_left _)).add_left (by rw [Measure.volume_eq_prod]; exact (h1.prod h2).smul_left _)
end OMA.S_mo_228204

namespace OMA.S_mo_228204
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
private lemma int_X {f : ℝ → ℝ} (h1 : Integrable f γ) (h4 : Integrable f (gaussianReal 0 4)) :
    (∫ x,f x ∂μX)=((∫ x,f x ∂γ)+(∫ x,f x ∂gaussianReal 0 4))/2 := by
  rw [μX,integral_add_measure (h1.smul_measure (by finiteness)) (h4.smul_measure (by finiteness))]
  simp only [integral_smul_measure, smul_eq_mul]
  norm_num
  ring
private lemma id_lp (v : ℝ≥0) : MemLp (id : ℝ→ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal' _ (by norm_num)
private lemma gauss_sq (v : ℝ≥0) : (∫ z,z^2 ∂gaussianReal 0 v) = v := by
  have h := variance_eq_sub (id_lp v)
  simpa [variance_id_gaussianReal] using h.symm
private lemma stats : centered μX id ∧ centered ν id ∧ (∫ x,x^2 ∂μX)=5/2 ∧ (∫ y,y^2 ∂ν)=2 := by
  have h1 := id_lp 1
  have h4 := id_lp 4
  have hm : (∫ x,x ∂μX)=0 := by
    change (∫ x,id x ∂μX)=0
    rw [int_X (f := id) (h1.integrable (by norm_num)) (h4.integrable (by norm_num))]
    simp
  have hs : (∫ x,x^2 ∂μX)=5/2 := by
    change (∫ x,(id x)^2 ∂μX)=5/2
    rw [int_X h1.integrable_sq h4.integrable_sq]; simp only [id_eq,gauss_sq]; norm_num
  refine ⟨⟨measurable_id, ?_,hm⟩,⟨measurable_id,id_lp 2,integral_id_gaussianReal⟩,hs,?_⟩
  · apply (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
    exact (h1.integrable_sq.smul_measure (by finiteness)).add_measure (h4.integrable_sq.smul_measure (by finiteness))
  · simpa using gauss_sq 2
private lemma nongauss (m : ℝ) (v : ℝ≥0) : μX ≠ gaussianReal m v := by
  intro he
  have hm := stats.1.2.2
  rw [he] at hm
  change (∫ x,x ∂gaussianReal m v)=0 at hm
  rw [integral_id_gaussianReal] at hm
  subst m
  have hv := stats.2.2.1
  rw [he,gauss_sq] at hv
  have exp_int (w : ℝ≥0) : (∫ x,Real.exp x ∂gaussianReal 0 w)=Real.exp ((w:ℝ)/2) := by
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := w)) 1
    simpa [mgf] using h
  have integ (w : ℝ≥0) : Integrable Real.exp (gaussianReal 0 w) := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := w) 1
  have h := int_X (integ 1) (integ 4)
  rw [he,exp_int,exp_int,exp_int,hv] at h
  norm_num at h
  have he1 : Real.exp (1/2) = (Real.exp (1/4))^2 := by rw [←Real.exp_nat_mul]; norm_num
  have he2 : Real.exp 2 = (Real.exp 1)^2 := by rw [←Real.exp_nat_mul]; norm_num
  have he3 : Real.exp (5/4) = Real.exp (1/4)*Real.exp 1 := by rw [←Real.exp_add]; norm_num
  have hp : 0 < (Real.exp (1/4)-Real.exp 1)^2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (Real.exp_injective.ne (by norm_num)))
  nlinarith [he1,he2,he3]
private lemma l2_inner {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α→ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x,f x*g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  simp [hx,hy,mul_comm]
private lemma integral_cs {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α→ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,f x*g x ∂μ)^2 ≤ (∫ x,(f x)^2 ∂μ)*(∫ x,(g x)^2 ∂μ) := by
  simpa only [l2_inner,pow_two] using real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
end OMA.S_mo_228204

namespace OMA.S_mo_228204
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
private lemma mS : Measurable S := measurable_fst.add measurable_snd
private lemma pS : MeasurePreserving S D ν := ⟨mS,sum_map⟩
private lemma imul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α→ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x*g x) μ := hf.integrable_mul hg
private lemma int_sum (g : ℝ→ℝ) (hg : Measurable g) : (∫ p,g (S p) ∂D) = ∫ z,g z ∂ν := by
  rw [←sum_map,integral_map mS.aemeasurable hg.aestronglyMeasurable]
private lemma int_left (f : ℝ→ℝ) : (∫ p : ℝ×ℝ,f p.1 ∂D)=∫ z,f z ∂γ := by
  simpa [D] using (integral_prod_mul (μ := γ) (ν := γ) f (fun _ => (1:ℝ)))
private lemma int_right (f : ℝ→ℝ) : (∫ p : ℝ×ℝ,f p.2 ∂D)=∫ z,f z ∂γ := by
  simpa [D] using (integral_prod_mul (μ := γ) (ν := γ) (fun _ => (1:ℝ)) f)
private lemma int_sq_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α→ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,(f x+g x)^2 ∂μ)=(∫ x,(f x)^2 ∂μ)+2*(∫ x,f x*g x ∂μ)+(∫ x,(g x)^2 ∂μ) := by
  simp only [add_sq,mul_assoc]
  rw [integral_add (f := fun x => f x^2+2*(f x*g x)) (hf.integrable_sq.add ((imul hf hg).const_mul 2)) hg.integrable_sq,
    integral_add hf.integrable_sq ((imul hf hg).const_mul 2),integral_const_mul]
private lemma exchange {h g : ℝ→ℝ} (hh : MemLp h 2 γ) (hg : centered ν g) :
    (∫ p,h p.1*g (S p) ∂D)^2 ≤ (1/2:ℝ)*(∫ x,(h x)^2 ∂γ)*(∫ y,(g y)^2 ∂ν) := by
  let c := ∫ x,h x ∂γ
  let F := fun x => h x-c
  let G := fun p => g (S p)
  have hF : MemLp F 2 γ := hh.sub (memLp_const _)
  have hG : MemLp G 2 D := hg.2.1.comp_measurePreserving pS
  have hG0 : (∫ p,G p ∂D)=0 := (int_sum g hg.1).trans hg.2.2
  have hF0 : (∫ x,F x ∂γ)=0 := by
    dsimp [F]
    rw [integral_sub (hh.integrable (by norm_num)) (integrable_const _)]
    simp [c]
  have hFB : (∫ x,(F x)^2 ∂γ) ≤ ∫ x,(h x)^2 ∂γ := by
    change (∫ x,(h x - ∫ z,h z ∂γ)^2 ∂γ) ≤ _
    rw [←variance_eq_integral hh.aestronglyMeasurable.aemeasurable,variance_eq_sub hh]
    exact sub_le_self _ (sq_nonneg _)
  have hl := hF.comp_fst γ
  have hr := hF.comp_snd γ
  have hs : (∫ p,F p.2*G p ∂D) = ∫ p,F p.1*G p ∂D := by
    simpa [G,S,D,add_comm] using integral_prod_swap (μ := γ) (ν := γ) (fun p : ℝ×ℝ => F p.1*G p)
  have hcross : (∫ p,F p.1*G p ∂D) = ∫ p,h p.1*G p ∂D := by
    simp only [F,sub_mul]
    rw [integral_sub (imul (hh.comp_fst γ) hG) ((hG.integrable (by norm_num)).const_mul _),
      integral_const_mul,hG0,mul_zero,sub_zero]
  have hsum : (∫ p,(F p.1+F p.2)*G p ∂D)=2*(∫ p,h p.1*g (S p) ∂D) := by
    simp_rw [add_mul]
    rw [integral_add (imul hl hG) (imul hr hG),hs,hcross]
    ring
  have henergy : (∫ p : ℝ×ℝ,(F p.1+F p.2)^2 ∂D)=2*(∫ x,(F x)^2 ∂γ) := by
    rw [int_sq_add hl hr,int_left (fun z => F z^2),int_right (fun z => F z^2),
      integral_prod_mul,hF0]
    ring
  have hh' := integral_cs (hl.add hr) hG
  change (∫ p,(F p.1+F p.2)*G p ∂D)^2 ≤ (∫ p : ℝ×ℝ,(F p.1+F p.2)^2 ∂D)*(∫ p,G p^2 ∂D) at hh'
  rw [hsum,henergy,int_sum (fun y => g y^2) (hg.1.pow_const _)] at hh'
  nlinarith [mul_le_mul_of_nonneg_right hFB (integral_nonneg (fun y => sq_nonneg (g y)) (μ := ν))]
end OMA.S_mo_228204

namespace OMA.S_mo_228204
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
private noncomputable def H (f : ℝ→ℝ) (z : ℝ) : ℝ := (1/4)*f z+(1/2)*f (2*z)
private lemma split_lp {f : ℝ→ℝ} (hf : centered μX f) :
    MemLp f 2 γ ∧ MemLp f 2 (gaussianReal 0 4) := by
  have h := hf.2.1.integrable_sq
  rw [μX,integrable_add_measure,integrable_smul_measure (by norm_num) (by finiteness)] at h
  exact ⟨(memLp_two_iff_integrable_sq hf.1.aestronglyMeasurable).mpr h.1,
    (memLp_two_iff_integrable_sq hf.1.aestronglyMeasurable).mpr
      ((integrable_smul_measure (by norm_num) (by finiteness)).mp h.2)⟩
private lemma lp2 {f : ℝ→ℝ} (hf : centered μX f) : MemLp (fun x => f (2*x)) 2 γ :=
  (split_lp hf).2.comp_measurePreserving (show MeasurePreserving (2*·) γ (gaussianReal 0 4) from ⟨by fun_prop,twice_map⟩)
private lemma Hlp {f : ℝ→ℝ} (hf : centered μX f) : MemLp (H f) 2 γ :=
  ((split_lp hf).1.const_mul (1/4)).add ((lp2 hf).const_mul (1/2))
private lemma int_c {f g : ℝ→ℝ} (hf : Measurable f) (hg : Measurable g) (s : ℝ) :
    (∫ p,f p.1*g p.2 ∂coupled s) = ∫ p,f (s*p.1)*g (S p) ∂D := by
  rw [coupled,integral_map (φ := fun p : ℝ×ℝ => (s*p.1,p.1+p.2)) (by fun_prop) (by fun_prop)]
  rfl
private lemma score_repr {f g : ℝ→ℝ} (hf : centered μX f) (hg : centered ν g) :
    (∫ p,f p.1*g p.2 ∂joint) = ∫ p,H f p.1 * g (S p) ∂D := by
  have h1 : MemLp f 2 ((coupled 1).map Prod.fst) := by simpa only [cfst,one_mul,Measure.map_id'] using (split_lp hf).1
  have h2 : MemLp f 2 ((coupled 2).map Prod.fst) := by simpa only [cfst,twice_map] using (split_lp hf).2
  have hc (s : ℝ) (hs : MemLp f 2 ((coupled s).map Prod.fst)) : Integrable (fun p : ℝ×ℝ => f p.1*g p.2) (coupled s) :=
    imul (hs.comp_of_map measurable_fst.aemeasurable) (hg.2.1.comp_measurePreserving (show MeasurePreserving Prod.snd (coupled s) ν from ⟨measurable_snd,csnd _⟩))
  have h3 := imul ((split_lp hf).1.comp_fst ν) (hg.2.1.comp_snd γ)
  have h1' := (hc 1 h1).smul_measure (c := (1:ℝ≥0∞)/4) (by finiteness)
  have h2' := (hc 2 h2).smul_measure (c := (1:ℝ≥0∞)/2) (by finiteness)
  have h3' := h3.smul_measure (c := (1:ℝ≥0∞)/4) (by finiteness)
  rw [joint,integral_add_measure (h1'.add_measure h2') h3',integral_add_measure h1' h2']
  simp only [integral_smul_measure,smul_eq_mul,int_c hf.1 hg.1,integral_prod_mul,hg.2.2,mul_zero,
    add_zero,one_mul]
  have hG := hg.2.1.comp_measurePreserving pS
  have h1G : Integrable (fun p : ℝ×ℝ => f p.1*g (S p)) D := imul ((split_lp hf).1.comp_fst γ) hG
  have h2G : Integrable (fun p : ℝ×ℝ => f (2*p.1)*g (S p)) D := imul ((lp2 hf).comp_fst γ) hG
  simp only [H,add_mul,mul_assoc]
  rw [integral_add (h1G.const_mul _) (h2G.const_mul _),integral_const_mul,integral_const_mul]
  norm_num
private lemma Hsmall {f : ℝ→ℝ} (hf : centered μX f) :
    (∫ x,H f x^2 ∂γ) ≤ (5/8:ℝ)*(∫ x,f x^2 ∂μX) := by
  have h1 := (split_lp hf).1
  have h2 := lp2 hf
  have h4 := (split_lp hf).2
  have hfour : (∫ x,f (2*x)^2 ∂γ) = ∫ x,f x^2 ∂gaussianReal 0 4 := by
    rw [←twice_map,integral_map (φ := (2*·)) (by fun_prop) (hf.1.pow_const 2).aestronglyMeasurable]
  have h := integral_mono (Hlp hf).integrable_sq ((h1.integrable_sq.add h2.integrable_sq).const_mul (5/16)) (fun x => show H f x^2 ≤ (5/16)*(f x^2+f (2*x)^2) by dsimp [H]; nlinarith [sq_nonneg (2*f x-f (2*x))])
  simp only [Pi.add_apply] at h
  rw [integral_const_mul,integral_add h1.integrable_sq h2.integrable_sq,hfour] at h
  rw [int_X h1.integrable_sq h4.integrable_sq]
  linarith
private lemma cross_id : (∫ p,p.1*p.2 ∂joint)=5/4 := by
  have h := score_repr stats.1 stats.2.1
  change (∫ p,p.1*p.2 ∂joint) = ∫ p,H id p.1 * S p ∂D at h
  rw [h]
  have H' : H id = fun z => (5/4)*z := by funext z; dsimp [H]; ring
  simp only [H',S,mul_assoc]
  rw [integral_const_mul]
  simp_rw [mul_add,←sq]
  rw [integral_add (show Integrable (fun p : ℝ×ℝ => p.1^2) D from ((id_lp 1).comp_fst γ).integrable_sq)
      (show Integrable (fun p : ℝ×ℝ => p.1*p.2) D from imul ((id_lp 1).comp_fst γ) ((id_lp 1).comp_snd γ)),
      int_left (fun z => z^2),gauss_sq,integral_prod_mul (fun x : ℝ => x) (fun x => x)]
  norm_num
end OMA.S_mo_228204

open MeasureTheory
open OMA.S_mo_228204
theorem OMA.solution : type_of% @OMA.S_mo_228204.main := by
  have hid : squaredCorrelation id id=5/16 := by
    simp only [squaredCorrelation,id_eq,cross_id,stats.2.2.1,stats.2.2.2]
    norm_num
  refine ⟨fun _ _ _ U V x y => criterion U V x y, prob_joint,joint_ac,marginals.1,marginals.2,
    nongauss,stats.1,stats.2.1,stats.2.2.1,stats.2.2.2,cross_id,hid,?_,?_⟩
  · exact ⟨id,id,stats.1,stats.2.1,by simp [stats.2.2.1],
      by simp [stats.2.2.2],hid⟩
  · rintro v ⟨f,g,hf,hg,hf0,hg0,rfl⟩
    apply (div_le_iff₀ (mul_pos hf0 hg0)).mpr
    rw [score_repr hf hg]
    have h := exchange (Hlp hf) hg
    have hu := mul_le_mul_of_nonneg_right (Hsmall hf) (integral_nonneg (fun y => sq_nonneg (g y)) (μ := ν))
    nlinarith
