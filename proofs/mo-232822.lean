import OMAStatements.S_mo_232822

namespace OMA.S_mo_232822
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private noncomputable abbrev normal := gaussianReal 0 1
private noncomputable def moment (k : ℕ) := ∫ x : ℝ, x^k ∂normal

private lemma moment_zero : moment 0 = 1 := by simp [moment]
private lemma moment_one : moment 1 = 0 := by simp [moment]
private lemma moment_two : moment 2 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [moment] using h

private lemma moment_four : moment 4 = 3 := by
  let F (t : ℝ) := Real.exp (t^2/2)
  have hF (t : ℝ) : HasDerivAt F (t*F t) t := by
    convert (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;> simp [F]
    ring
  have h2 (t : ℝ) : HasDerivAt (fun t => t*F t) ((1+t^2)*F t) t := by
    convert (hasDerivAt_id t).mul (hF t) using 1 <;> first | rfl | (simp [id_eq]; ring)
  have h3 (t : ℝ) : HasDerivAt (fun t => (1+t^2)*F t) ((3*t+t^3)*F t) t := by
    convert (((hasDerivAt_id t).pow 2).const_add 1).mul (hF t) using 1 <;> first | rfl | (simp [Pi.pow_apply,id_eq]; ring)
  have h4 := (((hasDerivAt_id (0:ℝ)).const_mul 3).add ((hasDerivAt_id (0:ℝ)).pow 3)).mul (hF 0)
  have hm : mgf (fun x : ℝ => x) normal = F := by simp [mgf_fun_id_gaussianReal,F]
  change (∫ x : ℝ, x^4 ∂normal) = 3
  have hmv := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := normal) (by simp) 4
  change _ = (∫ x : ℝ, x^4 ∂normal) at hmv
  rw [← hmv,hm]
  simp only [show 4 = 1+1+1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_zero,
    funext fun t => (hF t).deriv, funext fun t => (h2 t).deriv, funext fun t => (h3 t).deriv]
  have h4' := h4.deriv
  change deriv (fun t => (3*t+t^3)*F t) 0 = _ at h4'
  simpa [F] using h4'

private def mon (i j k : ℕ) (w : Ω) : ℝ := w.1^i*(w.2.1^j*w.2.2^k)

private lemma mon_integrable (i j k : ℕ) : Integrable (mon i j k) law := by
  have hp (u : ℕ) : Integrable (fun t : ℝ => t^u) normal := by
    exact integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) u
  exact (hp i).mul_prod ((hp j).mul_prod (hp k))

private lemma mon_eval (i j k : ℕ) : (∫ w, mon i j k w ∂law) = moment i*(moment j*moment k) := by
  unfold mon law moment
  rw [integral_prod_mul (fun x : ℝ => x^i) (fun y : ℝ×ℝ => y.1^j*y.2^k),
    integral_prod_mul (fun x : ℝ => x^j) (fun y : ℝ => y^k)]

private lemma mon_mem (i j k : ℕ) : MemLp (mon i j k) 2 law := by
  apply (memLp_two_iff_integrable_sq (by unfold mon; fun_prop)).2
  have he : (fun w => (mon i j k w)^2) = mon (i*2) (j*2) (k*2) := by
    funext w
    simp [mon, pow_mul, mul_pow]
  rw [he]
  exact mon_integrable ..

lemma Y_memLp : MemLp Y 2 law := by
  rw [show Y = mon 1 0 0 by funext w; simp [Y,mon]]
  exact mon_mem ..
lemma Z_memLp : MemLp Z 2 law := by
  have he : Z = mon 1 0 0 + mon 0 1 0 := by funext w; simp [mon,Z]
  rw [he]
  exact (mon_mem ..).add (mon_mem ..)
lemma X_memLp : MemLp X 2 law := by
  have he : X = mon 2 0 0 + mon 0 0 1 := by funext w; simp [mon,X]
  rw [he]
  exact (mon_mem ..).add (mon_mem ..)
lemma xz_memLp : MemLp (fun w => X w*Z w) 2 law := by
  have he : (fun w => X w*Z w) = mon 3 0 0 + mon 2 1 0 + mon 1 0 1 + mon 0 1 1 := by
    funext w; simp [mon,X,Z]; ring
  rw [he]
  exact (((mon_mem ..).add (mon_mem ..)).add (mon_mem ..)).add (mon_mem ..)

lemma Y_mean : (∫ w, Y w ∂law) = 0 := by
  simpa [Y,mon,moment_zero,moment_one] using mon_eval 1 0 0
lemma Y_second : (∫ w, (Y w)^2 ∂law) = 1 := by
  simpa [Y,mon,moment_zero,moment_two] using mon_eval 2 0 0
lemma half_error : (∫ w, (Y w-Z w/2)^2 ∂law) = 1/2 := by
  have he (w : Ω) : (Y w-Z w/2)^2 = (mon 2 0 0 w - 2*mon 1 1 0 w + mon 0 2 0 w)/4 := by
    simp [Y,Z,mon]; ring
  simp_rw [he]
  simp (disch := solve_by_elim (maxDepth := 12) only
    [mon_integrable, Integrable.add, Integrable.sub, Integrable.const_mul])
    [integral_add, integral_sub, integral_div, integral_const_mul, mon_eval,
      moment_zero, moment_one, moment_two]
  norm_num
lemma residual_corr : (∫ w, (Y w-Z w/2)*(X w*Z w) ∂law) = 1 := by
  have he (w : Ω) : (Y w-Z w/2)*(X w*Z w) =
      (mon 4 0 0 w - mon 2 2 0 w + mon 2 0 1 w - mon 0 2 1 w)/2 := by
    simp [X,Y,Z,mon]; ring
  simp_rw [he]
  simp (disch := solve_by_elim (maxDepth := 12) only
    [mon_integrable, Integrable.add, Integrable.sub, Integrable.const_mul])
    [integral_add, integral_sub, integral_div, mon_eval,
      moment_zero, moment_one, moment_two, moment_four]
  norm_num

lemma not_indep_x_z : ¬IndepFun X Z law := by
  intro h
  have hX : (∫ w, X w ∂law) = 1 := by
    have he (w : Ω) : X w = mon 2 0 0 w + mon 0 0 1 w := by simp [X,mon]
    simp_rw [he]
    simp (disch := solve_by_elim (maxDepth := 12) only
      [mon_integrable, Integrable.add, Integrable.sub, Integrable.const_mul])
      [integral_add, mon_eval,
        moment_zero, moment_one, moment_two]
  have hZ : (∫ w, (Z w)^2 ∂law) = 2 := by
    have he (w : Ω) : (Z w)^2 = mon 2 0 0 w + 2*mon 1 1 0 w + mon 0 2 0 w := by simp [Z,mon]; ring
    simp_rw [he]
    simp (disch := solve_by_elim (maxDepth := 12) only
      [mon_integrable, Integrable.add, Integrable.sub, Integrable.const_mul])
      [integral_add, integral_const_mul, mon_eval,
        moment_zero, moment_one, moment_two]
    norm_num
  have hXZ : (∫ w, X w*(Z w)^2 ∂law) = 4 := by
    have he (w : Ω) : X w*(Z w)^2 = mon 4 0 0 w + 2*mon 3 1 0 w + mon 2 2 0 w +
        mon 2 0 1 w + 2*mon 1 1 1 w + mon 0 2 1 w := by simp [X,Z,mon]; ring
    simp_rw [he]
    simp (disch := solve_by_elim (maxDepth := 12) only
      [mon_integrable, Integrable.add, Integrable.sub, Integrable.const_mul])
      [integral_add, integral_const_mul, mon_eval,
        moment_zero, moment_one, moment_two, moment_four]
    norm_num
  have h' : IndepFun X (fun w => (Z w)^2) law := h.comp measurable_id (measurable_id.pow_const 2)
  have := h'.integral_fun_mul_eq_mul_integral (by unfold X; fun_prop) (by unfold Z; fun_prop)
  rw [hX,hZ,hXZ] at this
  norm_num at this

end OMA.S_mo_232822

namespace OMA.S_mo_232822

open MeasureTheory ProbabilityTheory

private noncomputable abbrev stdG := gaussianReal 0 1

lemma noiseSwap_preserving :
    MeasurePreserving (fun ω : Ω => (ω.2.1,(ω.1,ω.2.2))) law law := by
  have h := measurePreserving_prodAssoc stdG stdG stdG
  exact h.comp (((Measure.measurePreserving_swap (μ := stdG) (ν := stdG)).prod
    (MeasurePreserving.id stdG)).comp (MeasurePreserving.symm MeasurableEquiv.prodAssoc h))

private def noiseSwapEquiv : Ω ≃ᵐ Ω where
  toFun ω := (ω.2.1,(ω.1,ω.2.2))
  invFun ω := (ω.2.1,(ω.1,ω.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun ω : Ω => (ω.2.1,(ω.1,ω.2.2))); fun_prop
  measurable_invFun := by change Measurable (fun ω : Ω => (ω.2.1,(ω.1,ω.2.2))); fun_prop

private def reflectEquiv : Ω ≃ᵐ Ω where
  toFun ω := (-ω.1,ω.2)
  invFun ω := (-ω.1,ω.2)
  left_inv _ := by simp
  right_inv _ := by simp
  measurable_toFun := by change Measurable (fun ω : Ω => (-ω.1,ω.2)); fun_prop
  measurable_invFun := by change Measurable (fun ω : Ω => (-ω.1,ω.2)); fun_prop

private lemma reflect_preserving : MeasurePreserving reflectEquiv law law := by
  have h : MeasurePreserving (fun x : ℝ => -x) stdG stdG :=
    ⟨by fun_prop,by simp [stdG,gaussianReal_map_neg]⟩
  exact h.prod (MeasurePreserving.id (stdG.prod stdG))

private lemma set_integral_symmetry (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e law law)
    (U : Ω → ℝ) (hU : ∀ ω, U (e ω) = U ω) (s : Set Ω)
    (hs : MeasurableSet[MeasurableSpace.comap U (borel ℝ)] s) :
    (∫ ω in s, Y (e ω) ∂law) = ∫ ω in s, Y ω ∂law := by
  obtain ⟨t,_,rfl⟩ := hs
  have heq : e ⁻¹' (U ⁻¹' t) = U ⁻¹' t := by
    ext ω
    simp [Set.mem_preimage,hU]
  simpa only [heq] using he.setIntegral_preimage_emb e.measurableEmbedding Y (U ⁻¹' t)

private lemma coordinate_integrable : Integrable Y law :=
  measurePreserving_fst.integrable_comp_of_integrable
    (IsGaussian.integrable_id (μ := stdG))

lemma cond_X_zero : law[Y | mX] =ᵐ[law] 0 := by
  let : IsProbabilityMeasure law := by unfold law; infer_instance
  have hm : mX ≤ (inferInstance : MeasurableSpace Ω) := (show Measurable X by unfold X; fun_prop).comap_le
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm coordinate_integrable
    (fun _ _ _ => integrable_zero _ _ _) ?_ aestronglyMeasurable_zero
  intro s hs _
  have h := set_integral_symmetry reflectEquiv reflect_preserving X
    (fun ω => by simp [X,reflectEquiv]) s hs
  change (∫ ω in s, -Y ω ∂law) = ∫ ω in s, Y ω ∂law at h
  rw [integral_neg] at h
  simp only [Pi.zero_apply, integral_zero]
  linarith

lemma cond_Z_half : law[Y | mZ] =ᵐ[law] fun ω => Z ω / 2 := by
  let : IsProbabilityMeasure law := by unfold law; infer_instance
  have hm : mZ ≤ (inferInstance : MeasurableSpace Ω) := (show Measurable Z by unfold Z; fun_prop).comap_le
  have hmZ : Measurable[mZ] Z := measurable_iff_comap_le.mpr le_rfl
  have hY := coordinate_integrable
  have hN : Integrable (fun ω : Ω => ω.2.1) law :=
    noiseSwap_preserving.integrable_comp_of_integrable hY
  have hhalf : Integrable (fun ω => Z ω/2) law := (hY.add hN).div_const _
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hY
    (fun _ _ _ => hhalf.integrableOn) ?_ (hmZ.div_const _).aestronglyMeasurable
  intro s hs _
  have h := set_integral_symmetry noiseSwapEquiv noiseSwap_preserving Z
    (fun ω => add_comm _ _) s hs
  change (∫ ω in s, ω.2.1 ∂law) = ∫ ω in s, Y ω ∂law at h
  change (∫ ω in s, (Y ω + ω.2.1)/2 ∂law) = ∫ ω in s, Y ω ∂law
  rw [integral_div,integral_add hY.integrableOn hN.integrableOn,h]
  ring

end OMA.S_mo_232822

namespace OMA.S_mo_232822
open MeasureTheory ProbabilityTheory

private lemma residual_orthogonal {T : Type*} [m₀ : MeasurableSpace T] {μ : Measure T}
    [IsFiniteMeasure μ] {m : MeasurableSpace T} (hm : m ≤ m₀) {f g : T → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hmg : StronglyMeasurable[m] g) :
    (∫ x, (f x-(μ[f|m]) x)*g x ∂μ) = 0 := by
  have hfg := hf.integrable_mul hg
  have hcg := (hf.condExp (m := m) (by norm_num)).integrable_mul hg
  have h := condExp_mul_of_stronglyMeasurable_right hmg hfg (hf.integrable (by norm_num))
  simp only [sub_mul]
  rw [integral_sub (f := fun x => f x*g x) (g := fun x => (μ[f|m]) x*g x) hfg hcg,sub_eq_zero]
  exact (integral_condExp (f := f*g) hm).symm.trans (integral_congr_ae h)


lemma mmse_strict (hY : MemLp Y 2 law) (_hZ : MemLp Z 2 law)
    (hg : MemLp (fun ω => X ω*Z ω) 2 law)
    (hc : law[Y|mZ] =ᵐ[law] fun ω => Z ω/2)
    (hr : (∫ ω, (Y ω-Z ω/2)*(X ω*Z ω) ∂law) = 1) : mmse (mX ⊔ mZ) < mmse mZ := by
  have hmX : mX ≤ (inferInstance : MeasurableSpace Ω) := (show Measurable X by unfold X; fun_prop).comap_le
  have hmZ : mZ ≤ (inferInstance : MeasurableSpace Ω) := (show Measurable Z by unfold Z; fun_prop).comap_le
  have hm : (mX ⊔ mZ) ≤ (inferInstance : MeasurableSpace Ω) := sup_le hmX hmZ
  let P := law[Y|(mX ⊔ mZ)]
  let Q := law[Y|mZ]
  let D := P-Q
  have hP : MemLp P 2 law := hY.condExp (by norm_num)
  have hQ : MemLp Q 2 law := hY.condExp (by norm_num)
  have hD : MemLp D 2 law := hP.sub hQ
  have hsmD : StronglyMeasurable[(mX ⊔ mZ)] D :=
    (stronglyMeasurable_condExp (m := (mX ⊔ mZ))).sub (stronglyMeasurable_condExp.mono (show mZ ≤ (mX ⊔ mZ) from le_sup_right))
  have hX := (comap_measurable X (m := borel ℝ)).mono (show mX ≤ (mX ⊔ mZ) from le_sup_left) le_rfl
  have hZ := (comap_measurable Z (m := borel ℝ)).mono (show mZ ≤ (mX ⊔ mZ) from le_sup_right) le_rfl
  have ho := residual_orthogonal hm hY hg (hX.mul hZ).stronglyMeasurable
  have Hpos : 0 < ∫ ω, (D ω)^2 ∂law := by
    by_contra! hle
    have he : (∫ ω, (D ω)^2 ∂law) = 0 := le_antisymm hle (integral_nonneg fun _ => sq_nonneg _)
    have haz := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hD.integrable_sq).mp he
    have heq : (fun ω => (Y ω-Z ω/2)*(X ω*Z ω)) =ᵐ[law] fun ω => (Y ω-P ω)*(X ω*Z ω) := by
      filter_upwards [haz,hc] with ω hz hcω
      change (P ω-Q ω)^2 = 0 at hz
      change Q ω = _ at hcω
      rw [←hcω,sub_eq_zero.mp (sq_eq_zero_iff.mp hz)]
    linarith [integral_congr_ae heq]
  have orth := residual_orthogonal hm hY hD hsmD
  have htop : Integrable (fun ω => (Y ω-P ω)^2+(D ω)^2) law :=
    (hY.sub hP).integrable_sq.add hD.integrable_sq
  have hcross : Integrable (fun ω => (Y ω-P ω)*D ω) law := (hY.sub hP).integrable_mul hD
  have hpyth (ω : Ω) : (Y ω-Q ω)^2 = ((Y ω-P ω)^2+(D ω)^2)+2*((Y ω-P ω)*D ω) := by
    change (Y ω-Q ω)^2 = ((Y ω-P ω)^2+(P ω-Q ω)^2)+2*((Y ω-P ω)*(P ω-Q ω))
    ring
  unfold mmse
  change (∫ ω, (Y ω-P ω)^2 ∂law) < ∫ ω, (Y ω-Q ω)^2 ∂law
  simp_rw [hpyth]
  rw [integral_add htop (hcross.const_mul 2),integral_add (f := fun ω => (Y ω-P ω)^2) (hY.sub hP).integrable_sq hD.integrable_sq,
    integral_const_mul]
  change (∫ ω, (Y ω-P ω)^2 ∂law) < (∫ ω, (Y ω-P ω)^2 ∂law)+(∫ ω, (D ω)^2 ∂law)+2*(∫ ω, (Y ω-P ω)*D ω ∂law)
  change (∫ ω, (Y ω-P ω)*D ω ∂law) = 0 at orth
  linarith
end OMA.S_mo_232822

namespace OMA.S_mo_232822
open MeasureTheory ProbabilityTheory

private lemma input_ac : law.map (fun ω => (X ω,Y ω)) ≪ volume := by
  let γ := gaussianReal 0 1
  have hcoord : MeasurePreserving (fun ω : Ω => (ω.1,ω.2.2)) law (γ.prod γ) :=
    (MeasurePreserving.id γ).prod (measurePreserving_snd (μ:=γ) (ν:=γ))
  let V : Measure ℝ := volume
  have hshear : MeasurePreserving (fun p : ℝ × ℝ => (p.1,p.1^2+p.2)) (V.prod V) (V.prod V) :=
    (MeasurePreserving.id V).skew_product (g:=fun y e : ℝ => y^2+e)
      (by change Measurable (fun p : ℝ×ℝ => p.1^2+p.2); fun_prop)
      (Filter.Eventually.of_forall (fun y => (measurePreserving_add_left V (y^2)).map_eq))
  have hbase : γ ≪ V := gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hs := (Measure.measurePreserving_swap (μ:=V) (ν:=V)).comp hshear
  exact ((hs.quasiMeasurePreserving.mono_left (hbase.prod hbase)).comp
    hcoord.quasiMeasurePreserving).absolutelyContinuous

private lemma noise_law
    (hsw : MeasurePreserving (fun ω : Ω => (ω.2.1,(ω.1,ω.2.2))) law law) :
    law.map (fun ω : Ω => ω.2.1) = gaussianReal 0 1 ∧
    IndepFun (fun ω : Ω => ω.2.1) (fun ω => (X ω,Y ω)) law := by
  let γ := gaussianReal 0 1
  let f (p : ℝ × ℝ) := (p.1^2+p.2,p.1)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hfirst : MeasurePreserving (fun ω : Ω => ω.2.1) law γ :=
    (measurePreserving_fst (μ:=γ) (ν:=γ.prod γ)).comp hsw
  have hsecond : MeasurePreserving (fun ω => (X ω,Y ω)) law ((γ.prod γ).map f) :=
    (hf.measurePreserving _).comp ((measurePreserving_snd (μ:=γ) (ν:=γ.prod γ)).comp hsw)
  have hboth := ((MeasurePreserving.id γ).prod (hf.measurePreserving (γ.prod γ))).comp hsw
  refine ⟨hfirst.map_eq,(indepFun_iff_map_prod_eq_prod_map_map hfirst.measurable.aemeasurable
    hsecond.measurable.aemeasurable).mpr ?_⟩
  rw [hfirst.map_eq,hsecond.map_eq]
  exact hboth.map_eq

end OMA.S_mo_232822

open OMA.S_mo_232822 MeasureTheory ProbabilityTheory InformationTheory

theorem OMA.solution : type_of% @OMA.S_mo_232822.main := by
  have hvar : variance Y law = 1 := by
    rw [variance_eq_integral Y_memLp.aemeasurable,Y_mean]
    simpa using Y_second
  have hx : mmse mX=1 := by
    rw [mmse,← Y_second]
    apply integral_congr_ae
    filter_upwards [cond_X_zero] with x h
    simp [h]
  have hz : mmse mZ=1/2 := by
    rw [mmse,← half_error]
    apply integral_congr_ae
    filter_upwards [cond_Z_half] with x h
    rw [h]
  obtain ⟨hlaw,hnoise⟩ := noise_law noiseSwap_preserving
  refine ⟨input_ac,hlaw,hnoise,hx.trans hvar.symm,hvar,hz,?_,?_⟩
  · have hs := mmse_strict Y_memLp Z_memLp xz_memLp cond_Z_half residual_corr
    rw [hz] at hs
    rw [hx,hvar,hz]
    linarith
  · rw [hx,hvar]
    simp only [div_one,sub_self,ENNReal.ofReal_zero,zero_mul]
    apply pos_iff_ne_zero.mpr
    intro he
    apply not_indep_x_z
    have hX : Measurable X := by unfold X; fun_prop
    have hZ : Measurable Z := by unfold Z; fun_prop
    exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).mpr
      (klDiv_eq_zero_iff.mp he)
