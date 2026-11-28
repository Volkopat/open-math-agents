import OMAStatements.S_mse_4893052

-- Original proof: @connoranderson, published 2026-11-28.
-- Uses: team notes #94310 and #94680.
-- Source: connoranderson/open-math-agents commit
-- 9ee7f81d4cbbb99b81f83ca0ff381bcdd5e3366a, proofs/mse-4893052.lean.
-- Independently checked and submitted as a proof companion by @CubeJerry.

namespace OMA.S_mse_4893052
open MeasureTheory

/-- In coordinates rotated through the contact point, a displacement along the
tangent line has zero real part. This verifies the intersection formula. -/
theorem meetTangents_on_tangent (u v : Circle) (h : (u:ℂ)+v≠0) :
    ((meetTangents u v - u)/(u:ℂ)).re = 0 := by
  have hz : (meetTangents u v-u)/(u:ℂ) = ((v:ℂ)-u)/(u+v:ℂ) := by
    unfold meetTangents
    field_simp [h,Circle.coe_ne_zero u]
    ring
  rw [hz,Complex.div_re,← add_div]
  have hu := Circle.normSq_coe u
  have hv := Circle.normSq_coe v
  rw [Complex.normSq_apply] at hu hv
  simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im]
  rw [show ((v:ℂ).re-(u:ℂ).re)*((u:ℂ).re+(v:ℂ).re)+
    ((v:ℂ).im-(u:ℂ).im)*((u:ℂ).im+(v:ℂ).im)=0 by linarith only [hu,hv], zero_div]

private lemma scaled_ratios (a b c d : ℝ) (hd : d≠0) :
    ratios (d*a) (d*b) (d*c) = ratios a b c := by
  by_cases h : a*b*c=0
  · have h' : d*a*(d*b)*(d*c)=0 := by
      rw [show d*a*(d*b)*(d*c) = d^3*(a*b*c) by ring,h,mul_zero]
    simp [ratios,h,h']
  · have h' : d*a*(d*b)*(d*c)≠0 := by
      rw [show d*a*(d*b)*(d*c) = d^3*(a*b*c) by ring]
      exact mul_ne_zero (pow_ne_zero _ hd) h
    simp only [ratios,if_neg h,if_neg h',←mul_add,mul_div_mul_left _ _ hd]

private lemma cycle_denominator (u v w : Circle) : denominator v w u=denominator u v w := by
  unfold denominator
  ring

private lemma side_identity (u v w : Circle) (hd : denominator u v w ≠ 0) :
    chord (v^2) (w^2) = (denominator u v w/2)*tangentSide u v w := by
  obtain ⟨huv, hvw, hwu⟩ : (u:ℂ)+v≠0 ∧ (v:ℂ)+w≠0 ∧ (w:ℂ)+u≠0 := by
    simpa [denominator,not_or,and_assoc] using hd
  have huw : (u:ℂ)+w≠0 := add_comm (u:ℂ) w ▸ hwu
  have h : (((u:ℂ)+v)*(v+w)*(w+u))*(meetTangents u v-meetTangents u w) =
      2*(u:ℂ)^2*((v:ℂ)^2-(w:ℂ)^2) := by
    unfold meetTangents
    field_simp [huv,huw]
    ring
  have hnorm := congrArg norm h
  simp only [norm_mul,norm_pow,Circle.norm_coe,one_pow,mul_one,Complex.norm_ofNat] at hnorm
  unfold chord tangentSide denominator
  simp only [Circle.coe_pow]
  linarith

private lemma chord_square (v w : Circle) :
    chord (v^2) (w^2) = ‖(v:ℂ)-w‖*‖(v:ℂ)+w‖ := by
  simp only [chord,Circle.coe_pow,←norm_mul]
  congr 1
  ring

private lemma pointwise_shape (z : Sample) :
    inscribed (fun i => z i ^ 2) = tangential z := by
  set u := z 0
  set v := z 1
  set w := z 2
  change ratios (chord (v^2) (w^2)) (chord (w^2) (u^2)) (chord (u^2) (v^2)) =
    if denominator u v w = 0 then 0 else _
  by_cases hd : denominator u v w = 0
  · rw [if_pos hd,chord_square,chord_square,chord_square]
    change ‖(u:ℂ)+v‖*‖(v:ℂ)+w‖*‖(w:ℂ)+u‖=0 at hd
    rcases mul_eq_zero.mp hd with h|h
    · rcases mul_eq_zero.mp h with h|h <;> simp [ratios,h]
    · simp [ratios,h]
  · have hd' : denominator v w u ≠ 0 := (cycle_denominator u v w).symm ▸ hd
    have hd'' : denominator w u v ≠ 0 := (cycle_denominator v w u).symm ▸ hd'
    rw [if_neg hd,side_identity u v w hd,side_identity v w u hd',side_identity w u v hd'',
      cycle_denominator v w u,cycle_denominator u v w]
    apply scaled_ratios
    exact div_ne_zero hd (by norm_num)

/-- For two different samples, their coincidence and antipodality are null
events. More generally, the second point almost surely avoids any prescribed
measurable function of the first. -/
theorem ae_avoids_graph (μ : Measure Circle) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (i j : Fin 3) (hij : i≠j) (f : Circle → Circle) (hf : Measurable f) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin 3 => μ), z j ≠ f (z i) := by
  letI : Nontrivial Circle := ⟨⟨-(1:Circle),1,Circle.neg_ne_self 1⟩⟩
  let ρ := Measure.pi fun _ : Fin 3 => μ
  have hi := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin 3 => μ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hmap := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  change Measure.map (fun z : Sample => (z i,z j)) ρ =
    (Measure.map (fun z : Sample => z i) ρ).prod (Measure.map (fun z : Sample => z j) ρ) at hmap
  rw [(measurePreserving_eval (fun _ : Fin 3 => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin 3 => μ) j).map_eq] at hmap
  let S : Set (Circle × Circle) := {x | x.2 = f x.1}
  have hS : MeasurableSet S := measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  have hnull : μ.prod μ S = 0 := by
    apply Measure.measure_prod_null_of_ae_null hS
    filter_upwards with x
    change μ {f x}=0
    exact measure_singleton _
  rw [← hmap,Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hS] at hnull
  apply ae_iff.mpr
  simpa [S] using hnull

private lemma measurable_inscribed : Measurable inscribed := by
  have hf (i j : Fin 3) : Continuous (fun z : Sample => chord (z i) (z j)) :=
    ((continuous_subtype_val.comp (continuous_apply i)).sub
      (continuous_subtype_val.comp (continuous_apply j))).norm
  have hm (i j : Fin 3) := (hf i j).measurable
  unfold inscribed ratios
  apply Measurable.ite
  · exact measurableSet_eq_fun (((hm 1 2).mul (hm 2 0)).mul (hm 0 1)) measurable_const
  · fun_prop
  · fun_prop (disch := exact hm _ _)

private lemma square_preserves (μ : Measure Circle) [μ.IsHaarMeasure] :
    MeasurePreserving (fun z : Circle => z^2) μ μ := by
  have hsur : Function.Surjective (powMonoidHom (α := Circle) 2) := by
    intro z
    obtain ⟨a,rfl⟩ := Circle.exp_surjective z
    refine ⟨Circle.exp (a/2), ?_⟩
    change Circle.exp (a/2)^2=Circle.exp a
    rw [← Circle.exp_nsmul,two_nsmul]
    congr 1
    ring
  exact MonoidHom.measurePreserving (μ := μ) (ν := μ) (f := powMonoidHom (α := Circle) 2)
    (continuous_pow 2) hsur rfl

end OMA.S_mse_4893052
open OMA.S_mse_4893052 MeasureTheory

theorem OMA.solution : type_of% @OMA.S_mse_4893052.main := by
  intro μ hH hP
  let ρ := Measure.pi fun _ : Fin 3 => μ
  let f (z : Sample) : Sample := fun i => z i ^ 2
  have hm : MeasurePreserving f ρ ρ :=
    measurePreserving_pi (fun _ => μ) (fun _ => μ) (fun _ => square_preserves μ)
  change Measure.map inscribed ρ = Measure.map tangential ρ
  calc
    _ = Measure.map inscribed (Measure.map f ρ) := by rw [hm.map_eq]
    _ = Measure.map (inscribed ∘ f) ρ := Measure.map_map measurable_inscribed hm.measurable
    _ = _ := by rw [show inscribed ∘ f = tangential from funext pointwise_shape]
