import OMAStatements.S_mo_332533

open Set MeasureTheory OMA.S_mo_332533

private theorem smooth_weak (f : Space 1 → ℝ) (D : Space 1)
    (hf : ContDiff ℝ ⊤ f)
    (hD : ∀ i x, fderiv ℝ f x (Pi.single i 1) = D i) :
    sobolev f (fun _ => D) := by
  have loc (g : Space 1 → ℝ) (hg : Continuous g) : locallyL2 g :=
    ⟨hg.aestronglyMeasurable, (hg.pow 2).locallyIntegrable⟩
  refine ⟨loc f hf.continuous, fun i => ⟨loc (fun _ => D i) continuous_const, ?_⟩⟩
  intro φ hφ hcompact
  let e : Space 1 := Pi.single i 1
  have hder : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have ha : Integrable (fun x => (fderiv ℝ f x e) * φ x) := by
    simp_rw [e, hD]
    exact (continuous_const.mul hφ.continuous).integrable_of_hasCompactSupport hcompact.mul_left
  have hb : Integrable (fun x => f x * fderiv ℝ φ x e) :=
    (hf.continuous.mul hder).integrable_of_hasCompactSupport (hcompact.fderiv_apply ℝ e).mul_left
  have hc : Integrable (fun x => f x * φ x) :=
    (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hcompact.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ha hb hc
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hφ.differentiable (by simp) x)
  simpa only [e, hD] using h

private theorem fails (full : Bool) : ¬ positiveForSmall full := by
  intro h
  obtain ⟨δ, hδ, hall⟩ := h 1 1 (by norm_num)
  let ε : ℝ := δ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεδ : ε < δ := by dsimp [ε]; linarith
  let u : Space 1 → ℝ := fun _ => 1 - ε
  let v : Space 1 → ℝ := fun x => x 1 - x 0
  let D : Space 1 := fun i => (Pi.single i (1 : ℝ) : Space 1) 1 - (Pi.single i (1 : ℝ) : Space 1) 0
  have hu : periodic 1 u := by intro x; rfl
  have hv : periodic 1 v := by intro x; simp [v]
  have hu' : sobolev u (fun _ => 0) :=
    smooth_weak u 0 (by exact contDiff_const) (by intros; simp [u])
  have hv' : sobolev v (fun _ => D) := by
    apply smooth_weak v D
    · unfold v
      fun_prop
    · intro i x
      have hproj (j : Fin 2) :
          HasFDerivAt (fun y : Space 1 => y j) (ContinuousLinearMap.proj j) x :=
        (ContinuousLinearMap.proj j : Space 1 →L[ℝ] ℝ).hasFDerivAt
      rw [show fderiv ℝ v x = ContinuousLinearMap.proj (1 : Fin 2) - ContinuousLinearMap.proj (0 : Fin 2) from
        ((hproj 1).sub (hproj 0)).fderiv]
      rfl
  have hD : D 0 = -1 := by norm_num [D, Pi.single_apply]
  have hvol : volume (Icc (0 : Space 1) (fun _ => (1 : ℝ))) = 1 := by
    rw [Real.volume_Icc_pi]
    simp
  have hc : constraint 1 u (fun _ => D) = ε := by
    have hint : (fun x : Space 1 => D 0 * (u x - 1)) = fun _ => ε := by
      ext x
      rw [hD]
      dsimp [u]
      ring
    simp [constraint, hint, Measure.real, hvol]
  have hE : energy full 1 u (fun _ => 0) (fun _ => D) = (-1 / Real.sqrt 2) * ε ^ 2 := by
    unfold energy
    have hfun : (fun x : Space 1 =>
        (if full then ∑ i : Fin 2, ((0 : Space 1) i)^2 else ((0 : Space 1) 0)^2)/2 +
          D 0 / Real.sqrt 2 * (u x - 1)^2) = fun _ => (-1 / Real.sqrt 2) * ε ^ 2 := by
      ext x
      rw [hD]
      cases full <;> simp [u]
    rw [hfun, setIntegral_const]
    simp [Measure.real, hvol]
  have hpos := hall ε hε hεδ u v (fun _ => 0) (fun _ => D) hu hv hu' hv' hc
  rw [hE] at hpos
  have hnonpos : (-1 / Real.sqrt 2) * ε ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (sq_nonneg _)
  exact (not_lt_of_ge hnonpos) hpos

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_332533.main) := by
  intro h
  exact h.elim (fails false) (fails true)