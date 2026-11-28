import OMAStatements.S_mo_481234

open MeasureTheory Set OMA.S_mo_481234
open scoped ENNReal

private theorem affineRestricted (a b lo hi lo' hi' : ℝ) (ha : a ≠ 0)
    (himage : (fun x => a*x+b) '' Icc lo hi = Icc lo' hi') :
    (volume.restrict (Icc lo hi)).map (fun x => a*x+b) =
      ENNReal.ofReal |a⁻¹| • volume.restrict (Icc lo' hi') := by
  let f : ℝ → ℝ := fun x => a * x + b
  have hf : Measurable f := (measurable_const.mul measurable_id).add measurable_const
  have hinj : Function.Injective f := by
    intro x y h
    exact mul_left_cancel₀ ha (add_right_cancel h)
  have hvol : (volume : Measure ℝ).map f = ENNReal.ofReal |a⁻¹| • volume := by
    change (volume : Measure ℝ).map ((· + b) ∘ (a * ·)) = _
    have hadd : Measurable (fun x : ℝ => x+b) := measurable_id.add measurable_const
    have hmul : Measurable (fun x : ℝ => a*x) := measurable_const.mul measurable_id
    rw [← Measure.map_map hadd hmul,
      Real.map_volume_mul_left ha, Measure.map_smul, map_add_right_eq_self]
  change (volume.restrict (Icc lo hi)).map f = _
  ext s hs
  rw [Measure.map_apply hf hs, Measure.restrict_apply (hf hs), Measure.smul_apply,
    Measure.restrict_apply hs, ← Measure.smul_apply, ← hvol,
    Measure.map_apply hf (hs.inter measurableSet_Icc), preimage_inter, ← himage,
    preimage_image_eq _ hinj]

private theorem translateHalf :
    (volume.restrict (Icc (0 : ℝ) (1/2))).map (fun x => x + 1/2) =
      volume.restrict (Icc (1/2 : ℝ) 1) := by
  have h := affineRestricted 1 (1/2) 0 (1/2) (1/2) 1 (by norm_num) (by
    ext y
    constructor
    · rintro ⟨x, ⟨hl, hu⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨hl, hu⟩
      exact ⟨y - 1/2, ⟨by linarith, by linarith⟩, by ring⟩)
  simpa using h

private theorem reflectHalf :
    (volume.restrict (Icc (0 : ℝ) (1/2))).map (fun x => -2*x + 1) =
      ENNReal.ofReal (1/2) • volume.restrict (Icc (0 : ℝ) 1) := by
  have h := affineRestricted (-2) 1 0 (1/2) 0 1 (by norm_num) (by
    ext y
    constructor
    · rintro ⟨x, ⟨hl, hu⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨hl, hu⟩
      exact ⟨(1-y)/2, ⟨by linarith, by linarith⟩, by ring⟩)
  convert h using 2
  norm_num

theorem OMA.solution : type_of% @OMA.S_mo_481234.main := by
  let f : ℝ → ℝ × ℝ × ℝ := fun x => (x, x+1/2, -2*x+1)
  let g : ℝ → ℝ × ℝ × ℝ := fun x => (x+1/2, x, -2*x+1)
  let μ : Measure ℝ := volume.restrict (Icc 0 (1/2))
  let U : Measure ℝ := volume.restrict (Icc 0 1)
  let ν := μ.map f + μ.map g
  have hp₁ : Measurable (fun x : ℝ => x + 1/2) := measurable_id.add measurable_const
  have hp₂ : Measurable (fun x : ℝ => -2*x+1) := (measurable_const.mul measurable_id).add measurable_const
  have hf : Measurable f := measurable_id.prodMk (hp₁.prodMk hp₂)
  have hg : Measurable g := hp₁.prodMk (measurable_id.prodMk hp₂)
  have hsplit : μ + volume.restrict (Icc (1/2 : ℝ) 1) = U := by
    have hd : Disjoint (Icc (0 : ℝ) (1/2)) (Ioc (1/2) 1) :=
      disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1
    have h := Measure.restrict_union (μ := (volume : Measure ℝ)) hd measurableSet_Ioc
    rw [Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num), restrict_Ioc_eq_restrict_Icc] at h
    exact h.symm
  have h₁ : ν.map (fun p => p.1) = U := by
    rw [Measure.map_add _ _ measurable_fst, Measure.map_map measurable_fst hf,
      Measure.map_map measurable_fst hg]
    change μ.map id + μ.map (fun x => x+1/2) = U
    rw [Measure.map_id, translateHalf]
    exact hsplit
  have h₂ : ν.map (fun p => p.2.1) = U := by
    have hm : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
    rw [Measure.map_add _ _ hm, Measure.map_map hm hf, Measure.map_map hm hg]
    change μ.map (fun x => x+1/2) + μ.map id = U
    rw [add_comm, Measure.map_id, translateHalf]
    exact hsplit
  have h₃ : ν.map (fun p => p.2.2) = U := by
    have hm : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
    rw [Measure.map_add _ _ hm, Measure.map_map hm hf, Measure.map_map hm hg]
    change μ.map (fun x => -2*x+1) + μ.map (fun x => -2*x+1) = U
    rw [reflectHalf, ← add_smul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num [U]
  have hs : MeasurableSet S := by
    have hsum : Continuous (fun p : ℝ × ℝ × ℝ => p.1+p.2.1+p.2.2) :=
      (continuous_fst.add (continuous_fst.comp continuous_snd)).add (continuous_snd.comp continuous_snd)
    exact (measurable_fst measurableSet_Icc).inter
      (((measurable_fst.comp measurable_snd) measurableSet_Icc).inter
        (((measurable_snd.comp measurable_snd) measurableSet_Icc).inter
          (hsum.measurable (measurableSet_singleton (3/2 : ℝ)))))
  have hsupport (h : ℝ → ℝ × ℝ × ℝ) (hm : Measurable h)
      (hr : ∀ x ∈ Icc (0 : ℝ) (1/2), h x ∈ S) : μ.map h Sᶜ = 0 := by
    rw [Measure.map_apply hm hs.compl, Measure.restrict_apply (hm hs.compl)]
    have hempty : h ⁻¹' Sᶜ ∩ Icc (0 : ℝ) (1/2) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => hx.1 (hr x hx.2)
    rw [hempty, measure_empty]
  refine ⟨ν, ⟨?_⟩, ?_, h₁, h₂, h₃⟩
  · have hmass := congrArg (fun m : Measure ℝ => m univ) h₁
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at hmass
    simpa [U, Measure.restrict_apply_univ, Real.volume_Icc] using hmass
  · rw [Measure.add_apply, hsupport f hf, hsupport g hg, zero_add]
    · rintro x ⟨hl, hu⟩
      change (x+1/2 ∈ Icc (0 : ℝ) 1) ∧ x ∈ Icc (0 : ℝ) 1 ∧ -2*x+1 ∈ Icc (0 : ℝ) 1 ∧ _
      exact ⟨⟨by linarith, by linarith⟩, ⟨hl, by linarith⟩, ⟨by linarith, by linarith⟩, by ring⟩
    · rintro x ⟨hl, hu⟩
      change x ∈ Icc (0 : ℝ) 1 ∧ x+1/2 ∈ Icc (0 : ℝ) 1 ∧ -2*x+1 ∈ Icc (0 : ℝ) 1 ∧ _
      exact ⟨⟨hl, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by ring⟩