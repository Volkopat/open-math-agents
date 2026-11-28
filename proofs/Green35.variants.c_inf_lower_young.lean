import FormalConjectures.GreensOpenProblems.«35»

/-! Shorter proof of `Green35.variants.c_inf_lower_young`. -/

open MeasureTheory
open scoped Convolution ENNReal

theorem OMA.solution : type_of% @Green35.variants.c_inf_lower_young := by
  refine le_sInf ?_
  rintro _ ⟨f, hf, rfl⟩
  have hc : Green35.c 2 ≤ eLpNorm (f ⋆ f) 2 := sInf_le ⟨f, hf, rfl⟩
  obtain ⟨hi, h0, -, h1⟩ := hf
  have hgi := hi.integrable_convolution (.lsmul ℝ ℝ) hi
  have hg0 : ∀ x, 0 ≤ (f ⋆ f) x := fun x => by
    rw [convolution_lsmul]; exact integral_nonneg fun _ => mul_nonneg (h0 _) (h0 _)
  have hL1 : ∫⁻ x, ‖(f ⋆ f) x‖ₑ = 1 := by
    simp_rw [Real.enorm_eq_ofReal (hg0 _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (.of_forall hg0),
      integral_convolution (.lsmul ℝ ℝ) hi hi, h1]
    simp
  calc Green35.c 2 ^ 2
      ≤ eLpNorm (f ⋆ f) 2 volume ^ 2 := by gcongr
    _ = ∫⁻ x, ‖(f ⋆ f) x‖ₑ ^ (2 : ℝ) := by
        have h := eLpNorm_enorm_rpow (μ := volume) (p := 1) (q := 2) (f ⋆ f) (by norm_num)
        rw [eLpNorm_one_eq_lintegral_enorm] at h
        simpa [ENNReal.rpow_two] using h.symm
    _ ≤ ∫⁻ x, eLpNormEssSup (f ⋆ f) volume * ‖(f ⋆ f) x‖ₑ := lintegral_mono_ae <|
        (ae_le_eLpNormEssSup (μ := volume) (f := f ⋆ f)).mono fun _ _ => by
          rw [ENNReal.rpow_two, sq]; gcongr
    _ = eLpNorm (f ⋆ f) ⊤ volume := by
        rw [lintegral_const_mul'' _ hgi.aemeasurable.enorm, hL1, mul_one, eLpNorm_exponent_top]
