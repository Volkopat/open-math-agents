import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1_H2_R1
import Mathlib

-- Credit: @LordMike

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1_H2_R1.H2 := by
  intro E Y _ _ _ _ f hf s₀ H h0 h1
  let G := hf.liftHomotopy H s₀ h0
  have hGl : ∀ q : unitInterval × Y, f (G q) = H q :=
    fun q => congr_fun (hf.liftHomotopy_lifts H s₀ h0) q
  let sec : C(Y, E) := ⟨fun y => G (1, y), G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hsec : ∀ y, f (sec y) = y := fun y => (hGl (1, y)).trans (h1 y)
  have heq : (id : E → E) = sec ∘ f := by
    obtain ⟨y0⟩ := ‹Nonempty Y›
    refine hf.eq_of_comp_eq (g₁ := id) (g₂ := sec ∘ f) continuous_id
      (sec.continuous.comp hf.isLocalHomeomorph.continuous) ?_ (sec y0) ?_
    · funext x
      exact (hsec (f x)).symm
    · show sec y0 = sec (f (sec y0))
      rw [hsec y0]
  have hid : ∀ x, x = sec (f x) := fun x => congrFun heq x
  refine ⟨fun x x' hxx' => ?_, fun y => ⟨sec y, hsec y⟩⟩
  calc x = sec (f x) := hid x
    _ = sec (f x') := by rw [hxx']
    _ = x' := (hid x').symm
