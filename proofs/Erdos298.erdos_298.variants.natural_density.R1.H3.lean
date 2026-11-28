import OMAReductions.R_Erdos298_erdos_298_variants_natural_density_R1

-- Step Erdos298.erdos_298.variants.natural_density.R1.H3: hypothesis H3 of reduction Erdos298.erdos_298.variants.natural_density.R1

/-!
If the partial densities of `A` converge to `α > 0`, their limsup, which is the upper density, is
also `α`.
-/

theorem OMA.solution : OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H3 := by
  rintro A ⟨α, hα, hd⟩
  have h : A.upperDensity = α := hd.limsup_eq
  exact h.symm ▸ hα
