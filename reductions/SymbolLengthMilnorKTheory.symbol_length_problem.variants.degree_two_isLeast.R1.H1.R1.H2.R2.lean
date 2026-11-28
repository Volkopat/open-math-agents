import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.H1.R1.H2.R2 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.H1.R1.H2
-- Credit: @witeg4

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1_H2_R2

-- The two steps use restriction of scalars on symbols: each unit is sent
-- to its image in the larger field. Construct the induced ring map once.
lemma existsRestriction {F E : Type} [Field F] [Field E] (f : F →+* E) (m : ℕ) :
    ∃ r : MilnorK F m →+* MilnorK E m, ∀ a : Fˣ,
      r (MilnorK.of m a) = MilnorK.of m (Units.map f.toMonoidHom a) := by
  let g := Units.map f.toMonoidHom
  let h := (MilnorK.ofHom (F := E) m).comp (MonoidHom.toAdditive g)
  let t := (TensorAlgebra.lift ℤ h.toIntLinearMap).toRingHom
  have ht (a : Fˣ) : t (TensorAlgebra.ι ℤ (Additive.ofMul a)) = MilnorK.of m (g a) := by
    exact TensorAlgebra.lift_ι_apply _ _
  have respects : ∀ ⦃x y⦄, MilnorK.Rel F m x y → t x = t y := by
    intro x y hxy
    cases hxy with
    | steinberg a b hab =>
      rw [map_mul, ht, ht, map_zero]
      exact MilnorK.of_mul_of_eq_zero m _ _ (by
        change f (a : F) + f (b : F) = 1
        rw [← map_add, hab, map_one])
    | natCast => simpa only [map_natCast, map_zero] using MilnorK.natCast_eq_zero (F := E) m
  refine ⟨RingQuot.lift ⟨t, respects⟩, fun a => ?_⟩
  simpa only [MilnorK.of, RingQuot.lift_mkRingHom_apply] using ht a

-- Cyclic splitting for the surface function field. By period-index and degree-three
-- cyclicity a nonzero class has a Galois cubic splitting field.
def H1 : Prop :=
  let F := MvRatFunc (Fin 2) ℂ
  ∀ x ∈ MilnorK.grade F 3 2, x ≠ 0 →
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E), IsGalois F E ∧ Module.finrank F E = 3 ∧
      ∀ r : MilnorK F 3 →+* MilnorK E 3,
        (∀ a : Fˣ, r (MilnorK.of 3 a) =
          MilnorK.of 3 (Units.map (algebraMap F E).toMonoidHom a)) → r x = 0

-- Relative cyclic kernel theorem: a class killed in a fixed Galois cubic extension
-- is represented by one symbol. This is the relative Brauer group / norm-residue step.
def H2 : Prop :=
  let F := MvRatFunc (Fin 2) ℂ
  ∀ (E : Type) [Field E] [Algebra F E], IsGalois F E → Module.finrank F E = 3 →
    ∀ r : MilnorK F 3 →+* MilnorK E 3,
      (∀ a : Fˣ, r (MilnorK.of 3 a) =
        MilnorK.of 3 (Units.map (algebraMap F E).toMonoidHom a)) →
      ∀ x ∈ MilnorK.grade F 3 2, r x = 0 →
        ∃ s : Fin 2 → Fˣ, x = MilnorK.symbol 3 s

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1.H2 := by
  intro split kernel x hx
  by_cases hzero : x = 0
  · exact ⟨0, by decide, Fin.elim0, by simpa using hzero⟩
  obtain ⟨E, fld, alg, gal, dim, vanishes⟩ := split x hx hzero
  obtain ⟨r, hr⟩ := existsRestriction (algebraMap (MvRatFunc (Fin 2) ℂ) E) 3
  obtain ⟨s, hs⟩ := kernel E gal dim r hr x hx (vanishes r hr)
  exact ⟨1, le_rfl, fun _ => s, by simpa using hs⟩

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1_H2_R2
