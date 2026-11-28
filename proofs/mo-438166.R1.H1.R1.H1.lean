import OMAReductions.R_mo_438166_R1_H1_R1
import Mathlib.CategoryTheory.Adjunction.Lifting.Left

/-! Restriction of scalars keeps the underlying set and function. The adjoint
triangle theorem therefore lifts the free-module adjunction, since every module
is a quotient of the free module on its elements. -/

open CategoryTheory CategoryTheory.Limits

theorem OMA.solution : OMA.R_mo_438166_R1_H1_R1.H1 := by
  intro A D _ _ _ _ e
  let R := ModuleCat.restrictScalars.{0} e.toRingHom
  let U := forget (ModuleCat.{0} A)
  have : (R ⋙ U).IsRightAdjoint := by
    change (forget (ModuleCat.{0} D)).IsRightAdjoint
    infer_instance
  apply isRightAdjoint_triangle_lift R (ModuleCat.adj A)
  intro X
  haveI : Epi ((ModuleCat.adj A).counit.app X) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    refine ⟨(ModuleCat.adj A).unit.app (U.obj X) x, ?_⟩
    exact ConcreteCategory.congr_hom ((ModuleCat.adj A).right_triangle_components X) x
  exact regularEpiOfEpi _
