import Mathlib

/-!
# The diagonal torus and fourth rational homology of PGL₂

The updated question asks whether the diagonal inclusion induces a surjection
on fourth group homology with rational coefficients, over every field.

[MathOverflow question](https://mathoverflow.net/questions/298336/homology-of-mathrmpgl-2f)
-/

open CategoryTheory

namespace OMA.S_mo_298336

abbrev GL₂ (F : Type) [Field F] := Matrix.GeneralLinearGroup (Fin 2) F

abbrev PGL₂ (F : Type) [Field F] := GL₂ F ⧸ Subgroup.center (GL₂ F)

noncomputable def diagonalInclusion (F : Type) [Field F] : Fˣ →* PGL₂ F :=
  let coordinate : Fˣ →* (Fin 2 → Fˣ) :=
    MonoidHom.mulSingle (f := fun _ : Fin 2 => Fˣ) 0
  let piUnits : (Fin 2 → F)ˣ ≃* (Fin 2 → Fˣ) := MulEquiv.piUnits
  let diagonal : (Fin 2 → F) →+* Matrix (Fin 2) (Fin 2) F :=
    Matrix.diagonalRingHom (n := Fin 2) (α := F)
  (QuotientGroup.mk' (Subgroup.center (GL₂ F))).comp
    ((Units.map diagonal.toMonoidHom).comp (piUnits.symm.toMonoidHom.comp coordinate))

theorem main :
    ∀ (F : Type) [Field F],
      Function.Surjective
        (SSet.homologyMap
          (nerveMap (SingleObj.mapHom Fˣ (PGL₂ F) (diagonalInclusion F)))
          (ModuleCat.of ℚ ℚ) 4) := by
  sorry

end OMA.S_mo_298336
