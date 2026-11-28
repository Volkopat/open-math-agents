import Mathlib

/-!
# Path connected spectra in the reduced C*-algebra of the free group

The question names the reduced group C*-algebra of the free group on two
generators and asks whether every element has path connected complex spectrum.

[MathOverflow question](https://mathoverflow.net/questions/195900/unital-c-algebras-whose-all-elements-have-path-connected-spectrum)
-/

namespace OMA.S_mo_195900

abbrev FreeGroupTwo := FreeGroup (Fin 2)

abbrev HilbertSpace := ↥(lp (fun _ : FreeGroupTwo => ℂ) 2)

abbrev Operators := HilbertSpace →L[ℂ] HilbertSpace

noncomputable def ReducedFreeGroupAlgebra : StarSubalgebra ℂ Operators :=
  (StarAlgebra.adjoin ℂ
    {T : Operators | ∃ g : FreeGroupTwo, ∀ ξ : HilbertSpace, ∀ x : FreeGroupTwo,
      (T ξ) x = ξ (g⁻¹ * x)}).topologicalClosure

theorem main :
    ∀ a : ReducedFreeGroupAlgebra, IsPathConnected (spectrum ℂ a) := by
  sorry

end OMA.S_mo_195900
