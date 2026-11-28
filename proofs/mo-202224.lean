import OMAStatements.S_mo_202224
import Mathlib

/-! Adapt @nerotulip90's shortening in #32035 of @ivillar's proof (#14374).
Use minpoly.aeval_algHom directly for every embedded generator. -/

theorem OMA.solution : type_of% @OMA.S_mo_202224.main := by
  intro a h r
  let K := IntermediateField.adjoin ℚ ({a} : Set ℂ)
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional h.tower_top
  have : NumberField K := ⟨⟩
  let x := IntermediateField.AdjoinSimple.gen ℚ a
  obtain ⟨n, hn, e⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ
    ((isIntegral_algebraMap_iff (x := x) (algebraMap K ℂ).injective).mp h) fun φ => r _ (by
      rw [← IntermediateField.minpoly_gen ℚ a]
      exact minpoly.aeval_algHom ℚ φ.toRatAlgHom x)
  exact ⟨n, hn, by simpa [x] using congrArg (algebraMap K ℂ) e⟩
