import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Finite.Basic

/-! Source: https://mathoverflow.net/questions/515540 -/

namespace OMA.S_mo_515540

/-- The logarithmic-remainder term from the source. -/
noncomputable def logarithmicRemainderTerm (n : ℕ) : ℝ :=
  let l := Real.log (n : ℝ)
  let q : ℝ := Int.floor ((n : ℝ) / l)
  q * ((n : ℝ) - q * l)

theorem main : Set.Infinite {n : ℕ | 1 < n ∧ logarithmicRemainderTerm n < 1} := by
  sorry

end OMA.S_mo_515540
