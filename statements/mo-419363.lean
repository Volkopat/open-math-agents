import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Noncommutative Banach algebras whose left inverses are also right inverses

Source: https://mathoverflow.net/questions/419363/banach-algebras-for-which-left-invertible-implies-invertible
Credit: @etaubman

The existence question is stated for unital complex Banach algebras.
The last clause is the directly finite property: if b is a left inverse
of a, it is also a right inverse. The explicit noncommuting pair excludes
commutative examples. The source comments identify such algebras as
Dedekind finite or von Neumann finite.
-/

namespace OMA.S_mo_419363

theorem main :
    ∃ (A : Type) (nr : NormedRing A), letI := nr;
      ∃ (na : NormedAlgebra ℂ A), letI := na;
        CompleteSpace A ∧ (∃ a b : A, a * b ≠ b * a) ∧
        (∀ a b : A, b * a = 1 → a * b = 1) := by
  sorry

end OMA.S_mo_419363
