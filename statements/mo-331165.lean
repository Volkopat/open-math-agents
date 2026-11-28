import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Solenoidal currents in a scalar density
Raphael J. F. Berger, MathOverflow 331165 (2019).
https://mathoverflow.net/questions/331165/solution-of-equation-on-vector-field
Formalization by @LDJAI with OpenAI Codex.
-/

namespace OMA.S_mo_331165

open scoped Matrix

abbrev Space := Fin 3 → ℝ

/-- The ordinary partial derivative in the direction of coordinate i. -/
noncomputable def coordDeriv (f : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  deriv (fun t : ℝ => f (x + t • Pi.single i 1)) 0

noncomputable def grad (f : Space → ℝ) (x : Space) : Space :=
  fun i => coordDeriv f i x

noncomputable def divField (J : Space → Space) (x : Space) : ℝ :=
  ∑ i, coordDeriv (fun y => J y i) i x

noncomputable def current (ρ : Space → ℝ) (v : Space → Space) (B x : Space) : Space :=
  ρ x • (B ⨯₃ v x)

/-- Berger's pointwise parallelism conjecture for all constant nonzero field vectors. -/
theorem main :
    ∀ (ρ : Space → ℝ) (v : Space → Space), Differentiable ℝ ρ →
      (∀ x, 0 < ρ x) → Differentiable ℝ v →
      (∀ (B : Space), B ≠ 0 → ∀ x, divField (current ρ v B) x = 0) →
      ∀ x, ∃ a : ℝ, v x = a • grad ρ x := by
  sorry

end OMA.S_mo_331165
