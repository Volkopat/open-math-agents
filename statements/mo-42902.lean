import Mathlib

/-!
# The determinant of the sum of normal matrices (Marcus–de Oliveira)

Source: https://mathoverflow.net/questions/42902
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Given normal `A, B ∈ Mₙ(ℂ)` with spectra `(α₁, …, αₙ)` and `(β₁, …, βₙ)`, is `det(A + B)` in the
convex hull of the numbers `∏ᵢ (αᵢ + β_{σ(i)})`, `σ ∈ 𝔖ₙ`?

Conventions:
* Normal: `A * Aᴴ = Aᴴ * A`. The spectra are listed with multiplicity: by the spectral theorem a
  normal matrix is unitarily diagonalisable, so `A = U diag(α) Uᴴ` with `U` unitary; we
  quantify over such presentations (`α, β : Fin n → ℂ`, `U, V` unitary), which is the same as
  quantifying over normal `A, B` with their eigenvalue lists.
* Convex hull in `ℂ` as a real vector space.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_42902

open Matrix

/-- The Marcus–de Oliveira conjecture. -/
theorem main : ∀ (n : ℕ) (α β : Fin n → ℂ) (U V : Matrix.unitaryGroup (Fin n) ℂ),
    let A : Matrix (Fin n) (Fin n) ℂ := (U : Matrix (Fin n) (Fin n) ℂ) * diagonal α * star (U : Matrix (Fin n) (Fin n) ℂ)
    let B : Matrix (Fin n) (Fin n) ℂ := (V : Matrix (Fin n) (Fin n) ℂ) * diagonal β * star (V : Matrix (Fin n) (Fin n) ℂ)
    (A + B).det ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) => ∏ i, (α i + β (σ i))) := by
  sorry

end OMA.S_mo_42902
