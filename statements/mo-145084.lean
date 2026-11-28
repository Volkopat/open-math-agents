import Mathlib

/-!
# Euclidean real quadratic fields

Source: https://mathoverflow.net/questions/145084/euclidean-real-quadratic-fields
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The question asks for an unconditional route to: there are infinitely many real quadratic fields
whose ring of integers is Euclidean (known under GRH plus Gauss's class-number-one conjecture).
That statement is `main`.

Conventions: the real quadratic fields are `ℚ(√d) ⊆ ℝ` for squarefree `d > 1` (pairwise
distinct). "Euclidean" is with respect to some Euclidean function in the general sense, i.e. a
well-founded relation `≺` with division with remainder `a = b q + r`, `r = 0 ∨ r ≺ b`
(the notion behind Mathlib's `EuclideanDomain`), not only the norm.
-/

namespace OMA.S_mo_145084

open NumberField

/-- A commutative ring admits a Euclidean function (well-founded remainder relation). -/
def IsEuclidean (R : Type*) [CommRing R] : Prop :=
  ∃ r : R → R → Prop, WellFounded r ∧
    ∀ a b : R, b ≠ 0 → ∃ q c : R, a = b * q + c ∧ (c = 0 ∨ r c b)

/-- The real quadratic field `ℚ(√d)` inside `ℝ`. -/
noncomputable abbrev K (d : ℕ) : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ {Real.sqrt d}

/-- Infinitely many real quadratic fields have a Euclidean ring of integers. -/
theorem main : Set.Infinite {d : ℕ | 1 < d ∧ Squarefree d ∧ IsEuclidean (𝓞 (K d))} := by
  sorry

end OMA.S_mo_145084
