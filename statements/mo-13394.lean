import Mathlib

/-!
# Finite rank commutators

Source: https://mathoverflow.net/questions/13394/finite-rank-commutators
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Dosev–Johnson): there is an infinite dimensional Banach space `X` such that every
finite rank commutator `T = AB - BA` in `L(X)` has zero trace.

Conventions. Real Banach spaces (the source does not fix the scalar field; the real case is
stated). `L(X)` is `X →L[ℝ] X`. A finite rank operator `T` maps its (finite dimensional) range
into itself, and its trace is the trace of that restriction (this agrees with the usual trace
of finite rank operators).
-/

namespace OMA.S_mo_13394

/-- Trace of an operator, computed on its range (meaningful for finite rank operators). -/
noncomputable def rangeTrace {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : X →L[ℝ] X) : ℝ :=
  LinearMap.trace ℝ (LinearMap.range (T : X →ₗ[ℝ] X))
    ((T : X →ₗ[ℝ] X).restrict (p := LinearMap.range (T : X →ₗ[ℝ] X))
      (q := LinearMap.range (T : X →ₗ[ℝ] X)) (fun x _ => LinearMap.mem_range_self _ x))

/-- The Dosev–Johnson conjecture. -/
theorem main :
    ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X),
      ¬ FiniteDimensional ℝ X ∧
      ∀ T A B : X →L[ℝ] X, FiniteDimensional ℝ (LinearMap.range (T : X →ₗ[ℝ] X)) →
        T = A * B - B * A → rangeTrace T = 0 := by
  sorry

end OMA.S_mo_13394
