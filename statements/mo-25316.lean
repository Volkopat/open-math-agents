import Mathlib

/-!
# Square powers of hemicontinuous operators

Source: https://mathoverflow.net/questions/25316
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `H` be an infinite-dimensional real Hilbert space. A map `V : H → H` is hemicontinuous if it
is continuous from each line segment of `H` to the weak topology of `H`. Question: for every map
`U : H → H` (possibly discontinuous), is there a hemicontinuous `V : H → H` with `U² = V²`?

Conventions:
* `H` is a real inner product space that is complete and infinite-dimensional. The weak topology
  is Mathlib's `WeakSpace ℝ H`. Continuity on every segment `[x, y]` is equivalent to continuity
  of `t ↦ V (x + t • y)` on all of `ℝ` for all `x, y` (lines are unions of segments, and segments
  are images of intervals), which is the form used.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_25316

/-- `V` is hemicontinuous. -/
def Hemicontinuous {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (V : H → H) : Prop :=
  ∀ x y : H, Continuous fun t : ℝ => toWeakSpace ℝ H (V (x + t • y))

/-- Every self-map of `H` has the same square as some hemicontinuous self-map. -/
theorem main : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ¬ FiniteDimensional ℝ H → ∀ U : H → H, ∃ V : H → H, Hemicontinuous V ∧ U ∘ U = V ∘ V := by
  sorry

end OMA.S_mo_25316
