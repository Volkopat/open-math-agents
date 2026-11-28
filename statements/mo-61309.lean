import Mathlib

/-!
# Fixed point theorem for convex, closed multivalued mappings without metrizability

Source: https://mathoverflow.net/questions/61309
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Known (via Michael's selection theorem): if `X` is a compact, convex, metrizable subset of a
Hausdorff locally convex space, then every lower semicontinuous map `F : X → 2^X` with nonempty
closed convex values has a fixed point `x ∈ F(x)`. Question (Xian Wu): does this hold without
metrizability?

Conventions:
* `E` is a real Hausdorff locally convex topological vector space, `X ⊆ E` nonempty, compact,
  convex. `F` sends points of `X` to nonempty, closed, convex subsets of `X`. Lower
  semicontinuity: for every open `U ⊆ E`, `{x ∈ X | F x ∩ U ≠ ∅}` is relatively open in `X`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_61309

/-- The fixed point theorem without metrizability. -/
theorem main : ∀ (E : Type) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (X : Set E) (F : E → Set E),
    X.Nonempty → IsCompact X → Convex ℝ X →
    (∀ x ∈ X, (F x).Nonempty ∧ F x ⊆ X ∧ IsClosed (F x) ∧ Convex ℝ (F x)) →
    (∀ U : Set E, IsOpen U → ∃ V : Set E, IsOpen V ∧ {x ∈ X | (F x ∩ U).Nonempty} = V ∩ X) →
    ∃ x ∈ X, x ∈ F x := by
  sorry

end OMA.S_mo_61309
