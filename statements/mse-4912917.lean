import Mathlib

/-!
# A path-connected set containing all pairs of irrational numbers and no line segment

Source: https://math.stackexchange.com/questions/4912917
Credit: @zarnab222-dev

The question calls a set anti-convex if every two distinct members have a point
outside the set strictly between them. It asks whether such a path-connected set
can contain the square of the irrationals. This is the main planar question.
-/

namespace OMA.S_mse_4912917

theorem main : ∃ S : Set (ℝ × ℝ),
    {p : ℝ × ℝ | Irrational p.1 ∧ Irrational p.2} ⊆ S ∧ IsPathConnected S ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      ∃ t ∈ Set.Ioo (0 : ℝ) 1, b + t • (a - b) ∉ S := by
  sorry

end OMA.S_mse_4912917
