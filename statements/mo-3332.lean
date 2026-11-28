import Mathlib

/-!
# Two commuting mappings in the disk

Source: https://mathoverflow.net/questions/3332
Question (fedja): if `f` and `g` are commuting continuous self-maps of the closed unit disk,
is there always a point `x` with `f x = g x`? (If one of them is invertible this is Brouwer's
fixed point theorem.) `main` states the affirmative answer for the disk in `ℝ²`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_3332

open Metric

theorem main :
    ∀ f g : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      Continuous f → Continuous g → f ∘ g = g ∘ f → ∃ x, f x = g x := by
  sorry

end OMA.S_mo_3332
