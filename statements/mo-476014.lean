import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Source: https://mathoverflow.net/questions/476014/an-s-convex-function-lying-between-two-convex-functions
Credit: @etaubman.

The positive half-line is used for the source's R_+. The counterexample also
extends to zero, so either common convention for R_+ gives a negative answer.
The s-convexity parameter is in its usual range 0 < s <= 1.
-/

namespace OMA.S_mo_476014

def SConvex (s : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → ∀ y : ℝ, 0 < y →
    ∀ a : ℝ, 0 < a → a < 1 →
      f (a * x + (1 - a) * y) ≤ a ^ s * f x + (1 - a) ^ s * f y

def claim : Prop :=
  ∀ (s : ℝ) (f g : ℝ → ℝ) (a b : ℝ),
    0 < s → s ≤ 1 →
    (∀ x : ℝ, 0 < x → 0 < f x) → SConvex s f →
    (∀ x : ℝ, 0 < x → 0 < g x) → ConvexOn ℝ (Set.Ioi 0) g →
    0 < a → a < b →
    (∀ x : ℝ, 0 < x → a * g x ≤ f x ∧ f x ≤ b * g x) →
    ConvexOn ℝ (Set.Ioi 0) f

theorem main : claim := by
  sorry

end OMA.S_mo_476014
