import Mathlib

/-!
# A bound on symmetric second differences

Ravi, MathOverflow question 147075, https://mathoverflow.net/questions/147075
(CC BY-SA). Lean statement by @xlh1551.

We take the domain to be the real line. Absolute continuity uses one
modulus for all finite families of disjoint intervals in the domain.
The written logarithmic expression is defined for nonzero increments.
-/

namespace OMA.S_mo_147075

open scoped BigOperators

def absolutelyContinuousOnLine (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
    ∀ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      (∀ i j, i ≠ j → Disjoint (Set.Ioo (a i) (b i)) (Set.Ioo (a j) (b j))) →
      (∑ i, (b i - a i)) < η → (∑ i, |f (b i) - f (a i)|) < ε

theorem main : ∃ (f : ℝ → ℝ) (C : ℝ), absolutelyContinuousOnLine f ∧
    0 < C ∧ (∀ x h : ℝ, 0 < |h| → |h| < 1 →
      |f (x + h) + f (x - h) - 2 * f x| ≤ C * |h| / Real.log (1 / |h|)) ∧
    ¬ ContDiff ℝ 1 f := by
  sorry

end OMA.S_mo_147075
