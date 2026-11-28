import FormalConjectures.GreensOpenProblems.«75»
import Mathlib

-- Reduction Green75.green_75.R1
-- Credit: @marcusbuffett

/-!
# Green 75 (Kupitz-Perles): the general-position case

A classical case of the problem: when no three points of `X` are collinear, there is a line
through two points of `X` with imbalance at most `1` (take the lexicographically lowest point `p`;
the other points are totally ordered by angle around `p`, and the line from `p` to the median
point halves the rest). This is `H1`. The open core `H2` is the problem for configurations that
contain three collinear points; Alon's examples, where every line through two points has
imbalance at least `2`, necessarily lie there.
-/

namespace OMA.R_Green75_green_75_R1
open Green75 Finset

/-- General position case, with the sharp constant `1`: if no three points of `X` lie on a
common line (`cross p q x ≠ 0` for distinct `p, q, x`), some line through two points of `X` has
the numbers of points on its two sides differing by at most `1`. -/
def H1 : Prop :=
  ∀ X : Finset (ℝ × ℝ), 2 ≤ #X →
    (∀ p ∈ X, ∀ q ∈ X, ∀ x ∈ X, p ≠ q → x ≠ p → x ≠ q → cross p q x ≠ 0) →
    ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ imbalance X p q ≤ 1

/-- The open core: configurations with three distinct collinear points. -/
def H2 : Prop :=
  ∀ X : Finset (ℝ × ℝ), 2 ≤ #X →
    (∃ p ∈ X, ∃ q ∈ X, ∃ x ∈ X, p ≠ q ∧ x ≠ p ∧ x ≠ q ∧ cross p q x = 0) →
    ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ imbalance X p q ≤ 100

theorem main : H1 → H2 → type_of% @Green75.green_75 := by
  intro h1 h2 X hX
  by_cases hc : ∃ p ∈ X, ∃ q ∈ X, ∃ x ∈ X, p ≠ q ∧ x ≠ p ∧ x ≠ q ∧ cross p q x = 0
  · exact h2 X hX hc
  · obtain ⟨p, hp, q, hq, hpq, h⟩ := h1 X hX (fun p hp q hq x hx hpq hxp hxq h0 =>
      hc ⟨p, hp, q, hq, x, hx, hpq, hxp, hxq, h0⟩)
    exact ⟨p, hp, q, hq, hpq, h.trans (by norm_num)⟩

end OMA.R_Green75_green_75_R1
