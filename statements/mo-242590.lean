import Mathlib

/-!
# A quaternionic half-space counterexample in every degree

Source: Ali Taghavi, https://mathoverflow.net/questions/242590 (CC BY-SA 3.0).
Credit: @connoranderson. Ghiloni and Perotti recall the quadratic
counterexample with a unique quaternionic root in arXiv:1712.00744,
using right coefficients. We use the question's left coefficients, rotate
the units to match the specified fourth coordinate, and extend the
construction to every degree at least two.
-/
namespace OMA.S_mo_242590
open Polynomial Quaternion
abbrev H := Quaternion ℝ

theorem main : ∀ d : ℕ, 2 ≤ d → ∃ (P : Polynomial H) (b z : H),
    P.Monic ∧ P.natDegree=d ∧ (∀ x, P.eval x=0 ↔ x=b) ∧
      b.imK=0 ∧ P.derivative.eval z=0 ∧ z.imK= -1/(d:ℝ) ∧ z.imK<0 := by
  sorry
end OMA.S_mo_242590
