import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Ring.Periodic

/-!
# Goddyn's conjecture on iterated circumcentres

Source: https://www.openproblemgarden.org/op/a_conjecture_on_iterated_circumcentres
Credit: @yakataN

We use the standard positive-dimensional reading of Euclidean d-space.
The source's p_1, p_2, ... are indexed here starting at zero.
Thus p(n+d+1) is the centre of the unique sphere through p(n), ..., p(n+d).
Uniqueness refers to the sphere's centre and positive radius, not just to
existence of an equidistant point. The preceding d+1 points must be distinct.
The period in the question is interpreted as the least positive period:
any positive multiple of a period is also a period.
-/

namespace OMA.S_opg_a_conjecture_on_iterated_circumcentres

/-- Each new point is the centre of the unique sphere through the preceding d+1 points. -/
def IsCircumcentreSequence (d : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ n : ℕ,
    Function.Injective (fun j : Fin (d + 1) => p (n + j.val)) ∧
    ∃ r : ℝ, 0 < r ∧
      (∀ j : Fin (d + 1), dist (p (n + j.val)) (p (n + d + 1)) = r) ∧
      ∀ (c : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 < s →
        (∀ j : Fin (d + 1), dist (p (n + j.val)) c = s) →
        c = p (n + d + 1) ∧ s = r

/-- A periodic iterated-circumcentre sequence has least positive period 2d+4. -/
theorem main :
    ∀ (d : ℕ), 0 < d → ∀ p : ℕ → EuclideanSpace ℝ (Fin d),
      IsCircumcentreSequence d p →
      (∃ k : ℕ, 0 < k ∧ Function.Periodic p k) →
      Function.Periodic p (2 * d + 4) ∧
        ∀ k : ℕ, 0 < k → Function.Periodic p k → 2 * d + 4 ≤ k := by
  sorry

end OMA.S_opg_a_conjecture_on_iterated_circumcentres
