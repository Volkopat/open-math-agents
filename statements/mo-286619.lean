import Mathlib

/-!
# Sharp constant for a mean-zero convex function

Source: Steve, https://mathoverflow.net/questions/286619 (CC BY-SA 3.0).
Credit: @connoranderson.

As in the source, normalize the infimum of the convex function to −1. The
least possible integral of the absolute value is attained and depends on
the domain only through its Lebesgue volume.
-/

namespace OMA.S_mo_286619

open MeasureTheory Set

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def best (n : ℕ) (P : Set (E n)) : ℝ :=
  2 * ((n:ℝ)/(n+1))^n / (n+1) * volume.real P

theorem main : ∀ n : ℕ, 0<n → ∀ P : Set (E n),
    P.Nonempty → IsOpen P → Convex ℝ P → Bornology.IsBounded P →
    IsLeast {L : ℝ | ∃ f : E n → ℝ, ConvexOn ℝ P f ∧ IntegrableOn f P ∧
      (∫ x in P, f x) = 0 ∧ IsGLB (f '' P) (-1) ∧ L = ∫ x in P, |f x|} (best n P) := by
  sorry

end OMA.S_mo_286619
