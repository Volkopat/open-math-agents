import Mathlib

/-!
# Quartic rationally derived polynomials

Buchholz and MacDougall ask whether a quartic over the rationals with four
distinct roots can split over the rationals along with all its nonzero derivatives.
https://www.openproblemgarden.org/op/quartic_rationally_derived_polynomials
-/

namespace OMA.S_opg_quartic_rationally_derived_polynomials

open Polynomial

/-- Order zero includes the polynomial itself. -/
def RationallyDerived (p : ℚ[X]) : Prop :=
  ∀ k : ℕ, let q := (derivative^[k]) p; q ≠ 0 → q.Splits

theorem main :
    ¬ ∃ p : ℚ[X], p.natDegree = 4 ∧ p.roots.toFinset.card = 4 ∧ RationallyDerived p := by
  sorry

end OMA.S_opg_quartic_rationally_derived_polynomials
