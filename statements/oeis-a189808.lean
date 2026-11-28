import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a189808

/-- Three lattice points form a nondegenerate right triangle. -/
def IsRightTriple (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) ≠ (q.2 - p.2) * (r.1 - p.1) ∧
  ((q.1 - p.1) * (r.1 - p.1) + (q.2 - p.2) * (r.2 - p.2) = 0 ∨
   (p.1 - q.1) * (r.1 - q.1) + (p.2 - q.2) * (r.2 - q.2) = 0 ∨
   (p.1 - r.1) * (q.1 - r.1) + (p.2 - r.2) * (q.2 - r.2) = 0)

/-- Predicate that a 3-element subset of the `4 × (n + 1)` grid forms a right triangle. -/
def IsRightSet {n : ℕ} (S : Finset (Fin 4 × Fin (n + 1))) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S,
    S = {p, q, r} ∧
    IsRightTriple (p.1.1, p.2.1) (q.1.1, q.2.1) (r.1.1, r.2.1)

open Classical in
/-- OEIS A189808: Number of right triangles on an `(n + 1) × 4` grid. -/
noncomputable def A189808 (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin 4 × Fin (n + 1))).powersetCard 3).filter IsRightSet).card

/-- OEIS A189808 conjecture (Colin Barker, 2018):
Rational generating function
`(1 - X)^3 * ∑_{n≥1} a(n) X^n = 2*X*(14 + 5*X + X^2 - 2*X^3 + 2*X^4 - 7*X^5 + 3*X^6 - 4*X^7 + 2*X^9 - 2*X^10)`. -/
theorem main :
    (1 - PowerSeries.X) ^ 3 *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A189808 n : ℤ)) =
      2 * PowerSeries.X *
        (14 + 5 * PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 +
          2 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6 -
          4 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 9 - 2 * PowerSeries.X ^ 10) := by
  sorry

end OMA.S_oeis_a189808
