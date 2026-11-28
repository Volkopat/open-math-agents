import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a189809

/-- Three lattice points form a nondegenerate right triangle. -/
def IsRightTriple (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) ≠ (q.2 - p.2) * (r.1 - p.1) ∧
  ((q.1 - p.1) * (r.1 - p.1) + (q.2 - p.2) * (r.2 - p.2) = 0 ∨
   (p.1 - q.1) * (r.1 - q.1) + (p.2 - q.2) * (r.2 - q.2) = 0 ∨
   (p.1 - r.1) * (q.1 - r.1) + (p.2 - r.2) * (q.2 - r.2) = 0)

/-- Predicate that a 3-element subset of the `5 × (n + 1)` grid forms a right triangle. -/
def IsRightSet {n : ℕ} (S : Finset (Fin 5 × Fin (n + 1))) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S,
    S = {p, q, r} ∧
    IsRightTriple (p.1.1, p.2.1) (q.1.1, q.2.1) (r.1.1, r.2.1)

open Classical in
/-- OEIS A189809: Number of right triangles on an `(n + 1) × 5` grid. -/
noncomputable def A189809 (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin (n + 1))).powersetCard 3).filter IsRightSet).card

/-- OEIS A189809 conjecture (Colin Barker, 2018):
Rational generating function
`(1 - X)^3 * ∑_{n≥1} a(n) X^n = 2*X*(23 + 10*X + 3*X^2 - X^3 + 3*X^4 - 12*X^5 + 6*X^6 - 7*X^7 - X^8 + 2*X^9 - 6*X^10 + 4*X^12 - 4*X^13 + 2*X^16 - 2*X^17)`. -/
theorem main :
    (1 - PowerSeries.X) ^ 3 *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A189809 n : ℤ)) =
      2 * PowerSeries.X *
        (23 + 10 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 +
          3 * PowerSeries.X ^ 4 - 12 * PowerSeries.X ^ 5 + 6 * PowerSeries.X ^ 6 -
          7 * PowerSeries.X ^ 7 - PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9 -
          6 * PowerSeries.X ^ 10 + 4 * PowerSeries.X ^ 12 - 4 * PowerSeries.X ^ 13 +
          2 * PowerSeries.X ^ 16 - 2 * PowerSeries.X ^ 17) := by
  sorry

end OMA.S_oeis_a189809
