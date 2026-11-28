import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a271915

/-- Squared Euclidean distance between two integer lattice points. -/
def sqDist (p q : ℤ × ℤ) : ℤ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Three lattice points form a nondegenerate isosceles triangle. -/
def IsIsoscelesTriple (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) ≠ (q.2 - p.2) * (r.1 - p.1) ∧
  (sqDist p q = sqDist q r ∨ sqDist q r = sqDist r p ∨ sqDist r p = sqDist p q)

/-- Predicate that a 3-element subset of the `5 × n` grid forms an isosceles triangle. -/
def IsIsoscelesSet {n : ℕ} (S : Finset (Fin 5 × Fin n)) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S,
    S = {p, q, r} ∧
    IsIsoscelesTriple (p.1.1, p.2.1) (q.1.1, q.2.1) (r.1.1, r.2.1)

open Classical in
/-- OEIS A271915: Number of ways to choose three distinct points from a `5 × n` grid
so that they form an isosceles triangle. -/
noncomputable def A271915 (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin 5 × Fin n)).powersetCard 3).filter IsIsoscelesSet).card

/-- OEIS A271915 conjectures:
1. Linear recurrence `a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4)` for `n > 18`.
2. Rational generating function (offset 2, `∑_{n≥1} a(n+1) X^n = 24*X + 108*X^2 + ...`):
   `(X + 1) * (X - 1)^3 * ∑_{n≥1} a(n+1) X^n =
    4*X*(X^16 - X^14 + 2*X^10 + 2*X^9 - X^8 - X^7 + 5*X^6 + 6*X^5 + 6*X^4 + X^3 - 8*X^2 - 15*X - 6)`. -/
theorem main :
    (∀ n : ℕ, 18 < n →
      (A271915 n : ℤ) = 2 * A271915 (n - 1) - 2 * A271915 (n - 3) + A271915 (n - 4)) ∧
    (PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 3 *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A271915 (n + 1) : ℤ)) =
      4 * PowerSeries.X *
        (PowerSeries.X ^ 16 - PowerSeries.X ^ 14 + 2 * PowerSeries.X ^ 10 +
          2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 8 - PowerSeries.X ^ 7 +
          5 * PowerSeries.X ^ 6 + 6 * PowerSeries.X ^ 5 + 6 * PowerSeries.X ^ 4 +
          PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 2 - 15 * PowerSeries.X - 6) := by
  sorry

end OMA.S_oeis_a271915
