import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a271913

/-- Squared Euclidean distance between two integer lattice points. -/
def sqDist (p q : ℤ × ℤ) : ℤ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Three lattice points form a nondegenerate isosceles triangle. -/
def IsIsoscelesTriple (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) ≠ (q.2 - p.2) * (r.1 - p.1) ∧
  (sqDist p q = sqDist q r ∨ sqDist q r = sqDist r p ∨ sqDist r p = sqDist p q)

/-- Predicate that a 3-element subset of the `4 × n` grid forms an isosceles triangle. -/
def IsIsoscelesSet {n : ℕ} (S : Finset (Fin 4 × Fin n)) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S,
    S = {p, q, r} ∧
    IsIsoscelesTriple (p.1.1, p.2.1) (q.1.1, q.2.1) (r.1.1, r.2.1)

open Classical in
/-- OEIS A271913: Number of ways to choose three distinct points from a `4 × n` grid
so that they form an isosceles triangle. -/
noncomputable def A271913 (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin 4 × Fin n)).powersetCard 3).filter IsIsoscelesSet).card

/-- OEIS A271913 conjectures:
1. Closed-form quasi-polynomial for `n > 8` (Colin Barker, 2016):
   `a(n) = 5*n^2 + 64*n - 216` for even `n`, `5*n^2 + 64*n - 213` for odd `n`.
2. Linear recurrence `a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4)` for `n > 12`.
3. Rational generating function (offset 2, `∑_{n≥1} a(n+1) X^n = 16*X + 68*X^2 + ...`):
   `(PowerSeries.X + 1) * (PowerSeries.X - 1)^3 * ∑_{n≥1} a(n+1) X^n = 4*X*(X^10 - X^8 + 2*X^6 + X^5 + 4*X^4 + 4*X^3 - 3*X^2 - 9*X - 4)`. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (A271913 n : ℤ) =
        if Even n then 5 * (n : ℤ) ^ 2 + 64 * n - 216 else 5 * (n : ℤ) ^ 2 + 64 * n - 213) ∧
    (∀ n : ℕ, 12 < n →
      (A271913 n : ℤ) = 2 * A271913 (n - 1) - 2 * A271913 (n - 3) + A271913 (n - 4)) ∧
    (PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 3 *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A271913 (n + 1) : ℤ)) =
      4 * PowerSeries.X *
        (PowerSeries.X ^ 10 - PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 5 +
          4 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 -
          9 * PowerSeries.X - 4) := by
  sorry

end OMA.S_oeis_a271913
