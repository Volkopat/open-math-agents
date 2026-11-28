import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a271912

/-- Squared Euclidean distance between two integer lattice points. -/
def sqDist (p q : ℤ × ℤ) : ℤ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Three lattice points form a nondegenerate isosceles triangle. -/
def IsIsoscelesTriple (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) ≠ (q.2 - p.2) * (r.1 - p.1) ∧
  (sqDist p q = sqDist q r ∨ sqDist q r = sqDist r p ∨ sqDist r p = sqDist p q)

/-- Predicate that a 3-element subset of the `3 × n` grid forms an isosceles triangle. -/
def IsIsoscelesSet {n : ℕ} (S : Finset (Fin 3 × Fin n)) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S,
    S = {p, q, r} ∧
    IsIsoscelesTriple (p.1.1, p.2.1) (q.1.1, q.2.1) (r.1.1, r.2.1)

open Classical in
/-- OEIS A271912: Number of ways to choose three distinct points from a `3 × n` grid
so that they form an isosceles triangle. -/
noncomputable def A271912 (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin 3 × Fin n)).powersetCard 3).filter IsIsoscelesSet).card

/-- OEIS A271912 conjectures:
1. Closed-form quasi-polynomial for `n > 2` (Colin Barker, 2016):
   `2*a(n) = 5*n^2 + 32*n - 72` for even `n`, `5*n^2 + 32*n - 69` for odd `n`.
2. Linear recurrence `a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4)` for `n > 6`.
3. Rational generating function (offset 2, `∑_{n≥1} a(n+1) X^n = 10*X + 36*X^2 + ...`):
   `(PowerSeries.X + 1) * (PowerSeries.X - 1)^3 * ∑_{n≥1} a(n+1) X^n = 2*X*(2*X^4 + 4*X^3 + 2*X^2 - 8*X - 5)`. -/
theorem main :
    (∀ n : ℕ, 2 < n →
      2 * (A271912 n : ℤ) =
        if Even n then 5 * (n : ℤ) ^ 2 + 32 * n - 72 else 5 * (n : ℤ) ^ 2 + 32 * n - 69) ∧
    (∀ n : ℕ, 6 < n →
      (A271912 n : ℤ) = 2 * A271912 (n - 1) - 2 * A271912 (n - 3) + A271912 (n - 4)) ∧
    (PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 3 *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A271912 (n + 1) : ℤ)) =
      2 * PowerSeries.X *
        (2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 2 -
          8 * PowerSeries.X - 5) := by
  sorry

end OMA.S_oeis_a271912
