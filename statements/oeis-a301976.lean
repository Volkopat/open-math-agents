import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a301976

/-- Degree of vertex `(i, j)` in a subgraph of the `3 × n` grid graph `P_3 □ P_n`,
specified by vertical edges `V : Fin 2 × Fin n → Bool` and horizontal edges
`H : Fin 3 × Fin (n - 1) → Bool`. -/
def gridDeg (n : ℕ) (V : Fin 2 × Fin n → Bool) (H : Fin 3 × Fin (n - 1) → Bool)
    (i : Fin 3) (j : Fin n) : ℕ :=
  (match i.1 with
   | 0 => if V (0, j) then 1 else 0
   | 1 => (if V (0, j) then 1 else 0) + (if V (1, j) then 1 else 0)
   | _ => if V (1, j) then 1 else 0) +
  (if hj : 0 < j.1 then if H (i, ⟨j.1 - 1, by omega⟩) then 1 else 0 else 0) +
  (if hj : j.1 + 1 < n then if H (i, ⟨j.1, by omega⟩) then 1 else 0 else 0)

/-- OEIS A301976: Number of no-leaf subgraphs (edge subsets with no vertex of degree 1)
of the `3 × n` grid graph `P_3 □ P_n`. -/
def A301976 (n : ℕ) : ℕ :=
  Fintype.card
    { p : (Fin 2 × Fin n → Bool) × (Fin 3 × Fin (n - 1) → Bool) //
      ∀ (i : Fin 3) (j : Fin n), gridDeg n p.1 p.2 i j ≠ 1 }

/-- OEIS A301976 conjectures:
1. `a(n) % 10 = 3` for all `n > 2`.
2. Linear recurrence `a(n) = 12*a(n-1) - 6*a(n-2) - 20*a(n-3) - 5*a(n-4)` for `n > 4`
   (Colin Barker, 2018).
3. Rational generating function
   `(1 - 12*X + 6*X^2 + 20*X^3 + 5*X^4) * ∑_{n≥1} a(n) X^n = X*(1 + X)*(1 - 8*X - 3*X^2)`. -/
theorem main :
    (∀ n : ℕ, 2 < n → A301976 n % 10 = 3) ∧
    (∀ n : ℕ, 4 < n →
      (A301976 n : ℤ) = 12 * A301976 (n - 1) - 6 * A301976 (n - 2) -
        20 * A301976 (n - 3) - 5 * A301976 (n - 4)) ∧
    (1 - 12 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3 +
        5 * PowerSeries.X ^ 4) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A301976 n : ℤ)) =
      PowerSeries.X * (1 + PowerSeries.X) * (1 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a301976
