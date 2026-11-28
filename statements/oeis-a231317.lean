import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a231317

/-- Diagonal and antidiagonal neighbors of `(i, j)` in an `(n + 1) × 2` grid:
two cells are diagonal/antidiagonal neighbors iff their row indices differ by 1 and their column
indices differ by 1. -/
def isDiagNeighbor {n : ℕ} (p q : Fin (n + 1) × Fin 2) : Bool :=
  decide ((p.1.1 + 1 = q.1.1 ∨ q.1.1 + 1 = p.1.1) ∧ p.2 ≠ q.2)

/-- No element is equal to a strict majority of its diagonal and antidiagonal neighbors. -/
def noDiagMajority (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Prop :=
  ∀ p : Fin (n + 1) × Fin 2,
    2 * (Finset.univ.filter (fun q => isDiagNeighbor p q = true ∧ A q = A p)).card ≤
      (Finset.univ.filter (fun q => isDiagNeighbor p q = true)).card

instance (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Decidable (noDiagMajority n A) := by
  unfold noDiagMajority; infer_instance

/-- Values `0..2` are introduced in row-major order (`0` before `1` before `2`). -/
def isRowMajor (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Prop :=
  ∀ p : Fin (n + 1) × Fin 2, A p ≠ 0 →
    ∃ q : Fin (n + 1) × Fin 2,
      2 * q.1.1 + q.2.1 < 2 * p.1.1 + p.2.1 ∧ (A q).1 + 1 = (A p).1

instance (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Decidable (isRowMajor n A) := by
  unfold isRowMajor; infer_instance

/-- OEIS A231317: Number of `(n + 1) × 2` `0..2` arrays with no element equal to a strict majority
of its diagonal and antidiagonal neighbors, with values `0..2` introduced in row-major order. -/
def A231317 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 3 =>
    noDiagMajority n A ∧ isRowMajor n A)).card

/-- OEIS A231317 conjectures (Colin Barker, Mar 18 2018):
1. Rational generating function:
   `(1 + 2 * X) * (1 - 8 * X + 4 * X^2) * ∑_{n≥1} a(n) X^n = 6 * X * (1 - 2 * X)`.
2. Closed form for all `n ≥ 1`:
   `a(n) = ((-2)^(1 + n) + (4 - 2*√3)^n + (2 * (2 + √3))^n) / 2`. -/
theorem main :
    (1 + 2 * PowerSeries.X) * (1 - 8 * PowerSeries.X + 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A231317 n : ℤ)) =
      6 * PowerSeries.X * (1 - 2 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A231317 n : ℝ) =
        ((-2 : ℝ) ^ (1 + n) + (4 - 2 * Real.sqrt 3) ^ n + (2 * (2 + Real.sqrt 3)) ^ n) / 2) := by
  sorry

end OMA.S_oeis_a231317
