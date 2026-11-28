import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a209789

/-- A `2 × 2` `0..2` subblock `[[a, b], [c, d]]` has exactly one duplicate clockwise edge
difference `(b - a, d - b, c - d, a - c)`, i.e., exactly 3 distinct values among the 4 differences. -/
def validBlock (a b c d : Fin 3) : Prop :=
  (({(b.1 : ℤ) - a.1, (d.1 : ℤ) - b.1, (c.1 : ℤ) - d.1, (a.1 : ℤ) - c.1} : Finset ℤ).card = 3)

instance (a b c d : Fin 3) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A209789: Half the number of `(n + 1) × 2` `0..2` arrays with every `2 × 2` subblock
having exactly one duplicate clockwise edge difference. -/
def A209789 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 3 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card / 2

/-- OEIS A209789 conjectures (Colin Barker, Jul 13 2018):
1. Rational generating function:
   `(1 - 5 * X - 12 * X^2) * ∑_{n≥1} a(n) X^n = 6 * X * (5 + 9 * X)`.
2. Binet closed form for all `n ≥ 1`:
   `a(n) = (2^(-2 - n) * (3 * (5 + √73)^n * (25 + 3*√73) + (5 - √73)^n * (-75 + 9*√73))) / √73`. -/
theorem main :
    (1 - 5 * PowerSeries.X - 12 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A209789 n : ℤ)) =
      6 * PowerSeries.X * (5 + 9 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A209789 n : ℝ) =
        ((2 : ℝ) ^ (-2 - (n : ℤ)) *
          (3 * (5 + Real.sqrt 73) ^ n * (25 + 3 * Real.sqrt 73) +
           (5 - Real.sqrt 73) ^ n * (-75 + 9 * Real.sqrt 73))) / Real.sqrt 73) := by
  sorry

end OMA.S_oeis_a209789
