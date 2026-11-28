import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a185761

/-- Trace of a `2 × 2` binary subblock `[[a, b], [c, d]]` (`a + d` as a natural number). -/
def blockTrace (a d : Bool) : ℕ :=
  (if a then 1 else 0) + (if d then 1 else 0)

/-- OEIS A185761: Number of `(n + 1) × 2` binary arrays with no `2 × 2` subblock trace equal to
any horizontal or vertical neighbor `2 × 2` subblock trace. -/
def A185761 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Bool =>
    ∀ i : Fin (n - 1),
      blockTrace (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)) ≠
      blockTrace (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 2, by omega⟩, 1)))).card

/-- OEIS A185761 conjectures (Colin Barker, Feb 22 2018):
1. Rational generating function:
   `(1 - X - 4 * X^2) * ∑_{n≥1} a(n) X^n = 8 * X * (2 + 3 * X)`.
2. Binet closed form for all `n ≥ 1`:
   `a(n) = (2^(-n) * ((1 - √17)^n * (-13 + 3*√17) + (1 + √17)^n * (13 + 3*√17))) / √17`. -/
theorem main :
    (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A185761 n : ℤ)) =
      8 * PowerSeries.X * (2 + 3 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A185761 n : ℝ) =
        ((2 : ℝ) ^ (-(n : ℤ)) *
          ((1 - Real.sqrt 17) ^ n * (-13 + 3 * Real.sqrt 17) +
           (1 + Real.sqrt 17) ^ n * (13 + 3 * Real.sqrt 17))) / Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a185761
