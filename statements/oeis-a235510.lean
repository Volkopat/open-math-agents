import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a235510

/-- Sum of the maximum and minimum of a `2 × 2` `0..1` subblock (`0`, `1`, or `2`). -/
def blockMaxMin (a b c d : Bool) : ℕ :=
  (if a || b || c || d then 1 else 0) + (if a && b && c && d then 1 else 0)

/-- OEIS A235510: Number of `(n + 1) × 2` `0..1` arrays with the sum of each `2 × 2` subblock
maximum and minimum nondecreasing downwards. -/
def A235510 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Bool =>
    ∀ i : Fin (n - 1),
      blockMaxMin (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
        (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)) ≤
      blockMaxMin (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))
        (A (⟨i.1 + 2, by omega⟩, 0)) (A (⟨i.1 + 2, by omega⟩, 1)))).card

/-- OEIS A235510 conjectures (Colin Barker, Mar 19 2018):
1. Rational generating function:
   `(1 - X)^2 * (1 + X) * (1 - 3*X - 2*X^2) * ∑_{n≥1} a(n) X^n = X*(16 - 6*X - 23*X^2 + 6*X^3 + 8*X^4)`.
2. Closed form for all `n ≥ 1`:
   `a(n) = (1/544) * (-221 - 68*(-1)^n + 2^(-1 - n)*((2533 - 611*√17)*(3 - √17)^n + (3 + √17)^n*(2533 + 611*√17)) - 68*(1 + n))`. -/
theorem main :
    (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235510 n : ℤ)) =
      PowerSeries.X * (16 - 6 * PowerSeries.X - 23 * PowerSeries.X ^ 2 +
        6 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A235510 n : ℝ) =
        (1 / 544 : ℝ) *
          (-221 - 68 * (-1 : ℝ) ^ n +
           (2 : ℝ) ^ (-1 - (n : ℤ)) *
             ((2533 - 611 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n +
              (3 + Real.sqrt 17) ^ n * (2533 + 611 * Real.sqrt 17)) -
           68 * (1 + (n : ℝ)))) := by
  sorry

end OMA.S_oeis_a235510
