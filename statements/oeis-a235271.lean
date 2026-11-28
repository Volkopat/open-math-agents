import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a235271

/-- A `2 × 2` `0..4` subblock `[[a, b], [c, d]]` has diagonal sum differing from antidiagonal sum
by 5 (`|(a + d) - (b + c)| = 5`). -/
def validBlock (a b c d : Fin 5) : Prop :=
  |((a.1 : ℤ) + d.1) - ((b.1 : ℤ) + c.1)| = 5

instance (a b c d : Fin 5) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A235271: Number of `(n + 1) × 2` `0..4` arrays with every `2 × 2` subblock having its
diagonal sum differing from its antidiagonal sum by 5. -/
def A235271 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 5 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card

/-- OEIS A235271 conjectures (Colin Barker, Oct 17 2018):
1. Rational generating function:
   `(1 - 2 * X) * (1 + 2 * X) * (1 - 6 * X^2) * ∑_{n≥1} a(n) X^n = 4 * X * (2 + 5 * X) * (5 - 24 * X^2)`.
2. Closed form for all `n ≥ 1`:
   `a(n) = (-2)^n + 9 * 2^n + 6^((1/2)*(-1 + n)) * (12 - 12*(-1)^n + 5*√6 + 5*(-1)^n*√6)`. -/
theorem main :
    (1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X) * (1 - 6 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235271 n : ℤ)) =
      4 * PowerSeries.X * (2 + 5 * PowerSeries.X) * (5 - 24 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A235271 n : ℝ) =
        (-2 : ℝ) ^ n + 9 * (2 : ℝ) ^ n +
        (6 : ℝ) ^ ((1 / 2 : ℝ) * (-1 + (n : ℝ))) *
          (12 - 12 * (-1 : ℝ) ^ n + 5 * Real.sqrt 6 + 5 * (-1 : ℝ) ^ n * Real.sqrt 6)) := by
  sorry

end OMA.S_oeis_a235271
