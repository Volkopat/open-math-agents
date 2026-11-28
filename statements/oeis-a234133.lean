import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a234133

/-- A `2 × 2` `0..3` subblock `[[a, b], [c, d]]` has the sum of the absolute values of all six
edge and diagonal differences equal to 9. -/
def validBlock (a b c d : Fin 4) : Prop :=
  |(a.1 : ℤ) - b.1| + |(c.1 : ℤ) - d.1| + |(a.1 : ℤ) - c.1| +
    |(b.1 : ℤ) - d.1| + |(a.1 : ℤ) - d.1| + |(b.1 : ℤ) - c.1| = 9

instance (a b c d : Fin 4) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A234133: Number of `(n + 1) × 2` `0..3` arrays with every `2 × 2` subblock having the
sum of the absolute values of all six edge and diagonal differences equal to 9. -/
def A234133 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 4 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card

/-- OEIS A234133 conjectures (Colin Barker, Oct 13 2018):
1. Rational generating function:
   `(1 - 2 * X) * (1 - 8 * X^2) * ∑_{n≥1} a(n) X^n = 16 * X * (2 + X - 14 * X^2)`.
2. Closed form for all `n ≥ 1`:
   `a(n) = 2^(3 + n) + 2^(-1/2 + (3*n)/2) * (4 - 4*(-1)^n + 3*√2 + 3*(-1)^n*√2)`. -/
theorem main :
    (1 - 2 * PowerSeries.X) * (1 - 8 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234133 n : ℤ)) =
      16 * PowerSeries.X * (2 + PowerSeries.X - 14 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A234133 n : ℝ) =
        (2 : ℝ) ^ (3 + n) +
        (2 : ℝ) ^ (-(1 : ℝ) / 2 + (3 * (n : ℝ)) / 2) *
          (4 - 4 * (-1 : ℝ) ^ n + 3 * Real.sqrt 2 + 3 * (-1 : ℝ) ^ n * Real.sqrt 2)) := by
  sorry

end OMA.S_oeis_a234133
