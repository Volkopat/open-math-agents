import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a235895

/-- A `2 × 2` `0..2` subblock `[[a, b], [c, d]]` has `min + max = lower_median + upper_median`
(equivalently, `2 * (min + max) = a + b + c + d`). -/
def validBlock (a b c d : Fin 3) : Prop :=
  2 * (min (min a.1 b.1) (min c.1 d.1) + max (max a.1 b.1) (max c.1 d.1)) =
    a.1 + b.1 + c.1 + d.1

instance (a b c d : Fin 3) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A235895: Number of `(n + 1) × 2` `0..2` arrays with the minimum plus the maximum equal to
the lower median plus the upper median in every `2 × 2` subblock. -/
def A235895 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 3 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card

/-- OEIS A235895 conjectures (Colin Barker, Oct 20 2018):
1. Rational generating function:
   `(1 - 4 * X) * (1 - 3 * X - 2 * X^2) * ∑_{n≥1} a(n) X^n = X * (33 - 106 * X - 72 * X^2)`.
2. Closed form for all `n ≥ 1`:
   `a(n) = 4^(1 + n) + (2^(-1 - n) * ((3 - √17)^n * (-19 + 5*√17) + (3 + √17)^n * (19 + 5*√17))) / √17`. -/
theorem main :
    (1 - 4 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235895 n : ℤ)) =
      PowerSeries.X * (33 - 106 * PowerSeries.X - 72 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A235895 n : ℝ) =
        (4 : ℝ) ^ (1 + n) +
        ((2 : ℝ) ^ (-1 - (n : ℤ)) *
          ((3 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) +
           (3 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a235895
