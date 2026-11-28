import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a234789

/-- A `2 × 2` `0..3` subblock `[[a, b], [c, d]]` has clockwise edge increases
(`a < b`, `b < d`, `d < c`, `c < a`) less than or equal to clockwise edge decreases
(`a > b`, `b > d`, `d > c`, `c > a`). -/
def validBlock (a b c d : Fin 4) : Prop :=
  (if a < b then 1 else 0) + (if b < d then 1 else 0) +
    (if d < c then 1 else 0) + (if c < a then 1 else 0) ≤
  (if b < a then 1 else 0) + (if d < b then 1 else 0) +
    (if c < d then 1 else 0) + (if a < c then 1 else 0)

instance (a b c d : Fin 4) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A234789: Number of `(n + 1) × 2` `0..3` arrays with each `2 × 2` subblock having the
number of clockwise edge increases less than or equal to the number of clockwise edge decreases. -/
def A234789 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 4 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card

/-- OEIS A234789 conjectures (Colin Barker, Oct 16 2018):
1. Rational generating function:
   `(1 - 2 * X) * (1 - 13 * X + 10 * X^2) * ∑_{n≥1} a(n) X^n = 4 * X * (51 - 139 * X + 80 * X^2)`.
2. Closed form for all `n ≥ 1`:
   `a(n) = (1/129) * 2^(-1 - n) * (-129 * 2^(1 + 2*n) + (2193 - 191*√129)*(13 - √129)^n + (13 + √129)^n*(2193 + 191*√129))`. -/
theorem main :
    (1 - 2 * PowerSeries.X) * (1 - 13 * PowerSeries.X + 10 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234789 n : ℤ)) =
      4 * PowerSeries.X * (51 - 139 * PowerSeries.X + 80 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A234789 n : ℝ) =
        (1 / 129 : ℝ) * (2 : ℝ) ^ (-1 - (n : ℤ)) *
          (-129 * (2 : ℝ) ^ (1 + 2 * n) +
           (2193 - 191 * Real.sqrt 129) * (13 - Real.sqrt 129) ^ n +
           (13 + Real.sqrt 129) ^ n * (2193 + 191 * Real.sqrt 129))) := by
  sorry

end OMA.S_oeis_a234789
