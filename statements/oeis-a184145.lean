import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a184145

/-- A `2 × 2` `0..3` subblock `[[a, b], [c, d]]` has at least two equal elements connected
horizontally or vertically. -/
def validBlock (a b c d : Fin 4) : Prop :=
  a = b ∨ c = d ∨ a = c ∨ b = d

instance (a b c d : Fin 4) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A184145: `1/4` the number of `(n + 1) × 2` `0..3` arrays with every `2 × 2` subblock
having at least two equal elements connected horizontally or vertically. -/
def A184145 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 4 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card / 4

/-- OEIS A184145 conjectures (Colin Barker, Apr 12 2018):
1. Rational generating function:
   `(1 - 9 * X - 28 * X^2) * ∑_{n≥1} a(n) X^n = X * (43 + 112 * X)`.
2. Binet closed form for all `n ≥ 1`:
   `a(n) = (2^(-n) * ((9 - √193)^n * (-25 + 2*√193) + (9 + √193)^n * (25 + 2*√193))) / √193`. -/
theorem main :
    (1 - 9 * PowerSeries.X - 28 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A184145 n : ℤ)) =
      PowerSeries.X * (43 + 112 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A184145 n : ℝ) =
        ((2 : ℝ) ^ (-(n : ℤ)) *
          ((9 - Real.sqrt 193) ^ n * (-25 + 2 * Real.sqrt 193) +
           (9 + Real.sqrt 193) ^ n * (25 + 2 * Real.sqrt 193))) / Real.sqrt 193) := by
  sorry

end OMA.S_oeis_a184145
