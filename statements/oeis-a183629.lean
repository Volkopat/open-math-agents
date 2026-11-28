import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a183629

/-- OEIS A183629: Number of `(n + 1) × 7` `0..2` arrays with every `2 × 2` subblock summing to `4`. -/
def A183629 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 7 → Fin 3 =>
    ∀ (i : Fin n) (j : Fin 6),
      (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)).1 +
      (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 +
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)).1 +
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 = 4)).card

/-- OEIS A183629 conjectures (Colin Barker, Mar 31 2018):
1. Closed form for all `n ≥ 1`: `a(n) = 3 * (644 + 21 * 2^(2 + n) + 3^n)`.
2. Rational generating function:
   `(1 - X) * (1 - 2 * X) * (1 - 3 * X) * ∑_{n≥1} a(n) X^n = 3 * X * (815 - 3901 * X + 4374 * X^2)`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → A183629 n = 3 * (644 + 21 * 2 ^ (2 + n) + 3 ^ n)) ∧
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183629 n : ℤ)) =
      3 * PowerSeries.X * (815 - 3901 * PowerSeries.X + 4374 * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a183629
