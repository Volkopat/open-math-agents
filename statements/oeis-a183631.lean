import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a183631

/-- OEIS A183631: Number of `(n + 1) × 9` `0..2` arrays with every `2 × 2` subblock summing to `4`. -/
def A183631 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 9 → Fin 3 =>
    ∀ (i : Fin n) (j : Fin 8),
      (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)).1 +
      (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 +
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)).1 +
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 = 4)).card

/-- OEIS A183631 conjectures (Colin Barker, Mar 31 2018):
1. Closed form for all `n ≥ 1`: `a(n) = 3 * (6220 + 85 * 2^(2 + n) + 3^n)`.
2. Rational generating function:
   `(1 - X) * (1 - 2 * X) * (1 - 3 * X) * ∑_{n≥1} a(n) X^n = 3 * X * (6903 - 33829 * X + 39366 * X^2)`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → A183631 n = 3 * (6220 + 85 * 2 ^ (2 + n) + 3 ^ n)) ∧
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183631 n : ℤ)) =
      3 * PowerSeries.X * (6903 - 33829 * PowerSeries.X + 39366 * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a183631
