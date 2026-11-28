import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a204707

/-- Permanent of a `2 × 2` `0..1` subblock. -/
def blockPerm (a b c d : Bool) : ℕ :=
  (if a && d then 1 else 0) + (if b && c then 1 else 0)

open scoped Classical in
/-- OEIS A204707: Number of `(n + 1) × 3` `0..1` arrays with the permanents of all `2 × 2`
subblocks equal and nonzero. -/
noncomputable def A204707 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 3 → Bool =>
    ∃ p : ℕ, p ≠ 0 ∧
      ∀ (i : Fin n) (j : Fin 2),
        blockPerm (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
          (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
          (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
          (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)) = p)).card

/-- OEIS A204707 conjectures (Colin Barker, Jun 09 2018):
1. Rational generating function:
   `(1 - X) * (1 - X - 4 * X^2) * ∑_{n≥1} a(n) X^n = X * (13 + 7 * X - 24 * X^2)`.
2. Binet closed form for all `n ≥ 1`:
   `a(n) = 1 + (2^(-1 - n) * ((1 - √17)^n * (-19 + 5*√17) + (1 + √17)^n * (19 + 5*√17))) / √17`. -/
theorem main :
    (1 - PowerSeries.X) * (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A204707 n : ℤ)) =
      PowerSeries.X * (13 + 7 * PowerSeries.X - 24 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A204707 n : ℝ) =
        1 + ((2 : ℝ) ^ (-1 - (n : ℤ)) *
          ((1 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) +
           (1 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a204707
