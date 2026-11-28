import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a183980

/-- Sum of a `2 × 2` binary subblock. -/
def blockSum (a b c d : Bool) : ℕ :=
  (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0)

open scoped Classical in
/-- OEIS A183980: `1/4` the number of `(n + 1) × 4` binary arrays with all `2 × 2` subblock sums
the same. -/
noncomputable def A183980 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 4 → Bool =>
    ∃ s : ℕ, ∀ (i : Fin n) (j : Fin 3),
      blockSum (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
        (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)) = s)).card / 4

/-- OEIS A183980 conjectures (Colin Barker, Apr 07 2018):
1. Rational generating function:
   `(1 - X) * (1 - 2 * X) * (1 - 2 * X^2) * ∑_{n≥1} a(n) X^n = X * (9 - 16 * X - 19 * X^2 + 32 * X^3)`.
2. Closed form for all `n ≥ 1`:
   - `2 * a(n) = 3 * 2^(n/2) + 2^n + 12` for `n` even;
   - `a(n) = 2^((n + 1)/2) + 2^(n - 1) + 6` for `n` odd. -/
theorem main :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183980 n : ℤ)) =
      PowerSeries.X * (9 - 16 * PowerSeries.X - 19 * PowerSeries.X ^ 2 + 32 * PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n →
      if Even n then 2 * A183980 n = 3 * 2 ^ (n / 2) + 2 ^ n + 12
      else A183980 n = 2 ^ ((n + 1) / 2) + 2 ^ (n - 1) + 6) := by
  sorry

end OMA.S_oeis_a183980
