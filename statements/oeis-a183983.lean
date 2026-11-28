import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a183983

/-- Sum of a `2 × 2` binary subblock. -/
def blockSum (a b c d : Bool) : ℕ :=
  (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0)

open scoped Classical in
/-- OEIS A183983: `1/4` the number of `(n + 1) × 7` binary arrays with all `2 × 2` subblock sums
the same. -/
noncomputable def A183983 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 7 → Bool =>
    ∃ s : ℕ, ∀ (i : Fin n) (j : Fin 6),
      blockSum (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
        (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)) = s)).card / 4

/-- OEIS A183983 conjectures (Colin Barker, Apr 07 2018):
1. Rational generating function:
   `(1 - X) * (1 - 2 * X) * (1 - 2 * X^2) * ∑_{n≥1} a(n) X^n = X * (45 - 88 * X - 91 * X^2 + 176 * X^3)`.
2. Closed form for all `n ≥ 1`:
   - `2 * a(n) = 3 * 2^(n/2) + 2^n + 84` for `n` even;
   - `a(n) = 2^((n + 1)/2) + 2^(n - 1) + 42` for `n` odd. -/
theorem main :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183983 n : ℤ)) =
      PowerSeries.X * (45 - 88 * PowerSeries.X - 91 * PowerSeries.X ^ 2 + 176 * PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n →
      if Even n then 2 * A183983 n = 3 * 2 ^ (n / 2) + 2 ^ n + 84
      else A183983 n = 2 ^ ((n + 1) / 2) + 2 ^ (n - 1) + 42) ∧
    (∀ n : ℕ, 4 < n →
      (A183983 n : ℤ) = 3 * A183983 (n - 1) - 6 * A183983 (n - 3) + 4 * A183983 (n - 4)) := by
  sorry

end OMA.S_oeis_a183983
