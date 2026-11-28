import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a262415

/-- Binary value of a column of length `m` with top being the most significant bit. -/
def colVal {m : ℕ} (f : Fin m → Bool) : ℕ :=
  ∑ i : Fin m, (if f i then 1 else 0) * 2 ^ (m - 1 - i.1)

/-- Binary value of a 4-bit row with left being the most significant bit. -/
def rowVal (r : Fin 4 → Bool) : ℕ :=
  (if r 0 then 8 else 0) + (if r 1 then 4 else 0) +
  (if r 2 then 2 else 0) + (if r 3 then 1 else 0)

/-- OEIS A262415: Number of `(n + 1) × 4` `0..1` arrays with each row divisible by `3`
and each column not divisible by `3`, read as binary numbers (top/left most significant). -/
def A262415 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 4 → Bool =>
    (∀ i : Fin (n + 1), 3 ∣ rowVal (fun j => A (i, j))) ∧
    (∀ j : Fin 4, ¬ (3 ∣ colVal (fun i => A (i, j)))))).card

/-- OEIS A262415 conjectures (Colin Barker, Dec 31 2018):
1. Rational generating function:
   `(1 - 3*X) * (1 + 3*X) * (1 - 6*X) * ∑_{n≥1} a(n) X^n = 3*X*(2 + 3*X - 18*X^2)`.
2. Closed form for all `n ≥ 1`:
   `2 * a(n) = 3^(n - 1) * (2^(n + 3) - 2)` for even `n`,
   `2 * a(n) = 3^(n - 1) * (2^(n + 3) - 4)` for odd `n`. -/
theorem main :
    (1 - 3 * PowerSeries.X) * (1 + 3 * PowerSeries.X) * (1 - 6 * PowerSeries.X) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A262415 n : ℤ)) =
      3 * PowerSeries.X * (2 + 3 * PowerSeries.X - 18 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      2 * A262415 n =
        if Even n then 3 ^ (n - 1) * (2 ^ (n + 3) - 2)
        else 3 ^ (n - 1) * (2 ^ (n + 3) - 4)) := by
  sorry

end OMA.S_oeis_a262415
