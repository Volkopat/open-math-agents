import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a209532

/-- A `2 × 2` `0..2` subblock `[[a, b], [c, d]]` has exactly two distinct clockwise edge
differences `(b - a, d - b, c - d, a - c)`. -/
def validBlock (a b c d : Fin 3) : Prop :=
  (({(b.1 : ℤ) - a.1, (d.1 : ℤ) - b.1, (c.1 : ℤ) - d.1, (a.1 : ℤ) - c.1} : Finset ℤ).card = 2)

instance (a b c d : Fin 3) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A209532: Half the number of `(n + 1) × 7` `0..2` arrays with every `2 × 2` subblock
having exactly two distinct clockwise edge differences. -/
def A209532 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 7 → Fin 3 =>
    ∀ (i : Fin n) (j : Fin 6),
      validBlock (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
        (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)))).card / 2

/-- OEIS A209532 conjectures (Colin Barker, Jul 11 2018):
1. Rational generating function:
   `(1 - X) * (1 - 128 * X^2) * ∑_{n≥1} a(n) X^n = X * (129 + 1408 * X - 1664 * X^2)`.
2. Closed form for all `n ≥ 1`:
   - `a(n) = 3 * 2^((7 * n) / 2 + 2) + 1` for `n` even;
   - `a(n) = 2^((7 * (n + 1)) / 2) + 1` for `n` odd. -/
theorem main :
    (1 - PowerSeries.X) * (1 - 128 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A209532 n : ℤ)) =
      PowerSeries.X * (129 + 1408 * PowerSeries.X - 1664 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      if Even n then A209532 n = 3 * 2 ^ ((7 * n) / 2 + 2) + 1
      else A209532 n = 2 ^ ((7 * (n + 1)) / 2) + 1) := by
  sorry

end OMA.S_oeis_a209532
