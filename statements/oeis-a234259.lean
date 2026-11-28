import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a234259

/-- A `2 × 2` `0..2` subblock `[[a, b], [c, d]]` has diagonal sum differing from antidiagonal sum
by `2`. -/
def validBlock (a b c d : Fin 3) : Prop :=
  |(a.1 : ℤ) + d.1 - ((b.1 : ℤ) + c.1)| = 2

instance (a b c d : Fin 3) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A234259: Number of `(n + 1) × 2` `0..2` arrays with every `2 × 2` subblock having its
diagonal sum differing from its antidiagonal sum by `2`. -/
def A234259 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 3 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card

/-- OEIS A234259 conjecture (Colin Barker, Oct 14 2018):
1. Rational generating function:
   `(1 - 2 * X) * (1 - 6 * X^2) * ∑_{n≥1} a(n) X^n = 2 * X * (10 + 3 * X - 54 * X^2)`.
2. Explicit closed form for all `n ≥ 1`:
   `a(n) = 2^(2 + n) + 5 * 6^(n / 2)` for even `n`,
   `a(n) = 2^(2 + n) + 12 * 6^((n - 1) / 2)` for odd `n`. -/
theorem main :
    (1 - 2 * PowerSeries.X) * (1 - 6 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234259 n : ℤ)) =
      2 * PowerSeries.X * (10 + 3 * PowerSeries.X - 54 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      A234259 n =
        if Even n then 2 ^ (2 + n) + 5 * 6 ^ (n / 2)
        else 2 ^ (2 + n) + 12 * 6 ^ ((n - 1) / 2)) := by
  sorry

end OMA.S_oeis_a234259
