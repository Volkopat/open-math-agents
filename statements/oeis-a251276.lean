import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a251276

/-- A `2 × 2` `0..3` subblock `[[a, b], [c, d]]` does not have its maximum diagonal element
less than its minimum antidiagonal element (`¬ (max a d < min b c)`). -/
def validBlock (a b c d : Fin 4) : Prop :=
  ¬ (max a.1 d.1 < min b.1 c.1)

instance (a b c d : Fin 4) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A251276: Number of `(n + 1) × 2` `0..3` arrays with no `2 × 2` subblock having its
maximum diagonal element less than its minimum antidiagonal element. -/
def A251276 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 4 =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)))).card

/-- OEIS A251276 conjectures (Colin Barker, Nov 27 2018):
1. Rational generating function:
   `(1 - 16 * X + 26 * X^2) * ∑_{n≥1} a(n) X^n = 2 * X * (115 - 208 * X)`.
2. Binet closed form for all `n ≥ 1`:
   `a(n) = ((8 - √38)^n * (-51 + 8*√38) + (8 + √38)^n * (51 + 8*√38)) / √38`. -/
theorem main :
    (1 - 16 * PowerSeries.X + 26 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A251276 n : ℤ)) =
      2 * PowerSeries.X * (115 - 208 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A251276 n : ℝ) =
        ((8 - Real.sqrt 38) ^ n * (-51 + 8 * Real.sqrt 38) +
         (8 + Real.sqrt 38) ^ n * (51 + 8 * Real.sqrt 38)) / Real.sqrt 38) := by
  sorry

end OMA.S_oeis_a251276
