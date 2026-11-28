import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a259243

/-- A 4-tuple of bits `(a, b, c, d)` has clockwise pattern `0000`, `0011`, or `0111`
(up to cyclic shift). -/
def validBlock (a b c d : Bool) : Prop :=
  (a = false ∧ b = false ∧ c = false ∧ d = false) ∨
  (a = false ∧ b = false ∧ c = true ∧ d = true) ∨
  (a = true ∧ b = false ∧ c = false ∧ d = true) ∨
  (a = true ∧ b = true ∧ c = false ∧ d = false) ∨
  (a = false ∧ b = true ∧ c = true ∧ d = false) ∨
  (a = false ∧ b = true ∧ c = true ∧ d = true) ∨
  (a = true ∧ b = false ∧ c = true ∧ d = true) ∨
  (a = true ∧ b = true ∧ c = false ∧ d = true) ∨
  (a = true ∧ b = true ∧ c = true ∧ d = false)

instance (a b c d : Bool) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A259243: Number of `(n + 1) × 2` `0..1` arrays with each `2 × 2` subblock
having clockwise pattern `0000`, `0011`, or `0111`. -/
def A259243 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Bool =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 1)) (A (⟨i.1 + 1, by omega⟩, 0)))).card

/-- OEIS A259243 conjectures (Colin Barker, Dec 24 2018):
1. Rational generating function:
   `(1 - X - 3 * X^2) * ∑_{n≥1} a(n) X^n = 3 * X * (3 + 4 * X)`.
2. Binet closed form for all `n ≥ 1`:
   `a(n) = (2^(-n) * ((1 - √13)^n * (-7 + 2*√13) + (1 + √13)^n * (7 + 2*√13))) / √13`. -/
theorem main :
    (1 - PowerSeries.X - 3 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A259243 n : ℤ)) =
      3 * PowerSeries.X * (3 + 4 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A259243 n : ℝ) =
        ((2 : ℝ) ^ (-(n : ℤ)) *
          ((1 - Real.sqrt 13) ^ n * (-7 + 2 * Real.sqrt 13) +
           (1 + Real.sqrt 13) ^ n * (7 + 2 * Real.sqrt 13))) / Real.sqrt 13) := by
  sorry

end OMA.S_oeis_a259243
