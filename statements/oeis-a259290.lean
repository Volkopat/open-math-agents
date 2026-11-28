import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a259290

/-- A 4-tuple of bits `(a, b, c, d)` has clockwise pattern `0001`, `0101`, or `0111`
(up to cyclic shift). -/
def validBlock (a b c d : Bool) : Prop :=
  (a = false ∧ b = false ∧ c = false ∧ d = true) ∨
  (a = true ∧ b = false ∧ c = false ∧ d = false) ∨
  (a = false ∧ b = true ∧ c = false ∧ d = false) ∨
  (a = false ∧ b = false ∧ c = true ∧ d = false) ∨
  (a = false ∧ b = true ∧ c = false ∧ d = true) ∨
  (a = true ∧ b = false ∧ c = true ∧ d = false) ∨
  (a = false ∧ b = true ∧ c = true ∧ d = true) ∨
  (a = true ∧ b = false ∧ c = true ∧ d = true) ∨
  (a = true ∧ b = true ∧ c = false ∧ d = true) ∨
  (a = true ∧ b = true ∧ c = true ∧ d = false)

instance (a b c d : Bool) : Decidable (validBlock a b c d) := by
  unfold validBlock; infer_instance

/-- OEIS A259290: Number of `(n + 1) × 2` `0..1` arrays with each `2 × 2` subblock
having clockwise pattern `0001`, `0101`, or `0111`. -/
def A259290 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Bool =>
    ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 1)) (A (⟨i.1 + 1, by omega⟩, 0)))).card

/-- OEIS A259290 conjectures (Colin Barker, Dec 25 2018):
1. Rational generating function:
   `(1 - X - 4 * X^2) * ∑_{n≥1} a(n) X^n = 2 * X * (5 + 8 * X)`.
2. Binet closed form for all `n ≥ 1`:
   `a(n) = (2^(1 - n) * ((1 - √17)^n * (-4 + √17) + (1 + √17)^n * (4 + √17))) / √17`. -/
theorem main :
    (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A259290 n : ℤ)) =
      2 * PowerSeries.X * (5 + 8 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n →
      (A259290 n : ℝ) =
        ((2 : ℝ) ^ (1 - (n : ℤ)) *
          ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) +
           (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a259290
