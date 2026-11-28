import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt

/-! Source: https://mathoverflow.net/questions/237737 -/

namespace OMA.S_mo_237737

/-- Coefficients of (1 + √2)^n, with the Pell number in the second coordinate. -/
def pellPair : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := pellPair n
    (x + 2 * y, x + y)

/-- The strict distance bound is equivalent to a witness integer k. -/
def qualifies (q : ℤ) : Prop :=
  ∃ k : ℤ, |(q : ℝ)| * |(q : ℝ) * (Real.sqrt 2 / 2) + 1 / 2 - (k : ℝ)| < 1 / 4

/-- The choice θ = √2 / 2 and α = 1 / 2 gives precisely the signed Pell numbers. -/
theorem main :
    Irrational (Real.sqrt 2 / 2) ∧
    (∀ a b : ℤ, (1 : ℝ) / 2 ≠ (a : ℝ) * (Real.sqrt 2 / 2) + (b : ℝ)) ∧
    StrictMono (fun n => (pellPair n).2) ∧
    (∀ q : ℤ, qualifies q ↔ ∃ n : ℕ, (q.natAbs : ℤ) = (pellPair n).2) := by
  sorry

end OMA.S_mo_237737
