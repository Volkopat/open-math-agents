import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Basic

/-! Source: https://mathoverflow.net/questions/479628
Sequence: https://oeis.org/A129179 -/

namespace OMA.S_mo_479628

noncomputable def P : ℕ → ℕ → Polynomial ℕ
  | _, 0 => 1
  | n, k + 1 => if n < k + 1 then 0 else
      P (n - 1) (k + 1) + Polynomial.X ^ (n - (k + 1)) * P (n + (n - (k + 1)) % 2) k
termination_by n k => (k, n)
decreasing_by
  · apply Prod.Lex.right; omega
  · apply Prod.Lex.left; omega

/-- The outer variable marks semilength and the coefficient polynomial records area. -/
theorem main :
    ∀ G : PowerSeries (Polynomial ℕ),
      G = 1 + PowerSeries.X * G + PowerSeries.C (Polynomial.X : Polynomial ℕ) *
        PowerSeries.X * PowerSeries.rescale (Polynomial.X ^ 2) G * G →
      ∀ n : ℕ, P (n + 1) (n + 1) = PowerSeries.coeff n G := by
  sorry

end OMA.S_mo_479628
