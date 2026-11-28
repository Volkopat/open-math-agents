import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

open Filter

namespace OMA.S_mo_344265

/-- The coefficient term in the Ramanujan-type series with rational argument z. -/
noncomputable def summand (s : ℕ) (a b : ℂ) (z : ℚ) (n : ℕ) : ℂ :=
  let p := ascPochhammer ℂ n
  p.eval (1 / 2) * p.eval (1 / (s : ℂ)) * p.eval (1 - 1 / (s : ℂ)) /
    (p.eval 1) ^ 3 * (b * n + a) * (z : ℂ) ^ n

/-- Rationality of z forces rationality of the ratio a divided by b. -/
theorem main :
    ∀ (s : ℕ) (a b : ℂ) (z : ℚ),
      (s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 6) → IsAlgebraic ℚ a → IsAlgebraic ℚ b → b ≠ 0 →
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, summand s a b z n)
          atTop (nhds (1 / (Real.pi : ℂ))) →
            ∃ q : ℚ, (q : ℂ) = a / b := by
  sorry

end OMA.S_mo_344265
