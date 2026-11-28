import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Rat.Defs

namespace OMA.S_oeis_a397348

/-- Conjecture (OEIS A397348): If the integer sequence `a : ℕ → ℤ` has ordinary generating
function `A(x) = ∑ a(n) x^n` satisfying
`A(x) = exp(x + ∑_{n ≥ 2} ((3 * n^2 - 1) / (3 * n^2)) * a(n) * x^n)`,
then for every `n : ℕ`, `a(n)` is odd if and only if `n + 1` is a power of `2`. -/
theorem main :
    ∀ a : ℕ → ℤ,
      PowerSeries.mk (fun n => (a n : ℚ)) =
        PowerSeries.subst
          (PowerSeries.mk fun n =>
            if n = 0 then (0 : ℚ)
            else if n = 1 then (1 : ℚ)
            else ((3 * (n : ℚ) ^ 2 - 1) / (3 * (n : ℚ) ^ 2)) * (a n : ℚ))
          (PowerSeries.exp ℚ) →
      ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  sorry

end OMA.S_oeis_a397348
