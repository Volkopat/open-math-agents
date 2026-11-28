import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Rat.Defs

namespace OMA.S_oeis_a397347

/-- Conjecture (OEIS A397347): If the integer sequence `a : ℕ → ℤ` has logarithmic generating
function `L(x) = ∑_{n ≥ 1} (a(n) / n) * x^n` satisfying
`exp(L(x)) = 1 + x + ∑_{n ≥ 2} (2 * n / (2 * n^2 - 1)) * a(n) * x^n`
(equivalently `L(x) = log(1 + x + ∑_{n ≥ 2} (2 * n / (2 * n^2 - 1)) * a(n) * x^n)`),
then for every `n ≥ 1`, `a(n) ≡ 1 (mod 4)` if `n % 4 = 1`, and `a(n) ≡ 3 (mod 4)` otherwise. -/
theorem main :
    ∀ a : ℕ → ℤ,
      PowerSeries.mk (fun n =>
        if n = 0 then (1 : ℚ)
        else if n = 1 then (1 : ℚ)
        else ((2 * (n : ℚ)) / (2 * (n : ℚ) ^ 2 - 1)) * (a n : ℚ)) =
        PowerSeries.subst
          (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) / (n : ℚ))
          (PowerSeries.exp ℚ) →
      ∀ n : ℕ, 1 ≤ n → a n % 4 = if n % 4 = 1 then 1 else 3 := by
  sorry

end OMA.S_oeis_a397347
