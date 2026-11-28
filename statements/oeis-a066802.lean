import Mathlib

/-!
# OEIS A066802: `a(n) = binomial(6n, 3n)`

Source: https://oeis.org/A066802
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n) = binomial(6n, 3n)`, offset 0 (`1, 20, 924, 48620, …`).

The entry: "Conjecture: a(n) = [x^n] G(x)^(2*n), where
G(x) = (1 + x)*(1 - 6*x + x^2)/(2*x) + (x^2 - 1)*sqrt(1 - 14*x + x^2)/(2*x)
= 1 + 10*x + 81*x^2 + 720*x^3 + ...." This file states that conjecture.

How `G` is pinned down without a square root of power series:
* Write `P = (1 + x)(1 - 6x + x²)` and `s = sqrt(1 - 14x + x²)`, the branch with `s(0) = 1` (the
  one for which `G` is a power series: `P + (x² - 1) s` then has constant term `1 - 1 = 0`, while
  the other branch would leave `2 / (2x)`). Then `G = (P + (x² - 1) s) / (2x)`, that is
  `2x G - P = (x² - 1) s`, so `(2x G - P)² = (x² - 1)² (1 - 14x + x²)`.
* Conversely, if a power series `G` satisfies `(2x G - P)² = (x² - 1)² (1 - 14x + x²)`, then
  `2x G - P` is a square root of `(x² - 1)² (1 - 14x + x²)` in `PowerSeries ℚ`, so it is
  `±(x² - 1) s`; its constant term is `-P(0) = -1`, which is the constant term of `(x² - 1) s`, so
  the sign is `+` and `G` is the series above. So the statement quantifies over every power series
  `G` satisfying this squared equation, and there is exactly one.
* A computation with exact rationals confirms that this `G` starts `1 + 10x + 81x² + 720x³ + …`,
  as in the entry, and that the conjectured identity holds for every `n ≤ 40`.
-/

namespace OMA.S_oeis_a066802

open PowerSeries

/-- `A066802(n) = binomial(6n, 3n)`. -/
def a (n : ℕ) : ℕ := (6 * n).choose (3 * n)

/-- Conjecture: `a(n) = [x^n] G(x)^(2n)` for the algebraic power series `G` of the entry. -/
theorem main :
    ∀ G : PowerSeries ℚ,
      (2 * X * G - (1 + X) * (1 - 6 * X + X ^ 2)) ^ 2
          = (X ^ 2 - 1) ^ 2 * (1 - 14 * X + X ^ 2) →
      ∀ n : ℕ, coeff n (G ^ (2 * n)) = (a n : ℚ) := by
  sorry

end OMA.S_oeis_a066802
