import Mathlib

/-!
# A245637: Integral_{x = 1..infinity} 1/x^x dx (Bala's double-integral identity)

Source: https://oeis.org/A245637 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A245637: decimal expansion of the constant Integral_{x = 1..infinity} 1/x^x dx = 0.7041699604...

The entry records (Peter Bala, Nov 10 2019):

  Conjecturally, equals 1 - Integral_{x = 1..oo, y = 1..oo} 1/(x*y)^(x*y) dx dy.
  [added Dec 21 2022: follows from Glasser's Theorem 1.]

The entry notes that the identity has since been derived from a theorem of Glasser; it is
stated here as the source records it.

Reading of the source:
* Both integrals are Lebesgue integrals over `[1, ∞)` (respectively `[1, ∞)²`, as an iterated
  integral) of positive continuous integrands, with `t^t` the real power `t ^ t` (`Real.rpow`).
  The integrands are integrable (they decay faster than any exponential), so the iterated
  integral equals the double integral.
* The statement: `∫_{1}^{∞} x^(-x) dx = 1 - ∫_{1}^{∞} ∫_{1}^{∞} (x y)^(-x y) dy dx`.
-/

namespace OMA.S_oeis_a245637

open MeasureTheory Set

/-- Bala's identity: `∫_{x ≥ 1} 1/x^x dx = 1 - ∫_{x ≥ 1} ∫_{y ≥ 1} 1/(x y)^(x y) dy dx`. -/
theorem main :
    ∫ x in Ici (1 : ℝ), 1 / x ^ x =
      1 - ∫ x in Ici (1 : ℝ), ∫ y in Ici (1 : ℝ), 1 / (x * y) ^ (x * y) := by
  sorry

end OMA.S_oeis_a245637
