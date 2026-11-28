import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The exponential growth rate of OEIS A124571

Source: https://oeis.org/A124571 (Michael Somos, with a generating function
by Paul D. Hanna and a limit conjecture by Václav Kotesovec).

The entry defines the generating function as the coefficientwise limit of
these polynomials. Each stage is divisible by X, so the increment from
stage k to stage k + 1 is divisible by X^(k + 2). In particular stage n
already gives the limiting coefficient of degree n. The sequence has
offset 1; its value at 0 has no effect on the limit.
-/

namespace OMA.S_oeis_a124571

noncomputable def stage : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | k + 1 => let p := stage k; p + Polynomial.X ^ k * p ^ 2

noncomputable def a (n : ℕ) : ℕ := (stage n).coeff n

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds Real.goldenRatio) := by
  sorry

end OMA.S_oeis_a124571
