import Mathlib

/-!
# A000155: Nearest integer to modified Bessel function K_n(1)

Source: https://oeis.org/A000155
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
For every `n ≥ 1`, the nearest integer to the modified Bessel function `K_n(1)` equals
`∫_0^∞ U_{n-1}(x) / exp(x) dx`, where `U_k(x)` is the `k`-th Chebyshev polynomial of
the second kind.

Conventions:
- `K_n(1)` is defined via its standard integral representation
  `K_n(1) = ∫_0^∞ exp(-cosh t) * cosh(n * t) dt`.
- `round` is Mathlib's nearest integer function (`ℝ → ℤ`).
-/

namespace OMA.S_oeis_a000155

/-- Modified Bessel function of the second kind evaluated at `1`:
`K_n(1) = ∫_0^∞ exp(-cosh t) * cosh(n * t) dt`. -/
noncomputable def besselK1 (n : ℕ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-Real.cosh t) * Real.cosh ((n : ℝ) * t)

/-- Chebyshev polynomial of the second kind `U_n(x)`. -/
def chebyshevU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * chebyshevU (n + 1) x - chebyshevU n x

/-- For every `n ≥ 1`, the nearest integer to `K_n(1)` equals
`∫_0^∞ U_{n-1}(x) / exp(x) dx`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((round (besselK1 n) : ℤ) : ℝ) =
        ∫ x in Set.Ioi (0 : ℝ), chebyshevU (n - 1) x / Real.exp x := by
  sorry

end OMA.S_oeis_a000155
