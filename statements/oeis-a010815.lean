import Mathlib

/-!
# OEIS A010815: a closed form for `∑ a(k) e^{-kπ}`

Source: https://oeis.org/A010815
`a k` is the coefficient of `x^k` in `∏_{m ≥ 1} (1 - x^m)`. Conjecture (Bala, Plouffe):
`∑_{k ≥ 0} a(k) / exp(k π) = (1/2) exp(π/24) π^(1/4) 2^(5/8) / Γ(3/4)` (A259148).
The OEIS entry notes that this follows from Euler's pentagonal number theorem and the value
of the Dedekind eta function at `i/2`.

Conventions. By Euler's pentagonal number theorem `a k = (-1)^m` when `k = m(3m-1)/2` for an
integer `m`, and `a k = 0` otherwise; this is used as the definition of `a` (the integer `m`
is unique when it exists, as `m ↦ m(3m-1)/2` is injective on `ℤ`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a010815

open Real

/-- Coefficients of `∏ (1 - x^m)`, via the pentagonal number theorem. -/
noncomputable def a (k : ℕ) : ℝ :=
  open Classical in
  if h : ∃ m : ℤ, 2 * (k : ℤ) = m * (3 * m - 1) then (-1 : ℝ) ^ (Classical.choose h).natAbs
  else 0

theorem main :
    ∑' k : ℕ, a k / exp (k * π) =
      (1 / 2) * exp (π / 24) * π ^ (1 / 4 : ℝ) * 2 ^ (5 / 8 : ℝ) / Gamma (3 / 4) := by
  sorry

end OMA.S_oeis_a010815
