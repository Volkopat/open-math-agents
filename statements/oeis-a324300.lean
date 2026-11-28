import Mathlib

/-!
# A324300: G.f.: Sum_{n>=0} x^n * (x^(n+1) + i)^n / (1 + i*x^(n+1))^(n+1).

Source: https://oeis.org/A324300
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

The entry (Paul D. Hanna, Feb 21 2019) states in its comments:
  Odd terms occur only at n = k*(k+2) for k >= 0 (conjecture);
and in its formula section, among the formulas involving terms:
  a(n*(n+2)) = 1 (mod 2) for n >= 0.
This file states both together: a(m) is odd if and only if m = k*(k+2) for some k ≥ 0.
The direction "odd → m = k*(k+2)" is the conjecture; the converse is the formula line.

Modelling choices:
* Here i is the imaginary unit, and the g.f. is taken in `GaussianInt⟦x⟧` (power series with
  coefficients in ℤ[i]). Each 1 + i*x^(n+1) has constant coefficient 1, so it is a unit, and
  1/(1 + i*x^(n+1))^(n+1) is written `Ring.inverse ((1 + C gi * X ^ (n + 1)) ^ (n + 1))`,
  the true inverse of that unit (`gi` is i).
* The n-th summand x^n * (x^(n+1) + i)^n / (1 + i*x^(n+1))^(n+1) is a multiple of x^n, so only
  the summands with n ≤ m contribute to the coefficient of x^m. The infinite sum therefore has
  the coefficient [x^m] Sum_{n=0..m} (n-th summand), which is used below.
* The entry remarks that this power series has only real coefficients; a(m) is defined as the
  real part of the coefficient of x^m. (The vanishing of the imaginary parts is not part of the
  statement; a numerical check of this definition reproduces the entry's DATA line, with all
  imaginary parts zero.)
* Offset 0, m ranges over all natural numbers, k over all natural numbers (k ≥ 0).
-/

namespace OMA.S_oeis_a324300

open PowerSeries

/-- The imaginary unit `i` of the Gaussian integers. -/
def gi : GaussianInt := ⟨0, 1⟩

/-- The `n`-th summand `x^n * (x^(n+1) + i)^n / (1 + i*x^(n+1))^(n+1)` of the g.f.,
in `GaussianInt⟦x⟧`. -/
noncomputable def summand (n : ℕ) : PowerSeries GaussianInt :=
  X ^ n * (X ^ (n + 1) + C gi) ^ n * Ring.inverse ((1 + C gi * X ^ (n + 1)) ^ (n + 1))

/-- A324300: `a m` is the (real part of the) coefficient of `x^m` in the g.f. (only the
summands `n ≤ m` contribute to it). -/
noncomputable def a (m : ℕ) : ℤ :=
  (coeff m (∑ n ∈ Finset.range (m + 1), summand n)).re

/-- Paul D. Hanna's conjecture (odd terms occur only at `m = k*(k+2)`), together with the
entry's formula `a(k*(k+2)) ≡ 1 (mod 2)`. -/
theorem main : ∀ m : ℕ, Odd (a m) ↔ ∃ k : ℕ, m = k * (k + 2) := by
  sorry

end OMA.S_oeis_a324300
