import Mathlib

/-!
# A323689: G.f.: Sum_{n>=0} (x^n + i)^n / (1 + i*x^n)^(n+1), in which the constant term is taken to be 1.

Source: https://oeis.org/A323689
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

The entry (Paul D. Hanna, Feb 14 2019) states in its comments:
  Odd terms occur only at n = k^2 for k >= 0 (conjecture);
and in its formula section, among the formulas involving terms:
  a(n^2) = 1 (mod 2) for n >= 0.
This file states both together, for indices m ≥ 1 (see below): a(m) is odd if and only if
m = k^2 for some k. The direction "odd → m = k^2" is the conjecture; the converse is the
formula line.

Modelling choices:
* Here i is the imaginary unit, and the g.f. is taken in `GaussianInt⟦x⟧` (power series with
  coefficients in ℤ[i]). For n ≥ 1, 1 + i*x^n has constant coefficient 1, so it is a unit, and
  1/(1 + i*x^n)^(n+1) is written `Ring.inverse ((1 + C gi * X ^ n) ^ (n + 1))`, the true inverse
  of that unit (`gi` is i).
* The constant term. The n-th summand (n ≥ 1) has constant term i^n, so the constant terms of
  the summands do not sum, and the n = 0 summand (1 + i)^0/(1 + i)^1 = 1/(1 + i) is a constant.
  This is why the entry says "the constant term is taken to be 1": a(0) = 1 by convention, and
  that is the definition used below. For m ≥ 1 the coefficient of x^m is unaffected by that
  convention: the n = 0 summand is a constant, and for n ≥ 1 the n-th summand is a power series
  in x^n, so it contributes to x^m only when n divides m, in particular only when n ≤ m.
  Hence a(m) = [x^m] Sum_{n=1..m} (n-th summand) for m ≥ 1, which is the definition used below.
  (A numerical check of this definition reproduces the entry's DATA line, all 83 terms.)
* The claim is stated only for m ≥ 1, the range on which the convention for the constant term
  plays no role. (At m = 0 it would read: a(0) = 1 is odd and 0 = 0^2, which holds by the
  convention alone.)
* The entry remarks that this power series has only real coefficients; a(m) is defined as the
  real part of the coefficient of x^m. (The vanishing of the imaginary parts is not part of the
  statement; in the numerical check all imaginary parts are zero.)
-/

namespace OMA.S_oeis_a323689

open PowerSeries

/-- The imaginary unit `i` of the Gaussian integers. -/
def gi : GaussianInt := ⟨0, 1⟩

/-- The `n`-th summand `(x^n + i)^n / (1 + i*x^n)^(n+1)` of the g.f., in `GaussianInt⟦x⟧`
(used for `n ≥ 1`). -/
noncomputable def summand (n : ℕ) : PowerSeries GaussianInt :=
  (X ^ n + C gi) ^ n * Ring.inverse ((1 + C gi * X ^ n) ^ (n + 1))

/-- A323689: `a 0 = 1` (the constant term is taken to be 1), and for `m ≥ 1`, `a m` is the
(real part of the) coefficient of `x^m` in the g.f., to which only the summands
`1 ≤ n ≤ m` contribute. -/
noncomputable def a (m : ℕ) : ℤ :=
  if m = 0 then 1 else (coeff m (∑ n ∈ Finset.Icc 1 m, summand n)).re

/-- Paul D. Hanna's conjecture (odd terms occur only at `m = k^2`), together with the entry's
formula `a(k^2) ≡ 1 (mod 2)`, for all indices `m ≥ 1`. -/
theorem main : ∀ m : ℕ, 1 ≤ m → (Odd (a m) ↔ ∃ k : ℕ, m = k ^ 2) := by
  sorry

end OMA.S_oeis_a323689
