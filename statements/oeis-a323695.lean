import Mathlib

/-!
# A323695: G.f.: Sum_{n>=0} x^n * (1 - x^(n+1))^n / (1 + x^(n+1))^(n+1).

Source: https://oeis.org/A323695
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

The entry (Paul D. Hanna, Feb 23 2019) states in its comments:
  Odd terms occur only at n = k*(k+2) for k >= 0 (conjecture);
and in its formula section, among the formulas involving terms:
  a(n*(n+2)) = 1 (mod 2) for n >= 0.
This file states both together: a(m) is odd if and only if m = k*(k+2) for some k ≥ 0.
The direction "odd → m = k*(k+2)" is the conjecture; the converse is the formula line.

Modelling choices:
* The g.f. is taken in ℤ⟦x⟧. Each 1 + x^(n+1) has constant coefficient 1, so it is a unit of
  ℤ⟦x⟧, and 1/(1 + x^(n+1))^(n+1) is written `Ring.inverse ((1 + X ^ (n + 1)) ^ (n + 1))`,
  the true inverse of that unit.
* The n-th summand x^n * (1 - x^(n+1))^n / (1 + x^(n+1))^(n+1) is a multiple of x^n, so only the
  summands with n ≤ m contribute to the coefficient of x^m. The infinite sum therefore has the
  coefficient a(m) = [x^m] Sum_{n=0..m} (n-th summand), which is the definition used below.
  (A numerical check of this definition reproduces the entry's DATA line.)
* Offset 0, m ranges over all natural numbers, k over all natural numbers (k ≥ 0).
-/

namespace OMA.S_oeis_a323695

open PowerSeries

/-- The `n`-th summand `x^n * (1 - x^(n+1))^n / (1 + x^(n+1))^(n+1)` of the g.f., in `ℤ⟦x⟧`. -/
noncomputable def summand (n : ℕ) : PowerSeries ℤ :=
  X ^ n * (1 - X ^ (n + 1)) ^ n * Ring.inverse ((1 + X ^ (n + 1)) ^ (n + 1))

/-- A323695: `a m` is the coefficient of `x^m` in the g.f. (only the summands `n ≤ m`
contribute to it). -/
noncomputable def a (m : ℕ) : ℤ :=
  coeff m (∑ n ∈ Finset.range (m + 1), summand n)

/-- Paul D. Hanna's conjecture (odd terms occur only at `m = k*(k+2)`), together with the
entry's formula `a(k*(k+2)) ≡ 1 (mod 2)`. -/
theorem main : ∀ m : ℕ, Odd (a m) ↔ ∃ k : ℕ, m = k * (k + 2) := by
  sorry

end OMA.S_oeis_a323695
