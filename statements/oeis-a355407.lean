import Mathlib

/-!
# A355407: Expansion of the e.g.f. log((1 - x) / (1 - 2*x)) / (1 - x)^4

Source: https://oeis.org/A355407

`a(n) = n! * [x^n] log((1 - x) / (1 - 2*x)) / (1 - x)^4`, offset 0. The first terms are
0, 1, 11, 110, 1154, 13144, 164136, 2251920, 33923760, 560180160, 10117886400.

The comment section of the entry consists of one line (unsigned, hence by the author of the entry,
Mélika Tebni, Jul 01 2022):

    Conjecture: For p prime, a(p) == -1 (mod p).

This file states that conjecture: one claim, for every prime `p`, the prime `2` included
(`a(2) = 11`). The entry does not say that it has been proved. The formula lines of the entry
(`a(n) = n!*Sum_{k=1..n} A000292(n-k+1)*(2^k-1)/k` and two others) are given there as facts and are
not part of the target; the definition below does not use them.

Formalized:
* The logarithm is Mathlib's formal logarithm of a power series: `PowerSeries.logOf f` is the series
  `log(1 + X) = X - X^2/2 + X^3/3 - ...` with `f - 1` substituted for `X`. Here
  `f = (1 - x) / (1 - 2*x)` has constant coefficient `1`, so `f - 1` has constant coefficient `0`
  and the substitution is the genuine composition of formal power series.
* Both quotients are products with the power series inverse over the rationals; `1 - 2*x` and
  `(1 - x)^4` have constant coefficient `1`, so these are the genuine inverses.
* `a n` is the rational number `n! * [x^n] egf`, following the convention of the other e.g.f. entries.
  The congruence `a(p) == -1 (mod p)` is stated as: `a p` is (the cast of) an integer `z`, and `p`
  divides `z - (-1)` in the integers. So the claim includes that `a(p)` is an integer.
-/

namespace OMA.S_oeis_a355407

/-- The exponential generating function `log((1 - x) / (1 - 2*x)) / (1 - x)^4`. -/
noncomputable def egf : PowerSeries ℚ :=
  PowerSeries.logOf ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X)⁻¹) *
    ((1 - PowerSeries.X) ^ 4)⁻¹

/-- A355407: `a(n) = n! * [x^n] log((1 - x) / (1 - 2*x)) / (1 - x)^4`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * PowerSeries.coeff n egf

/-- The conjecture of the entry: `a(p) == -1 (mod p)` for every prime `p`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ z : ℤ, a p = (z : ℚ) ∧ (p : ℤ) ∣ z - (-1) := by
  sorry

end OMA.S_oeis_a355407
