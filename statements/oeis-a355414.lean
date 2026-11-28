import Mathlib

/-!
# A355414: Expansion of the e.g.f. log((1 - x) / (1 - 2*x)) / (1 - x)^5

Source: https://oeis.org/A355414

`a(n) = n! * [x^n] log((1 - x) / (1 - 2*x)) / (1 - x)^5`, offset 0. The first terms are
0, 1, 13, 149, 1750, 21894, 295500, 4320420, 68487120, 1176564240, 21883528800.

The comment section of the entry reads (unsigned, hence by the author of the entry, Mélika Tebni,
Jul 01 2022):

    Conjecture: For p prime, a(p) == -1 (mod p).

This is the only conjectural claim of the entry, and the entry does not say that it has been proved.
The formula lines of the entry (among them `a(n) = n!*Sum_{k=1..n} A000332(n-k+4)*(2^k-1)/k`) are
given there as facts and are not part of the target.

Formalized:
* The series is taken in the power series over the rationals. `PowerSeries.logOf f` is the Mathlib
  logarithm of a power series: the series `log(1 + X) = X - X^2/2 + X^3/3 - ...` substituted at
  `f - 1`. Here `f = (1 - x) / (1 - 2*x)` has constant coefficient `1`, so `f - 1` has constant
  coefficient `0` and the substitution is the genuine one (no junk value).
* The two quotients are products with the power series inverses of `1 - 2*x` and of `(1 - x)^5`.
  Both have constant coefficient `1`, so these are the genuine inverses.
* `a n` is the rational number `n! * [x^n] egf`, following the convention of the other e.g.f. entries.
  The congruence `a(p) == -1 (mod p)` is stated as: `a p` is (the cast of) an integer `z`, and `p`
  divides `z + 1` in the integers. So the claim includes that `a(p)` is an integer.
* The claim is for all primes `p`, the prime `2` included (`a(2) = 13`).
-/

namespace OMA.S_oeis_a355414

/-- The exponential generating function `log((1 - x) / (1 - 2*x)) / (1 - x)^5`. -/
noncomputable def egf : PowerSeries ℚ :=
  PowerSeries.logOf ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X)⁻¹) *
    ((1 - PowerSeries.X) ^ 5)⁻¹

/-- A355414: `a(n) = n! * [x^n] log((1 - x) / (1 - 2*x)) / (1 - x)^5`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * PowerSeries.coeff n egf

/-- The conjecture of the entry: `a(p) == -1 (mod p)` for every prime `p`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ z : ℤ, a p = (z : ℚ) ∧ (p : ℤ) ∣ z + 1 := by
  sorry

end OMA.S_oeis_a355414
