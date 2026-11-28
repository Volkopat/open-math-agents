import Mathlib

/-!
# A355372: Expansion of the e.g.f. log((1 - x) / (1 - 2*x)) / (1 - x)^3

Source: https://oeis.org/A355372

`a(n) = n! * [x^n] log((1 - x) / (1 - 2*x)) / (1 - x)^3`, offset 0. The first terms are
0, 1, 9, 77, 714, 7374, 85272, 1102968, 15908400, 254866320, 4516084800.

The comment section of the entry reads (first line unsigned, hence by the author of the entry,
Mélika Tebni, Jun 30 2022):

    Conjecture: For p prime, a(p) == -1 (mod p).
    The conjecture is true (see Fried link). - Sela Fried, Dec 17 2025

So the entry makes one conjectural claim, stated here, and the entry itself records that it has
since been proved (Sela Fried, Proof of a conjecture stated in A355372, 2025; also
arXiv:2607.24832, Lemma 51). It is therefore a known result, not an open problem.

Formalized:
* The series is taken over the rationals. `PowerSeries.logOf f` is the logarithm of Mathlib: the
  series `log(1 + X) = X - X^2/2 + X^3/3 - ...` substituted at `f - 1`. Here
  `f = (1 - X) * (1 - 2*X)⁻¹` has constant coefficient `1`, so the substitution is the genuine
  formal logarithm of `(1 - x)/(1 - 2*x)`; it equals `Sum_{m>=1} (2^m - 1) * x^m / m`.
* The two quotients are products with power series inverses: `(1 - 2*X)⁻¹` and `((1 - X)^3)⁻¹`.
  Both series have constant coefficient `1`, so these are the genuine inverses.
* `a n` is the rational number `n! * [x^n] egf`, following the convention of the other e.g.f.
  entries. The congruence `a(p) == -1 (mod p)` is stated as: `a p` is (the cast of) an integer `z`,
  and `p` divides the difference `z - (-1)` in the integers. So the claim includes that `a(p)` is
  an integer.
* The range is every prime `p`, the prime `2` included (`a(2) = 9`).
-/

namespace OMA.S_oeis_a355372

/-- The exponential generating function `log((1 - x)/(1 - 2*x)) / (1 - x)^3`. -/
noncomputable def egf : PowerSeries ℚ :=
  PowerSeries.logOf ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X)⁻¹) *
    ((1 - PowerSeries.X) ^ 3)⁻¹

/-- A355372: `a(n) = n! * [x^n] log((1 - x)/(1 - 2*x)) / (1 - x)^3`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * PowerSeries.coeff n egf

/-- The conjecture of the entry: `a(p) == -1 (mod p)` for every prime `p`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ z : ℤ, a p = (z : ℚ) ∧ (p : ℤ) ∣ z - (-1) := by
  sorry

end OMA.S_oeis_a355372
