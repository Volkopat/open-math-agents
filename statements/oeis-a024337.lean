import Mathlib

/-!
# A024337: Expansion of sinh(log(1+x))*log(1+x)/2.

Source: https://oeis.org/A024337
Credit: @neutroxium

The conjecture listed in the entry (Benedict W. J. Irwin, Oct 14 2016):
* a(n) = Sum_{k=0..n/2} Stirling1(n,2*k)*k

Conventions: offset 0. The expansion is exponential, a(n) = n! * [x^n] sinh(log(1+x))*log(1+x)/2,
as shown by the listed terms 0, 0, 1, -3, 13, -70, 447, ... and by the Mathematica program in the
entry (CoefficientList of the series, multiplied by Range[0,nn]!). Stirling1 is the signed Stirling
number of the first kind, s(n,k) = (-1)^(n-k) c(n,k), and the sum runs over 0 <= k <= floor(n/2).
`PowerSeries.log ℚ` is Mathlib's series for log(1+X).
-/

namespace OMA.S_oeis_a024337

open PowerSeries

/-- Formal power series for `sinh(X) = (exp(X) - exp(-X)) / 2`. -/
noncomputable def sinhSeries : PowerSeries ℚ :=
  (PowerSeries.exp ℚ - PowerSeries.subst (-X) (PowerSeries.exp ℚ)) * C (1 / 2 : ℚ)

/-- Exponential generating function `sinh(log(1+X)) * log(1+X) / 2`. -/
noncomputable def egf : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.log ℚ) sinhSeries * PowerSeries.log ℚ * C (1 / 2 : ℚ)

/-- `a(n) = n! * [x^n] egf`, matching OEIS A024337 (offset 0: 0, 0, 1, -3, 13, -70, 447, ...). -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * PowerSeries.coeff n egf

/-- Signed Stirling number of the first kind `s(n, k) = (-1)^(n - k) * c(n, k)`. -/
def signedStirlingFirst (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

/-- Benedict W. J. Irwin's conjecture for OEIS A024337. -/
theorem main : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n / 2 + 1), (signedStirlingFirst n (2 * k) * (k : ℤ) : ℚ) := by
  sorry

end OMA.S_oeis_a024337
