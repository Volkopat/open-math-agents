import Mathlib

/-!
# Mathar's fifth-order Vatalan recurrence (OEIS A025758)

Source: https://oeis.org/A025758
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A025/A025758.seq
Credit: @Heart-galaxy

A025758 is indexed from zero and has ordinary generating function
5/(4+(1-25*X)^(1/5)). We define its exact rational coefficients using
Mathlib's formal binomial series of exponent 1/5 and constant term 1,
rescaled by -25. Thus T is the source's branch of (1-25*X)^(1/5), G is the
generating function, and a(n) is its nth coefficient. Its denominator has
constant coefficient 5, so its formal inverse is well-defined.

Mathar conjectured the displayed fifth-order recurrence on July 28, 2014.
We retain every n>=5, precisely the range in which all five preceding
indices are in the source's offset-zero sequence. Coefficients and values
are represented in the rationals, preserving all signs and the generating
function exactly. This is the source's only explicitly labeled conjecture.
The OEIS entry still labels it a conjecture; prior literature resolution
and mathematical novelty are not claimed.
-/

namespace OMA.S_oeis_a025758

noncomputable def H (r : ℚ) : PowerSeries ℚ :=
  PowerSeries.rescale (-25 : ℚ) (PowerSeries.binomialSeries ℚ r)
noncomputable def T : PowerSeries ℚ := H (1/5)
noncomputable def G : PowerSeries ℚ := 5 * (4+T)⁻¹
noncomputable def a (n : ℕ) : ℚ := PowerSeries.coeff n G

theorem main : ∀ n : ℕ, 5 ≤ n →
    41*(n : ℚ)*((n : ℚ)-1)*((n : ℚ)-2)*((n : ℚ)-3)*a n -
      3*(1367*(n : ℚ)-4100)*((n : ℚ)-1)*((n : ℚ)-2)*((n : ℚ)-3)*a (n-1) +
      50*((n : ℚ)-2)*((n : ℚ)-3)*(3077*(n : ℚ)^2-21533*(n : ℚ)+38136)*a (n-2) -
      250*((n : ℚ)-3)*(10265*(n : ℚ)^3-123135*(n : ℚ)^2+494446*(n : ℚ)-664572)*a (n-3) +
      1875*(8575*(n : ℚ)^4-154250*(n : ℚ)^3+1039765*(n : ℚ)^2-3112730*(n : ℚ)+3491808)*a (n-4) -
      625*(5*(n : ℚ)-22)*(5*(n : ℚ)-21)*(5*(n : ℚ)-24)*(5*(n : ℚ)-23)*a (n-5) = 0 := by
  sorry

end OMA.S_oeis_a025758
