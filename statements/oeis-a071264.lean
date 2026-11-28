import Mathlib

/-!
# A071264: Mathar's recurrence

Source: https://oeis.org/A071264
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A071264 (offset 0): expansion of (1+x*C^4)*C^3, where C = (1-(1-4*x)^(1/2))/(2*x) is g.f. for Catalan numbers, A000108;
data 1, 4, 16, 63, 244, 934, 3549, 13428, 50694, 191216, 721259, 2722073, ...

Conjecture (R. J. Mathar, Dec 10 2015): D-finite with recurrence
(n+6) *(8587*n^2 +62958*n +61667) *a(n) +(8587*n^3 -377960*n^2 -2268967*n
-1091596) *a(n-1) -2 *(2*n-1) *(42935*n^2 -14497*n -123334) *a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G = (1 + x*c^4)*c^3;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (1775448)*(16) + (-7072674)*(4) + (-116472)*(1) = 0.
-/

namespace OMA.S_oeis_a071264

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A071264, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G = (1 + X * c ^ 4) * c ^ 3 →
    ∀ n : ℕ, 2 ≤ n →
      (370002 + 439415 * (n : ℚ) + 114480 * (n : ℚ) ^ 2 + 8587 * (n : ℚ) ^ 3) * coeff n G + (-1091596 - 2268967 * (n : ℚ) - 377960 * (n : ℚ) ^ 2 + 8587 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-246668 + 464342 * (n : ℚ) + 143858 * (n : ℚ) ^ 2 - 171740 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a071264
