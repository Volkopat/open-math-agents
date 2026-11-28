import Mathlib

/-!
# A101596: Mathar's recurrence

Source: https://oeis.org/A101596
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A101596 (offset 0): expansion of g.f. c(2*x)^4, where c(x) is the g.f. of A000108;
data 1, 8, 56, 384, 2640, 18304, 128128, 905216, 6449664, 46305280, 334721024, 2434334720, ...

Conjecture (R. J. Mathar, Dec 13 2011):
(n+4)*a(n) - 4*(3n+7)*a(n-1) + 16*(2n+1)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-8*x and constant term 1, that is S = sqrt(1-8x)
(the constant term selects the branch of the square root); c is the series c(2x), with c(x) the Catalan
g.f., determined by 4*x*c = 1 - S; and the g.f. G is determined by G = c^4;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (6)*(56) + (-52)*(8) + (80)*(1) = 0.
-/

namespace OMA.S_oeis_a101596

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A101596, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 8 * X →
    coeff 0 S = 1 →
    4 * X * c = 1 - S →
    G = c ^ 4 →
    ∀ n : ℕ, 2 ≤ n →
      (4 + (n : ℚ)) * coeff n G + (-28 - 12 * (n : ℚ)) * coeff (n - 1) G +
        (16 + 32 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a101596
