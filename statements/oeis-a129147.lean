import Mathlib

/-!
# A129147: Mathar's recurrence

Source: https://oeis.org/A129147
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A129147 (offset 0): expansion of c(x(1+2x)), c(x) the g.f. of A000108;
data 1, 1, 4, 13, 52, 214, 928, 4141, 18940, 88258, 417616, 2001058, ...

Conjecture (R. J. Mathar, Dec 14 2011):
(n+1)*a(n) +2*(2-n)*a(n-1) +4*(5-4n)*a(n-2) +16*(2-n)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x-8*x^2 and constant term 1, that is
S = sqrt(1 - 4*y) for y = x*(1+2*x) (the constant term selects the branch of the square root), and the g.f.
G = c(y), with c the Catalan g.f., is determined by 2*x*(1+2*x)*G = 1 - S;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (4)*(13) + (-2)*(4) + (-28)*(1) + (-16)*(1) = 0.
-/

namespace OMA.S_oeis_a129147

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A129147, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X - 8 * X ^ 2 →
    coeff 0 S = 1 →
    2 * (X + 2 * X ^ 2) * G = 1 - S →
    ∀ n : ℕ, 3 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (4 - 2 * (n : ℚ)) * coeff (n - 1) G +
        (20 - 16 * (n : ℚ)) * coeff (n - 2) G + (32 - 16 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a129147
