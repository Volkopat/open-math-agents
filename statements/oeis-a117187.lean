import Mathlib

/-!
# A117187: Mathar's recurrence

Source: https://oeis.org/A117187
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A117187 (offset 0): expansion of (1+x)c(x^2)/((1-x^2*c(x^2))sqrt(1-4x^2)), c(x) the g.f. of A000108;
data 1, 1, 4, 4, 15, 15, 56, 56, 210, 210, 792, 792, ...

Conjecture (R. J. Mathar, Dec 10 2011): D-finite with recurrence
(n+4)*(31n-12)*a(n) +(37n^2+24n-156)*a(n-1) -4*(31n^2+81n+24)*a(n-2) -4*(37n+24)*(n-1)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1, that is S = sqrt(1-4x^2)
(the constant term selects the branch of the square root); c is the series c(x^2), with c(x) the Catalan
g.f., determined by 2*x^2*c = 1 - S; and the g.f. G is determined by G*(1 - x^2*c)*S = (1+x)*c;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (567)*(4) + (249)*(4) + (-2184)*(1) + (-1080)*(1) = 0.
-/

namespace OMA.S_oeis_a117187

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A117187, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X ^ 2 * c = 1 - S →
    G * ((1 - X ^ 2 * c) * S) = (1 + X) * c →
    ∀ n : ℕ, 3 ≤ n →
      (-48 + 112 * (n : ℚ) + 31 * (n : ℚ) ^ 2) * coeff n G + (-156 + 24 * (n : ℚ) + 37 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-96 - 324 * (n : ℚ) - 124 * (n : ℚ) ^ 2) * coeff (n - 2) G + (96 + 52 * (n : ℚ) - 148 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a117187
