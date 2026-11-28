import Mathlib

/-!
# A026672: Mathar's recurrence

Source: https://oeis.org/A026672
Credit: @ivillar

Status: false as stated at n = 5 in the indexing of the entry (offset 2: a(2) = 1, a(3) = 5,
a(4) = 22, a(5) = 94): the left side is (6)*(94) + (-24)*(22) + (-6)*(5) + (0)*(1) = 6. The g.f.
recorded in the entry, x*C(x)^4/(1 - x*C(x)^3) = x + 5x^2 + 22x^3 + ..., lists the same data one
index lower, and the recurrence holds for the coefficients of that g.f., that is for
b(n) = a(n+1). `main` is the corrected recurrence (for b(n), n ≥ 3). For it the entry records the
conjecture only; no proof or verification is noted there.

A026672 (offset 2): a(n) = T(2n,n-1), T given by A026670. Also T(2n,n-1)=T(2n+1,n+2), T given by
A026725; and T(2n,n-1), T given by A026736;
data 1, 5, 22, 94, 398, 1680, 7085, 29877, 126021, 531751, 2244627, 9478605, ...

Conjecture (R. J. Mathar, Aug 08 2015):
-(n+1)*(n-6)*a(n) +2*(4*n^2-23*n+3)*a(n-1) +3*(-5*n^2+33*n-42)*a(n-2) -2*(2*n-3)*(n-5)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and G is determined by (1 - x*c^3)*G = x*c^4, which is the g.f.
recorded in the entry, (x*C(x)^4)/(1-x*C(x)^3) (Philippe Deléham, Feb 02 2014), used as the
definition here; b(n) = [x^n] G, so b(n) = a(n+1) in the indexing of the entry. The recurrence
involves b(n-3), so it is stated for n ≥ 3; it is checked by the data, for example at n = 3:
(12)*(22) + (-60)*(5) + (36)*(1) + (12)*(0) = 0.
-/

namespace OMA.S_oeis_a026672

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A026672, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    (1 - X * c ^ 3) * G = X * c ^ 4 →
    ∀ n : ℕ, 3 ≤ n →
      (6 + 5 * (n : ℚ) - (n : ℚ) ^ 2) * coeff n G + (6 - 46 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-126 + 99 * (n : ℚ) - 15 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-30 + 26 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a026672
