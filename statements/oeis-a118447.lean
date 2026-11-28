import Mathlib

/-!
# A118447: Mathar's recurrence

Source: https://oeis.org/A118447
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A118447 (offset 2): number of rooted n-edge one-vertex maps on the Klein bottle (dually: one-face maps);
data 4, 42, 304, 1870, 10488, 55412, 280768, 1379286, 6616360, 31144300, 144367584, 660746892, ...

Conjecture (R. J. Mathar, Jun 22 2016):
-(n-2)*(n-1)^2*a(n) +2*n*(4*n-5)*(n-2)*a(n-1) -8*n*(n-1)*(2*n-3)*a(n-2) = 0.

Formalization: the entry gives the o.g.f. in closed form, (R-1)^2(R+1)(R+3)/8R^5, where R=sqrt(1-4x), and this
closed form is used as the definition here. S (the R of the entry) is the formal power series over ℚ
with S^2 = 1-4*x and constant term 1 (the constant term selects the branch of the square root), and
the g.f. G is determined by 8*S^5*G = (S - 1)^2*(S + 1)*(S + 3);
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (0)*(4) + (0)*(0) + (-16)*(0) = 0.
-/

namespace OMA.S_oeis_a118447

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A118447, for n ≥ 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    8 * S ^ 5 * G = (S - 1) ^ 2 * (S + 1) * (S + 3) →
    ∀ n : ℕ, 2 ≤ n →
      (2 - 5 * (n : ℚ) + 4 * (n : ℚ) ^ 2 - (n : ℚ) ^ 3) * coeff n G + (20 * (n : ℚ) - 26 * (n : ℚ) ^ 2 + 8 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-24 * (n : ℚ) + 40 * (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a118447
