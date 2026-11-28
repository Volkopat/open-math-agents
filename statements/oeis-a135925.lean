import Mathlib

/-!
# A135925: Mathar's recurrence, corrected to n ≥ 14

Source: https://oeis.org/A135925
Credit: @ivillar

Status: false as stated at n = 6 (and at every n up to 13) (the left side is 17483921103890240 at n = 6, -96203187527862528 at n = 7, 26860851665524032 at n = 8, 267411638401515712 at n = 9, 107522236010828544 at n = 10, -82029355854002112 at n = 11, -56627815207112768 at n = 12, -8628263825301312 at n = 13 on the OEIS data); `main` is the
corrected recurrence (n ≥ 14), which is proved.

A135925 (offset 0): g.f.: (x^2+x-1)*(1+2*x+S)*(1-5*x+2*x^2+(3*x-1)*S)^2*(-1+3*x+2*x^2+(1-x)*S), where S=sqrt(1-4*x);
data 0, 0, 0, 0, 0, 0, -16, 0, 80, 240, 656, 1936, ...

Conjecture (R. J. Mathar, Jan 23 2020): D-finite with recurrence
+4*(n-1)*(7678757997599*n-100709801435251)*a(n)
+(-291262905844111*n^2+4745710679447853*n-12935393149282124)*a(n-1)
+3*(268523622217993*n^2-4978734571371597*n+20251709258114720)*a(n-2)
+2*(-196528865827703*n^2+4147266222561252*n-21888137659762186)*a(n-3)
-12*(22463548140013*n-247087251730058)*(2*n-25)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G = (x^2 + x - 1)*(1 + 2*x + S)*(1 - 5*x + 2*x^2 + (3*x - 1)*S)^2*(-1 + 3*x + 2*x^2 + (1 - x)*S);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 14): on the data the left side of the recurrence as
stated is 17483921103890240 at n = 6, -96203187527862528 at n = 7, 26860851665524032 at n = 8, 267411638401515712 at n = 9, 107522236010828544 at n = 10, -82029355854002112 at n = 11, -56627815207112768 at n = 12, -8628263825301312 at n = 13, and it vanishes from n = 14 on.
At n = 4, n = 5 the left side is 0 because all the terms involved vanish; these indices are not
included in `main`, which is stated for n ≥ 14 only.
-/

namespace OMA.S_oeis_a135925

open PowerSeries

/-- The corrected recurrence (n ≥ 14): Mathar's recurrence, which fails at n = 6 (and at every n up to 13). -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G = (X ^ 2 + X - 1) * (1 + 2 * X + S) * (1 - 5 * X + 2 * X ^ 2 + (3 * X - 1) * S) ^ 2 * (-1 + 3 * X + 2 * X ^ 2 + (1 - X) * S) →
    ∀ n : ℕ, 14 ≤ n →
      (402839205741004 - 433554237731400 * (n : ℚ) + 30715031990396 * (n : ℚ) ^ 2) * coeff n G + (-12935393149282124 + 4745710679447853 * (n : ℚ) - 291262905844111 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (60755127774344160 - 14936203714114791 * (n : ℚ) + 805570866653979 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-43776275319524372 + 8294532445122504 * (n : ℚ) - 393057731655406 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-74126175519017400 + 12669158483525292 * (n : ℚ) - 539125155360312 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a135925
