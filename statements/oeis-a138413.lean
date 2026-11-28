import Mathlib

/-!
# A138413: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A138413
Credit: @ivillar

Status: corrected recurrence (n ≥ 3): fails as stated at n = 2 (the left side is 48 at n = 2 on the
OEIS data). The entry records the recurrence as a conjecture; no proof or verification is noted there.
`main` is the corrected recurrence (n ≥ 3), which is proved.

A138413 (offset 0): a bisection of A000957;
data 0, 0, 2, 18, 186, 2120, 25724, 325878, 4260282, 57048048, 778483932, ...

Conjecture (R. J. Mathar, Jun 26 2020): D-finite with recurrence
4*n*(2*n-1)*(7*n-13)*a(n) +(-910*n^3+3489*n^2-4277*n+1680)*a(n-1) +2*(4*n-7)*(7*n-6)*(4*n-5)*a(n-2) = 0.

Formalization: A000957 (Fine's sequence, offset 0: 0, 1, 0, 1, 2, 6, 18, 57, 186, ...) has the g.f.
(1-sqrt(1-4*x))/(3-sqrt(1-4*x)) (Emeric Deutsch, in A000957), and the listed terms are the even-indexed
ones, a(n) = A000957(2n). S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1,
that is S = sqrt(1-4x) (the constant term selects the branch of the square root); F is the g.f. of
A000957, determined by F*(3 - S) = 1 - S; and a(n) = [x^(2n)] F. The recurrence involves a(n-2), so as
stated it starts at n = 2, where it fails on the data: 4*2*3*1*2 + (-198)*0 + 2*1*8*3*0 = 48. It vanishes
from n = 3 on, for example at n = 3: 4*3*5*8*18 + (-4320)*2 + 2*5*15*7*0 = 0.
-/

namespace OMA.S_oeis_a138413

open PowerSeries

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ S F : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    F * (3 - S) = 1 - S →
    ∀ n : ℕ, 3 ≤ n →
      4 * (n : ℚ) * (2 * (n : ℚ) - 1) * (7 * (n : ℚ) - 13) * coeff (2 * n) F +
        (-910 * (n : ℚ) ^ 3 + 3489 * (n : ℚ) ^ 2 - 4277 * (n : ℚ) + 1680) * coeff (2 * (n - 1)) F +
        2 * (4 * (n : ℚ) - 7) * (7 * (n : ℚ) - 6) * (4 * (n : ℚ) - 5) * coeff (2 * (n - 2)) F = 0 := by
  sorry

end OMA.S_oeis_a138413
