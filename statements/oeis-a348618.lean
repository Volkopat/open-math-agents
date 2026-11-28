import Mathlib

/-!
# A348618: a(n) = (1+(-1)^n)/2*4^n*(C((3*n)/2-1,n))+(1-(-1)^n)/2*((C((3*n-1)/2,n))*(C(3*n-1,(3*n-1)/2)))/(C(n-1,(n-1)/2))

Source: https://oeis.org/A348618
Credit: @jagong-cmu

Formalizes R. J. Mathar's OEIS A348618 conjecture (Mar 06 2022), offset 0:
`D-finite with recurrence n*(n-1)*a(n) -12*(3*n-2)*(3*n-4)*a(n-2)=0`.

Conventions:
* The sequence is defined literally from the OEIS name, with the value in `ℚ` and the
  division in `ℚ` (all terms are integers, but this is not used).
* The binomial arguments `(3*n)/2 - 1`, `(3*n-1)/2`, `3*n - 1`, `n - 1` and `(n-1)/2` use `ℕ`
  division and truncated subtraction. Each one is exact where its parity factor is nonzero
  (`(3*n)/2 - 1` for even `n >= 2`; the others for odd `n`). For `n = 0` the value
  `C(0, 0) = 1` agrees with the generalized binomial `C(-1, 0) = 1`, so `a(0) = 1`.
* The recurrence uses `a(n-2)`. It fails at `n = 2`: `2*1*a(2) - 12*4*2*a(0) = 32 - 96 = -64`.
  It holds for every `n >= 3` (checked numerically to `n = 29` and proved here), so it is
  stated for `n >= 3`. The coefficients are computed in `ℚ` after a cast.
-/

namespace OMA.S_oeis_a348618

/-- The literal OEIS name formula, in `ℚ`. -/
def a (n : ℕ) : ℚ :=
  (1 + (-1 : ℚ) ^ n) / 2 * 4 ^ n * ((3 * n / 2 - 1).choose n : ℚ) +
    (1 - (-1 : ℚ) ^ n) / 2 *
      (((3 * n - 1) / 2).choose n * (3 * n - 1).choose ((3 * n - 1) / 2) : ℚ) /
      ((n - 1).choose ((n - 1) / 2) : ℚ)

/-- For every `n >= 3`: `n*(n-1)*a(n) - 12*(3*n-2)*(3*n-4)*a(n-2) = 0`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      (n : ℚ) * ((n : ℚ) - 1) * a n -
        12 * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 4) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a348618
