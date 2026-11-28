import Mathlib

/-!
# A026876: T(2n+1, n+1), T given by A026758 (algebraic equation for the generating function)

Source: https://oeis.org/A026876 (triangle: https://oeis.org/A026758)
Credit: @SSmurf

The triangle A026758 is defined in its OEIS name by `T(n,0) = T(n,n) = 1` for `n ≥ 0` and, for
`n ≥ 2` and `1 ≤ k ≤ n-1`,
`T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k)` if `n` is odd and `1 ≤ k ≤ (n-1)/2`,
and `T(n,k) = T(n-1,k-1) + T(n-1,k)` otherwise.

A026876 (offset 0) is `a(n) = T(2n+1, n+1)`: 1, 3, 11, 43, 174, 721, 3042, 13022, ….

The conjecture formalized here (Michael D. Weiner, Aug 04 2018, FORMULA section of A026876):

  G.f. f satisfies: x^6*f^4 + x^3*(4*x-1)*(x-1)*f^3 + x*(x-1)*(6*x^2-6*x+1)*f^2
  + (4*x-1)*(x-1)^2*f + (x-1)^2 = 0 (conjectured).

Formalization notes.
* `triangle` is the definition of A026758 used in the merged statement of A026765, extended by
  zero to all integer column indices: for row `n + 2` the extra term `T(n, k-1)` is present
  exactly when `n + 2` is odd and `2 k ≤ n + 1`, i.e. `k ≤ ((n + 2) - 1)/2`. The boundary values
  `T(n,0) = T(n,n) = 1` come out of the same recursion, and for `k ≤ 0` the extra term vanishes.
* `f` is the ordinary generating function `∑ a(n) x^n` (offset 0), as a formal power series
  over `ℚ`. With the definition below `a` starts 1, 3, 11, 43, 174, 721, as in the entry, and the
  equation was checked numerically through the coefficient of `x^22`.
* The other conjecture in the entry (invert transform and A165538) is not part of this statement.
-/

namespace OMA.S_oeis_a026876

/-- Kimberling's triangle A026758, extended by zero to all integer column indices. -/
def triangle : ℕ → ℤ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 ∨ k = 1 then 1 else 0
  | n + 2, k => triangle (n + 1) (k - 1) + triangle (n + 1) k +
      (if n % 2 = 1 ∧ 2 * k ≤ (n + 1 : ℕ) then triangle n (k - 1) else 0)

/-- A026876: `a(n) = T(2n+1, n+1)`. -/
def a (n : ℕ) : ℕ := triangle (2 * n + 1) ((n : ℤ) + 1)

open PowerSeries

/-- The ordinary generating function of A026876. -/
def f : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))

/-- Weiner's conjectured algebraic equation for the generating function of A026876. -/
theorem main :
    X ^ 6 * f ^ 4 + X ^ 3 * (4 * X - 1) * (X - 1) * f ^ 3 +
      X * (X - 1) * (6 * X ^ 2 - 6 * X + 1) * f ^ 2 +
      (4 * X - 1) * (X - 1) ^ 2 * f + (X - 1) ^ 2 = 0 := by
  sorry

end OMA.S_oeis_a026876
