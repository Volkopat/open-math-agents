import Mathlib

/-!
# Two recurrences for A013302

The OEIS gives the exponential generating function `(2-x²)/(2*sqrt(1-x²))`
for the even powers in `cosh(log(1+x) - arctanh(x))`. Write `X = x²`.
The sequence starts at `n=0`, so its `n`th term is the coefficient of `X^n`
multiplied by `(2n)!`. R. J. Mathar proposed both recurrences on October 5, 2014.

Source: https://oeis.org/A013302 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a013302
open PowerSeries

/-- The binomial power series for `(1-X)^(-1/2)` with constant term one. -/
noncomputable def invSqrt : PowerSeries ℚ :=
  rescale (-1 : ℚ) (binomialSeries ℚ (-1/2 : ℚ))

/-- Even exponential generating function coefficients for A013302. -/
noncomputable def a (n : ℕ) : ℚ :=
  ((2*n).factorial : ℚ) * coeff n ((1 - C (1/2 : ℚ) * X) * invSqrt)

/-- For the second recurrence at `n=1`, the convention `(-1)!!=1` is
encoded by `Nat.doubleFactorial 0 = 1`. All other arithmetic is signed. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → let x : ℚ := n
      a n + 2 * (-2*x^2 + 2*x - 3) * a (n-1)
        + 3 * (2*x - 3) * (2*x - 5) * a (n-2) = 0) ∧
    (∀ n : ℕ, 1 ≤ n → let x : ℚ := n
      a n = (4*x - 5) * (Nat.doubleFactorial (2*n-3) : ℚ)^2
        + (2*x - 3)^2 * a (n-1)) := by
  sorry

end OMA.S_oeis_a013302
