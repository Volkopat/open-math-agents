import Mathlib

/-!
# A213421: Real part of Q^n, Q being the quaternion 2+i+j+k.

Source: https://oeis.org/A213421
Credit: @rickmanelius

Conjecture (R. J. Mathar, Jun 25 2012): G.f. (1-2x)/(1-4x+7x^2).
a(n) = A168175(n)-2*A168175(n-1).
(Peter Bala, Mar 29 2015: The above o.g.f. is correct; this is the Lucas sequence V_n(4,7).)

Formalization notes:
* Offset 0. Q = 2+i+j+k is the element ⟨2, 1, 1, 1⟩ of Mathlib's `Quaternion ℤ`, the
  quaternions re + imI*i + imJ*j + imK*k with i^2 = j^2 = k^2 = ijk = -1, taken with integer
  coefficients (every power of Q has integer coefficients). `a n` is the real part
  `(Q ^ n).re`, with Q^0 = 1. The data begin 1, 2, 1, -10, -47, -118, -143, 254, 2017, ...,
  matching the entry.
* G.f. (1-2x)/(1-4x+7x^2) is stated in `PowerSeries ℤ` with the denominator multiplied out:
  (1 - 4x + 7x^2) * (sum of a(n) x^n) = 1 - 2x. The denominator has constant term 1, so it is
  a unit, and the two forms say the same thing.
* A168175 (offset 0) is the expansion of 1/(1 - 4x + 7x^2): its n-th term is the coefficient
  of x^n in the inverse power series, written `PowerSeries.invOfUnit (1 - 4x + 7x^2) 1` over ℤ
  (the inverse of a power series whose constant term is the unit 1, see
  `PowerSeries.mul_invOfUnit`). Its data begin 1, 4, 9, 8, -31, -180, -503, ..., matching
  A168175.
* A168175 starts at index 0, so A168175(n-1) is a term only for n ≥ 1. The second claim is
  stated for every n ≥ 1, where the natural-number subtraction n - 1 is exact.
-/

namespace OMA.S_oeis_a213421

/-- Q = 2 + i + j + k, a quaternion with integer coefficients. -/
def Q : Quaternion ℤ := ⟨2, 1, 1, 1⟩

/-- A213421: a(n) = the real part of Q^n. -/
def a (n : ℕ) : ℤ := (Q ^ n).re

/-- A168175: the coefficient of x^n in the expansion of 1/(1 - 4x + 7x^2). -/
noncomputable def A168175 (n : ℕ) : ℤ :=
  PowerSeries.coeff n
    (PowerSeries.invOfUnit (1 - 4 * PowerSeries.X + 7 * PowerSeries.X ^ 2 : PowerSeries ℤ) 1)

/-- Mathar's conjectures: the g.f. of a(n) is (1-2x)/(1-4x+7x^2), and
a(n) = A168175(n) - 2*A168175(n-1) for every n ≥ 1. -/
theorem main :
    (1 - 4 * PowerSeries.X + 7 * PowerSeries.X ^ 2 : PowerSeries ℤ) * PowerSeries.mk a =
        1 - 2 * PowerSeries.X ∧
      ∀ n : ℕ, 1 ≤ n → a n = A168175 n - 2 * A168175 (n - 1) := by
  sorry

end OMA.S_oeis_a213421
