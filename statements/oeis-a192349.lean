import Mathlib

/-!
# A192349: Coefficient of x in the reduction (by x^2->x+1) of polynomial p(n,x) identified in Comments.

Source: https://oeis.org/A192349
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (Jan 17 2013) in OEIS A192349:
a(n) = 2*a(n-1) + 8*a(n-2) - 4*a(n-3) - 4*a(n-4).

Conventions:
* The polynomials are defined in the COMMENTS section of the entry: let d = sqrt(x+3); then
  p(n,x) = (1/2)((x+d)^n + (x-d)^n). Since d^2 = x+3, one has (x+d)^n = P_n(x) + Q_n(x)*d and
  (x-d)^n = P_n(x) - Q_n(x)*d for polynomials P_n, Q_n with integer coefficients, determined by
  P_0 = 1, Q_0 = 0 and (P + Q*d)*(x + d) = (x*P + (x+3)*Q) + (P + x*Q)*d, so that
  p(n,x) = P_n(x). The pair (P_n, Q_n) is `pq n` below and p(n,x) is `p n`, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 1 and its first term comes from p(0,x) = 1 (data 0, 1, 2, 14, 40, 180, ...;
  EXAMPLE section of the entry: p(0,x) = 1 -> 1, p(1,x) = x -> x,
  p(2,x) = 3+x+x^2 -> 4+2x, p(3,x) = 9x+3x^2+x^3 -> 4+14x), so a(n) is the coefficient of x of the
  reduction of p(n-1,x). Only `n ≥ 1` is used.
* The recurrence involves a(n-4), so it is asserted for every `n > 4`, where all the indices
  `n - 1, ..., n - 4` are at least 1. The terms are integers.
* Barker's generating function x^2*(2*x^2+1) / (4*x^4+4*x^3-8*x^2-2*x+1) is not stated
  separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a192349

open Polynomial

/-- `(x + d)^n = P_n + Q_n * d` with `d^2 = x + 3`: the pair `(P_n, Q_n)`. -/
noncomputable def pq : ℕ → ℤ[X] × ℤ[X]
  | 0 => (1, 0)
  | n + 1 => (X * (pq n).1 + (X + 3) * (pq n).2, (pq n).1 + X * (pq n).2)

/-- p(n,x) = (1/2)((x+d)^n + (x-d)^n) with d = sqrt(x+3). -/
noncomputable def p (n : ℕ) : ℤ[X] := (pq n).1

/-- A192349 (offset 1): the coefficient of x of the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n > 4`, a(n) = 2*a(n-1) + 8*a(n-2) - 4*a(n-3) - 4*a(n-4). -/
theorem main : ∀ n : ℕ, 4 < n →
    a n = 2 * a (n - 1) + 8 * a (n - 2) - 4 * a (n - 3) - 4 * a (n - 4) := by
  sorry

end OMA.S_oeis_a192349
