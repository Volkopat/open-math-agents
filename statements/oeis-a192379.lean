import Mathlib

/-!
# A192379: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192379
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (May 11 2014) in OEIS A192379:
a(n) = 2*a(n-1) + 6*a(n-2) - 2*a(n-3) - a(n-4).

Conventions:
* The polynomials are defined in the COMMENTS section of the entry by
  p(n,x) = ((x+d)^n - (x-d)^n)/(2d), where d = sqrt(x+2). Since d^2 = x+2, one has
  (x+d)^n = P_n(x) + Q_n(x)*d and (x-d)^n = P_n(x) - Q_n(x)*d for polynomials P_n, Q_n with integer
  coefficients, determined by P_0 = 1, Q_0 = 0 and
  (P + Q*d)*(x + d) = (x*P + (x+2)*Q) + (P + x*Q)*d, so that p(n,x) = Q_n(x). The pair
  (P_n, Q_n) is `pq n` below and p(n,x) is `p n`, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its constant term is its coefficient of index 0.
* The sequence has offset 1 and a(n) is the constant term of the reduction of p(n,x) as given by
  the formula above: p(1,x) = 1, p(2,x) = 2x, ... (data 1, 0, 5, 8, 45, 128, ...). The EXAMPLE
  section of the entry lists the same polynomials 1 -> 1, 2x -> 2x, 2+x+3x^2 -> 5+4x, 8x+4x^2+4x^3 -> 8+20x
  with their index lowered by one (it calls them p(0,x), p(1,x), ...); the data and the offset
  agree with the formula as formalized here. Only `n ≥ 1` is used.
* The recurrence involves a(n-4), so it is asserted for every `n > 4`, where all the indices
  `n - 1, ..., n - 4` are at least 1. The terms are integers.
* Barker's generating function -x*(x^2+2*x-1) / (x^4+2*x^3-6*x^2-2*x+1) is not stated
  separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a192379

open Polynomial

/-- `(x + d)^n = P_n + Q_n * d` with `d^2 = x + 2`: the pair `(P_n, Q_n)`. -/
noncomputable def pq : ℕ → ℤ[X] × ℤ[X]
  | 0 => (1, 0)
  | n + 1 => (X * (pq n).1 + (X + 2) * (pq n).2, (pq n).1 + X * (pq n).2)

/-- p(n,x) = ((x+d)^n - (x-d)^n)/(2d) with d = sqrt(x+2). -/
noncomputable def p (n : ℕ) : ℤ[X] := (pq n).2

/-- A192379 (offset 1): the constant term of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 0

/-- For every `n > 4`, a(n) = 2*a(n-1) + 6*a(n-2) - 2*a(n-3) - a(n-4). -/
theorem main : ∀ n : ℕ, 4 < n →
    a n = 2 * a (n - 1) + 6 * a (n - 2) - 2 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a192379
