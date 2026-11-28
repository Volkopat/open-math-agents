import Mathlib

/-!
# A192351: Coefficient of x in the reduction (by x^2->x+1) of polynomial p(n,x) identified in Comments.

Source: https://oeis.org/A192351
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (Jan 17 2013) in OEIS A192351:
a(n) = 2*a(n-1) + 12*a(n-2) - 8*a(n-3) - 16*a(n-4).
The entry records a confirmation of the conjecture by Robert Israel (Jan 01 2018), so this is a
known result; the statement below is its Lean form.

Conventions:
* The polynomials are defined in the COMMENTS section of the entry: let d = sqrt(x+5); then
  p(n,x) = (1/2)((x+d)^n + (x-d)^n). Since d^2 = x+5, one has (x+d)^n = P_n(x) + Q_n(x)*d and
  (x-d)^n = P_n(x) - Q_n(x)*d for polynomials P_n, Q_n with integer coefficients, determined by
  P_0 = 1, Q_0 = 0 and (P + Q*d)*(x + d) = (x*P + (x+5)*Q) + (P + x*Q)*d, so that
  p(n,x) = P_n(x). The pair (P_n, Q_n) is `pq n` below and p(n,x) is `p n`, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 0 and a(n) is the coefficient of x of the reduction of p(n,x)
  (data 0, 1, 2, 20, 56, 320, ...; EXAMPLE section of the entry: p(0,x) = 1 -> 1, p(1,x) = x -> x,
  p(2,x) = 5+x+x^2 -> 6+2x, p(3,x) = 15x+3x^2+x^3 -> 4+20x).
* The recurrence involves a(n-4), so it is asserted for every `n ≥ 4`, the smallest index at
  which a(n-4) exists. The terms are integers.
* Barker's generating function x*(4*x^2+1) / (16*x^4+8*x^3-12*x^2-2*x+1) is not stated
  separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a192351

open Polynomial

/-- `(x + d)^n = P_n + Q_n * d` with `d^2 = x + 5`: the pair `(P_n, Q_n)`. -/
noncomputable def pq : ℕ → ℤ[X] × ℤ[X]
  | 0 => (1, 0)
  | n + 1 => (X * (pq n).1 + (X + 5) * (pq n).2, (pq n).1 + X * (pq n).2)

/-- p(n,x) = (1/2)((x+d)^n + (x-d)^n) with d = sqrt(x+5). -/
noncomputable def p (n : ℕ) : ℤ[X] := (pq n).1

/-- A192351 (offset 0): the coefficient of x of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n ≥ 4`, a(n) = 2*a(n-1) + 12*a(n-2) - 8*a(n-3) - 16*a(n-4). -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n = 2 * a (n - 1) + 12 * a (n - 2) - 8 * a (n - 3) - 16 * a (n - 4) := by
  sorry

end OMA.S_oeis_a192351
