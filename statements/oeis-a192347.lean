import Mathlib

/-!
# A192347: Coefficient of x in the reduction (by x^2->x+1) of polynomial p(n,x) identified in Comments.

Source: https://oeis.org/A192347
Credit: @jagong-cmu

Formalizes the conjecture of Colin Barker (Jan 17 2013) recorded in OEIS A192347:
a(n) = 2*a(n-1) + 6*a(n-2) - 2*a(n-3) - a(n-4).

Conventions:
* The COMMENTS section defines p(n,x) = (1/2)((x+d)^n + (x-d)^n) with d = sqrt(x+2).
  By the binomial theorem, (x+d)^n + (x-d)^n is the sum over j of C(n,j)*x^(n-j)*(d^j + (-d)^j);
  the terms with odd j cancel, and for even j the term is 2*C(n,j)*x^(n-j)*(x+2)^(j/2).
  So p(n,x) is the integer polynomial sum over even j in 0..n of C(n,j)*x^(n-j)*(x+2)^(j/2);
  it is `p n` below, in `ℤ[X]` (this is also what the Mathematica code of A192346 computes).
  For instance p(2,x) = x^2 + x + 2 and p(3,x) = x^3 + 3x^2 + 6x, as in the EXAMPLE section.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 1 and its first term comes from p(0,x) = 1 (data 0, 1, 2, 11, 32, ...:
  p(0,x) = 1 -> 1, p(1,x) = x -> x, p(2,x) -> 3 + 2x, p(3,x) -> 4 + 11x),
  so a(n) is the coefficient of x in the reduction of p(n-1,x). Only `n ≥ 1` is used.
* The recurrence involves a(n-4), so it is asserted for every `n > 4`, where all the indices
  `n - 1, ..., n - 4` are at least 1. The terms are compared in `ℤ`.
* Barker's generating function x^2*(x^2+1) / (x^4+2*x^3-6*x^2-2*x+1) is not stated
  separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a192347

open Polynomial

/-- p(n,x) = (1/2)((x+d)^n + (x-d)^n) with d = sqrt(x+2), expanded: the sum over even j in
0..n of C(n,j)*x^(n-j)*(x+2)^(j/2). -/
noncomputable def p (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    if Even j then C (n.choose j : ℤ) * X ^ (n - j) * (X + C 2) ^ (j / 2) else 0

/-- A192347 (offset 1): the coefficient of x in the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n > 4`, a(n) = 2*a(n-1) + 6*a(n-2) - 2*a(n-3) - a(n-4). -/
theorem main : ∀ n : ℕ, 4 < n →
    a n = 2 * a (n - 1) + 6 * a (n - 2) - 2 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a192347
