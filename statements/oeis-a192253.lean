import Mathlib

/-!
# A192253: 1-sequence of reduction of (n!) by x^2 -> x+1.

Source: https://oeis.org/A192253
Credit: @JeremyDevs

Formalizes the recurrence conjectured in OEIS A192253 (R. J. Mathar, May 04 2014):
a(n) - n*a(n-1) - (n-1)*(n-3)*a(n-2) + (n-1)*(n-2)*a(n-3) = 0.

Conventions:
* By the definition at A192232 ("k-sequence of reduction of [sequence] by [substitution]"), for a
  sequence b = (b(0), b(1), ...) one puts p(n,x) = b(0) + b(1)x + ... + b(n)x^n; the reduction of
  p(n,x) by x^2 -> x+1 is a polynomial of degree at most 1, and its constant terms form the
  0-sequence, its coefficients of x the 1-sequence. Here b(n) = n!, so
  p(n,x) = 1 + x + 2x^2 + ... + (n!)x^n; it is `p n` below, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 replaces x^2 by x+1 repeatedly until a polynomial
  of degree at most 1 is left; this is the remainder of the polynomial modulo x^2 - x - 1, here
  `p n %ₘ (X ^ 2 - X - 1)`.
* The sequence has offset 1 and its first term comes from p(0,x) = 1 (data 0, 1, 3, 15, 87, 687, ...:
  1 -> 1, 1+x -> 1+x, 1+x+2x^2 -> 3+3x, 1+x+2x^2+6x^3 -> 9+15x), so a(n) is the coefficient of x
  of the reduction of p(n-1,x). Only `n ≥ 1` is used.
* The recurrence involves a(n-3), so it is asserted for every `n ≥ 4`, the smallest index at
  which a(n-3) exists (index at least 1). The terms are integers.
* The entry records a second conjecture, partial sums of A005443 (Sean A. Irvine, Jul 12 2022); it is
  not stated here.
-/

namespace OMA.S_oeis_a192253

open Polynomial

/-- p(n,x) = 0! + 1! x + 2! x^2 + ... + n! x^n. -/
noncomputable def p (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n + 1), C (k.factorial : ℤ) * X ^ k

/-- A192253 (offset 1): the coefficient of x of the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n ≥ 4`, a(n) - n*a(n-1) - (n-1)*(n-3)*a(n-2) + (n-1)*(n-2)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n - (n : ℤ) * a (n - 1) - ((n : ℤ) - 1) * ((n : ℤ) - 3) * a (n - 2)
      + ((n : ℤ) - 1) * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a192253
