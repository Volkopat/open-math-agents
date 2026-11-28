import Mathlib

/-!
# A192251: 1-sequence of reduction of central binomial coefficient sequence by x^2 -> x+1.

Source: https://oeis.org/A192251
Credit: @JeremyDevs

Formalizes the recurrence conjectured in OEIS A192251 (R. J. Mathar, May 04 2014):
(n-1)*(n-2)*a(n) - (5*n-7)*(n-2)*a(n-1) - 2*(2*n-3)*(3*n-8)*a(n-2) + 4*(2*n-3)*(2*n-5)*a(n-3) = 0.

Conventions:
* By the definition at A192232 ("k-sequence of reduction of [sequence] by [substitution]"), for a
  sequence b = (b(0), b(1), ...) one puts p(n,x) = b(0) + b(1)x + ... + b(n)x^n; the reduction of
  p(n,x) by x^2 -> x+1 is a polynomial of degree at most 1, and its constant terms form the
  0-sequence, its coefficients of x the 1-sequence. Here b(n) = binomial(2n,n), the central
  binomial coefficients 1, 2, 6, 20, 70, ... (`Nat.centralBinom n`), so
  p(n,x) = 1 + 2x + 6x^2 + ... + binomial(2n,n)x^n; it is `p n` below, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 replaces x^2 by x+1 repeatedly until a polynomial
  of degree at most 1 is left; this is the remainder of the polynomial modulo x^2 - x - 1, here
  `p n %ₘ (X ^ 2 - X - 1)`.
* The sequence has offset 1 and its first term comes from p(0,x) = 1 (data 0, 2, 8, 48, 258, 1518, ...:
  1 -> 1, 1+2x -> 1+2x, 1+2x+6x^2 -> 7+8x, 1+2x+6x^2+20x^3 -> 27+48x), so a(n) is the
  coefficient of x of the reduction of p(n-1,x). Only `n ≥ 1` is used.
* The recurrence involves a(n-3), so it is asserted for every `n ≥ 4`, the smallest index at
  which a(n-3) exists (index at least 1). The terms are integers.
-/

namespace OMA.S_oeis_a192251

open Polynomial

/-- p(n,x) = sum of binomial(2k,k) x^k for k = 0..n. -/
noncomputable def p (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n + 1), C (k.centralBinom : ℤ) * X ^ k

/-- A192251 (offset 1): the coefficient of x of the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n ≥ 4`,
(n-1)*(n-2)*a(n) - (5*n-7)*(n-2)*a(n-1) - 2*(2*n-3)*(3*n-8)*a(n-2) + 4*(2*n-3)*(2*n-5)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) - 1) * ((n : ℤ) - 2) * a n - (5 * (n : ℤ) - 7) * ((n : ℤ) - 2) * a (n - 1)
      - 2 * (2 * (n : ℤ) - 3) * (3 * (n : ℤ) - 8) * a (n - 2)
      + 4 * (2 * (n : ℤ) - 3) * (2 * (n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a192251
