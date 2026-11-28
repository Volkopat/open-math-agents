import Mathlib

/-!
# A192255: 1-sequence of reduction of (n^2) by x^2 -> x+1.

Source: https://oeis.org/A192255
Credit: @jagong-cmu

Formalizes the formula conjectured in OEIS A192255 (Greg Dresden, Oct 10 2023):
a(n) = Sum_{i=1..n+1} i^2*Fibonacci(i-1).

Conventions:
* The polynomials are those of the Mathematica code of the companion entry A192254 (Peter J. C.
  Moses): p(0,x) = 1 and p(n,x) = p(n-1,x) + x^n*c(n+1) with c(n) = n^2, that is
  p(n,x) = 1 + 4x + 9x^2 + ... + (n+1)^2 x^n; it is `p n` below, in `ℤ[X]`, with the recursion
  written with `n + 1` in place of `n`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. The 1-sequence is its coefficient of x, that is
  its coefficient of index 1.
* The sequence has offset 1 and its first term comes from p(0,x) = 1 (data 0, 4, 13, 45, 120, ...:
  p(0,x) = 1 -> 1, p(1,x) = 1 + 4x -> 1 + 4x, p(2,x) = 1 + 4x + 9x^2 -> 10 + 13x), so the n-th
  term (offset 1) is the coefficient of x in the reduction of p(n-1,x); `a n` below is that
  term, and only `n ≥ 1` is used.
* Index shift: read with the offset 1 of the entry, the formula fails at every n (at n = 1 it
  gives 0 + 4 = 4, but the first term is 0; in general it gives the next term). It matches the
  data exactly when the terms are numbered from 0, that is, when its left side is the term with
  offset-1 index n+1. So it is asserted in that form, a(n+1) = Sum_{i=1..n+1} i^2*F(i-1),
  for every `n ≥ 0`, which covers every term of the sequence.
* Fibonacci(m) is `Nat.fib m`, with Fibonacci(0) = 0, Fibonacci(1) = 1; for 1 ≤ i the index
  `i - 1` is exact. The sum and the terms are compared in `ℤ`.
-/

namespace OMA.S_oeis_a192255

open Polynomial

/-- p(0,x) = 1, p(n,x) = p(n-1,x) + x^n*(n+1)^2. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => p n + X ^ (n + 1) * C (((n : ℤ) + 2) ^ 2)

/-- A192255 (offset 1): the coefficient of x in the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n ≥ 0`, the term with offset-1 index n+1 is Sum_{i=1..n+1} i^2*Fibonacci(i-1). -/
theorem main : ∀ n : ℕ,
    a (n + 1) = ∑ i ∈ Finset.Icc 1 (n + 1), (i : ℤ) ^ 2 * (Nat.fib (i - 1) : ℤ) := by
  sorry

end OMA.S_oeis_a192255
