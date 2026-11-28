import Mathlib

/-!
# A192240: Constant term in the reduction of the polynomial (x+3)^n by x^2 -> x+1.

Source: https://oeis.org/A192240
Credit: @JeremyDevs

Formalizes the formula conjectured in OEIS A192240 (Rigoberto Florez, Mar 25 2020):
a(n) = Sum_{i=0..n} (-1)^i*Fibonacci(i+1)*binomial(n,i)*4^(n-i).

Conventions:
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `(X + 3) ^ n %ₘ (X ^ 2 - X - 1)` in `ℤ[X]`. Its constant term is its
  coefficient of index 0.
* The sequence has offset 0 and a(n) is the constant term of the reduction of (x+3)^n
  (data 1, 3, 10, 37, 149, 636, ...; for instance (x+3)^2 = x^2 + 6x + 9 -> 10 + 7x).
* Fibonacci(0) = 0, Fibonacci(1) = 1 (`Nat.fib`). The sum is over `i = 0, ..., n` and is taken in
  `ℤ` because of the signs. The formula is asserted for every `n ≥ 0`.
-/

namespace OMA.S_oeis_a192240

open Polynomial

/-- A192240 (offset 0): the constant term of the reduction of (x+3)^n by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (((X + 3 : ℤ[X]) ^ n) %ₘ (X ^ 2 - X - 1)).coeff 0

/-- For every `n`, a(n) = Sum_{i=0..n} (-1)^i*Fibonacci(i+1)*binomial(n,i)*4^(n-i). -/
theorem main : ∀ n : ℕ,
    a n = ∑ i ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i) := by
  sorry

end OMA.S_oeis_a192240
