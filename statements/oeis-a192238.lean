import Mathlib

/-!
# A192238: Constant term in the reduction of the polynomial x(x+1)(x+2)...(x+n-1) by x^2 -> x+1

Source: https://oeis.org/A192238
Credit: @ivillar

Clark Kimberling's sequence (offset 1, data 1, 0, 1, 6, 37, 256, 1999, ...). The listed terms come from
the entry's program (Peter J. C. Moses), which uses p(0,x) = 1, p(1,x) = x and
p(n,x) = (x+n)*p(n-1,x) for n > 1, i.e. p(n,x) = x(x+2)(x+3)...(x+n), and lists the constant terms of
the reductions of p(0,x), p(1,x), ...; so a(n) is the constant term of the reduction of p(n-1,x). (The
product in the name, x(x+1)...(x+n-1), would give other numbers; we follow the program, which
produces the data.) Reducing by x^2 -> x+1 means replacing x^2 by x + 1 repeatedly until the degree
is at most 1 (see A192232); the result is the remainder modulo the monic polynomial x^2 - x - 1.

Conjecture (R. J. Mathar, May 04 2014): a(n) +2*(-n+1)*a(n-1) +(n^2-3*n+1)*a(n-2)=0.
Status: false as stated at n = 3: there the left side is a(3) - 4*a(2) + a(1) = 1 - 0 + 1 = 2 ≠ 0.
`main` is the corrected recurrence (n ≥ 4), stated over the integers.
-/

namespace OMA.S_oeis_a192238

open Polynomial

/-- The program's p(n,x): p(0,x) = 1, p(1,x) = x, p(n,x) = (x+n)*p(n-1,x) for n > 1. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (X + ((n + 2 : ℕ) : ℤ[X])) * p (n + 1)

/-- The reduction by x^2 -> x+1: the remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n) (offset 1): the constant term of the reduction of p(n-1,x). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p (n - 1))).coeff 0

/-- The corrected recurrence (n ≥ 4); the conjectured recurrence fails at n = 3. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + 2 * (-(n : ℤ) + 1) * a (n - 1) + ((n : ℤ) ^ 2 - 3 * n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a192238
