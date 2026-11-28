import Mathlib

/-!
# A024399: Mathar's recurrence and generating function

Source: https://oeis.org/A024399
Credit: @ivillar

A024399 (offset 1): a(n) = [ (3rd elementary symmetric function of S(n))/(first elementary
symmetric function of S(n)) ], where S(n) = {first n+2 positive integers congruent to 2 mod 3}
and [ ] is the floor; data 5, 31, 101, 248, 515, 952, 1619, 2586, ...

Conjecture (R. J. Mathar, Oct 08 2011):
a(n) = 4*a(n-1) - 6*a(n-2) + 5*a(n-3) - 5*a(n-4) + 6*a(n-5) - 4*a(n-6) + a(n-7), with
g.f. x*(-5-11*x-7*x^2-5*x^3+x^4) / ( (1+x+x^2)*(x-1)^5 ).

Formalization: S(n) is the multiset {2, 5, ..., 3(n+1)+2} of integers, `Multiset.esymm` gives the
elementary symmetric functions, and the quotient is taken in ℚ. The definition also makes sense
at n = 0, where S(0) = {2, 5} has third symmetric function 0, so a(0) = 0, the value needed for a
g.f. divisible by x. The recurrence is stated for n > 7, where it involves only a(1), a(2), ...
The g.f. is a formal power series over ℤ, stated with the denominator cleared.
-/

namespace OMA.S_oeis_a024399

open PowerSeries

/-- S(n): the first n + 2 positive integers congruent to 2 modulo 3. -/
def S (n : ℕ) : Multiset ℤ := (Multiset.range (n + 2)).map (fun i : ℕ => 3 * (i : ℤ) + 2)

/-- a(n) = floor(e_3(S(n)) / e_1(S(n))). -/
def a (n : ℕ) : ℤ := ⌊(((S n).esymm 3 : ℤ) : ℚ) / (((S n).esymm 1 : ℤ) : ℚ)⌋

/-- Mathar's conjectured recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 7 < n →
      a n = 4 * a (n - 1) - 6 * a (n - 2) + 5 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) -
        4 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk a * ((1 + X + X ^ 2) * (X - 1) ^ 5) =
      X * (-5 - 11 * X - 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  sorry

end OMA.S_oeis_a024399
