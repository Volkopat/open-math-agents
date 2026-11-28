import Mathlib

/-!
# A024401: Mathar's recurrence and generating function

Source: https://oeis.org/A024401
Credit: @ivillar

Status: known result: the entry records a proof through a closed form (Austen M. Fletcher, Aug 05 2026).

A024401 (offset 1): a(n) = [ (3rd elementary symmetric function of S(n))/(2nd elementary symmetric
function of S(n)) ], where S(n) = {first n+2 positive integers congruent to 2 mod 3} and [ ] is
the floor; data 1, 3, 6, 11, 16, 22, 30, 38, 47, 58, ...

Conjecture (R. J. Mathar, Oct 08 2011): a(n) = 2*a(n-1) - a(n-2) + a(n-3) - 2*a(n-4) + a(n-5),
with g.f. x*(-1-x-x^3-x^2+x^4) / ( (1+x+x^2)*(x-1)^3 ). Austen M. Fletcher (Aug 05 2026) records
in the entry a proof through the closed form a(n) = floor((3*n^2 + 5*n - 2)/6).

Formalization: S(n) is the multiset {2, 5, ..., 3(n+1)+2} of integers, `Multiset.esymm` gives the
elementary symmetric functions, and the quotient is taken in ℚ. The definition also makes sense
at n = 0, where S(0) = {2, 5} has third symmetric function 0, so a(0) = 0, the value needed for a
g.f. divisible by x. The recurrence involves only the terms a(1), a(2), ..., so it is stated for
n > 5. The g.f. is a formal power series over ℤ, stated with the denominator cleared.
-/

namespace OMA.S_oeis_a024401

open PowerSeries

/-- S(n): the first n + 2 positive integers congruent to 2 modulo 3. -/
def S (n : ℕ) : Multiset ℤ := (Multiset.range (n + 2)).map (fun i : ℕ => 3 * (i : ℤ) + 2)

/-- a(n) = floor(e_3(S(n)) / e_2(S(n))). -/
def a (n : ℕ) : ℤ := ⌊(((S n).esymm 3 : ℤ) : ℚ) / (((S n).esymm 2 : ℤ) : ℚ)⌋

/-- Mathar's conjectured recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      a n = 2 * a (n - 1) - a (n - 2) + a (n - 3) - 2 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk a * ((1 + X + X ^ 2) * (X - 1) ^ 3) = X * (-1 - X - X ^ 3 - X ^ 2 + X ^ 4) := by
  sorry

end OMA.S_oeis_a024401
