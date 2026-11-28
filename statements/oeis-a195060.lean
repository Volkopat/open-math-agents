import Mathlib

/-!
# A195060: Numbers on the main diagonals and on the axes (x,y) in the square spiral whose vertices are the generalized pentagonal numbers A001318.

Source: https://oeis.org/A195060
Credit: @agchua

R. J. Mathar (Oct 11 2011), in the formula section of A195060:
  Conjectures: a(n) = 2*a(n-1) - 2*a(n-2) + 2*a(n-3) - a(n-4) + a(n-8) - 2*a(n-9) + 2*a(n-10)
  - 2*a(n-11) + a(n-12); g.f.: -x*(1+x^2+x^3-x^4+x^5+x^7-2*x^8+x^11+2*x^9-2*x^10) /
  ( (1+x)*(x^4+1)*(x^2+1)^2*(x-1)^3 ).
This file states both parts (offset 0). The g.f. is stated as an identity of formal power series
over ℚ: (∑ a(n) X^n) * ((1+X)(X^4+1)(X^2+1)^2(X-1)^3) = -X (1 + X^2 + ... - 2X^10). The
recurrence is stated for n ≥ 13: at its first index n = 12 it fails, since a(12) = 22 while the
right side is 2*18 - 2*15 + 2*13 - 12 + 5 - 2*3 + 2*2 - 2*1 + 0 = 21 (it uses a(0) = 0, and the
g.f. numerator has degree 12); from n = 13 on it is equivalent to the g.f.

Definition, from the entry's comment: the sequence is the union of A001318, A032528 and A045943,
without repetitions, in increasing order: the generalized pentagonal numbers m(3m-1)/2 for
integers m (written without division as 2x = m(3m-1)), the concentric hexagonal numbers
floor(3n^2/2) and the triangular matchstick numbers 3n(n+1)/2 (natural-number quotients,
n ≥ 0). a(n) is the element of index n of the union (Nat.nth, offset 0, so a(0) = 0).
-/

namespace OMA.S_oeis_a195060

/-- A001318: x is a generalized pentagonal number m(3m-1)/2, m = 0, ±1, ±2, ... -/
def IsGenPent (x : ℕ) : Prop := ∃ m : ℤ, 2 * (x : ℤ) = m * (3 * m - 1)

/-- A032528: x is a concentric hexagonal number floor(3n^2/2). -/
def IsConcHex (x : ℕ) : Prop := ∃ n : ℕ, x = 3 * n ^ 2 / 2

/-- A045943: x is a triangular matchstick number 3n(n+1)/2. -/
def IsTriMatch (x : ℕ) : Prop := ∃ n : ℕ, x = 3 * n * (n + 1) / 2

/-- A195060 (offset 0): the union of A001318, A032528 and A045943 in increasing order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun x => IsGenPent x ∨ IsConcHex x ∨ IsTriMatch x) n

/-- Mathar's conjectures: the recurrence (for n ≥ 13, see above) and the g.f. -/
theorem main : (∀ n : ℕ, 13 ≤ n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) -
      a (n - 4) + a (n - 8) - 2 * a (n - 9) + 2 * a (n - 10) - 2 * a (n - 11) + a (n - 12)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 + PowerSeries.X) * (PowerSeries.X ^ 4 + 1) * (PowerSeries.X ^ 2 + 1) ^ 2 *
        (PowerSeries.X - 1) ^ 3) =
      -PowerSeries.X * (1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - PowerSeries.X ^ 4 +
        PowerSeries.X ^ 5 + PowerSeries.X ^ 7 - 2 * PowerSeries.X ^ 8 + PowerSeries.X ^ 11 +
        2 * PowerSeries.X ^ 9 - 2 * PowerSeries.X ^ 10) := by
  sorry

end OMA.S_oeis_a195060
