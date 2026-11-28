import Mathlib

/-!
# A344812: Numbers that are the sum of six squares in eight or more ways.

Source: https://oeis.org/A344812
Credit: @xor2k

Chai Wah Wu (Jan 05 2024), in the formula section of A344812:
  Conjectures: a(n) = 2*a(n-1) - a(n-2) for n > 27.
  G.f.: x*(-x^26 + x^25 - x^21 + x^20 - 2*x^7 + x^6 + x^5 - x^4 - x^3 - 75*x + 78)/(x - 1)^2.

Conventions:
* A way of writing m as a sum of six squares is a multiset of six positive integers whose squares
  sum to m (order does not matter, squares are of positive integers), as in the Python program of
  the entry (combinations with replacement of the squares 1, 4, 9, ...). `r m` is the number of
  ways; it is finite for every m.
* The terms are the m with r m ≥ 8, in increasing order, offset 1: a(n) is `Nat.nth S (n - 1)`,
  the (n-1)-th element of the set S counted from 0.
* The g.f. is stated for the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1,
  as an identity of formal power series over ℚ, (∑ a(n) X^n) * (X - 1)^2 = numerator.
* The recurrence is stated in ℤ for every n ≥ 28 (n > 27).

Numerical check: a Python copy of the definition gives 78, 81, 84, 86, 87, 89, 92, 93, 94, 95, 96, 97, ... for the first 12 elements
of S; the first 40 coefficients of the series times (x-1)^2 agree with the numerator of the g.f. above.
-/

namespace OMA.S_oeis_a344812

/-- The number of ways to write m as a sum of six squares of positive integers. -/
noncomputable def r (m : ℕ) : ℕ :=
  Nat.card {s : Multiset ℕ // Multiset.card s = 6 ∧ (∀ x ∈ s, 0 < x) ∧ (s.map (· ^ 2)).sum = m}

/-- Numbers that are the sum of six squares in eight or more ways. -/
def S : Set ℕ := {m | 8 ≤ r m}

/-- A344812 (offset 1): the n-th element of S in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- Wu's conjectures: the recurrence for n > 27 and the rational g.f. -/
theorem main : (∀ n : ℕ, 28 ≤ n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (PowerSeries.X - 1) ^ 2 =
      PowerSeries.X * (-PowerSeries.X ^ 26 + PowerSeries.X ^ 25 - PowerSeries.X ^ 21
        + PowerSeries.X ^ 20 - 2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 6
        + PowerSeries.X ^ 5 - PowerSeries.X ^ 4 - PowerSeries.X ^ 3
        - 75 * PowerSeries.X + 78) := by
  sorry

end OMA.S_oeis_a344812
