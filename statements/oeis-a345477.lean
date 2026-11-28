import Mathlib

/-!
# A345477: Numbers that are the sum of six squares in ten or more ways.

Source: https://oeis.org/A345477
Credit: @rtflynn

Chai Wah Wu (Jan 05 2024), in the formula section of A345477:
  Conjectures: a(n) = 2*a(n-1) - a(n-2) for n > 20.
  G.f.: x*(-x^19 + x^18 - x^17 + x^16 - x^15 + x^14 - x^13 + x^12 - x^11 + x^10 - 4*x^8 + 3*x^7 + x^6 - 2*x^5 + x^3 - x^2 - 78*x + 81)/(x - 1)^2.

Conventions:
* A way of writing m as a sum of six squares is a multiset of six positive integers whose squares
  sum to m (order does not matter, squares are of positive integers), as in the Python program of
  the entry (combinations with replacement of the squares 1, 4, 9, ...). `r m` is the number of
  ways; it is finite for every m.
* The terms are the m with r m ≥ 10, in increasing order, offset 1: a(n) is `Nat.nth S (n - 1)`,
  the (n-1)-th element of the set S counted from 0.
* The g.f. is stated for the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1,
  as an identity of formal power series over ℚ, (∑ a(n) X^n) * (X - 1)^2 = numerator.
* The recurrence is stated in ℤ for every n ≥ 21 (n > 20).

Numerical check: a Python copy of the definition gives 81, 84, 86, 89, 92, 93, 95, 100, 101, 102, 104, 105, ... for the first 12 elements
of S, the DATA of the entry.
-/

namespace OMA.S_oeis_a345477

/-- The number of ways to write m as a sum of six squares of positive integers. -/
noncomputable def r (m : ℕ) : ℕ :=
  Nat.card {s : Multiset ℕ // Multiset.card s = 6 ∧ (∀ x ∈ s, 0 < x) ∧ (s.map (· ^ 2)).sum = m}

/-- Numbers that are the sum of six squares in ten or more ways. -/
def S : Set ℕ := {m | 10 ≤ r m}

/-- A345477 (offset 1): the n-th element of S in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- Wu's conjectures: the recurrence for n > 20 and the rational g.f. -/
theorem main : (∀ n : ℕ, 21 ≤ n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (PowerSeries.X - 1) ^ 2 =
      PowerSeries.X * (-PowerSeries.X ^ 19 + PowerSeries.X ^ 18 - PowerSeries.X ^ 17
        + PowerSeries.X ^ 16 - PowerSeries.X ^ 15 + PowerSeries.X ^ 14
        - PowerSeries.X ^ 13 + PowerSeries.X ^ 12 - PowerSeries.X ^ 11
        + PowerSeries.X ^ 10 - 4 * PowerSeries.X ^ 8 + 3 * PowerSeries.X ^ 7
        + PowerSeries.X ^ 6 - 2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 3
        - PowerSeries.X ^ 2 - 78 * PowerSeries.X + 81) := by
  sorry

end OMA.S_oeis_a345477
