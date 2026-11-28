import Mathlib

/-!
# A221968: Number of -n..n arrays of length 5 with the sum ahead of each element differing from the sum following that element by n or less.

Source: https://oeis.org/A221968 (OEIS Foundation, CC BY-SA 4.0)
Credit: @marcusbuffett

Entry (R. H. Hardin, Feb 01 2013), offset 1, row 5 of A221967. Data:
  63, 705, 3647, 12609, 34111, 78273, 159615, 297857, 518719, 854721, 1345983, 2041025, 2997567,
  4283329, 5976831, 8168193, 10959935, 14467777, 18821439, 24165441, 30659903, 38481345,
  47823487, 58898049, 71935551, 87186113
The formula section states:
  Empirical: a(n) = (20/3)*n^5 + (50/3)*n^4 + 20*n^3 + (40/3)*n^2 + (16/3)*n + 1.
Conjectures from Colin Barker, Aug 14 2018:
  G.f.: x*(9 + 12*x - x^2)*(7 + 27*x + 5*x^2 + x^3) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.

Conventions:
* An array of length 5 is a function `x : Fin 5 → ℤ`, x i being the element at position i
  (counted from 0); a -n..n array has every element in -n..n.
* The sum ahead of the element at position i is the sum of the elements at positions j < i, the sum
  following it is the sum of the elements at positions j > i (an empty sum is 0). The two differ by
  n or less when the absolute value of their difference is at most n.
* `a n` is `Set.ncard` of the set of such arrays (a finite set, inside the box (-n..n)^5).
* Offset 1. The definition also gives a value at n = 0, which is not a term: the g.f. is stated for
  the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1, as an identity of formal
  power series over ℚ, (∑ a(n) X^n) * (1 - X)^6 = numerator, which is equivalent because
  (1 - X)^6 has constant term 1.
* The recurrence is stated in ℤ for every n > 6.
* `main` is the conjunction of Barker's two conjectures.

Numerical check: a brute-force count of the definition gives 63, 705, 3647 for n = 1..3, the
first terms of the DATA.
-/

namespace OMA.S_oeis_a221968

open PowerSeries

/-- The sum of the elements ahead of position i: those at positions j < i. -/
def ahead (x : Fin 5 → ℤ) (i : Fin 5) : ℤ := ∑ j ∈ Finset.univ.filter (fun j => j < i), x j

/-- The sum of the elements following position i: those at positions j > i. -/
def following (x : Fin 5 → ℤ) (i : Fin 5) : ℤ := ∑ j ∈ Finset.univ.filter (fun j => i < j), x j

/-- A221968(n): the number of -n..n arrays of length 5 in which, at every position, the sum ahead of
the element differs from the sum following it by n or less. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin 5 → ℤ | (∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n) ∧
    ∀ i, |ahead x i - following x i| ≤ n}

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 6. -/
theorem main : mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * ((9 + 12 * X - X ^ 2) * (7 + 27 * X + 5 * X ^ 2 + X ^ 3)) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4)
      + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a221968
