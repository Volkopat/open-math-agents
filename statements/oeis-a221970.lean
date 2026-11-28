import Mathlib

/-!
# A221970: Number of -n..n arrays of length 7 with the sum ahead of each element differing from the sum following that element by n or less.

Source: https://oeis.org/A221970 (OEIS Foundation, CC BY-SA 4.0)
Credit: @marcusbuffett

Entry (R. H. Hardin, Feb 01 2013), offset 1, row 7 of A221967. Data:
  255, 7425, 73983, 419841, 1690623, 5407233, 14661375, 35111681, 76335103, 153588225,
  290033151, 519482625, 889719039, 1466441985, 2337899007, 3620254209, 5463749375, 8059712257,
  11648466687, 16528199169, 23064836607
The formula section states:
  Empirical: a(n) = (488/45)*n^7 + (1708/45)*n^6 + (2912/45)*n^5 + (602/9)*n^4 + (2072/45)*n^3 +
    (952/45)*n^2 + (32/5)*n + 1.
Conjectures from Colin Barker, Aug 14 2018:
  G.f.: x*(255 + 5385*x + 21723*x^2 + 21597*x^3 + 5469*x^4 + 219*x^5 + 9*x^6 - x^7) / (1 - x)^8.
  a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8)
    for n>8.

Conventions:
* An array of length 7 is a function `x : Fin 7 → ℤ`, x i being the element at position i
  (counted from 0); a -n..n array has every element in -n..n.
* The sum ahead of the element at position i is the sum of the elements at positions j < i, the sum
  following it is the sum of the elements at positions j > i (an empty sum is 0). The two differ by
  n or less when the absolute value of their difference is at most n.
* `a n` is `Set.ncard` of the set of such arrays (a finite set, inside the box (-n..n)^7).
* Offset 1. The definition also gives a value at n = 0, which is not a term: the g.f. is stated for
  the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1, as an identity of formal
  power series over ℚ, (∑ a(n) X^n) * (1 - X)^8 = numerator, which is equivalent because
  (1 - X)^8 has constant term 1.
* The recurrence is stated in ℤ for every n > 8.
* `main` is the conjunction of Barker's two conjectures.

Numerical check: a brute-force count of the definition gives 255, 7425, 73983 for n = 1..3, the
first terms of the DATA.
-/

namespace OMA.S_oeis_a221970

open PowerSeries

/-- The sum of the elements ahead of position i: those at positions j < i. -/
def ahead (x : Fin 7 → ℤ) (i : Fin 7) : ℤ := ∑ j ∈ Finset.univ.filter (fun j => j < i), x j

/-- The sum of the elements following position i: those at positions j > i. -/
def following (x : Fin 7 → ℤ) (i : Fin 7) : ℤ := ∑ j ∈ Finset.univ.filter (fun j => i < j), x j

/-- A221970(n): the number of -n..n arrays of length 7 in which, at every position, the sum ahead of
the element differs from the sum following it by n or less. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin 7 → ℤ | (∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n) ∧
    ∀ i, |ahead x i - following x i| ≤ n}

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 8. -/
theorem main : mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * ((255 + 5385 * X + 21723 * X ^ 2 + 21597 * X ^ 3 + 5469 * X ^ 4 + 219 * X ^ 5 +
        9 * X ^ 6 - X ^ 7)) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4)
      + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a221970
