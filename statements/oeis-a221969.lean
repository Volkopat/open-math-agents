import Mathlib

/-!
# A221969: Number of -n..n arrays of length 6 with the sum ahead of each element differing from the sum following that element by n or less.

Source: https://oeis.org/A221969 (OEIS Foundation, CC BY-SA 4.0)
Credit: @marcusbuffett

Entry (R. H. Hardin, Feb 01 2013), offset 1, row 6 of A221967. Data:
  129, 2305, 16513, 73089, 241153, 653185, 1535745, 3246337, 6316417, 11500545, 19831681,
  32682625, 51833601, 79545985, 118642177, 172591617, 245602945, 342722305, 469937793,
  634290049, 843988993, 1108536705, 1438856449
The formula section states:
  Empirical: a(n) = (128/15)*n^6 + (128/5)*n^5 + (112/3)*n^4 + 32*n^3 + (272/15)*n^2 + (32/5)*n +
    1.
Conjectures from Colin Barker, Aug 14 2018:
  G.f.: x*(3 + x)*(43 + 453*x + 878*x^2 + 170*x^3 - 9*x^4 + x^5) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions:
* An array of length 6 is a function `x : Fin 6 → ℤ`, x i being the element at position i
  (counted from 0); a -n..n array has every element in -n..n.
* The sum ahead of the element at position i is the sum of the elements at positions j < i, the sum
  following it is the sum of the elements at positions j > i (an empty sum is 0). The two differ by
  n or less when the absolute value of their difference is at most n.
* `a n` is `Set.ncard` of the set of such arrays (a finite set, inside the box (-n..n)^6).
* Offset 1. The definition also gives a value at n = 0, which is not a term: the g.f. is stated for
  the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1, as an identity of formal
  power series over ℚ, (∑ a(n) X^n) * (1 - X)^7 = numerator, which is equivalent because
  (1 - X)^7 has constant term 1.
* The recurrence is stated in ℤ for every n > 7.
* `main` is the conjunction of Barker's two conjectures.

Numerical check: a brute-force count of the definition gives 129, 2305, 16513 for n = 1..3, the
first terms of the DATA.
-/

namespace OMA.S_oeis_a221969

open PowerSeries

/-- The sum of the elements ahead of position i: those at positions j < i. -/
def ahead (x : Fin 6 → ℤ) (i : Fin 6) : ℤ := ∑ j ∈ Finset.univ.filter (fun j => j < i), x j

/-- The sum of the elements following position i: those at positions j > i. -/
def following (x : Fin 6 → ℤ) (i : Fin 6) : ℤ := ∑ j ∈ Finset.univ.filter (fun j => i < j), x j

/-- A221969(n): the number of -n..n arrays of length 6 in which, at every position, the sum ahead of
the element differs from the sum following it by n or less. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin 6 → ℤ | (∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n) ∧
    ∀ i, |ahead x i - following x i| ≤ n}

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 7. -/
theorem main : mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * ((3 + X) * (43 + 453 * X + 878 * X ^ 2 + 170 * X ^ 3 - 9 * X ^ 4 + X ^ 5)) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4)
      + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a221969
