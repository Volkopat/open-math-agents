import Mathlib

/-!
# A229013: Number of arrays of median of three adjacent elements of some length-5 0..n array, with no adjacent equal elements in the latter.

Source: https://oeis.org/A229013 (OEIS Foundation, CC BY-SA 4.0)
Credit: @marcusbuffett

Entry (R. H. Hardin, Sep 10 2013), offset 1. Data:
  2, 15, 46, 101, 186, 307, 470, 681, 946, 1271, 1662, 2125, 2666, 3291, 4006, 4817, 5730, 6751,
  7886, 9141, 10522, 12035, 13686, 15481, 17426, 19527, 21790, 24221, 26826, 29611, 32582
The formula section states:
  Empirical: a(n) = n^3 + 3*n^2 - 3*n + 1.
Conjectures from Colin Barker, Sep 13 2018:
  G.f.: x*(2 - x)*(1 + 4*x + x^2) / (1 - x)^4.
  a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.

Conventions:
* A length-5 0..n array is a function `x : Fin 5 → Fin (n + 1)`, x i being the element at
  position i (counted from 0). It has no adjacent equal elements when x i ≠ x (i + 1) for
  i = 0, 1, 2, 3.
* `med3 a b c` is the median of the three numbers a, b, c. The array of medians of three adjacent
  elements of x is the length-3 array (med3 x0 x1 x2, med3 x1 x2 x3, med3 x2 x3 x4), written as a
  triple of natural numbers.
* `a n` is the number of distinct arrays of medians over all length-5 0..n arrays with no
  adjacent equal elements.
* Offset 1. The definition gives a(0) = 0 (a 0..0 array has equal neighbours), which is the
  constant term of the g.f.; the g.f. is stated as an identity of formal power series over ℚ,
  (∑ a(n) X^n) * (1 - X)^4 = numerator, equivalent to the quotient form because (1 - X)^4 has
  constant term 1.
* The empirical formula is stated for n ≥ 1 and the recurrence for n > 4, both in ℤ.
* `main` is the conjunction of the three formulas.

Numerical check: a brute-force count of the definition gives 2, 15, 46, 101, 186 for n = 1..5,
the first terms of the DATA.
-/

namespace OMA.S_oeis_a229013

open PowerSeries

/-- The median of three natural numbers. -/
def med3 (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

/-- No two adjacent elements of the array are equal. -/
def NoAdjEq {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Prop :=
  ∀ i : Fin 4, x i.castSucc ≠ x i.succ

instance {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Decidable (NoAdjEq x) := by
  unfold NoAdjEq; infer_instance

/-- The array of medians of three adjacent elements, as a triple. -/
def medians {n : ℕ} (x : Fin 5 → Fin (n + 1)) : ℕ × ℕ × ℕ :=
  (med3 (x 0) (x 1) (x 2), med3 (x 1) (x 2) (x 3), med3 (x 2) (x 3) (x 4))

/-- A229013(n): the number of distinct arrays of medians of three adjacent elements of length-5
0..n arrays with no adjacent equal elements. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => NoAdjEq x)).image medians).card

/-- Hardin's empirical formula and Barker's two conjectures. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = n ^ 3 + 3 * n ^ 2 - 3 * n + 1) ∧
    mk (fun n => (a n : ℚ)) * (1 - X) ^ 4 = X * (2 - X) * (1 + 4 * X + X ^ 2) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a229013
