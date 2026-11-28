import Mathlib

/-!
# A233083: Number of 2 X n 0..3 arrays with no element x(i,j) adjacent to value 3-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 in row major order.

Source: https://oeis.org/A233083
Credit: @agchua

Colin Barker (Oct 07 2018), in the formula section of A233083:
  Conjectures from Colin Barker, Oct 07 2018: (Start)
  G.f.: x*(3 - 10*x + 4*x^2) / ((1 - x)*(1 - 7*x)).
  a(n) = (49 + 27*7^n) / 98 for n>1.
  (End)
This file states both. The sequence has offset 1 (data 3, 14, 95, 662, 4631, ...).

A 2 X n array with entries in 0..3 is a function x : Fin n → Fin 2 → Fin 4, where x j i is the
element x(i,j) in row i (0 = top, 1 = bottom) and column j. An element is adjacent to the value
3 minus a neighbour u exactly when the two add up to 3. Horizontal neighbours are x(i,j) and
x(i,j+1); antidiagonal neighbours are x(0,j+1) and x(1,j) (the two ends of a step from upper
right to lower left). The top left element is x(0,0). In row major order the element x(i',j')
comes before x(i,j) iff i' < i, or i' = i and j' < j; 1 appearing before 2 means that every
element equal to 2 has an element equal to 1 before it (so the first of the values 1 and 2 that
occurs, if any occurs, is 1). This reading gives the listed terms (checked by brute force for
n ≤ 5); the mirror reading of antidiagonal, x(0,j) and x(1,j+1), gives the same numbers.

The g.f. is stated for the series of the terms (n ≥ 1), as an identity of formal power series
over ℚ: (sum of a(n) X^n over n ≥ 1) * ((1 - X)(1 - 7X)) = X(3 - 10X + 4X^2). The closed form
is stated over ℚ for n ≥ 2, as Barker states it (at n = 1 it is not an integer).
-/

namespace OMA.S_oeis_a233083

/-- No element is adjacent to 3 minus itself horizontally or antidiagonally. -/
def noClash (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ j k : Fin n, k.val = j.val + 1 →
    (∀ i : Fin 2, (x j i).val + (x k i).val ≠ 3) ∧ (x k 0).val + (x j 1).val ≠ 3

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Decidable (noClash n x) := by
  unfold noClash
  infer_instance

/-- The top left element is zero. -/
def topLeftZero (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ j : Fin n, j.val = 0 → x j 0 = 0

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Decidable (topLeftZero n x) := by
  unfold topLeftZero
  infer_instance

/-- 1 appears before 2 in row major order. -/
def oneBeforeTwo (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ j : Fin n, ∀ i : Fin 2, x j i = 2 →
    ∃ j' : Fin n, ∃ i' : Fin 2, (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) ∧ x j' i' = 1

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Decidable (oneBeforeTwo n x) := by
  unfold oneBeforeTwo
  infer_instance

/-- A233083(n): the number of such 2 X n arrays. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 2 → Fin 4)).filter
    (fun x => noClash n x ∧ topLeftZero n x ∧ oneBeforeTwo n x)).card

/-- Barker's conjectures: the g.f. x(3 - 10x + 4x^2)/((1 - x)(1 - 7x)) of the terms, and
a(n) = (49 + 27*7^n)/98 for n ≥ 2. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 7 * PowerSeries.X)) =
      PowerSeries.X * (3 - 10 * PowerSeries.X + 4 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (49 + 27 * 7 ^ n) / 98 := by
  sorry

end OMA.S_oeis_a233083
