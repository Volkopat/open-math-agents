import Mathlib

/-!
# A233175: Number of 2 X n 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally, diagonally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabelled 6-colorings with no clashing color pairs).

Source: https://oeis.org/A233175
Credit: @agchua

Colin Barker (Oct 10 2018), in the formula section of A233175:
  Conjectures from Colin Barker, Oct 10 2018: (Start)
  G.f.: x*(3 - 28*x - 16*x^2 + 224*x^3) / ((1 - 4*x)*(1 - 8*x - 32*x^2)).
  a(n) = 2^(2*n-3) + (1/32)*sqrt(3)*(-(4-4*sqrt(3))^n + (4*(1+sqrt(3)))^n) for n>1.
  (End)
This file states both. The sequence has offset 1 (data 3, 8, 80, 800, 8576, ...).

A 2 X n array with entries in 0..5 is a function x : Fin n → Fin 2 → Fin 6, where x j i is the
element x(i,j) in row i (0 = top, 1 = bottom) and column j. Two neighbouring elements clash when
they are equal or one is 5 minus the other (they add up to 5). Horizontal neighbours are x(i,j)
and x(i,j+1); diagonal neighbours are x(0,j) and x(1,j+1); antidiagonal neighbours are x(1,j) and
x(0,j+1). The top left element is x(0,0). In row major order the element x(i',j') comes before
x(i,j) iff i' < i, or i' = i and j' < j. 1 appearing before 2 3 and 4 means that every element
equal to 2, 3 or 4 has an element equal to 1 before it; 2 appearing before 3 means that every
element equal to 3 has an element equal to 2 before it. This reading gives the listed terms
(checked by brute force for n ≤ 3, and for n ≤ 12 through the transfer count used in the proof).

The g.f. is stated for the series of the terms (n ≥ 1), as an identity of formal power series
over ℚ: (sum of a(n) X^n over n ≥ 1) * ((1 - 4X)(1 - 8X - 32X^2)) = X(3 - 28X - 16X^2 + 224X^3).
The closed form is stated over ℝ for n ≥ 2, as Barker states it (n>1, where 2n-3 is not negative).
-/

namespace OMA.S_oeis_a233175

/-- Two elements clash when they are equal or add up to 5. -/
def clash (u v : Fin 6) : Prop := u = v ∨ u.val + v.val = 5

instance (u v : Fin 6) : Decidable (clash u v) := by
  unfold clash
  infer_instance

/-- No element clashes with a horizontal, diagonal or antidiagonal neighbour. -/
def noClash (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j k : Fin n, k.val = j.val + 1 →
    (∀ i : Fin 2, ¬ clash (x j i) (x k i)) ∧
    ¬ clash (x j 0) (x k 1) ∧ ¬ clash (x j 1) (x k 0)

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Decidable (noClash n x) := by
  unfold noClash
  infer_instance

/-- The top left element is zero. -/
def topLeftZero (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j : Fin n, j.val = 0 → x j 0 = 0

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Decidable (topLeftZero n x) := by
  unfold topLeftZero
  infer_instance

/-- 1 appears before 2, 3 and 4 in row major order. -/
def oneFirst (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j : Fin n, ∀ i : Fin 2, (x j i = 2 ∨ x j i = 3 ∨ x j i = 4) →
    ∃ j' : Fin n, ∃ i' : Fin 2, (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) ∧ x j' i' = 1

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Decidable (oneFirst n x) := by
  unfold oneFirst
  infer_instance

/-- 2 appears before 3 in row major order. -/
def twoBeforeThree (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j : Fin n, ∀ i : Fin 2, x j i = 3 →
    ∃ j' : Fin n, ∃ i' : Fin 2, (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) ∧ x j' i' = 2

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Decidable (twoBeforeThree n x) := by
  unfold twoBeforeThree
  infer_instance

/-- A233175(n): the number of such 2 X n arrays. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 2 → Fin 6)).filter
    (fun x => noClash n x ∧ topLeftZero n x ∧ oneFirst n x ∧ twoBeforeThree n x)).card

/-- Barker's conjectures: the g.f. x(3 - 28x - 16x^2 + 224x^3)/((1 - 4x)(1 - 8x - 32x^2)) of
the terms, and a(n) = 2^(2n-3) + (1/32)sqrt(3)(-(4 - 4sqrt(3))^n + (4(1 + sqrt(3)))^n) for n ≥ 2. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 4 * PowerSeries.X) * (1 - 8 * PowerSeries.X - 32 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (3 - 28 * PowerSeries.X - 16 * PowerSeries.X ^ 2 + 224 * PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℝ) = (2 : ℝ) ^ (2 * n - 3) +
        (1 / 32 : ℝ) * Real.sqrt 3 *
          (-((4 - 4 * Real.sqrt 3) ^ n) + (4 * (1 + Real.sqrt 3)) ^ n) := by
  sorry

end OMA.S_oeis_a233175
