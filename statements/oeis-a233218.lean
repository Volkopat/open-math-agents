import Mathlib

/-!
# A233218: Number of 2 X n 0..5 arrays with no element x(i,j) adjacent to value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order.

Source: https://oeis.org/A233218
Credit: @agchua

Colin Barker (Oct 10 2018), in the formula section of A233218:
  Conjectures from Colin Barker, Oct 10 2018: (Start)
  G.f.: x*(3 - 64*x + 234*x^2 - 98*x^3) / ((1 - x)*(1 - 7*x)*(1 - 21*x)).
  a(n) = (2205 + 486*7^n + 125*21^n) / 3528 for n>1.
  (End)
This file states both. The sequence has offset 1 (data 3, 23, 376, 7222, 147019, ...).

A 2 X n array with entries in 0..5 is a function x : Fin n → Fin 2 → Fin 6, where x j i is the
element x(i,j) in row i (0 = top, 1 = bottom) and column j. Two neighbouring elements clash when
one is 5 minus the other (they add up to 5). Horizontal neighbours are x(i,j) and x(i,j+1);
antidiagonal neighbours are x(1,j) and x(0,j+1) (the two ends of a step from lower left to upper
right). The top left element is x(0,0). In row major order the element x(i',j') comes before
x(i,j) iff i' < i, or i' = i and j' < j. 1 appearing before 2 3 and 4 means that every element
equal to 2, 3 or 4 has an element equal to 1 before it; 2 appearing before 3 means that every
element equal to 3 has an element equal to 2 before it. This reading gives the listed terms
(checked by brute force for n ≤ 3, and for n ≤ 8 through the transfer count used in the proof).

The g.f. is stated for the series of the terms (n ≥ 1), as an identity of formal power series
over ℚ: (sum of a(n) X^n over n ≥ 1) * ((1 - X)(1 - 7X)(1 - 21X)) = X(3 - 64X + 234X^2 - 98X^3).
The closed form is stated over ℚ for n ≥ 2, as Barker states it (at n = 1 it is not 3).
-/

namespace OMA.S_oeis_a233218

/-- Two elements clash when they add up to 5. -/
def clash (u v : Fin 6) : Prop := u.val + v.val = 5

instance (u v : Fin 6) : Decidable (clash u v) := by
  unfold clash
  infer_instance

/-- No element clashes with a horizontal or antidiagonal neighbour. -/
def noClash (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j k : Fin n, k.val = j.val + 1 →
    (∀ i : Fin 2, ¬ clash (x j i) (x k i)) ∧ ¬ clash (x j 1) (x k 0)

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

/-- A233218(n): the number of such 2 X n arrays. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 2 → Fin 6)).filter
    (fun x => noClash n x ∧ topLeftZero n x ∧ oneFirst n x ∧ twoBeforeThree n x)).card

/-- Barker's conjectures: the g.f. x(3 - 64x + 234x^2 - 98x^3)/((1 - x)(1 - 7x)(1 - 21x)) of the
terms, and a(n) = (2205 + 486*7^n + 125*21^n)/3528 for n ≥ 2. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 7 * PowerSeries.X) * (1 - 21 * PowerSeries.X)) =
      PowerSeries.X * (3 - 64 * PowerSeries.X + 234 * PowerSeries.X ^ 2 - 98 * PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (2205 + 486 * 7 ^ n + 125 * 21 ^ n) / 3528 := by
  sorry

end OMA.S_oeis_a233218
