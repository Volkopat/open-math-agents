import Mathlib

/-!
# OEIS A267227: arrays over 0..3 with no later element at least the first repeated value

Source: https://oeis.org/A267227 (OEIS Foundation, CC BY-SA 4.0), R. H. Hardin, Jan 12 2016.
Entry, offset 1: Number of length-n 0..3 arrays with no following elements greater than or equal
to the first repeated value. Data: 4, 16, 54, 176, 564, 1790, 5646, 17732, ...
Formula section: Conjectures from Colin Barker, Feb 05 2018:
G.f.: 2*x*(2 - 10*x + 13*x^2 - x^3 - 3*x^4) / ((1 - x)*(1 - 2*x)*(1 - 3*x)^2).
a(n) = (-9 - 9*2^n + 11*3^(1+n) + 2*3^n*n) / 18 for n>1.

Formalization notes:
* An array is `x : Fin n → Fin 4`. The first repeated value is read as the value at the first
  place where an element equals the element right before it, x(i) = x(i+1) with i + 1 minimal;
  every element after position i + 1 must then be smaller than it. Arrays with no such
  repetition are counted. This reading reproduces the entry's data (checked by brute force for
  n = 1..10, and through an exact count for all 25 listed terms).
* The sequence has offset 1, so the generating function is A(x) = Sum_{n >= 1} a(n) x^n; the
  term for n = 0 is set to 0 in the power series. The g.f. is stated as A(x) times the
  denominator equal to the numerator in Q[[x]] (the denominator is invertible there).
* The closed form is stated over Q, with the division as written.
-/

namespace OMA.S_oeis_a267227

/-- The array `x` is counted: whenever `x i = x j` with `j = i + 1` is the first adjacent repeat
(no earlier adjacent pair `x k = x l`, `l = k + 1 < j`), every later element `x t`, `t > j`,
is smaller than the repeated value `x j`. -/
abbrev Good {n : ℕ} (x : Fin n → Fin 4) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → x i = x j →
    (∀ k l : Fin n, k.val + 1 = l.val → l.val < j.val → x k ≠ x l) →
    ∀ t : Fin n, j < t → x t < x j

/-- A267227(n): the number of length-n arrays over 0..3 with no following element greater than
or equal to the first repeated value. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun x : Fin n → Fin 4 => Good x)).card

open PowerSeries in
/-- Barker's conjectures for A267227: the generating function, and the closed form for n > 1. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) * (1 - 2 * X) * (1 - 3 * X) ^ 2) =
      2 * X * (2 - 10 * X + 13 * X ^ 2 - X ^ 3 - 3 * X ^ 4) ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) = (-9 - 9 * 2 ^ n + 11 * 3 ^ (1 + n) + 2 * 3 ^ n * n) / 18 := by
  sorry

end OMA.S_oeis_a267227
