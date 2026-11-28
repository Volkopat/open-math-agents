import Mathlib

/-!
# OEIS A267230: arrays over 0..6 with no later element at least the first repeated value

Source: https://oeis.org/A267230 (OEIS Foundation, CC BY-SA 4.0), R. H. Hardin, Jan 12 2016.
Entry, offset 1: Number of length-n 0..6 arrays with no following elements greater than or equal
to the first repeated value. Data: 7, 49, 315, 1981, 12327, 76237, 469623, 2884909, ...
Formula section: Conjectures from Colin Barker, Feb 05 2018:
G.f.: x*(7 - 140*x + 1099*x^2 - 4270*x^3 + 8428*x^4 - 7476*x^5 + 1512*x^6 + 720*x^7) / ((1 - x)*(1
- 2*x)*(1 - 3*x)*(1 - 4*x)*(1 - 5*x)*(1 - 6*x)^2).
a(n) = (-45*2^n - 40*3^n - 45*4^n - 72*5^n + 557*6^n + 5*2^(1 + n)*3^n*n - 72) / 360 for n>1.

Formalization notes:
* An array is `x : Fin n → Fin 7`. The first repeated value is read as the value at the first
  place where an element equals the element right before it, x(i) = x(i+1) with i + 1 minimal;
  every element after position i + 1 must then be smaller than it. Arrays with no such
  repetition are counted. This reading reproduces the entry's data (checked by brute force for
  n = 1..7, and through an exact count for all 20 listed terms).
* The sequence has offset 1, so the generating function is A(x) = Sum_{n >= 1} a(n) x^n; the
  term for n = 0 is set to 0 in the power series. The g.f. is stated as A(x) times the
  denominator equal to the numerator in Q[[x]] (the denominator is invertible there).
* The closed form is stated over Q, with the division as written, for n > 1 as in the entry.
-/

namespace OMA.S_oeis_a267230

/-- The array `x` is counted: whenever `x i = x j` with `j = i + 1` is the first adjacent repeat
(no earlier adjacent pair `x k = x l`, `l = k + 1 < j`), every later element `x t`, `t > j`,
is smaller than the repeated value `x j`. -/
abbrev Good {n : ℕ} (x : Fin n → Fin 7) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → x i = x j →
    (∀ k l : Fin n, k.val + 1 = l.val → l.val < j.val → x k ≠ x l) →
    ∀ t : Fin n, j < t → x t < x j

/-- A267230(n): the number of length-n arrays over 0..6 with no following element
greater than or equal to the first repeated value. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun x : Fin n → Fin 7 => Good x)).card

open PowerSeries in
/-- Barker's conjectures for A267230: the generating function, and the closed form for n > 1. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X) * (1 - 6 * X) ^ 2) =
      X * (7 - 140 * X + 1099 * X ^ 2 - 4270 * X ^ 3 + 8428 * X ^ 4 - 7476 * X ^ 5 +
        1512 * X ^ 6 + 720 * X ^ 7) ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) = (-45 * 2 ^ n - 40 * 3 ^ n - 45 * 4 ^ n - 72 * 5 ^ n + 557 * 6 ^ n +
        5 * 2 ^ (1 + n) * 3 ^ n * n - 72) / 360 := by
  sorry

end OMA.S_oeis_a267230
