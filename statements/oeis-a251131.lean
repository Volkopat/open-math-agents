import Mathlib

/-!
# A251131: Number of (n+1) X (2+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements

Source: https://oeis.org/A251131
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 133, 416, 1002, 2264, 4786, 9786, 19548, 38674, ...).

Conventions:
* An `(n + 1) X 3` `0..2` array is `x : Fin (n + 1) → Fin 3 → Fin 3`: row `i`, column `j`, entry `x i j` in `0..2`.
* Each `2 X 2` subblock at row pair `(i.castSucc, i.succ)` and column pair `(j.castSucc, j.succ)` has
  top-left `a = x i.castSucc j.castSucc`, top-right `b = x i.castSucc j.succ`,
  bottom-left `c = x i.succ j.castSucc`, bottom-right `d = x i.succ j.succ`.
* Diagonal elements are `(a, d)` and antidiagonal elements are `(b, c)`; no `2 X 2` subblock has `a + d > max b c`.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Nov 26 2018):
Empirical: a(n) = 6*a(n-1) - 13*a(n-2) + 10*a(n-3) + 5*a(n-4) - 14*a(n-5) + 9*a(n-6) - 2*a(n-7) for n>9.
Conjectures from _Colin Barker_, Nov 26 2018: (Start)
G.f.: x*(133 - 382*x + 235*x^2 + 330*x^3 - 597*x^4 + 264*x^5 + 27*x^6 - 26*x^7 - 4*x^8) / ((1 - x)^5*(1 + x)*(1 - 2*x)).
a(n) = (-873 + 49*(-1)^n + 841*2^(1+n) - 614*n - 11*n^2 + 38*n^3 + 5*n^4) / 12 for n>2.
(End)
The generating function is stated after multiplication by its denominator, whose constant
term is nonzero.
-/

namespace OMA.S_oeis_a251131

open PowerSeries

/-- A `2 X 2` `0..2` subblock does not have diagonal sum greater than antidiagonal maximum. -/
def okBlock (a b c d : Fin 3) : Prop :=
  ¬ (a.val + d.val > max b.val c.val)

instance (a b c d : Fin 3) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 3` `0..2` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 3) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 2,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 3) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A251131: Number of (n+1) X (2+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

theorem main :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
      X * (133 - 382 * X + 235 * X ^ 2 + 330 * X ^ 3 - 597 * X ^ 4 + 264 * X ^ 5 + 27 * X ^ 6 - 26 * X ^ 7 - 4 * X ^ 8)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (-873 + 49 * (-1 : ℚ) ^ n + 841 * (2 : ℚ) ^ (1 + n) - 614 * n - 11 * (n : ℚ) ^ 2 + 38 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12) := by
  sorry

end OMA.S_oeis_a251131
