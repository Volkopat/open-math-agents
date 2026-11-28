import Mathlib

/-!
# A251130: Number of (n+1) X (1+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements

Source: https://oeis.org/A251130
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 40, 133, 369, 919, 2129, 4699, 10033, 20947, ...).

Conventions:
* An `(n + 1) X 2` `0..2` array is `x : Fin (n + 1) → Fin 2 → Fin 3`: row `i`, column `j`, entry `x i j` in `0..2`.
* Each `2 X 2` subblock at row pair `(i.castSucc, i.succ)` and column pair `(j.castSucc, j.succ)` has
  top-left `a = x i.castSucc j.castSucc`, top-right `b = x i.castSucc j.succ`,
  bottom-left `c = x i.succ j.castSucc`, bottom-right `d = x i.succ j.succ`.
* Diagonal elements are `(a, d)` and antidiagonal elements are `(b, c)`; no `2 X 2` subblock has `a + d > max b c`.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Nov 26 2018):
Empirical: a(n) = 5*a(n-1) - 8*a(n-2) + 2*a(n-3) + 7*a(n-4) - 7*a(n-5) + 2*a(n-6).
Conjectures from _Colin Barker_, Nov 26 2018: (Start)
G.f.: x*(40 - 67*x + 24*x^2 + 58*x^3 - 60*x^4 + 17*x^5) / ((1 - x)^4*(1 + x)*(1 - 2*x)).
a(n) = (-957 + (-1)^n + 529*2^(1+n) - 540*n - 126*n^2 - 12*n^3) / 12.
(End)
The generating function is stated after multiplication by its denominator, whose constant
term is nonzero.
-/

namespace OMA.S_oeis_a251130

open PowerSeries

/-- A `2 X 2` `0..2` subblock does not have diagonal sum greater than antidiagonal maximum. -/
def okBlock (a b c d : Fin 3) : Prop :=
  ¬ (a.val + d.val > max b.val c.val)

instance (a b c d : Fin 3) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 2` `0..2` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 3) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 1,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 3) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A251130: Number of (n+1) X (1+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

theorem main :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 8 * a (n - 2) + 2 * a (n - 3) + 7 * a (n - 4) - 7 * a (n - 5) + 2 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) * (1 - 2 * X)) =
      X * (40 - 67 * X + 24 * X ^ 2 + 58 * X ^ 3 - 60 * X ^ 4 + 17 * X ^ 5)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-957 + (-1 : ℚ) ^ n + 529 * (2 : ℚ) ^ (1 + n) - 540 * n - 126 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) / 12) := by
  sorry

end OMA.S_oeis_a251130
