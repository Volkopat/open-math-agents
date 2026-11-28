import Mathlib

/-!
# A250791: Number of (n+1) X (2+1) 0..1 arrays with nondecreasing min(x(i,j),x(i,j-1)) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250791
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 24, 66, 180, 490, 1336, 3646, 9956, 27194, ...).

Conventions:
* An `(n + 1) X 3` `0..1` array is `x : Fin (n + 1) → Fin 3 → Fin 2`: row `i`, column `j`, entry `x i j` in `0..1`.
* Each `2 X 2` subblock at row pair `(i.castSucc, i.succ)` and column pair `(j.castSucc, j.succ)` has
  top-left `a = x i.castSucc j.castSucc`, top-right `b = x i.castSucc j.succ`,
  bottom-left `c = x i.succ j.castSucc`, bottom-right `d = x i.succ j.succ`.
* In each `2 X 2` subblock, `min(x(i,j), x(i,j-1))` nondecreasing in the `i` direction means `min a b ≤ min c d`, and `|x(i,j) - x(i-1,j)|` nondecreasing in the `j` direction means `|c - a| ≤ |d - b|`; every such comparison lies in exactly one `2 X 2` subblock.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Nov 20 2018):
Empirical: a(n) = 4*a(n-1) - 3*a(n-2) - 2*a(n-3) + 2*a(n-4).
Conjectures from _Colin Barker_, Nov 20 2018: (Start)
G.f.: 2*x*(12 - 15*x - 6*x^2 + 8*x^3) / ((1 - x)^2*(1 - 2*x - 2*x^2)).
a(n) = (-6 + (39-23*sqrt(3))*(1-sqrt(3))^n + 39*(1+sqrt(3))^n + 23*sqrt(3)*(1+sqrt(3))^n + 6*n) / 9.
(End)
The generating function is stated after multiplication by its denominator, whose constant
term is nonzero.
-/

namespace OMA.S_oeis_a250791

open PowerSeries

/-- A `2 X 2` binary subblock `(a, b / c, d)` has `min a b ≤ min c d` and `|c - a| ≤ |d - b|`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  min a.val b.val ≤ min c.val d.val ∧ |(c.val : ℤ) - a.val| ≤ |(d.val : ℤ) - b.val|

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 3` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 2,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250791: Number of (n+1) X (2+1) 0..1 arrays with nondecreasing min(x(i,j),x(i,j-1)) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

theorem main :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 3 * a (n - 2) - 2 * a (n - 3) + 2 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X - 2 * X ^ 2)) =
      2 * X * (12 - 15 * X - 6 * X ^ 2 + 8 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (-6 + (39 - 23 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n + 39 * (1 + Real.sqrt 3) ^ n + 23 * Real.sqrt 3 * (1 + Real.sqrt 3) ^ n + 6 * (n : ℝ)) / 9) := by
  sorry

end OMA.S_oeis_a250791
