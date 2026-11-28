import Mathlib

/-!
# A234875: Number of (n+1) X (1+1) 0..4 arrays with every 2 X 2 subblock having its diagonal sum differing from its antidiagonal sum by 1, with no adjacent elements equal (constant-stress tilted 1 X 1 tilings)

Source: https://oeis.org/A234875
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 32, 68, 128, 268, 512, 1068, 2048, 4268, ...).

Conventions:
* An `(n + 1) X 2` `0..4` array is `x : Fin (n + 1) → Fin 2 → Fin 5`: row `i`, column `j`, entry `x i j` in `0..4`.
* Each `2 X 2` subblock at row pair `(i.castSucc, i.succ)` and column pair `(j.castSucc, j.succ)` has
  top-left `a = x i.castSucc j.castSucc`, top-right `b = x i.castSucc j.succ`,
  bottom-left `c = x i.succ j.castSucc`, bottom-right `d = x i.succ j.succ`.
* In an `(n + 1) X 2` array with `n ≥ 1`, every horizontally or vertically adjacent pair is an edge of some `2 X 2` subblock, so `no adjacent elements equal` holds iff `a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ b ≠ d` on every `2 X 2` subblock; diagonal sum `a + d` differs from antidiagonal sum `b + c` by 1.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Oct 16 2018):
Empirical: a(n) = 5*a(n-2) - 4*a(n-4).
Conjectures from _Colin Barker_, Oct 16 2018: (Start)
G.f.: 4*x*(8 + 17*x - 8*x^2 - 18*x^3) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
a(n) = (4 + (-2)^n + 49*2^n) / 3 for n even.
a(n) = ((-2)^n + 49*2^n) / 3 for n odd.
(End)
The generating function is stated after multiplication by its denominator, whose constant
term is nonzero.
-/

namespace OMA.S_oeis_a234875

open PowerSeries

/-- A `2 X 2` `0..4` subblock has no orthogonally adjacent elements equal and diagonal sum differing from antidiagonal sum by 1. -/
def okBlock (a b c d : Fin 5) : Prop :=
  a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ b ≠ d ∧ |(a.val + d.val : ℤ) - (b.val + c.val : ℤ)| = 1

instance (a b c d : Fin 5) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 2` `0..4` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 5) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 1,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 5) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A234875: Number of (n+1) X (1+1) 0..4 arrays with every 2 X 2 subblock having its diagonal sum differing from its antidiagonal sum by 1, with no adjacent elements equal (constant-stress tilted 1 X 1 tilings). -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

theorem main :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (4 + (-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = ((-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3) := by
  sorry

end OMA.S_oeis_a234875
