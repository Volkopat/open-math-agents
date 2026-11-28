import Mathlib

/-!
# A269822: Number of n X 1 0..4 arrays with some element plus some horizontally, diagonally, antidiagonally or vertically adjacent neighbor totalling four exactly once

Source: https://oeis.org/A269822
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 0, 5, 40, 240, 1280, ...).

Conventions:
* An n X 1 array is a column `x : Fin n → Fin 5` of entries in `0..4`.
* In a single column the only adjacent neighbors are vertical: the entries at rows `i` and
  `i + 1`. Horizontal, diagonal and antidiagonal neighbors do not exist.
* Totalling four exactly once: exactly one unordered pair of adjacent entries sums to 4.
  For a column of length `m + 1` these pairs are indexed by `i : Fin m`
  (rows `i.castSucc` and `i.succ`).
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Mar 22 2018):
a(n) = 8*a(n-1) - 16*a(n-2); G.f.: 5*x^2 / (1 - 4*x)^2; a(n) = 5*4^(n-2)*(n-1).
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a269822

open PowerSeries

/-- The number of vertically adjacent pairs of the column `x` (length `m + 1`) totalling four. -/
def pairsTotallingFour (m : ℕ) (x : Fin (m + 1) → Fin 5) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (x i.castSucc : ℕ) + (x i.succ : ℕ) = 4)).card

/-- A269822: the number of n X 1 arrays over `0..4` with exactly one adjacent pair totalling four. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 => (Finset.univ.filter (fun x : Fin (m + 1) → Fin 5 => pairsTotallingFour m x = 1)).card

theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 16 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 4 * X) ^ 2 = 5 * X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 5 * 4 ^ (n - 2) * (n - 1)) := by
  sorry

end OMA.S_oeis_a269822
