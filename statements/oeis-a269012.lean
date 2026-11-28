import Mathlib

/-!
# A269012: Number of 2 X n binary arrays with some element plus some horizontally, diagonally or antidiagonally adjacent neighbor totalling two exactly once

Source: https://oeis.org/A269012
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 0, 4, 8, 36, 88, ...).

Conventions:
* A 2 X n array is `x : Fin 2 → Fin n → Fin 2`: row `i`, column `j`, entry `x i j` in `0..1`.
* Horizontally adjacent pairs: the entries `x i j` and `x i (j + 1)` for each row `i`.
  For an array with `m + 1` columns these are indexed by `(i, j) : Fin 2 × Fin m`
  (columns `j.castSucc` and `j.succ`).
* Diagonally adjacent pairs: the entries `x 0 j` and `x 1 (j + 1)`, indexed by `j : Fin m`.
* Antidiagonally adjacent pairs: the entries `x 1 j` and `x 0 (j + 1)`, indexed by `j : Fin m`.
* Totalling two exactly once: exactly one unordered pair of adjacent entries sums to 2.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
18 2019): a(n) = 2*a(n-1) + 5*a(n-2) - 6*a(n-3) - 9*a(n-4); G.f.: 4*x^2 / (1 - x - 3*x^2)^2.
a(n) = 4*(-((1/2)*(1+sqrt(13)))^n*(sqrt(13)-13*n) + ((1/2)*(1-sqrt(13)))^n*(sqrt(13)+13*n)) / 169.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
The closed form is stated in `ℝ`, where `-u ^ n` means `-(u ^ n)` as in the OEIS text.
-/

namespace OMA.S_oeis_a269012

open PowerSeries

/-- The number of horizontally, diagonally or antidiagonally adjacent pairs of the array `x`
(with `m + 1` columns) totalling two. -/
def pairsTotallingTwo (m : ℕ) (x : Fin 2 → Fin (m + 1) → Fin 2) : ℕ :=
  (Finset.univ.filter
      (fun p : Fin 2 × Fin m => (x p.1 p.2.castSucc : ℕ) + (x p.1 p.2.succ : ℕ) = 2)).card +
    (Finset.univ.filter (fun j : Fin m => (x 0 j.castSucc : ℕ) + (x 1 j.succ : ℕ) = 2)).card +
    (Finset.univ.filter (fun j : Fin m => (x 1 j.castSucc : ℕ) + (x 0 j.succ : ℕ) = 2)).card

/-- A269012: the number of 2 X n arrays over `0..1` with exactly one adjacent pair totalling
two. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin 2 → Fin (m + 1) → Fin 2 => pairsTotallingTwo m x = 1)).card

theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 2 * a (n - 1) + 5 * a (n - 2) - 6 * a (n - 3) - 9 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 3 * X ^ 2) ^ 2 =
      4 * X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = 4 * (-((1 / 2) * (1 + Real.sqrt 13)) ^ n * (Real.sqrt 13 - 13 * n) +
        ((1 / 2) * (1 - Real.sqrt 13)) ^ n * (Real.sqrt 13 + 13 * n)) / 169) := by
  sorry

end OMA.S_oeis_a269012
