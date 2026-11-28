import Mathlib

/-!
# A269202: Number of 2 X n 0..3 arrays with some element plus some horizontally, diagonally or antidiagonally adjacent neighbor totalling three no more than once

Source: https://oeis.org/A269202
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 16, 180, 1284, 9612, 68052, ...).

Conventions:
* A 2 X n array is `x : Fin 2 → Fin n → Fin 4`: row `i`, column `j`, entry `x i j` in `0..3`.
* Horizontally adjacent pairs: the entries `x i j` and `x i (j + 1)` for each row `i`.
  For an array with `m + 1` columns these are indexed by `(i, j) : Fin 2 × Fin m`
  (columns `j.castSucc` and `j.succ`).
* Diagonally adjacent pairs: the entries `x 0 j` and `x 1 (j + 1)`, indexed by `j : Fin m`.
* Antidiagonally adjacent pairs: the entries `x 1 j` and `x 0 (j + 1)`, indexed by `j : Fin m`.
* Totalling three no more than once: at most one unordered pair of adjacent entries sums
  to 3.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
20 2019): a(n) = 10*a(n-1) - 13*a(n-2) - 60*a(n-3) - 36*a(n-4); G.f.: 4*x*(4 + 5*x - 77*x^2 +
18*x^3) / ((1 + x)^2*(1 - 6*x)^2).
a(n) = (6*(-678*(-1)^n+335*6^n) + 56*(144*(-1)^n+25*6^n)*n) / 1029.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a269202

open PowerSeries

/-- The number of horizontally, diagonally or antidiagonally adjacent pairs of the array `x`
(with `m + 1` columns) totalling three. -/
def pairsTotallingThree (m : ℕ) (x : Fin 2 → Fin (m + 1) → Fin 4) : ℕ :=
  (Finset.univ.filter
      (fun p : Fin 2 × Fin m => (x p.1 p.2.castSucc : ℕ) + (x p.1 p.2.succ : ℕ) = 3)).card +
    (Finset.univ.filter (fun j : Fin m => (x 0 j.castSucc : ℕ) + (x 1 j.succ : ℕ) = 3)).card +
    (Finset.univ.filter (fun j : Fin m => (x 1 j.castSucc : ℕ) + (x 0 j.succ : ℕ) = 3)).card

/-- A269202: the number of 2 X n arrays over `0..3` with at most one adjacent pairs totalling
three. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin 2 → Fin (m + 1) → Fin 4 => pairsTotallingThree m x ≤ 1)).card

theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 10 * a (n - 1) - 13 * a (n - 2) - 60 * a (n - 3) - 36 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) ^ 2 * (1 - 6 * X) ^ 2) =
      4 * X * (4 + 5 * X - 77 * X ^ 2 + 18 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (6 * (-678 * (-1) ^ n + 335 * 6 ^ n) + 56 * (144 * (-1) ^ n + 25 * 6 ^ n) * n) / 1029) := by
  sorry

end OMA.S_oeis_a269202
