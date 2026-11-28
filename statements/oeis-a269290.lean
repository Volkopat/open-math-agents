import Mathlib

/-!
# A269290: Number of 2 X n 0..3 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling three no more than once

Source: https://oeis.org/A269290
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 16, 216, 2124, 19188, 164556, ...).

Conventions:
* A 2 X n array is `x : Fin 2 → Fin n → Fin 4`: row `i`, column `j`, entry `x i j` in `0..3`.
* Horizontally adjacent pairs: the entries `x i j` and `x i (j + 1)` for each row `i`.
  For an array with `m + 1` columns these are indexed by `(i, j) : Fin 2 × Fin m`
  (columns `j.castSucc` and `j.succ`).
* Antidiagonally adjacent pairs: the entries `x 1 j` and `x 0 (j + 1)`, indexed by `j : Fin m`.
  (Reflecting the rows swaps diagonal and antidiagonal pairs and fixes the other pairs,
  so the count does not depend on which of the two directions is called antidiagonal.)
* Totalling three no more than once: at most one unordered pair of adjacent entries sums
  to 3.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
21 2019): a(n) = 14*a(n-1) - 49*a(n-2) for n>4; G.f.: 4*x*(4 - 2*x - 29*x^2 + 9*x^3) / (1 -
7*x)^2.
a(n) = 36 * 7^(n-4) * (120*n+53) for n>2.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
The closed form has a negative exponent at `n = 3`, so it is stated in `ℚ` with
integer exponents.
-/

namespace OMA.S_oeis_a269290

open PowerSeries

/-- The number of horizontally or antidiagonally adjacent pairs of the array `x` (with `m + 1`
columns) totalling three. -/
def pairsTotallingThree (m : ℕ) (x : Fin 2 → Fin (m + 1) → Fin 4) : ℕ :=
  (Finset.univ.filter
      (fun p : Fin 2 × Fin m => (x p.1 p.2.castSucc : ℕ) + (x p.1 p.2.succ : ℕ) = 3)).card +
    (Finset.univ.filter (fun j : Fin m => (x 1 j.castSucc : ℕ) + (x 0 j.succ : ℕ) = 3)).card

/-- A269290: the number of 2 X n arrays over `0..3` with at most one adjacent pairs totalling
three. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin 2 → Fin (m + 1) → Fin 4 => pairsTotallingThree m x ≤ 1)).card

theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 14 * a (n - 1) - 49 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X) ^ 2 =
      4 * X * (4 - 2 * X - 29 * X ^ 2 + 9 * X ^ 3)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 36 * 7 ^ ((n : ℤ) - 4) * (120 * n + 53)) := by
  sorry

end OMA.S_oeis_a269290
