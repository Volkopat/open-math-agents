import Mathlib

/-!
# A269284: Number of n X 3 0..3 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling three no more than once

Source: https://oeis.org/A269284
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 60, 2124, 62748, 1698732, 43674876, ...).

Conventions:
* An n X 3 array is `x : Fin n → Fin 3 → Fin 4`: row `i`, column `j`, entry `x i j` in `0..3`.
* Horizontally adjacent pairs: `x i j` and `x i (j + 1)`, indexed by `(i, j) : Fin (m + 1) × Fin 2`
  for an array with `m + 1` rows (columns `j.castSucc` and `j.succ`).
* Antidiagonally adjacent pairs: `x i (j + 1)` and `x (i + 1) j`, indexed by
  `(i, j) : Fin m × Fin 2`.
  (Reflecting the columns swaps diagonal and antidiagonal pairs and fixes the other pairs,
  so the count does not depend on which of the two directions is called antidiagonal.)
* Totalling three no more than once: at most one unordered pair of adjacent entries sums
  to 3.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
21 2019): a(n) = 42*a(n-1) - 441*a(n-2); G.f.: 12*x*(5 - 33*x) / (1 - 21*x)^2.
a(n) = 4 * 3^n * 7^(n-2) * (24*n+11).
The generating function is stated after multiplication by its denominator, whose constant
term is one.
The closed form has a negative exponent at `n = 1`, so it is stated in `ℚ` with
integer exponents.
-/

namespace OMA.S_oeis_a269284

open PowerSeries

/-- The number of horizontally or antidiagonally adjacent pairs of the array `x` (with `m + 1`
rows) totalling three. -/
def pairsTotallingThree (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 4) : ℕ :=
  (Finset.univ.filter
      (fun p : Fin (m + 1) × Fin 2 => (x p.1 p.2.castSucc : ℕ) + (x p.1 p.2.succ : ℕ) = 3)).card +
    (Finset.univ.filter
      (fun p : Fin m × Fin 2 => (x p.1.castSucc p.2.succ : ℕ) + (x p.1.succ p.2.castSucc : ℕ) = 3)).card

/-- A269284: the number of n X 3 arrays over `0..3` with at most one adjacent pairs totalling
three. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin (m + 1) → Fin 3 → Fin 4 => pairsTotallingThree m x ≤ 1)).card

theorem main :
    (∀ n : ℕ, 3 ≤ n →
      (a n : ℤ) = 42 * a (n - 1) - 441 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 21 * X) ^ 2 =
      12 * X * (5 - 33 * X)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * 3 ^ n * 7 ^ ((n : ℤ) - 2) * (24 * n + 11)) := by
  sorry

end OMA.S_oeis_a269284
