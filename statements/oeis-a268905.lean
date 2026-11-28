import Mathlib

/-!
# A268905: Number of 2 X n 0..2 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling two exactly once

Source: https://oeis.org/A268905
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 0, 36, 168, 696, 2664, ...).

Conventions:
* A 2 X n array is `x : Fin 2 → Fin n → Fin 3`: row `i`, column `j`, entry `x i j` in `0..2`.
* Horizontally adjacent pairs: the entries `x i j` and `x i (j + 1)` for each row `i`.
  For an array with `m + 1` columns these are indexed by `(i, j) : Fin 2 × Fin m`
  (columns `j.castSucc` and `j.succ`).
* Antidiagonally adjacent pairs: the entries `x 1 j` and `x 0 (j + 1)`, indexed by `j : Fin m`.
  (Reflecting the rows swaps diagonal and antidiagonal pairs and fixes the other pairs,
  so the count does not depend on which of the two directions is called antidiagonal.)
* Totalling two exactly once: exactly one unordered pair of adjacent entries sums to 2.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
16 2019): a(n) = 6*a(n-1) - 9*a(n-2) for n>4; G.f.: 12*x^2*(3 - x)*(1 - x) / (1 - 3*x)^2.
a(n) = 8*3^(n-3) * (8*n-3) for n>2.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a268905

open PowerSeries

/-- The number of horizontally or antidiagonally adjacent pairs of the array `x` (with `m + 1`
columns) totalling two. -/
def pairsTotallingTwo (m : ℕ) (x : Fin 2 → Fin (m + 1) → Fin 3) : ℕ :=
  (Finset.univ.filter
      (fun p : Fin 2 × Fin m => (x p.1 p.2.castSucc : ℕ) + (x p.1 p.2.succ : ℕ) = 2)).card +
    (Finset.univ.filter (fun j : Fin m => (x 1 j.castSucc : ℕ) + (x 0 j.succ : ℕ) = 2)).card

/-- A268905: the number of 2 X n arrays over `0..2` with exactly one adjacent pair totalling
two. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin 2 → Fin (m + 1) → Fin 3 => pairsTotallingTwo m x = 1)).card

theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 6 * a (n - 1) - 9 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 3 * X) ^ 2 =
      12 * X ^ 2 * (3 - X) * (1 - X)) ∧
    (∀ n : ℕ, 3 ≤ n →
      (a n : ℚ) = 8 * 3 ^ (n - 3) * (8 * n - 3)) := by
  sorry

end OMA.S_oeis_a268905
