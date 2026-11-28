import Mathlib

/-!
# A268900: Number of n X 4 0..2 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling two exactly once

Source: https://oeis.org/A268900
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 36, 696, 9720, 118584, 1347192, ...).

Conventions:
* An n X 4 array is `x : Fin n → Fin 4 → Fin 3`: row `i`, column `j`, entry `x i j` in `0..2`.
* Horizontally adjacent pairs: `x i j` and `x i (j + 1)`, indexed by `(i, j) : Fin (m + 1) × Fin 3`
  for an array with `m + 1` rows (columns `j.castSucc` and `j.succ`).
* Antidiagonally adjacent pairs: `x i (j + 1)` and `x (i + 1) j`, indexed by
  `(i, j) : Fin m × Fin 3`.
  (Reflecting the columns swaps diagonal and antidiagonal pairs and fixes the other pairs,
  so the count does not depend on which of the two directions is called antidiagonal.)
* Totalling two exactly once: exactly one unordered pair of adjacent entries sums to 2.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
16 2019): a(n) = 18*a(n-1) - 81*a(n-2) for n>3; G.f.: 12*x*(3 + 4*x + 9*x^2) / (1 - 9*x)^2.
a(n) = 8 * 3^(2*n-3) * (16*n-3) for n>1.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a268900

open PowerSeries

/-- The number of horizontally or antidiagonally adjacent pairs of the array `x` (with `m + 1`
rows) totalling two. -/
def pairsTotallingTwo (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 3) : ℕ :=
  (Finset.univ.filter
      (fun p : Fin (m + 1) × Fin 3 => (x p.1 p.2.castSucc : ℕ) + (x p.1 p.2.succ : ℕ) = 2)).card +
    (Finset.univ.filter
      (fun p : Fin m × Fin 3 => (x p.1.castSucc p.2.succ : ℕ) + (x p.1.succ p.2.castSucc : ℕ) = 2)).card

/-- A268900: the number of n X 4 arrays over `0..2` with exactly one adjacent pair totalling
two. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin (m + 1) → Fin 4 → Fin 3 => pairsTotallingTwo m x = 1)).card

theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (a n : ℤ) = 18 * a (n - 1) - 81 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 9 * X) ^ 2 =
      12 * X * (3 + 4 * X + 9 * X ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 8 * 3 ^ (2 * n - 3) * (16 * n - 3)) := by
  sorry

end OMA.S_oeis_a268900
