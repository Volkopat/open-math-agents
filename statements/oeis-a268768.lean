import Mathlib

/-!
# A268768: Number of n X 2 0..2 arrays with some element plus some horizontally, vertically, diagonally or antidiagonally adjacent neighbor totalling two exactly once

Source: https://oeis.org/A268768
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 3, 12, 32, 100, 248, ...).

Conventions:
* An n X 2 array is `x : Fin n → Fin 2 → Fin 3`: row `i`, column `j`, entry `x i j` in `0..2`.
* Horizontally adjacent pairs: the two entries `x i 0` and `x i 1` of each row `i`.
* Vertically adjacent pairs: the entries `x i j` and `x (i + 1) j` for each column `j`.
  For an array with `m + 1` rows these are indexed by `(i, j) : Fin m × Fin 2`
  (rows `i.castSucc` and `i.succ`).
* Diagonally adjacent pairs: the entries `x i 0` and `x (i + 1) 1`, indexed by `i : Fin m`.
* Antidiagonally adjacent pairs: the entries `x i 1` and `x (i + 1) 0`, indexed by `i : Fin m`.
* Totalling two exactly once: exactly one unordered pair of adjacent entries sums to 2.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
14 2019): a(n) = 2*a(n-1) + 3*a(n-2) - 4*a(n-3) - 4*a(n-4) for n>5; G.f.: x*(3 + 6*x - x^2 +
12*x^3 + 12*x^4) / ((1 + x)^2*(1 - 2*x)^2).
a(n) = (4/27)*(7*((-1)^n-2^n) + 3*((-1)^n + 2^(2+n))*n) for n>1.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a268768

open PowerSeries

/-- The number of horizontally, vertically, diagonally or antidiagonally adjacent pairs of the
array `x` (with `m + 1` rows) totalling two. -/
def pairsTotallingTwo (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin (m + 1) => (x i 0 : ℕ) + (x i 1 : ℕ) = 2)).card +
    (Finset.univ.filter
      (fun p : Fin m × Fin 2 => (x p.1.castSucc p.2 : ℕ) + (x p.1.succ p.2 : ℕ) = 2)).card +
    (Finset.univ.filter (fun i : Fin m => (x i.castSucc 0 : ℕ) + (x i.succ 1 : ℕ) = 2)).card +
    (Finset.univ.filter (fun i : Fin m => (x i.castSucc 1 : ℕ) + (x i.succ 0 : ℕ) = 2)).card

/-- A268768: the number of n X 2 arrays over `0..2` with exactly one adjacent pair totalling
two. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin (m + 1) → Fin 2 → Fin 3 => pairsTotallingTwo m x = 1)).card

theorem main :
    (∀ n : ℕ, 6 ≤ n →
      (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) - 4 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2) =
      X * (3 + 6 * X - X ^ 2 + 12 * X ^ 3 + 12 * X ^ 4)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = 4 / 27 * (7 * ((-1) ^ n - 2 ^ n) + 3 * ((-1) ^ n + 2 ^ (2 + n)) * n)) := by
  sorry

end OMA.S_oeis_a268768
