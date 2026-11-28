import Mathlib

/-!
# A270145: Number of n X 2 0..7 arrays with some element plus some horizontally, diagonally, antidiagonally or vertically adjacent neighbor totalling seven exactly once

Source: https://oeis.org/A270145
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 8, 1440, 85056, 4126368, 182257536, ...).

Conventions:
* An n X 2 array is `x : Fin n → Fin 2 → Fin 8`: row `i`, column `j`, entry `x i j` in `0..7`.
* Horizontally adjacent pairs: the two entries `x i 0` and `x i 1` of each row `i`.
* Vertically adjacent pairs: the entries `x i j` and `x (i + 1) j` for each column `j`.
  For an array with `m + 1` rows these are indexed by `(i, j) : Fin m × Fin 2`
  (rows `i.castSucc` and `i.succ`).
* Diagonally adjacent pairs: the entries `x i 0` and `x (i + 1) 1`, indexed by `i : Fin m`.
* Antidiagonally adjacent pairs: the entries `x i 1` and `x (i + 1) 0`, indexed by `i : Fin m`.
* Totalling seven exactly once: exactly one unordered pair of adjacent entries sums to 7.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence by R. H. Hardin in the formula section, and Colin Barker, Jan
30 2019): a(n) = 66*a(n-1) - 1021*a(n-2) - 2244*a(n-3) - 1156*a(n-4) for n>5; G.f.: 8*x*(1 -
x)^2*(1 + 116*x + 4*x^2) / ((1 + x)^2*(1 - 34*x)^2).
a(n) = (48*(-383214*(-1)^n - 2660911*34^n + 35*(363562*(-1)^n + 115797*34^n)*n)) / 210644875 for n>1.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a270145

open PowerSeries

/-- The number of horizontally, diagonally, antidiagonally or vertically adjacent pairs of the
array `x` (with `m + 1` rows) totalling seven. -/
def pairsTotallingSeven (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 8) : ℕ :=
  (Finset.univ.filter (fun i : Fin (m + 1) => (x i 0 : ℕ) + (x i 1 : ℕ) = 7)).card +
    (Finset.univ.filter
      (fun p : Fin m × Fin 2 => (x p.1.castSucc p.2 : ℕ) + (x p.1.succ p.2 : ℕ) = 7)).card +
    (Finset.univ.filter (fun i : Fin m => (x i.castSucc 0 : ℕ) + (x i.succ 1 : ℕ) = 7)).card +
    (Finset.univ.filter (fun i : Fin m => (x i.castSucc 1 : ℕ) + (x i.succ 0 : ℕ) = 7)).card

/-- A270145: the number of n X 2 arrays over `0..7` with exactly one adjacent pair totalling
seven. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin (m + 1) → Fin 2 → Fin 8 => pairsTotallingSeven m x = 1)).card

theorem main :
    (∀ n : ℕ, 6 ≤ n →
      (a n : ℤ) = 66 * a (n - 1) - 1021 * a (n - 2) - 2244 * a (n - 3) - 1156 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) ^ 2 * (1 - 34 * X) ^ 2) =
      8 * X * (1 - X) ^ 2 * (1 + 116 * X + 4 * X ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = 48 * (-383214 * (-1) ^ n - 2660911 * 34 ^ n + 35 * (363562 * (-1) ^ n + 115797 * 34 ^ n) * n) / 210644875) := by
  sorry

end OMA.S_oeis_a270145
