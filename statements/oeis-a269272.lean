import Mathlib

/-!
# A269272: Number of n X 4 0..3 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling three exactly once

Source: https://oeis.org/A269272

OEIS Foundation and contributors, CC BY-SA 4.0.
Offset 1 (data 108, 13896, 1104264, 74853576, ...).

Conventions:
* An n X 4 array is `x : Fin n → Fin 4 → Fin 4`: row `i`, column `j`, entry `x i j` in `0..3`.
* Horizontally adjacent pairs: the entries `x i j` and `x i (j + 1)` of each row `i`, indexed by
  `(i, j) : Fin (m + 1) × Fin 3` (columns `j.castSucc` and `j.succ`).
* Antidiagonally adjacent pairs: the entries `x i (j + 1)` and `x (i + 1) j` (the lower-left
  neighbour), indexed by `(i, j) : Fin m × Fin 3` (rows `i.castSucc`, `i.succ` and columns
  `j.succ`, `j.castSucc`).
* Totalling three exactly once: exactly one unordered pair of adjacent entries sums to 3.
  (A direct count with this reading reproduces the listed data.)
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Jan 20 2019):
a(n) = 98*a(n-1) - 2401*a(n-2) for n > 3; G.f.: 36*x*(3 + 92*x + 49*x^2) / (1 - 49*x)^2;
a(n) = 72 * 49^(n-2) * (120*n-47) for n>1.
The generating function is stated after multiplication by its denominator, whose constant
term is one. The closed form has negative exponents at small `n`, so it is stated in `ℚ`
with integer exponents.
-/

namespace OMA.S_oeis_a269272

open PowerSeries

/-- The number of horizontally or antidiagonally adjacent pairs of the array `x` (with `m + 1` rows)
totalling three. -/
def pairsTotallingThree (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 4) : ℕ :=
  (Finset.univ.filter (fun p : Fin (m + 1) × Fin 3 =>
      (x p.1 p.2.castSucc : ℕ) + (x p.1 p.2.succ : ℕ) = 3)).card +
    (Finset.univ.filter (fun p : Fin m × Fin 3 =>
      (x p.1.castSucc p.2.succ : ℕ) + (x p.1.succ p.2.castSucc : ℕ) = 3)).card

/-- A269272: the number of n X 4 arrays over `0..3` with exactly one adjacent pair totalling
three. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin (m + 1) → Fin 4 → Fin 4 => pairsTotallingThree m x = 1)).card

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 98 * a (n - 1) - 2401 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 49 * X) ^ 2 =
      36 * X * (3 + 92 * X + 49 * X ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 72 * 49 ^ ((n : ℤ) - 2) * (120 * n - 47)) := by
  sorry

end OMA.S_oeis_a269272
