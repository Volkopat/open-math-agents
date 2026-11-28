import Mathlib

/-!
# A269103: Number of n X 2 0..3 arrays with some element plus some horizontally or vertically adjacent neighbor totalling three no more than once

Source: https://oeis.org/A269103

OEIS Foundation and contributors, CC BY-SA 4.0.
Offset 1 (data 16, 180, 1740, 15540, 132300, ...).

Conventions:
* An n X 2 array is `x : Fin n → Fin 2 → Fin 4`: row `i`, column `j`, entry `x i j` in `0..3`.
* Horizontally adjacent pairs: the two entries `x i 0` and `x i 1` of each row `i`.
* Vertically adjacent pairs: the entries `x i j` and `x (i + 1) j` for each column `j`.
  For an array with `m + 1` rows these are indexed by `(i, j) : Fin m × Fin 2`
  (rows `i.castSucc` and `i.succ`).
* Totalling three no more than once: at most one unordered pair of adjacent entries sums to 3.
  (A direct count with this reading reproduces the listed data.)
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Mar 21 2018):
a(n) = 14*a(n-1) - 49*a(n-2) for n>3; G.f.: 4*x*(4 - 11*x + x^2) / (1 - 7*x)^2;
a(n) = 60*7^(n-3)*(8*n+5) for n>1.
The generating function is stated after multiplication by its denominator, whose constant
term is one. The closed form has negative exponents at small `n`, so it is stated in `ℚ`
with integer exponents.
-/

namespace OMA.S_oeis_a269103

open PowerSeries

/-- The number of horizontally or vertically adjacent pairs of the array `x` (with `m + 1` rows)
totalling three. -/
def pairsTotallingThree (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin (m + 1) => (x i 0 : ℕ) + (x i 1 : ℕ) = 3)).card +
    (Finset.univ.filter
      (fun p : Fin m × Fin 2 => (x p.1.castSucc p.2 : ℕ) + (x p.1.succ p.2 : ℕ) = 3)).card

/-- A269103: the number of n X 2 arrays over `0..3` with at most one adjacent pair totalling
three. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin (m + 1) → Fin 2 → Fin 4 => pairsTotallingThree m x ≤ 1)).card

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 14 * a (n - 1) - 49 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X) ^ 2 =
      4 * X * (4 - 11 * X + X ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 60 * 7 ^ ((n : ℤ) - 3) * (8 * n + 5)) := by
  sorry

end OMA.S_oeis_a269103
