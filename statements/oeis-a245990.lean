import Mathlib

/-!
# A245990: Number of length n+2 0..3 arrays with no pair in any consecutive three terms totalling exactly 3

Source: https://oeis.org/A245990
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 28, 68, 164, 396, 956, 2308, ...).

Conventions:
* A length `m` array over `0..3` is `x : Fin m → Fin 4`.
* No pair in any consecutive three terms totalling exactly 3: for all indices `i < j` with
  `j - i ≤ 2`, `(x i : ℕ) + (x j : ℕ) ≠ 3`. For `m ≥ 3`, two distinct indices lie in a common
  block of three consecutive positions if and only if their distance is at most two.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Nov 05 2018):
a(n) = 2*a(n-1) + a(n-2);
G.f.: 4*x*(7 + 3*x) / (1 - 2*x - x^2);
a(n) = sqrt(2)*((1-sqrt(2))^n*(-4+3*sqrt(2)) + (1+sqrt(2))^n*(4+3*sqrt(2))).
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a245990

open PowerSeries

/-- An array `x` of length `m` over `0..3` has no pair in any consecutive three terms
totalling 3 when any two distinct positions at distance at most two do not sum to 3. -/
abbrev isValid (m : ℕ) (x : Fin m → Fin 4) : Prop :=
  ∀ i j : Fin m, i < j → (j : ℕ) - (i : ℕ) ≤ 2 → (x i : ℕ) + (x j : ℕ) ≠ 3

/-- A245990: the number of length `n + 2` arrays over `0..3` with no pair in any consecutive
three terms totalling 3. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (fun x : Fin (n + 3) → Fin 4 => isValid (n + 3) x)).card

theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 1) + a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 2 * X - X ^ 2) = 4 * X * (7 + 3 * X)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = Real.sqrt 2 *
        ((1 - Real.sqrt 2) ^ n * (-4 + 3 * Real.sqrt 2) +
         (1 + Real.sqrt 2) ^ n * (4 + 3 * Real.sqrt 2))) := by
  sorry

end OMA.S_oeis_a245990
