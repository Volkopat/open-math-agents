import Mathlib

/-!
# A203829: Number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having equal diagonal elements or equal antidiagonal elements.

Source: https://oeis.org/A203829
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = 9*a(n-1) - 2*a(n-2), stated for n > 2.
* G.f.: 9*x*(25 - 6*x) / (1 - 9*x + 2*x^2) (Colin Barker).
* a(n) = (9*2^(-1-n)*((9-sqrt(73))^n*(-23+3*sqrt(73)) + (9+sqrt(73))^n*(23+3*sqrt(73)))) / sqrt(73)
  (Colin Barker), stated for n >= 1.

Conventions:
* An (n+1) X 3 array is the list of its n + 1 rows from top to bottom; a row is a function
  `Fin 3 → Fin 3` giving its entries from left to right, each in `0..2`.
* A 2 X 2 subblock (rows i, i+1 and columns j, j+1) has equal diagonal elements when
  x(i,j) = x(i+1,j+1), and equal antidiagonal elements when x(i,j+1) = x(i+1,j).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a203829

open PowerSeries Real

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 3)) : Prop :=
  l.IsChain (fun r s => ∀ j : Fin 2, r j.castSucc = s j.succ ∨ r j.succ = s j.castSucc)

/-- A203829(n): the number of such (n+1) X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 3) // l.length = n + 1 ∧ IsSolution l}

theorem main :
    (∀ n > 2, (a n : ℤ) = 9 * a (n - 1) - 2 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - 9 * X + 2 * X ^ 2) = 9 * (25 - 6 * X)) ∧
    (∀ n ≥ 1, (a n : ℝ) = 9 * (2 : ℝ) ^ (-1 - (n : ℤ)) * ((9 - √73) ^ n * (-23 + 3 * √73) +
      (9 + √73) ^ n * (23 + 3 * √73)) / √73) := by
  sorry

end OMA.S_oeis_a203829
