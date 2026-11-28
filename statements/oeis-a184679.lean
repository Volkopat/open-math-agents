import Mathlib

/-!
# A184679: Number of (n+1) X 3 binary arrays with every 2 X 2 subblock singular.

Source: https://oeis.org/A184679
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = 5*a(n-1) - 12*a(n-3), stated for n > 3.
* G.f.: 4*x*(7 - 3*x - 24*x^2) / ((1 - 2*x)*(1 - 3*x - 6*x^2)) (Colin Barker).
* a(n) = 2^(-2-n)*(11*2^(1+2*n) - 3*(3-sqrt(33))^n*(-55+7*sqrt(33))
  + 3*(3+sqrt(33))^n*(55+7*sqrt(33))) / 11 (Colin Barker), stated for n >= 1.

Conventions:
* An (n+1) X 3 array is the list of its n + 1 rows from top to bottom; a row is a function
  `Fin 3 → Fin 2` giving its entries from left to right.
* A 2 X 2 subblock (rows i, i+1 and columns j, j+1) is singular when its determinant
  x(i,j)*x(i+1,j+1) - x(i,j+1)*x(i+1,j) is zero.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a184679

open PowerSeries Real

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 2)) : Prop :=
  l.IsChain (fun r s => ∀ j : Fin 2,
    (r j.castSucc : ℤ) * s j.succ - (r j.succ : ℤ) * s j.castSucc = 0)

/-- A184679(n): the number of such (n+1) X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 2) // l.length = n + 1 ∧ IsSolution l}

theorem main :
    (∀ n > 3, (a n : ℤ) = 5 * a (n - 1) - 12 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - 2 * X) * (1 - 3 * X - 6 * X ^ 2)) =
      4 * (7 - 3 * X - 24 * X ^ 2)) ∧
    (∀ n ≥ 1, (a n : ℝ) = (2 : ℝ) ^ (-2 - (n : ℤ)) * (11 * 2 ^ (1 + 2 * n) -
      3 * (3 - √33) ^ n * (-55 + 7 * √33) + 3 * (3 + √33) ^ n * (55 + 7 * √33)) / 11) := by
  sorry

end OMA.S_oeis_a184679
