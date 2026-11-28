import Mathlib

/-!
# A183635: Number of (n+1) X 3 0..3 arrays with every 2 X 2 subblock summing to 6.

Source: https://oeis.org/A183635
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 10*a(n-1) - 35*a(n-2) + 50*a(n-3) - 24*a(n-4), stated for n > 4.
* G.f.: 4*x*(34 - 255*x + 578*x^2 - 384*x^3) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)) (Colin Barker).
* a(n) = 18 + 3*2^(3+n) + 2*3^(2+n) + 4^(1+n) (Colin Barker), stated for n >= 1.
(The entry notes that these were proved by Christian Krause.)

Conventions:
* An (n+1) X 3 array is the list of its n + 1 rows from top to bottom; a row is a function
  `Fin 3 → Fin 4` giving its entries from left to right, each in `0..3`.
* Every 2 X 2 subblock sums to 6: for any two consecutive rows and any two consecutive columns,
  the four entries sum to 6.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a183635

open PowerSeries

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 4)) : Prop :=
  l.IsChain (fun r s => ∀ j : Fin 2,
    (r j.castSucc : ℕ) + r j.succ + s j.castSucc + s j.succ = 6)

/-- A183635(n): the number of such (n+1) X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 4) // l.length = n + 1 ∧ IsSolution l}

theorem main :
    (∀ n > 4, (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      4 * (34 - 255 * X + 578 * X ^ 2 - 384 * X ^ 3)) ∧
    (∀ n ≥ 1, (a n : ℚ) = 18 + 3 * 2 ^ (3 + n) + 2 * 3 ^ (2 + n) + 4 ^ (1 + n)) := by
  sorry

end OMA.S_oeis_a183635
