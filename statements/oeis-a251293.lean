import Mathlib

/-!
# A251293: Number of (n+1) X (1+1) 0..3 arrays with every 2 X 2 subblock summing to 3 6 or 9.

Source: https://oeis.org/A251293
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = 10*a(n-1) - 21*a(n-2) - 20*a(n-3), stated for n > 3.
* G.f.: 4*x*(21 - 99*x - 80*x^2) / ((1 - 5*x)*(1 - 5*x - 4*x^2)) (Colin Barker).
* a(n) = (1/41)*2^(-n)*(41*10^(1+n) + (123-19*sqrt(41))*(5-sqrt(41))^n
  + (5+sqrt(41))^n*(123+19*sqrt(41))) (Colin Barker), stated for n >= 1.

Conventions:
* An (n+1) X 2 array is the list of its n + 1 rows from top to bottom; a row is a function
  `Fin 2 → Fin 4` giving its two entries from left to right, each in `0..3`.
* Every 2 X 2 subblock sums to 3, 6 or 9: for any two consecutive rows, the four entries sum to 3,
  6 or 9.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a251293

open PowerSeries Real

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 2 → Fin 4)) : Prop :=
  l.IsChain (fun r s => (r 0 : ℕ) + r 1 + s 0 + s 1 ∈ ({3, 6, 9} : Finset ℕ))

/-- A251293(n): the number of such (n+1) X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 2 → Fin 4) // l.length = n + 1 ∧ IsSolution l}

theorem main :
    (∀ n > 3, (a n : ℤ) = 10 * a (n - 1) - 21 * a (n - 2) - 20 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - 5 * X) * (1 - 5 * X - 4 * X ^ 2)) =
      4 * (21 - 99 * X - 80 * X ^ 2)) ∧
    (∀ n ≥ 1, (a n : ℝ) = (1 / 41) * (2 : ℝ) ^ (-(n : ℤ)) * (41 * 10 ^ (1 + n) +
      (123 - 19 * √41) * (5 - √41) ^ n + (5 + √41) ^ n * (123 + 19 * √41))) := by
  sorry

end OMA.S_oeis_a251293
