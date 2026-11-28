import Mathlib

/-!
# A188555: Number of 4 X n binary arrays without the pattern 0 1 diagonally, vertically, antidiagonally or horizontally.

Source: https://oeis.org/A188555
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/24)*n^4 - (1/12)*n^3 + (23/24)*n^2 + (13/12)*n + 3, stated
  for n >= 1 (the entry's a(0) = 1 is not of this form).
* G.f.: -(2*x^5 - 7*x^4 + 11*x^3 - 6*x^2 + 1)/(x - 1)^5 (Colin Barker), written below as
  (1 - 6*x^2 + 11*x^3 - 7*x^4 + 2*x^5)/(1 - x)^5.
* a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 5 (Colin Barker).

Conventions:
* A 4 X n array is the list of its columns from left to right; a column is a function
  `Fin 4 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* The pattern 0 1 in a direction is a 0 immediately followed, in that direction, by a 1:
  vertically (a 1 directly below a 0), horizontally (a 1 directly to the right of a 0),
  diagonally (a 1 one row down and one column to the right of a 0) and antidiagonally (a 1 one row
  down and one column to the left of a 0). This reading reproduces the OEIS data.
* Offset 0 as in the OEIS (a(0) = 1 counts the empty array); the generating function is the series
  `Sum_{n>=0} a(n) x^n`.
-/

namespace OMA.S_oeis_a188555

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  (∀ c ∈ l, ∀ i : Fin 3, ¬ (c i.castSucc = 0 ∧ c i.succ = 1)) ∧
  l.IsChain (fun c d => (∀ i, ¬ (c i = 0 ∧ d i = 1)) ∧
    ∀ i : Fin 3, ¬ (c i.castSucc = 0 ∧ d i.succ = 1) ∧ ¬ (d i.castSucc = 0 ∧ c i.succ = 1))

/-- A188555(n): the number of such 4 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 24) * n ^ 4 - (1 / 12) * n ^ 3 + (23 / 24) * n ^ 2 + (13 / 12) * n + 3) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 5 =
      1 - 6 * X ^ 2 + 11 * X ^ 3 - 7 * X ^ 4 + 2 * X ^ 5) ∧
    (∀ n > 5, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + 1 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a188555
