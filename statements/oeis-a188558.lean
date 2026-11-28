import Mathlib

/-!
# A188558: Number of 7 X n binary arrays without the pattern 0 1 diagonally, vertically, antidiagonally or horizontally.

Source: https://oeis.org/A188558
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/5040)*n^7 - (1/360)*n^6 + (11/360)*n^5 - (1/9)*n^4 + (427/720)*n^3 + (41/360)*n^2 + (709/210)*n + 4.
* G.f.: x*(8 - 49*x + 132*x^2 - 200*x^3 + 184*x^4 - 102*x^5 + 32*x^6 - 4*x^7) / (1 - x)^8 (Colin Barker).
* a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - 1*a(n-8) for n>8 (Colin Barker).

Conventions:
* A 7 X n array is the list of its columns from left to right; a column is a function
  `Fin 7 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* The pattern 0 1 in a direction is a 0 immediately followed, in that direction, by a 1:
  vertically (a 1 directly below a 0), horizontally (a 1 directly to the right of a 0),
  diagonally (a 1 one row down and one column to the right of a 0) and antidiagonally (a 1 one row
  down and one column to the left of a 0). This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a188558

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 7 → Fin 2)) : Prop :=
  (∀ c ∈ l, ∀ i : Fin 6, ¬ (c i.castSucc = 0 ∧ c i.succ = 1)) ∧
  l.IsChain (fun c d => (∀ i, ¬ (c i = 0 ∧ d i = 1)) ∧
    ∀ i : Fin 6, ¬ (c i.castSucc = 0 ∧ d i.succ = 1) ∧ ¬ (d i.castSucc = 0 ∧ c i.succ = 1))

/-- A188558(n): the number of such 7 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 7 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 5040) * n ^ 7 - (1 / 360) * n ^ 6 + (11 / 360) * n ^ 5 - (1 / 9) * n ^ 4 + (427 / 720) * n ^ 3 + (41 / 360) * n ^ 2 + (709 / 210) * n + 4) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 8 =
      8 - 49 * X + 132 * X ^ 2 - 200 * X ^ 3 + 184 * X ^ 4 - 102 * X ^ 5 + 32 * X ^ 6 - 4 * X ^ 7) ∧
    (∀ n > 8, (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - 1 * a (n - 8)) := by
  sorry

end OMA.S_oeis_a188558
