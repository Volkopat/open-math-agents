import Mathlib

/-!
# A188557: Number of 6 X n binary arrays without the pattern 0 1 diagonally, vertically, antidiagonally or horizontally.

Source: https://oeis.org/A188557
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/720)*n^6 - (1/80)*n^5 + (17/144)*n^4 - (3/16)*n^3 + (497/360)*n^2 + (17/10)*n + 4.
* G.f.: x*(7 - 36*x + 80*x^2 - 96*x^3 + 66*x^4 - 24*x^5 + 4*x^6) / (1 - x)^7 (Colin Barker).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + 1*a(n-7) for n>7 (Colin Barker).

Conventions:
* A 6 X n array is the list of its columns from left to right; a column is a function
  `Fin 6 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* The pattern 0 1 in a direction is a 0 immediately followed, in that direction, by a 1:
  vertically (a 1 directly below a 0), horizontally (a 1 directly to the right of a 0),
  diagonally (a 1 one row down and one column to the right of a 0) and antidiagonally (a 1 one row
  down and one column to the left of a 0). This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a188557

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 6 → Fin 2)) : Prop :=
  (∀ c ∈ l, ∀ i : Fin 5, ¬ (c i.castSucc = 0 ∧ c i.succ = 1)) ∧
  l.IsChain (fun c d => (∀ i, ¬ (c i = 0 ∧ d i = 1)) ∧
    ∀ i : Fin 5, ¬ (c i.castSucc = 0 ∧ d i.succ = 1) ∧ ¬ (d i.castSucc = 0 ∧ c i.succ = 1))

/-- A188557(n): the number of such 6 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 6 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 720) * n ^ 6 - (1 / 80) * n ^ 5 + (17 / 144) * n ^ 4 - (3 / 16) * n ^ 3 + (497 / 360) * n ^ 2 + (17 / 10) * n + 4) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      7 - 36 * X + 80 * X ^ 2 - 96 * X ^ 3 + 66 * X ^ 4 - 24 * X ^ 5 + 4 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + 1 * a (n - 7)) := by
  sorry

end OMA.S_oeis_a188557
