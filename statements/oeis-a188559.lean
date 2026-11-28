import Mathlib

/-!
# A188559: Number of 8 X n binary arrays without the pattern 0 1 diagonally, vertically, antidiagonally or horizontally.

Source: https://oeis.org/A188559
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/40320)*n^8 - (1/2016)*n^7 + (19/2880)*n^6 - (7/180)*n^5 + (1247/5760)*n^4 - (85/288)*n^3 + (17911/10080)*n^2 + (1961/840)*n + 5.
* G.f.: x*(9 - 64*x + 203*x^2 - 372*x^3 + 430*x^4 - 320*x^5 + 150*x^6 - 40*x^7 + 5*x^8) / (1 - x)^9 (Colin Barker).
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + 1*a(n-9) for n>9 (Colin Barker).

Conventions:
* A 8 X n array is the list of its columns from left to right; a column is a function
  `Fin 8 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* The pattern 0 1 in a direction is a 0 immediately followed, in that direction, by a 1:
  vertically (a 1 directly below a 0), horizontally (a 1 directly to the right of a 0),
  diagonally (a 1 one row down and one column to the right of a 0) and antidiagonally (a 1 one row
  down and one column to the left of a 0). This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a188559

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 8 → Fin 2)) : Prop :=
  (∀ c ∈ l, ∀ i : Fin 7, ¬ (c i.castSucc = 0 ∧ c i.succ = 1)) ∧
  l.IsChain (fun c d => (∀ i, ¬ (c i = 0 ∧ d i = 1)) ∧
    ∀ i : Fin 7, ¬ (c i.castSucc = 0 ∧ d i.succ = 1) ∧ ¬ (d i.castSucc = 0 ∧ c i.succ = 1))

/-- A188559(n): the number of such 8 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 8 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 40320) * n ^ 8 - (1 / 2016) * n ^ 7 + (19 / 2880) * n ^ 6 - (7 / 180) * n ^ 5 + (1247 / 5760) * n ^ 4 - (85 / 288) * n ^ 3 + (17911 / 10080) * n ^ 2 + (1961 / 840) * n + 5) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      9 - 64 * X + 203 * X ^ 2 - 372 * X ^ 3 + 430 * X ^ 4 - 320 * X ^ 5 + 150 * X ^ 6 - 40 * X ^ 7 + 5 * X ^ 8) ∧
    (∀ n > 9, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + 1 * a (n - 9)) := by
  sorry

end OMA.S_oeis_a188559
