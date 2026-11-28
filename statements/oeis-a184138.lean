import Mathlib

/-!
# A184138: Number of n X 3 binary arrays with rows and columns in nondecreasing order.

Source: https://oeis.org/A184138
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) -
  28*a(n-6) + 8*a(n-7) - a(n-8) (= polynomial degree 7), stated for n > 8.
* G.f.: x*(4 - 18*x + 45*x^2 - 62*x^3 + 52*x^4 - 27*x^5 + 8*x^6 - x^7) / (1 - x)^8 (Colin Barker).
* a(n) = (5040 + 7860*n + 4494*n^2 + 2044*n^3 + 525*n^4 + 175*n^5 + 21*n^6 + n^7) / 5040
  (Colin Barker), stated below with the coefficients divided out.

Conventions:
* An n X 3 array is the list of its rows from top to bottom; a row is a function `Fin 3 → Fin 2`
  giving its entries from left to right.
* Rows and columns in nondecreasing order, with rows and columns compared lexicographically (this
  reading reproduces the OEIS data and examples): each row is lexicographically `≤` the row below
  it (`toLex` on functions `Fin 3 → Fin 2`), and column `j`, read top to bottom, is
  lexicographically `≤` column `j + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a184138

open PowerSeries

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 2)) : Prop :=
  l.IsChain (fun r s => toLex r ≤ toLex s) ∧
  ∀ j : Fin 2, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A184138(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 5040) * n ^ 7 + (1 / 240) * n ^ 6 + (5 / 144) * n ^ 5 + (5 / 48) * n ^ 4 + (73 / 180) * n ^ 3 + (107 / 120) * n ^ 2 + (131 / 84) * n + 1) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 8 =
      4 - 18 * X + 45 * X ^ 2 - 62 * X ^ 3 + 52 * X ^ 4 - 27 * X ^ 5 + 8 * X ^ 6 - 1 * X ^ 7) ∧
    (∀ n > 8, (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - 1 * a (n - 8)) := by
  sorry

end OMA.S_oeis_a184138
