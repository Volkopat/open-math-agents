import Mathlib

/-!
# A223616: Number of n X 4 0..1 arrays with rows and columns unimodal.

Source: https://oeis.org/A223616
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(11 + 22*x + 183*x^2 + 14*x^3 + 158*x^4 - 56*x^5 + 35*x^6 - 8*x^7 + x^8) / (1 - x)^9 (Colin Barker, Aug 21 2018).
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9 (Colin Barker, Aug 21 2018).

Conventions:
* An n X 4 array is the list of its n rows from top to bottom; a row is a function
  `Fin 4 → Fin 2` giving its entries from left to right.
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms). Every row, read from
  left to right, and every column, read from top to bottom, is unimodal. This reading reproduces
  the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223616

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  ∀ j : Fin 4, Unimodal (l.map fun r => (r j : ℕ))

/-- A223616(n): the number of such n X 4 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      11 + 22 * X ^ 1 + 183 * X ^ 2 + 14 * X ^ 3 + 158 * X ^ 4 - 56 * X ^ 5 + 35 * X ^ 6 - 8 * X ^ 7 + X ^ 8) ∧
    (∀ n > 9, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a223616
