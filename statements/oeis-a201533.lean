import Mathlib

/-!
# OEIS A201533: Barker's g.f. and recurrence for n X 2 0..2 arrays with ordered rows and columns and an equal neighbor for every element

Source: https://oeis.org/A201533 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A201533 (R. H. Hardin, Dec 02 2011), offset 1: Number of n X 2 0..2 arrays with rows and
columns lexicographically nondecreasing and every element equal to at least one horizontal or
vertical neighbor. Column 2 of A201539.
Formula section:
Conjectures from Colin Barker, May 23 2018:
G.f.: x*(3 - 18*x + 52*x^2 - 84*x^3 + 76*x^4 - 25*x^5 - 19*x^6 + 20*x^7 + x^8 - 9*x^9 + 5*x^10 -
x^11) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8)
+ a(n-9) for n>12.

Formalization notes:
* An array is x : Fin n → Fin 2 → Fin 3 (n rows, 2 columns), x i j being the entry in row i
  (counted from the top) and column j (counted from the left).
* lexLE u v is the lexicographic order on words of the same length: u = v, or u has the smaller
  letter at the first position where they differ. Rows are lexicographically nondecreasing:
  lexLE (x i) (x i') for consecutive rows (i' = i + 1). Columns, read from the top, are
  lexicographically nondecreasing from left to right in the same way.
* A horizontal neighbor of an element is an element in the same row and an adjacent column, a
  vertical neighbor one in the same column and an adjacent row (adj). Every element equals at least
  one of its horizontal or vertical neighbors.
* By brute force this reading reproduces every cell with at most 18 entries of the table A201353
  (0..1 arrays, 43 cells) and every cell with at most 12 entries of the table A201539 (0..2 arrays,
  30 cells).
* The g.f. is stated as A(x) (1 - x)^9 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^9 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 12, as in the entry.
* main is the conjunction of Barker's two conjectures.
* The Formula section also has an empirical polynomial for a(n) by R. H. Hardin; it is not part of
  the problem and is not stated here.
* Controls proved in the proof file from the definition, through the proved bijection with the row
  transfer: a(1..32) = 3, 9, 25, 69, 175, 410, 899, 1859, 3649, 6840, 12311, 21378, 35964, 58819,
  93800, 146222, 223292, 334639, 492954, 714755, 1021293, 1439616, 2003809, 2756429, 3750155,
  5049674, 6733825, 8898024, 11656994, 15147825, 19533390, 25006144 (the entry's data).
-/

namespace OMA.S_oeis_a201533

open PowerSeries Finset

/-- u ≤ v in the lexicographic order: u = v, or at the first index where they differ u is
smaller. -/
def lexLE {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  u = v ∨ ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance

/-- Two indices are adjacent. -/
def adj {m : ℕ} (a b : Fin m) : Prop := a.val + 1 = b.val ∨ b.val + 1 = a.val

instance {m : ℕ} : DecidableRel (@adj m) := fun a b => by unfold adj; infer_instance

/-- The array x (row i, column j) has its rows lexicographically nondecreasing from the top, its
columns (read from the top) lexicographically nondecreasing from the left, and every element
equal to at least one horizontal neighbor (same row, adjacent column) or vertical neighbor (same
column, adjacent row). -/
def good {n : ℕ} (x : Fin n → Fin 2 → Fin 3) : Prop :=
  (∀ i i' : Fin n, i.val + 1 = i'.val → lexLE (x i) (x i')) ∧
  (∀ j j' : Fin 2, j.val + 1 = j'.val → lexLE (fun i => x i j) (fun i => x i j')) ∧
  ∀ i : Fin n, ∀ j : Fin 2, ∃ i' : Fin n, ∃ j' : Fin 2,
    ((i' = i ∧ adj j j') ∨ (adj i i' ∧ j' = j)) ∧ x i' j' = x i j

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A201533(n): the number of good n X 2 arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin n → Fin 2 → Fin 3 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 12. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (3 - 18 * X + 52 * X ^ 2 - 84 * X ^ 3 + 76 * X ^ 4 - 25 * X ^ 5 - 19 * X ^ 6 + 20 * X ^ 7 + X ^ 8 - 9 * X ^ 9 + 5 * X ^ 10 - X ^ 11) ∧
    ∀ n : ℕ, 12 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a201533
