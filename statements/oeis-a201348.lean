import Mathlib

/-!
# OEIS A201348: Barker's g.f. and recurrence for n X 3 0..1 arrays with ordered rows and columns and an equal neighbor for every element

Source: https://oeis.org/A201348 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A201348 (R. H. Hardin, Nov 30 2011), offset 1: Number of n X 3 0..1 arrays with rows and
columns lexicographically nondecreasing and every element equal to at least one horizontal or
vertical neighbor. Column 3 of A201353.
Formula section:
Conjectures from Colin Barker, May 22 2018:
G.f.: x*(2 - 8*x + 10*x^2 + 15*x^3 - 62*x^4 + 85*x^5 - 59*x^6 + 20*x^7 - 2*x^8) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for
n>9.

Formalization notes:
* An array is x : Fin n → Fin 3 → Fin 2 (n rows, 3 columns), x i j being the entry in row i
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
* The g.f. is stated as A(x) (1 - x)^8 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^8 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 9, as in the entry.
* main is the conjunction of Barker's two conjectures.
* The Formula section also has an empirical polynomial for a(n) by R. H. Hardin; it is not part of
  the problem and is not stated here.
* Controls proved in the proof file from the definition, through the proved bijection with the row
  transfer: a(1..34) = 2, 8, 18, 47, 118, 273, 585, 1174, 2228, 4030, 6992, 11697, 18950, 29839,
  45807, 68736, 101044, 145796, 206830, 288899, 397830, 540701, 726037, 964026, 1266756, 1648474,
  2125868, 2718373, 3448502, 4342203, 5429243, 6743620, 8324004, 10214208 (the entry's data).
-/

namespace OMA.S_oeis_a201348

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
def good {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  (∀ i i' : Fin n, i.val + 1 = i'.val → lexLE (x i) (x i')) ∧
  (∀ j j' : Fin 3, j.val + 1 = j'.val → lexLE (fun i => x i j) (fun i => x i j')) ∧
  ∀ i : Fin n, ∀ j : Fin 3, ∃ i' : Fin n, ∃ j' : Fin 3,
    ((i' = i ∧ adj j j') ∨ (adj i i' ∧ j' = j)) ∧ x i' j' = x i j

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A201348(n): the number of good n X 3 arrays with entries 0..1. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin n → Fin 3 → Fin 2 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 9. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (2 - 8 * X + 10 * X ^ 2 + 15 * X ^ 3 - 62 * X ^ 4 + 85 * X ^ 5 - 59 * X ^ 6 + 20 * X ^ 7 - 2 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a201348
