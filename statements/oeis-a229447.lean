import Mathlib

/-!
# OEIS A229447: Barker's g.f. and recurrence for 4 X n 0..2 arrays with differences mod 3 restricted and lexicographically ordered rows and columns

Source: https://oeis.org/A229447 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A229447 (R. H. Hardin, Sep 23 2013), offset 1: Number of 4 X n 0..2 arrays with horizontal
differences mod 3 never 1, vertical differences mod 3 never -1, and rows and columns
lexicographically nondecreasing. Row 4 of A229445.
Formula section:
Conjectures from Colin Barker, Sep 17 2018:
G.f.: x*(12 - 35*x + 48*x^2 - 26*x^3 + 7*x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Formalization notes:
* An array is x : Fin 4 → Fin n → Fin 3 (4 rows, n columns), x i j being the entry in row i (counted
  from the top) and column j
  (counted from the left).
* A horizontal difference is x i j' - x i j for horizontally adjacent entries (j' = j + 1, the
  entry on the right minus the entry on the left); a vertical difference is x i' j - x i j for
  vertically adjacent entries (i' = i + 1, the lower entry minus the upper one). Both are computed
  in the integers and compared modulo 3: horizontal differences are never 1 mod 3 and vertical
  differences never -1 mod 3 (Int.ModEq). Of the four choices of sign for the two differences only
  this one reproduces the data, and with it a brute force reproduces every cell with at most 8
  entries of the tables A229428 (columns nonincreasing) and A229445 (rows and columns
  nondecreasing).
* lexLE u v is the lexicographic order on words of the same length: u = v, or u has the smaller
  letter at the first position where they differ. Rows are lexicographically nondecreasing:
  lexLE (x i) (x i') for consecutive rows. Columns, read from the top, are lexicographically
  nondecreasing from left to right: lexLE (column j) (column j+1) for consecutive columns.
* The g.f. is stated as A(x) (1 - x)^5 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^5 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 5.
* main is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..37) = 12, 25, 53, 109, 212, 387, 665, 1083, 1684, 2517,
  3637, 5105, 6988, 9359, 12297, 15887, 20220, 25393, 31509, 38677, 47012, 56635, 67673, 80259,
  94532, 110637, 128725, 148953, 171484, 196487, 224137, 254615, 288108, 324809, 364917, 408637,
  456180 (the entry's data),
  and a(1) = 12 by direct enumeration of all arrays with n = 1.
-/

namespace OMA.S_oeis_a229447

open PowerSeries Finset

/-- u ≤ v in the lexicographic order: u = v, or at the first index where they differ u is
smaller. -/
def lexLE {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  u = v ∨ ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance

/-- The array x (row i, column j): every horizontal difference x i j' - x i j (j' = j + 1) is not 1
mod 3, every vertical difference x i' j - x i j (i' = i + 1) is not -1 mod 3, the rows are
lexicographically nondecreasing from the top, and the columns (read from the top) are
lexicographically nondecreasing from the left. -/
def good {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : Prop :=
  (∀ i : Fin 4, ∀ j j' : Fin n, j.val + 1 = j'.val → ¬ ((x i j' : ℤ) - x i j ≡ 1 [ZMOD 3])) ∧
  (∀ i i' : Fin 4, ∀ j : Fin n, i.val + 1 = i'.val → ¬ ((x i' j : ℤ) - x i j ≡ -1 [ZMOD 3])) ∧
  (∀ i i' : Fin 4, i.val + 1 = i'.val → lexLE (x i) (x i')) ∧
  (∀ j j' : Fin n, j.val + 1 = j'.val → lexLE (fun i => x i j) (fun i => x i j'))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A229447(n): the number of good 4 X n arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin 4 → Fin n → Fin 3 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 5. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (12 - 35 * X + 48 * X ^ 2 - 26 * X ^ 3 + 7 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a229447
