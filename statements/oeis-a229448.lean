import Mathlib

/-!
# OEIS A229448: Barker's g.f. and recurrence for 5 X n 0..2 arrays with differences mod 3 restricted and lexicographically ordered rows and columns

Source: https://oeis.org/A229448 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A229448 (R. H. Hardin, Sep 23 2013), offset 1: Number of 5 X n 0..2 arrays with horizontal
differences mod 3 never 1, vertical differences mod 3 never -1, and rows and columns
lexicographically nondecreasing. Row 5 of A229445.
Formula section:
Conjectures from Colin Barker, Sep 17 2018:
G.f.: x*(17 - 55*x + 101*x^2 - 79*x^3 + 44*x^4 - 6*x^5) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.

Formalization notes:
* An array is x : Fin 5 → Fin n → Fin 3 (5 rows, n columns), x i j being the entry in row i (counted
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
* The g.f. is stated as A(x) (1 - x)^6 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^6 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 6.
* main is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..33) = 17, 47, 128, 324, 753, 1609, 3184, 5890, 10281,
  17075, 27176, 41696, 61977, 89613, 126472, 174718, 236833, 315639, 414320, 536444, 685985, 867345,
  1085376, 1345402, 1653241, 2015227, 2438232, 2929688, 3497609, 4150613, 4897944, 5749494, 6715825
  (the entry's data),
  and a(1) = 17 by direct enumeration of all arrays with n = 1.
-/

namespace OMA.S_oeis_a229448

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
def good {n : ℕ} (x : Fin 5 → Fin n → Fin 3) : Prop :=
  (∀ i : Fin 5, ∀ j j' : Fin n, j.val + 1 = j'.val → ¬ ((x i j' : ℤ) - x i j ≡ 1 [ZMOD 3])) ∧
  (∀ i i' : Fin 5, ∀ j : Fin n, i.val + 1 = i'.val → ¬ ((x i' j : ℤ) - x i j ≡ -1 [ZMOD 3])) ∧
  (∀ i i' : Fin 5, i.val + 1 = i'.val → lexLE (x i) (x i')) ∧
  (∀ j j' : Fin n, j.val + 1 = j'.val → lexLE (fun i => x i j) (fun i => x i j'))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A229448(n): the number of good 5 X n arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin 5 → Fin n → Fin 3 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (17 - 55 * X + 101 * X ^ 2 - 79 * X ^ 3 + 44 * X ^ 4 - 6 * X ^ 5) ∧
    ∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a229448
