import Mathlib

/-!
# OEIS A229441: Barker's g.f. and recurrence for n X 4 0..2 arrays with differences mod 3 restricted and lexicographically ordered rows and columns

Source: https://oeis.org/A229441 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A229441 (R. H. Hardin, Sep 23 2013), offset 1: Number of n X 4 0..2 arrays with horizontal
differences mod 3 never 1, vertical differences mod 3 never -1, and rows and columns
lexicographically nondecreasing. Column 4 of A229445.
Formula section:
Conjectures from Colin Barker, Sep 17 2018:
G.f.: x*(6 - 40*x + 127*x^2 - 224*x^3 + 255*x^4 - 177*x^5 + 77*x^6 - 19*x^7 + 2*x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8)
+ a(n-9) for n>9.

Formalization notes:
* An array is x : Fin n → Fin 4 → Fin 3 (n rows, 4 columns), x i j being the entry in row i (counted
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
* The g.f. is stated as A(x) (1 - x)^9 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^9 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 9.
* main is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..30) = 6, 14, 37, 109, 324, 915, 2402, 5843, 13229, 28071,
  56234, 107080, 194989, 341334, 576993, 945488, 1506848, 2342300, 3559899, 5301215, 7749202,
  11137381, 15760476, 21986649, 30271487, 41173901, 55374104, 73693842, 97119059, 126825184 (the
  entry's data),
  and a(1) = 6 by direct enumeration of all arrays with n = 1.
-/

namespace OMA.S_oeis_a229441

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
def good {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Prop :=
  (∀ i : Fin n, ∀ j j' : Fin 4, j.val + 1 = j'.val → ¬ ((x i j' : ℤ) - x i j ≡ 1 [ZMOD 3])) ∧
  (∀ i i' : Fin n, ∀ j : Fin 4, i.val + 1 = i'.val → ¬ ((x i' j : ℤ) - x i j ≡ -1 [ZMOD 3])) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → lexLE (x i) (x i')) ∧
  (∀ j j' : Fin 4, j.val + 1 = j'.val → lexLE (fun i => x i j) (fun i => x i j'))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A229441(n): the number of good n X 4 arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin n → Fin 4 → Fin 3 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 9. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (6 - 40 * X + 127 * X ^ 2 - 224 * X ^ 3 + 255 * X ^ 4 - 177 * X ^ 5 + 77 * X ^ 6 - 19 * X ^ 7 + 2 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a229441
