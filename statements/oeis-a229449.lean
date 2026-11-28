import Mathlib

/-!
# OEIS A229449: Barker's g.f. and recurrence for 6 X n 0..2 arrays with differences mod 3 restricted and lexicographically ordered rows and columns

Source: https://oeis.org/A229449 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A229449 (R. H. Hardin, Sep 23 2013), offset 1: Number of 6 X n 0..2 arrays with horizontal
differences mod 3 never 1, vertical differences mod 3 never -1, and rows and columns
lexicographically nondecreasing. Row 6 of A229445.
Formula section:
Conjectures from Colin Barker, Sep 17 2018:
G.f.: x*(23 - 77*x + 188*x^2 - 177*x^3 + 159*x^4 - 31*x^5 + 11*x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Formalization notes:
* An array is x : Fin 6 → Fin n → Fin 3 (6 rows, n columns), x i j being the entry in row i (counted
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
* The g.f. is stated as A(x) (1 - x)^7 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^7 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 7.
* main is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..30) = 23, 84, 293, 915, 2546, 6374, 14536, 30571, 59969,
  110816, 194535, 326723, 528084, 825458, 1252946, 1853131, 2678395, 3792332, 5271257, 7205811,
  9702662, 12886302, 16900940, 21912491, 28110661, 35711128, 44957819, 56125283, 69521160, 85488746
  (the entry's data),
  and a(1) = 23 by direct enumeration of all arrays with n = 1.
-/

namespace OMA.S_oeis_a229449

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
def good {n : ℕ} (x : Fin 6 → Fin n → Fin 3) : Prop :=
  (∀ i : Fin 6, ∀ j j' : Fin n, j.val + 1 = j'.val → ¬ ((x i j' : ℤ) - x i j ≡ 1 [ZMOD 3])) ∧
  (∀ i i' : Fin 6, ∀ j : Fin n, i.val + 1 = i'.val → ¬ ((x i' j : ℤ) - x i j ≡ -1 [ZMOD 3])) ∧
  (∀ i i' : Fin 6, i.val + 1 = i'.val → lexLE (x i) (x i')) ∧
  (∀ j j' : Fin n, j.val + 1 = j'.val → lexLE (fun i => x i j) (fun i => x i j'))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A229449(n): the number of good 6 X n arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin 6 → Fin n → Fin 3 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 7. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (23 - 77 * X + 188 * X ^ 2 - 177 * X ^ 3 + 159 * X ^ 4 - 31 * X ^ 5 + 11 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a229449
