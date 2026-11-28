import Mathlib

/-!
# OEIS A201696: Barker's g.f. and recurrence for n X 4 arrays over 0..2 with rows and columns lexicographically nondecreasing forwards and nonincreasing backwards

Source: https://oeis.org/A201696 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A201696 (R. H. Hardin, Dec 03 2011), offset 1: Number of n X 4 0..2 arrays with rows and
columns lexicographically nondecreasing read forwards and nonincreasing read backwards. Column 4 of
A201700.
Formula section:
Conjectures from Colin Barker, May 23 2018:
G.f.: x*(3 - 6*x + 263*x^2 + 1643*x^3 - 1328*x^4 - 4426*x^5 + 5086*x^6 - 1972*x^7 + 1789*x^8 -
1233*x^9 + 185*x^10) / (1 - x)^11.
a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) -
165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>11.

Formalization notes:
* An array is x : Fin n → Fin 4 → Fin 3, x i j being the entry in row i (counted from the top)
  and column j (counted from the left). Row i is the word x i read from left to right, column j
  the word (fun i => x i j) read from top to bottom.
* lexLE u v is the lexicographic order on words of the same length: u = v, or u has the smaller
  letter at the first position where the two words differ. bwd u is the word u read backwards
  (last letter first).
* Rows lexicographically nondecreasing read forwards: lexLE (x i) (x i') for consecutive rows i,
  i' = i + 1. Nonincreasing read backwards: each row read backwards is at least the next row read
  backwards, lexLE (bwd (x i')) (bwd (x i)). The same two conditions hold for every column and
  the column to its right. By brute force this reading reproduces every cell of the tables
  A201375 (0..1, arrays of at most 22 entries), A201700 (0..2, at most 10) and A201981 (0..3, at
  most 7), and the proof file derives all of this entry's listed terms from it; the reading in
  which read backwards adds nothing (rows and columns only lexicographically nondecreasing) gives
  different numbers.
* The g.f. is stated as A(x) (1 - x)^11 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^11 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 11.
* main is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..24) = 3, 27, 395, 4998, 35390, 167625, 607919, 1826778,
  4775228, 11211034, 24167306, 48600665, 92261185, 166831642, 289389192, 484248471, 785251265,
  1238574341, 1906133765, 2869671064, 4235613920, 6140811719, 8759254221, 12309889872 (the entry's
  data),
  and a(1) = 3 by direct enumeration of all arrays with 1 row(s).
-/

namespace OMA.S_oeis_a201696

open PowerSeries Finset

/-- u ≤ v in the lexicographic order: u = v, or at the first index where they differ u is
smaller. -/
def lexLE {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  u = v ∨ ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance

/-- The word u read backwards. -/
def bwd {m q : ℕ} (u : Fin m → Fin q) : Fin m → Fin q := fun i => u (Fin.rev i)

/-- The array x (row i, column j) has its rows (x i) and its columns (fun i => x i j)
lexicographically nondecreasing read forwards and nonincreasing read backwards: each row is at
most the next one and its reversal at least the next one's reversal, and the same for each column
and the column to its right. -/
def good {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Prop :=
  (∀ i i' : Fin n, i.val + 1 = i'.val → lexLE (x i) (x i') ∧ lexLE (bwd (x i')) (bwd (x i))) ∧
  (∀ j j' : Fin 4, j.val + 1 = j'.val →
    lexLE (fun i => x i j) (fun i => x i j') ∧ lexLE (bwd fun i => x i j') (bwd fun i => x i j))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A201696(n): the number of good n X 4 arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin n → Fin 4 → Fin 3 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 11. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 11 =
      X * (3 - 6 * X + 263 * X ^ 2 + 1643 * X ^ 3 - 1328 * X ^ 4 - 4426 * X ^ 5 + 5086 * X ^ 6 - 1972 * X ^ 7 + 1789 * X ^ 8 - 1233 * X ^ 9 + 185 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n →
      (a n : ℤ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) := by
  sorry

end OMA.S_oeis_a201696
