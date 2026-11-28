import Mathlib

/-!
# OEIS A263869: Barker's g.f. and closed form for (n+1) X 5 binary arrays with rows and columns divisible by 3 and lexicographically nondecreasing

Source: https://oeis.org/A263869 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A263869 (R. H. Hardin, Oct 28 2015), offset 1: Number of (n+1) X (4+1) 0..1 arrays with each
row and column divisible by 3, read as a binary number with top and left being the most significant
bits, and rows and columns lexicographically nondecreasing. Column 4 of A263873.
Formula section:
Conjectures from Colin Barker, Jan 03 2019:
G.f.: x*(3 - 3*x - 14*x^2 + 14*x^3 + 30*x^4 - 29*x^5 - 31*x^6 + 31*x^7 + 20*x^8 - 20*x^9 - 7*x^10 +
7*x^11 + x^12 - x^13) / ((1 - x)^8*(1 + x)^6).
a(n) = (315*(2889-841*(-1)^n) + (537927 - 96327*(-1)^n)*n - 21*(-4723+755*(-1)^n)*n^2 - 7*(-1469 +
45*(-1)^n)*n^3 - 105*(3+5*(-1)^n)*n^4 - 7*(-29+9*(-1)^n)*n^5 + 42*n^6 + 2*n^7) / 645120.

Formalization notes:
* a(n) counts arrays x : Fin (n + 1) → Fin 5 → Fin 2 (n + 1 rows, 5 columns), x i j being the
  entry in row i (counted from the top) and column j (counted from the left).
* A row is read as a binary number with the leftmost entry the most significant bit (rowVal), and
  a column with the top entry the most significant bit (colVal); every row and every column is
  divisible by 3.
* lexLE u v is the lexicographic order on words of the same length: u = v, or u has the smaller
  letter at the first position where they differ. Rows lexicographically nondecreasing:
  lexLE (x i) (x i') for consecutive rows; columns (read from the top) lexicographically
nondecreasing from left to right in the same way. By brute force this reading reproduces every cell
with at most 20 entries of the tables A263799 (nonincreasing) and A263873 (nondecreasing), 27 cells
  each.
* The g.f. is stated as A(x) times Barker's denominator equal to his numerator in the formal power
  series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term
  is 0); the denominator has constant term 1 and is invertible, so this is the entry's quotient.
* main is the conjunction of Barker's two conjectures: the g.f. and the closed form, stated in the
  rationals for every n >= 1 (the offset).
* Controls proved in the proof file: a(1..40) = 3, 3, 7, 7, 16, 17, 41, 48, 113, 141, 303, 387, 752,
  962, 1713, 2175, 3607, 4531, 7095, 8811, 13168, 16171, 23257, 28262, 39365, 47373, 64223, 76599,
  101472, 120036, 155873, 183005, 233547, 272307, 342247, 396511, 491664, 566277, 693769, 794716
  (the entry's data),
  (the data follow from the closed form, which is proved from the definition).
-/

namespace OMA.S_oeis_a263869

open PowerSeries Finset

/-- u ≤ v in the lexicographic order: u = v, or at the first index where they differ u is
smaller. -/
def lexLE {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  u = v ∨ ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance

/-- A row read as a binary number, the leftmost entry being the most significant bit. -/
def rowVal (r : Fin 5 → Fin 2) : ℕ := ∑ j : Fin 5, (r j : ℕ) * 2 ^ (5 - 1 - (j : ℕ))

/-- Column j of an array with m rows read as a binary number, the top entry being the most
significant bit. -/
def colVal {m : ℕ} (x : Fin m → Fin 5 → Fin 2) (j : Fin 5) : ℕ :=
  ∑ i : Fin m, (x i j : ℕ) * 2 ^ (m - 1 - (i : ℕ))

/-- The array x (row i, column j): every row and every column is divisible by 3 as a binary
number, the rows are lexicographically nondecreasing from the top and the columns (read from the
top) lexicographically nondecreasing from the left. -/
def good {m : ℕ} (x : Fin m → Fin 5 → Fin 2) : Prop :=
  (∀ i : Fin m, 3 ∣ rowVal (x i)) ∧ (∀ j : Fin 5, 3 ∣ colVal x j) ∧
  (∀ i i' : Fin m, i.val + 1 = i'.val → lexLE (x i) (x i')) ∧
  (∀ j j' : Fin 5, j.val + 1 = j'.val → lexLE (fun i => x i j) (fun i => x i j'))

instance {m : ℕ} : DecidablePred (@good m) := fun x => by unfold good; infer_instance

/-- A263869(n): the number of good (n+1) X 5 arrays with entries 0..1. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin (n + 1) → Fin 5 → Fin 2 => good x)).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (((1 - X) ^ 8 * (1 + X) ^ 6)) =
      X * (3 - 3 * X - 14 * X ^ 2 + 14 * X ^ 3 + 30 * X ^ 4 - 29 * X ^ 5 - 31 * X ^ 6 + 31 * X ^ 7 + 20 * X ^ 8 - 20 * X ^ 9 - 7 * X ^ 10 + 7 * X ^ 11 + X ^ 12 - X ^ 13) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (315 * (2889 - 841 * (-1) ^ n) + (537927 - 96327 * (-1) ^ n) * n - 21 * (-4723 + 755 * (-1) ^ n) * n ^ 2 - 7 * (-1469 + 45 * (-1) ^ n) * n ^ 3 - 105 * (3 + 5 * (-1) ^ n) * n ^ 4 - 7 * (-29 + 9 * (-1) ^ n) * n ^ 5 + 42 * n ^ 6 + 2 * n ^ 7) / 645120 := by
  sorry

end OMA.S_oeis_a263869
