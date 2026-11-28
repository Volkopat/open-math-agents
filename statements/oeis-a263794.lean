import Mathlib

/-!
# OEIS A263794: Barker's closed forms and g.f. for (n+1) X 4 binary arrays with rows and columns divisible by 3 and lexicographically nonincreasing

Source: https://oeis.org/A263794 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A263794 (R. H. Hardin, Oct 26 2015), offset 1: Number of (n+1) X (3+1) 0..1 arrays with each
row and column divisible by 3, read as a binary number with top and left being the most significant
bits, and rows and columns lexicographically nonincreasing. Column 3 of A263799.
Formula section:
Conjectures from Colin Barker, Dec 14 2016:
a(n) = (n^3 + 6*n^2 + 32*n + 48)/48 for n even.
a(n) = (n^3 + 9*n^2 + 47*n + 87)/48 for n odd.
G.f.: x*(3 - 5*x^2 + 4*x^4 - x^6) / ((1 - x)^4*(1 + x)^3).

Formalization notes:
* a(n) counts arrays x : Fin (n + 1) → Fin 4 → Fin 2 (n + 1 rows, 4 columns), x i j being the
  entry in row i (counted from the top) and column j (counted from the left).
* A row is read as a binary number with the leftmost entry the most significant bit (rowVal), and
  a column with the top entry the most significant bit (colVal); every row and every column is
  divisible by 3.
* lexLE u v is the lexicographic order on words of the same length: u = v, or u has the smaller
  letter at the first position where they differ. Rows lexicographically nonincreasing:
  lexLE (x i') (x i) for consecutive rows; columns (read from the top) lexicographically
nonincreasing from left to right in the same way. By brute force this reading reproduces every cell
with at most 20 entries of the tables A263799 (nonincreasing) and A263873 (nondecreasing), 27 cells
  each.
* The g.f. is stated as A(x) times Barker's denominator equal to his numerator in the formal power
  series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term
  is 0); the denominator has constant term 1 and is invertible, so this is the entry's quotient.
* main is the conjunction of Barker's three conjectures: the closed form for even n and for odd n
  (stated in the rationals for n >= 1, the offset; the divisions by 48 are exact) and the g.f.
* Controls proved in the proof file: a(1..52) = 3, 3, 7, 7, 14, 14, 25, 25, 41, 41, 63, 63, 92, 92,
  129, 129, 175, 175, 231, 231, 298, 298, 377, 377, 469, 469, 575, 575, 696, 696, 833, 833, 987,
  987, 1159, 1159, 1350, 1350, 1561, 1561, 1793, 1793, 2047, 2047, 2324, 2324, 2625, 2625, 2951,
  2951, 3303, 3303 (the entry's data),
  and a(1) = 3 by direct enumeration of the 256 arrays with two rows.
-/

namespace OMA.S_oeis_a263794

open PowerSeries Finset

/-- u ≤ v in the lexicographic order: u = v, or at the first index where they differ u is
smaller. -/
def lexLE {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  u = v ∨ ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance

/-- A row read as a binary number, the leftmost entry being the most significant bit. -/
def rowVal (r : Fin 4 → Fin 2) : ℕ := ∑ j : Fin 4, (r j : ℕ) * 2 ^ (4 - 1 - (j : ℕ))

/-- Column j of an array with m rows read as a binary number, the top entry being the most
significant bit. -/
def colVal {m : ℕ} (x : Fin m → Fin 4 → Fin 2) (j : Fin 4) : ℕ :=
  ∑ i : Fin m, (x i j : ℕ) * 2 ^ (m - 1 - (i : ℕ))

/-- The array x (row i, column j): every row and every column is divisible by 3 as a binary
number, the rows are lexicographically nonincreasing from the top and the columns (read from the
top) lexicographically nonincreasing from the left. -/
def good {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Prop :=
  (∀ i : Fin m, 3 ∣ rowVal (x i)) ∧ (∀ j : Fin 4, 3 ∣ colVal x j) ∧
  (∀ i i' : Fin m, i.val + 1 = i'.val → lexLE (x i') (x i)) ∧
  (∀ j j' : Fin 4, j.val + 1 = j'.val → lexLE (fun i => x i j') (fun i => x i j))

instance {m : ℕ} : DecidablePred (@good m) := fun x => by unfold good; infer_instance

/-- A263794(n): the number of good (n+1) X 4 arrays with entries 0..1. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin (n + 1) → Fin 4 → Fin 2 => good x)).card

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (n ^ 3 + 6 * n ^ 2 + 32 * n + 48) / 48) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = (n ^ 3 + 9 * n ^ 2 + 47 * n + 87) / 48) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (((1 - X) ^ 4 * (1 + X) ^ 3)) =
      X * (3 - 5 * X ^ 2 + 4 * X ^ 4 - X ^ 6) := by
  sorry

end OMA.S_oeis_a263794
