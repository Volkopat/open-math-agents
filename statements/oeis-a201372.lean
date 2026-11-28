import Mathlib

/-!
# OEIS A201372: Barker's g.f. and recurrence for n X 5 arrays over 0..1 with rows and columns lexicographically nondecreasing forwards and nonincreasing backwards

Source: https://oeis.org/A201372 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A201372 (R. H. Hardin, Nov 30 2011), offset 1: Number of n X 5 0..1 arrays with rows and
columns lexicographically nondecreasing read forwards, and nonincreasing read backwards. Column 5 of
A201375.
Formula section:
Conjectures from Colin Barker, May 22 2018:
G.f.: 2*x*(1 - 4*x + 11*x^2 - 9*x^3 + 15*x^4 - 6*x^5) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Formalization notes:
* An array is x : Fin n → Fin 5 → Fin 2, x i j being the entry in row i (counted from the top)
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
* The g.f. is stated as A(x) (1 - x)^7 = numerator in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0). The
  denominator (1 - x)^7 has constant term 1 and is invertible, so this is the entry's quotient.
  The recurrence is stated in the integers for every n > 7.
* main is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..32) = 2, 6, 22, 80, 268, 786, 2016, 4608, 9582, 18446,
  33330, 57136, 93704, 147994, 226284, 336384, 487866, 692310, 963566, 1318032, 1774948, 2356706,
  3089176, 4002048, 5129190, 6509022, 8184906, 10205552, 12625440, 15505258, 18912356, 22921216 (the
  entry's data),
  and a(1) = 2 by direct enumeration of all arrays with 1 row(s).
-/

namespace OMA.S_oeis_a201372

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
def good {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  (∀ i i' : Fin n, i.val + 1 = i'.val → lexLE (x i) (x i') ∧ lexLE (bwd (x i')) (bwd (x i))) ∧
  (∀ j j' : Fin 5, j.val + 1 = j'.val →
    lexLE (fun i => x i j) (fun i => x i j') ∧ lexLE (bwd fun i => x i j') (bwd fun i => x i j))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A201372(n): the number of good n X 5 arrays with entries 0..1. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin n → Fin 5 → Fin 2 => good x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 7. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (1 - 4 * X + 11 * X ^ 2 - 9 * X ^ 3 + 15 * X ^ 4 - 6 * X ^ 5) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a201372
