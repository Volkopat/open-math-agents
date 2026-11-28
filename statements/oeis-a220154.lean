import Mathlib

/-!
# OEIS A220154: Barker's conjectures for 2 X n arrays of neighbourhood minima of sorted 0..2 arrays

Source: https://oeis.org/A220154 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A220154 (R. H. Hardin, Dec 06 2012), offset 1: Number of 2 X n arrays of the minimum value of corresponding elements and their horizontal or diagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..2 2 X n array.
Formula section:
Empirical: a(n) = (11/2)*n^2 - (23/2)*n + 8 for n>2.
Conjectures from _Colin Barker_, Mar 13 2018: (Start)
G.f.: x*(6 - 7*x + 8*x^2 + 8*x^3 - 4*x^4) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>5.
(End)

Formalization notes:
* A 2 X n array with entries in 0..2 is a map A : Fin 2 → Fin n → Fin 3, row index first. Entries are compared as natural numbers.
* Sorted with lexicographically nondecreasing rows and nonincreasing columns: the rows, each read
  left to right as a list, are nondecreasing in lexicographic order from top to bottom, and the
  columns, each read top to bottom as a list, are nonincreasing in lexicographic order from left to
  right (`IsSorted`).
* The derived array holds at each position the minimum of the element there and of its
  horizontal or diagonal neighbours that lie inside the array (`minNb`). The relation
  `nb i j i' j'` says that position (i', j') is (i, j) itself or such a neighbour; the diagonal
  neighbours of (i, j) are (i - 1, j - 1) and (i + 1, j + 1), the antidiagonal ones
  (i - 1, j + 1) and (i + 1, j - 1).
* Counting the arrays of minima of a random sorted array means counting the distinct derived
  arrays as the source ranges over all sorted arrays: a(n) is the cardinality of the image of
  `minNb` on the sorted arrays. This reading reproduces the first terms by direct enumeration
  and every listed term of the entry by an exact transfer-matrix count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^3 = (the entry's numerator) in the formal power series ring over the rationals with
  A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 5, as an identity of integers.
-/

namespace OMA.S_oeis_a220154

open PowerSeries Finset

/-- Position (i', j') is (i, j) itself or one of its horizontal or diagonal neighbours. -/
def nb (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ j' = j) ∨
    (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨
    ((i' + 1 = i ∧ j' + 1 = j) ∨ (i' = i + 1 ∧ j' = j + 1))

instance (i j i' j' : ℕ) : Decidable (nb i j i' j') := by unfold nb; infer_instance

/-- Rows lexicographically nondecreasing from top to bottom, columns lexicographically
nonincreasing from left to right. -/
def IsSorted {r c : ℕ} (A : Fin r → Fin c → Fin 3) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ Antitone (fun j => List.ofFn (fun i => A i j))

instance {r c : ℕ} (A : Fin r → Fin c → Fin 3) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

/-- The array of minima of each element and its neighbours inside the array. -/
def minNb {r c : ℕ} (A : Fin r → Fin c → Fin 3) : Fin r → Fin c → Fin 3 := fun i j =>
  ((univ : Finset (Fin r × Fin c)).filter (fun p => nb i j p.1 p.2)).inf (fun p => A p.1 p.2)

/-- A220154: the number of distinct arrays of neighbourhood minima of sorted 2 X n 0..2 arrays. -/
def a (n : ℕ) : ℕ := ((univ.filter (fun A : Fin 2 → Fin n → Fin 3 => IsSorted A)).image minNb).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (6 - 7 * X + 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a220154
