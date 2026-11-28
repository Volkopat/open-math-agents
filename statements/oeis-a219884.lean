import Mathlib

/-!
# OEIS A219884: Barker's conjectures for 3 X n arrays of neighbourhood minima of sorted 0..2 arrays

Source: https://oeis.org/A219884 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A219884 (R. H. Hardin, Nov 30 2012), offset 1: Number of 3 X n arrays of the minimum value of corresponding elements and their horizontal, diagonal or antidiagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..2 3 X n array.
Formula section:
Empirical: a(n) = (1/362880)*n^9 - (1/13440)*n^8 + (17/12096)*n^7 - (37/2880)*n^6 + (1813/17280)*n^5 + (1579/5760)*n^4 - (76849/9072)*n^3 + (768487/10080)*n^2 - (590021/2520)*n + 217 for n>6.
Conjectures from _Colin Barker_, Jul 28 2018: (Start)
G.f.: x*(10 - 79*x + 287*x^2 - 596*x^3 + 697*x^4 - 265*x^5 - 504*x^6 + 984*x^7 - 895*x^8 + 565*x^9 - 351*x^10 + 273*x^11 - 206*x^12 + 112*x^13 - 36*x^14 + 5*x^15) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>16.
(End)

Formalization notes:
* A 3 X n array with entries in 0..2 is a map A : Fin 3 → Fin n → Fin 3, row index first. Entries are compared as natural numbers.
* Sorted with lexicographically nondecreasing rows and nonincreasing columns: the rows, each read
  left to right as a list, are nondecreasing in lexicographic order from top to bottom, and the
  columns, each read top to bottom as a list, are nonincreasing in lexicographic order from left to
  right (`IsSorted`).
* The derived array holds at each position the minimum of the element there and of its
  horizontal, diagonal or antidiagonal neighbours that lie inside the array (`minNb`). The relation
  `nb i j i' j'` says that position (i', j') is (i, j) itself or such a neighbour; the diagonal
  neighbours of (i, j) are (i - 1, j - 1) and (i + 1, j + 1), the antidiagonal ones
  (i - 1, j + 1) and (i + 1, j - 1).
* Counting the arrays of minima of a random sorted array means counting the distinct derived
  arrays as the source ranges over all sorted arrays: a(n) is the cardinality of the image of
  `minNb` on the sorted arrays. This reading reproduces the first terms by direct enumeration
  and every listed term of the entry by an exact transfer-matrix count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^10 = (the entry's numerator) in the formal power series ring over the rationals with
  A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 16, as an identity of integers.
-/

namespace OMA.S_oeis_a219884

open PowerSeries Finset

/-- Position (i', j') is (i, j) itself or one of its horizontal, diagonal or antidiagonal neighbours. -/
def nb (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ j' = j) ∨
    (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨
    ((i' + 1 = i ∧ j' + 1 = j) ∨ (i' = i + 1 ∧ j' = j + 1)) ∨
    ((i' + 1 = i ∧ j' = j + 1) ∨ (i' = i + 1 ∧ j' + 1 = j))

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

/-- A219884: the number of distinct arrays of neighbourhood minima of sorted 3 X n 0..2 arrays. -/
def a (n : ℕ) : ℕ := ((univ.filter (fun A : Fin 3 → Fin n → Fin 3 => IsSorted A)).image minNb).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (10 - 79 * X + 287 * X ^ 2 - 596 * X ^ 3 + 697 * X ^ 4 - 265 * X ^ 5 - 504 * X ^ 6 + 984 * X ^ 7 - 895 * X ^ 8 + 565 * X ^ 9 - 351 * X ^ 10 + 273 * X ^ 11 - 206 * X ^ 12 + 112 * X ^ 13 - 36 * X ^ 14 + 5 * X ^ 15) ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a219884
