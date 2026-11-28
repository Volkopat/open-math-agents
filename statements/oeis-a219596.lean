import Mathlib

/-!
# OEIS A219596: Barker's conjectures for 3 X n arrays of neighbourhood minima of sorted 0..2 arrays

Source: https://oeis.org/A219596 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A219596 (R. H. Hardin, Nov 23 2012), offset 1: Number of 3 X n arrays of the minimum value of corresponding elements and their horizontal or vertical neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..2 3 X n array.
Formula section:
Empirical: a(n) = (1/181440)*n^9 - (1/8064)*n^8 + (11/3780)*n^7 - (107/2880)*n^6 + (749/1728)*n^5 - (1943/1152)*n^4 + (168241/90720)*n^3 + (355057/10080)*n^2 - (306913/2520)*n + 137 for n>3.
Conjectures from _Colin Barker_, Jul 26 2018: (Start)
G.f.: x*(6 - 39*x + 144*x^2 - 382*x^3 + 740*x^4 - 1009*x^5 + 933*x^6 - 554*x^7 + 195*x^8 - 32*x^9 - 5*x^10 + 7*x^11 - 2*x^12) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>13.
(End)

Formalization notes:
* A 3 X n array with entries in 0..2 is a map A : Fin 3 → Fin n → Fin 3, row index first. Entries are compared as natural numbers.
* Sorted with lexicographically nondecreasing rows and nonincreasing columns: the rows, each read
  left to right as a list, are nondecreasing in lexicographic order from top to bottom, and the
  columns, each read top to bottom as a list, are nonincreasing in lexicographic order from left to
  right (`IsSorted`).
* The derived array holds at each position the minimum of the element there and of its
  horizontal or vertical neighbours that lie inside the array (`minNb`). The relation
  `nb i j i' j'` says that position (i', j') is (i, j) itself or such a neighbour; the diagonal
  neighbours of (i, j) are (i - 1, j - 1) and (i + 1, j + 1), the antidiagonal ones
  (i - 1, j + 1) and (i + 1, j - 1).
* Counting the arrays of minima of a random sorted array means counting the distinct derived
  arrays as the source ranges over all sorted arrays: a(n) is the cardinality of the image of
  `minNb` on the sorted arrays. This reading reproduces the first terms by direct enumeration
  and every listed term of the entry by an exact transfer-matrix count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^10 = (the entry's numerator) in the formal power series ring over the rationals with
  A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 13, as an identity of integers.
-/

namespace OMA.S_oeis_a219596

open PowerSeries Finset

/-- Position (i', j') is (i, j) itself or one of its horizontal or vertical neighbours. -/
def nb (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ j' = j) ∨
    (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨
    (j' = j ∧ (i' + 1 = i ∨ i' = i + 1))

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

/-- A219596: the number of distinct arrays of neighbourhood minima of sorted 3 X n 0..2 arrays. -/
def a (n : ℕ) : ℕ := ((univ.filter (fun A : Fin 3 → Fin n → Fin 3 => IsSorted A)).image minNb).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (6 - 39 * X + 144 * X ^ 2 - 382 * X ^ 3 + 740 * X ^ 4 - 1009 * X ^ 5 + 933 * X ^ 6 - 554 * X ^ 7 + 195 * X ^ 8 - 32 * X ^ 9 - 5 * X ^ 10 + 7 * X ^ 11 - 2 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a219596
