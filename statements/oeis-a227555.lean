import Mathlib

/-!
# OEIS A227555: Barker's conjectures for indicator arrays of 2 X 2 subblocks with nonzero determinant

Source: https://oeis.org/A227555 (OEIS Foundation, CC BY-SA 4.0).

Entry A227555 (R. H. Hardin, Jul 16 2013), offset 1: Number of n X 3 0,1 arrays indicating 2 X 2 subblocks of some larger (n+1) X 4 binary array having nonzero determinant, with rows and columns of the latter in lexicographically nondecreasing order.
Data: 7, 33, 147, 585, 2080, 6653, 19356, 51827, 129090, 301882, 668004, 1407882, ...
Formula section: Conjectures from Colin Barker, Sep 08 2018: (Start) G.f.: x*(7 - 51*x + 213*x^2 - 541*x^3 + 967*x^4 - 1246*x^5 + 1197*x^6 - 848*x^7 + 439*x^8 - 150*x^9 + 31*x^10) / (1 - x)^12. a(n) = 12*a(n-1) - 66*a(n-2) + 220*a(n-3) - 495*a(n-4) + 792*a(n-5) - 924*a(n-6) + 792*a(n-7) - 495*a(n-8) + 220*a(n-9) - 66*a(n-10) + 12*a(n-11) - a(n-12) for n>12. (End)

Formalization notes:
* The larger array is an (n + 1) X 4 binary array, a map A : Fin (n + 1) → Fin 4 → Fin 2,
  row index first.
* Rows and columns in lexicographically nondecreasing order: the rows, each read left to right as
  a list, are nondecreasing in lexicographic order from top to bottom, and the columns, each read
  top to bottom as a list, are nondecreasing in lexicographic order from left to right
  (`IsSorted`).
* The n X 3 indicator array of A has a 1 at (i, j) exactly when the 2 X 2 subblock
  [[x, y], [z, t]] = [[A i j, A i (j + 1)], [A (i + 1) j, A (i + 1) (j + 1)]] has nonzero determinant, that
  is, when its determinant x t - y z is nonzero (`blk`, `ind`).
* The entry counts the n X 3 0,1 arrays that arise as such indicator arrays: a(n) is the
  cardinality of the image of `ind` on the sorted arrays. This reading reproduces the first terms
  of the data by direct enumeration and all listed terms by an exact automaton count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^12 = (the entry's numerator) in the formal power series ring over the rationals,
  with A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 12, as an identity of
  integers.
-/

namespace OMA.S_oeis_a227555

open PowerSeries Finset

/-- Rows lexicographically nondecreasing from top to bottom, columns lexicographically
nondecreasing from left to right. -/
def IsSorted {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ Monotone (fun j => List.ofFn (fun i => A i j))

instance {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

/-- The 2 X 2 subblock [[x, y], [z, t]] has nonzero determinant. -/
def blk (x y z t : Fin 2) : Prop := (x : ℤ) * t - y * z ≠ 0

instance (x y z t : Fin 2) : Decidable (blk x y z t) := by unfold blk; infer_instance

/-- The n X 3 indicator array of the 2 X 2 subblocks of an (n + 1) X 4 array. -/
def ind {n : ℕ} (A : Fin (n + 1) → Fin 4 → Fin 2) : Fin n → Fin 3 → Fin 2 := fun i j =>
  if blk (A i.castSucc j.castSucc) (A i.castSucc j.succ) (A i.succ j.castSucc) (A i.succ j.succ)
  then 1 else 0

/-- A227555(n): the number of distinct indicator arrays of sorted (n + 1) X 4 binary arrays. -/
def a (n : ℕ) : ℕ :=
  ((univ.filter (fun A : Fin (n + 1) → Fin 4 → Fin 2 => IsSorted A)).image ind).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 12 =
      X * (7 - 51 * X + 213 * X ^ 2 - 541 * X ^ 3 + 967 * X ^ 4 - 1246 * X ^ 5 + 1197 * X ^ 6 - 848 * X ^ 7 + 439 * X ^ 8 - 150 * X ^ 9 + 31 * X ^ 10) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) := by
  sorry

end OMA.S_oeis_a227555
