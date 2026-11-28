import Mathlib

/-!
# OEIS A227638: Barker's conjectures for indicator arrays of 2 X 2 subblocks with determinant equal to one

Source: https://oeis.org/A227638 (OEIS Foundation, CC BY-SA 4.0).

Entry A227638 (R. H. Hardin, Jul 18 2013), offset 1: Number of n X 3 0,1 arrays indicating 2 X 2 subblocks of some larger (n+1) X 4 binary array having determinant equal to one, with rows and columns of the latter in nondecreasing lexicographic order.
Data: 3, 11, 39, 127, 377, 1014, 2518, 5844, 12790, 26582, 52769, 100547, ...
Formula section: Conjectures from Colin Barker, Sep 09 2018: (Start) G.f.: x*(3 - 19*x + 64*x^2 - 128*x^3 + 172*x^4 - 167*x^5 + 151*x^6 - 154*x^7 + 151*x^8 - 107*x^9 + 49*x^10 - 13*x^11 + 2*x^12) / (1 - x)^10. a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>13. (End)

Formalization notes:
* The larger array is an (n + 1) X 4 binary array, a map A : Fin (n + 1) → Fin 4 → Fin 2,
  row index first.
* Rows and columns in lexicographically nondecreasing order: the rows, each read left to right as
  a list, are nondecreasing in lexicographic order from top to bottom, and the columns, each read
  top to bottom as a list, are nondecreasing in lexicographic order from left to right
  (`IsSorted`).
* The n X 3 indicator array of A has a 1 at (i, j) exactly when the 2 X 2 subblock
  [[x, y], [z, t]] = [[A i j, A i (j + 1)], [A (i + 1) j, A (i + 1) (j + 1)]] has determinant equal to one, that
  is, when its determinant x t - y z equals 1 (`blk`, `ind`).
* The entry counts the n X 3 0,1 arrays that arise as such indicator arrays: a(n) is the
  cardinality of the image of `ind` on the sorted arrays. This reading reproduces the first terms
  of the data by direct enumeration and all listed terms by an exact automaton count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^10 = (the entry's numerator) in the formal power series ring over the rationals,
  with A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 13, as an identity of
  integers.
-/

namespace OMA.S_oeis_a227638

open PowerSeries Finset

/-- Rows lexicographically nondecreasing from top to bottom, columns lexicographically
nondecreasing from left to right. -/
def IsSorted {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ Monotone (fun j => List.ofFn (fun i => A i j))

instance {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

/-- The 2 X 2 subblock [[x, y], [z, t]] has determinant equal to one. -/
def blk (x y z t : Fin 2) : Prop := (x : ℤ) * t - y * z = 1

instance (x y z t : Fin 2) : Decidable (blk x y z t) := by unfold blk; infer_instance

/-- The n X 3 indicator array of the 2 X 2 subblocks of an (n + 1) X 4 array. -/
def ind {n : ℕ} (A : Fin (n + 1) → Fin 4 → Fin 2) : Fin n → Fin 3 → Fin 2 := fun i j =>
  if blk (A i.castSucc j.castSucc) (A i.castSucc j.succ) (A i.succ j.castSucc) (A i.succ j.succ)
  then 1 else 0

/-- A227638(n): the number of distinct indicator arrays of sorted (n + 1) X 4 binary arrays. -/
def a (n : ℕ) : ℕ :=
  ((univ.filter (fun A : Fin (n + 1) → Fin 4 → Fin 2 => IsSorted A)).image ind).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (3 - 19 * X + 64 * X ^ 2 - 128 * X ^ 3 + 172 * X ^ 4 - 167 * X ^ 5 + 151 * X ^ 6 - 154 * X ^ 7 + 151 * X ^ 8 - 107 * X ^ 9 + 49 * X ^ 10 - 13 * X ^ 11 + 2 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a227638
