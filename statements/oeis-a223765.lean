import Mathlib

/-!
# OEIS A223765: Barker's conjectures for n X 3 0..1 arrays with rows, columns and antidiagonals unimodal and diagonals nondecreasing

Source: https://oeis.org/A223765 (OEIS Foundation, CC BY-SA 4.0).

Entry A223765 (R. H. Hardin), offset 1: Number of n X 3 0..1 arrays with rows, columns and antidiagonals unimodal and diagonals nondecreasing.
Formula section:
Conjectures from Colin Barker, Aug 22 2018: (Start)
G.f.: x*(7 - 21*x + 22*x^2 + x^3 - 12*x^4 - 9*x^5 + 26*x^6 - 17*x^7 + 4*x^8) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>9.
(End)

Formalization notes:
* An n X 3 array with entries 0..1 is a map x : Fin n -> Fin 3 -> Fin 2, with x i j the
  entry in row i and column j. Row i is read from left to right, column j from top to bottom.
* The diagonals are the lines i - j = c (`diag`), the antidiagonals the lines i + j = c
  (`antidiag`), both read from top to bottom; every diagonal and antidiagonal of the array
  is the one through some cell (i, j).
* A finite sequence is unimodal when it is nondecreasing up to some position and nonincreasing
  from that position on (`Unimodal`, with the split position m ranging over 0..length). Reading a
  line in the opposite direction does not change whether it is unimodal.
* The diagonals are required to be nondecreasing read from top to bottom. Reading them from
  bottom to top instead gives the same count, by the rotation of the array through 180 degrees,
  which preserves unimodal rows, columns and lines.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 9 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (7, 28, 71, 155, 317, 607, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 34 terms.
-/

namespace OMA.S_oeis_a223765

open PowerSeries Finset

/-- A list is unimodal: nondecreasing up to some position m and nonincreasing from m on. -/
def Unimodal (l : List (Fin 2)) : Prop :=
  ∃ m : Fin (l.length + 1), (l.take m).IsChain (· ≤ ·) ∧ (l.drop m).IsChain (· ≥ ·)

instance : DecidablePred Unimodal := fun l => by unfold Unimodal; infer_instance

/-- The diagonal of x on which i - j = c, read from top to bottom. -/
def diag {n : ℕ} (x : Fin n → Fin 3 → Fin 2) (c : ℤ) : List (Fin 2) :=
  (List.finRange n).filterMap fun i : Fin n =>
    if h : 0 ≤ (i : ℤ) - c ∧ (i : ℤ) - c < 3 then some (x i ⟨((i : ℤ) - c).toNat, by omega⟩) else none

/-- The antidiagonal of x on which i + j = c, read from top to bottom. -/
def antidiag {n : ℕ} (x : Fin n → Fin 3 → Fin 2) (c : ℤ) : List (Fin 2) :=
  (List.finRange n).filterMap fun i : Fin n =>
    if h : 0 ≤ c - (i : ℤ) ∧ c - (i : ℤ) < 3 then some (x i ⟨(c - (i : ℤ)).toNat, by omega⟩) else none

/-- The array x has every row unimodal, every column unimodal, every diagonal nondecreasing and every antidiagonal unimodal. -/
def good {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  (∀ i, Unimodal (List.ofFn (x i))) ∧
    (∀ j, Unimodal (List.ofFn fun i => x i j)) ∧
    (∀ (i : Fin n) (j : Fin 3), (diag x ((i : ℤ) - (j : ℕ))).IsChain (· ≤ ·)) ∧
    (∀ (i : Fin n) (j : Fin 3), Unimodal (antidiag x ((i : ℤ) + (j : ℕ))))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A223765: number of n X 3 0..1 arrays with rows, columns and antidiagonals unimodal and diagonals nondecreasing. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 3 → Fin 2)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (7 - 21 * X + 22 * X ^ 2 + X ^ 3 - 12 * X ^ 4 - 9 * X ^ 5 + 26 * X ^ 6 - 17 * X ^ 7 + 4 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223765
