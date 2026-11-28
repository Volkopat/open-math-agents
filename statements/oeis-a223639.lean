import Mathlib

/-!
# OEIS A223639: Barker's conjectures for n X 3 0..1 arrays with rows, columns, diagonals and antidiagonals unimodal

Source: https://oeis.org/A223639 (OEIS Foundation, CC BY-SA 4.0).

Entry A223639 (R. H. Hardin), offset 1: Number of n X 3 0..1 arrays with rows, columns, diagonals and antidiagonals unimodal.
Formula section:
Conjectures from Colin Barker, Aug 22 2018: (Start)
G.f.: x*(7 + 22*x^2 - 16*x^3 + 40*x^4 - 10*x^5 + 3*x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
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
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 7 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (7, 49, 218, 726, 2014, 4904, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 30 terms.
-/

namespace OMA.S_oeis_a223639

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

/-- The array x has every row unimodal, every column unimodal, every diagonal unimodal and every antidiagonal unimodal. -/
def good {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  (∀ i, Unimodal (List.ofFn (x i))) ∧
    (∀ j, Unimodal (List.ofFn fun i => x i j)) ∧
    (∀ (i : Fin n) (j : Fin 3), Unimodal (diag x ((i : ℤ) - (j : ℕ)))) ∧
    (∀ (i : Fin n) (j : Fin 3), Unimodal (antidiag x ((i : ℤ) + (j : ℕ))))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A223639: number of n X 3 0..1 arrays with rows, columns, diagonals and antidiagonals unimodal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 3 → Fin 2)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (7 + 22 * X ^ 2 - 16 * X ^ 3 + 40 * X ^ 4 - 10 * X ^ 5 + 3 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223639
