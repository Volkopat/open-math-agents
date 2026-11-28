import Mathlib

/-!
# OEIS A223640: Barker's conjectures for n X 4 0..1 arrays with rows, columns, diagonals and antidiagonals unimodal

Source: https://oeis.org/A223640 (OEIS Foundation, CC BY-SA 4.0).

Entry A223640 (R. H. Hardin), offset 1: Number of n X 4 0..1 arrays with rows, columns, diagonals and antidiagonals unimodal.
Formula section:
Conjectures from Colin Barker, Aug 22 2018: (Start)
G.f.: x*(11 + 22*x + 33*x^2 - 140*x^3 + 508*x^4 - 314*x^5 - 17*x^6 + 432*x^7 - 233*x^8 + 28*x^9 + 56*x^10 - 28*x^11 + 2*x^12) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>13.
(End)

Formalization notes:
* An n X 4 array with entries 0..1 is a map x : Fin n -> Fin 4 -> Fin 2, with x i j the
  entry in row i and column j. Row i is read from left to right, column j from top to bottom.
* The diagonals are the lines i - j = c (`diag`), the antidiagonals the lines i + j = c
  (`antidiag`), both read from top to bottom; every diagonal and antidiagonal of the array
  is the one through some cell (i, j).
* A finite sequence is unimodal when it is nondecreasing up to some position and nonincreasing
  from that position on (`Unimodal`, with the split position m ranging over 0..length). Reading a
  line in the opposite direction does not change whether it is unimodal.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 13 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (11, 121, 726, 2962, 9808, 28450, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 26 terms.
-/

namespace OMA.S_oeis_a223640

open PowerSeries Finset

/-- A list is unimodal: nondecreasing up to some position m and nonincreasing from m on. -/
def Unimodal (l : List (Fin 2)) : Prop :=
  ∃ m : Fin (l.length + 1), (l.take m).IsChain (· ≤ ·) ∧ (l.drop m).IsChain (· ≥ ·)

instance : DecidablePred Unimodal := fun l => by unfold Unimodal; infer_instance

/-- The diagonal of x on which i - j = c, read from top to bottom. -/
def diag {n : ℕ} (x : Fin n → Fin 4 → Fin 2) (c : ℤ) : List (Fin 2) :=
  (List.finRange n).filterMap fun i : Fin n =>
    if h : 0 ≤ (i : ℤ) - c ∧ (i : ℤ) - c < 4 then some (x i ⟨((i : ℤ) - c).toNat, by omega⟩) else none

/-- The antidiagonal of x on which i + j = c, read from top to bottom. -/
def antidiag {n : ℕ} (x : Fin n → Fin 4 → Fin 2) (c : ℤ) : List (Fin 2) :=
  (List.finRange n).filterMap fun i : Fin n =>
    if h : 0 ≤ c - (i : ℤ) ∧ c - (i : ℤ) < 4 then some (x i ⟨(c - (i : ℤ)).toNat, by omega⟩) else none

/-- The array x has every row unimodal, every column unimodal, every diagonal unimodal and every antidiagonal unimodal. -/
def good {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  (∀ i, Unimodal (List.ofFn (x i))) ∧
    (∀ j, Unimodal (List.ofFn fun i => x i j)) ∧
    (∀ (i : Fin n) (j : Fin 4), Unimodal (diag x ((i : ℤ) - (j : ℕ)))) ∧
    (∀ (i : Fin n) (j : Fin 4), Unimodal (antidiag x ((i : ℤ) + (j : ℕ))))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A223640: number of n X 4 0..1 arrays with rows, columns, diagonals and antidiagonals unimodal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 4 → Fin 2)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (11 + 22 * X + 33 * X ^ 2 - 140 * X ^ 3 + 508 * X ^ 4 - 314 * X ^ 5 - 17 * X ^ 6 + 432 * X ^ 7 - 233 * X ^ 8 + 28 * X ^ 9 + 56 * X ^ 10 - 28 * X ^ 11 + 2 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a223640
