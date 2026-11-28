import Mathlib

/-!
# OEIS A223681: Barker's conjectures for 3 X n 0..1 arrays with rows and antidiagonals unimodal

Source: https://oeis.org/A223681 (OEIS Foundation, CC BY-SA 4.0).

Entry A223681 (R. H. Hardin), offset 1: Number of 3 X n 0..1 arrays with rows and antidiagonals unimodal.
Formula section:
Conjectures from Colin Barker, Aug 22 2018: (Start)
G.f.: x*(8 + 8*x + 36*x^2 - 30*x^3 + 27*x^4 - 4*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A 3 X n array with entries 0..1 is a map x : Fin 3 -> Fin n -> Fin 2, with x i j the
  entry in row i and column j. Row i is read from left to right.
* The antidiagonals are the lines i + j = c, read from left to right (`antidiag`).
* A finite sequence is unimodal when it is nondecreasing up to some position and nonincreasing
  from that position on (`Unimodal`, with the split position m ranging over 0..length). Reading a
  line in the opposite direction does not change whether it is unimodal.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 7 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (8, 64, 316, 1118, 3177, 7745, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 30 terms.
-/

namespace OMA.S_oeis_a223681

open PowerSeries Finset

/-- A list is unimodal: nondecreasing up to some position m and nonincreasing from m on. -/
def Unimodal (l : List (Fin 2)) : Prop :=
  ∃ m : Fin (l.length + 1), (l.take m).IsChain (· ≤ ·) ∧ (l.drop m).IsChain (· ≥ ·)

instance : DecidablePred Unimodal := fun l => by unfold Unimodal; infer_instance

/-- The antidiagonal of x on which i + j = c, read from left to right. -/
def antidiag {n : ℕ} (x : Fin 3 → Fin n → Fin 2) (c : ℤ) : List (Fin 2) :=
  (List.finRange n).filterMap fun j : Fin n =>
    if h : 0 ≤ c - (j : ℤ) ∧ c - (j : ℤ) < 3 then some (x ⟨(c - (j : ℤ)).toNat, by omega⟩ j) else none

/-- The array x has every row unimodal and every antidiagonal unimodal. -/
def good {n : ℕ} (x : Fin 3 → Fin n → Fin 2) : Prop :=
  (∀ i, Unimodal (List.ofFn (x i))) ∧
    (∀ (i : Fin 3) (j : Fin n), Unimodal (antidiag x ((i : ℕ) + (j : ℤ))))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A223681: number of 3 X n 0..1 arrays with rows and antidiagonals unimodal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n → Fin 2)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (8 + 8 * X + 36 * X ^ 2 - 30 * X ^ 3 + 27 * X ^ 4 - 4 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223681
