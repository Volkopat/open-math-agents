import Mathlib

/-!
# OEIS A223682: Barker's conjectures for 4 X n 0..1 arrays with rows and antidiagonals unimodal

Source: https://oeis.org/A223682 (OEIS Foundation, CC BY-SA 4.0).

Entry A223682 (R. H. Hardin), offset 1: Number of 4 X n 0..1 arrays with rows and antidiagonals unimodal.
Formula section:
Conjectures from Colin Barker, Aug 22 2018: (Start)
G.f.: x*(16 + 112*x + 304*x^2 - 594*x^3 + 775*x^4 - 442*x^5 + 216*x^6 - 36*x^7 + 9*x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.
(End)

Formalization notes:
* A 4 X n array with entries 0..1 is a map x : Fin 4 -> Fin n -> Fin 2, with x i j the
  entry in row i and column j. Row i is read from left to right.
* The antidiagonals are the lines i + j = c, read from left to right (`antidiag`).
* A finite sequence is unimodal when it is nondecreasing up to some position and nonincreasing
  from that position on (`Unimodal`, with the split position m ranging over 0..length). Reading a
  line in the opposite direction does not change whether it is unimodal.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 9 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (16, 256, 2032, 9822, 35509, 105995, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 24 terms.
-/

namespace OMA.S_oeis_a223682

open PowerSeries Finset

/-- A list is unimodal: nondecreasing up to some position m and nonincreasing from m on. -/
def Unimodal (l : List (Fin 2)) : Prop :=
  ∃ m : Fin (l.length + 1), (l.take m).IsChain (· ≤ ·) ∧ (l.drop m).IsChain (· ≥ ·)

instance : DecidablePred Unimodal := fun l => by unfold Unimodal; infer_instance

/-- The antidiagonal of x on which i + j = c, read from left to right. -/
def antidiag {n : ℕ} (x : Fin 4 → Fin n → Fin 2) (c : ℤ) : List (Fin 2) :=
  (List.finRange n).filterMap fun j : Fin n =>
    if h : 0 ≤ c - (j : ℤ) ∧ c - (j : ℤ) < 4 then some (x ⟨(c - (j : ℤ)).toNat, by omega⟩ j) else none

/-- The array x has every row unimodal and every antidiagonal unimodal. -/
def good {n : ℕ} (x : Fin 4 → Fin n → Fin 2) : Prop :=
  (∀ i, Unimodal (List.ofFn (x i))) ∧
    (∀ (i : Fin 4) (j : Fin n), Unimodal (antidiag x ((i : ℕ) + (j : ℤ))))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A223682: number of 4 X n 0..1 arrays with rows and antidiagonals unimodal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 4 → Fin n → Fin 2)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (16 + 112 * X + 304 * X ^ 2 - 594 * X ^ 3 + 775 * X ^ 4 - 442 * X ^ 5 + 216 * X ^ 6 - 36 * X ^ 7 + 9 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a223682
