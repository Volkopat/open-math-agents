import Mathlib

/-!
# OEIS A223615: Barker's conjectures for n X 3 0..1 arrays with rows and columns unimodal

Source: https://oeis.org/A223615 (OEIS Foundation, CC BY-SA 4.0).

Entry A223615 (R. H. Hardin), offset 1: Number of n X 3 0..1 arrays with rows and columns unimodal.
Formula section:
Conjectures from Colin Barker, Aug 21 2018: (Start)
G.f.: x*(7 + 44*x^2 - 20*x^3 + 20*x^4 - 6*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An n X 3 array with entries 0..1 is a map x : Fin n -> Fin 3 -> Fin 2, with x i j the
  entry in row i and column j. Row i is read from left to right, column j from top to bottom.
* A finite sequence is unimodal when it is nondecreasing up to some position and nonincreasing
  from that position on (`Unimodal`, with the split position m ranging over 0..length). Reading a
  line in the opposite direction does not change whether it is unimodal.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 7 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (7, 49, 240, 876, 2582, 6504, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 30 terms.
-/

namespace OMA.S_oeis_a223615

open PowerSeries Finset

/-- A list is unimodal: nondecreasing up to some position m and nonincreasing from m on. -/
def Unimodal (l : List (Fin 2)) : Prop :=
  ∃ m : Fin (l.length + 1), (l.take m).IsChain (· ≤ ·) ∧ (l.drop m).IsChain (· ≥ ·)

instance : DecidablePred Unimodal := fun l => by unfold Unimodal; infer_instance

/-- The array x has every row unimodal and every column unimodal. -/
def good {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  (∀ i, Unimodal (List.ofFn (x i))) ∧
    (∀ j, Unimodal (List.ofFn fun i => x i j))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A223615: number of n X 3 0..1 arrays with rows and columns unimodal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 3 → Fin 2)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (7 + 44 * X ^ 2 - 20 * X ^ 3 + 20 * X ^ 4 - 6 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223615
