import Mathlib

/-!
# A268255: 0..2 arrays with new repeated values introduced in order starting with zero

A268255(n) is the number of arrays `x 0, ..., x n` (length n+1) with entries in 0..2 in
which "new repeated values are introduced in sequential order starting with zero".

Reading of the definition (the OEIS name is terse): a repeated value is a value `v` with
`x i = x (i + 1) = v` (an element equal to its predecessor). Listing these repeats from left
to right, each repeated value not seen before as a repeat must be the next one in the order
0, 1, 2: whenever there is a repeat of value `v` at positions `i, i + 1`, every value
`w < v` has already been repeated at some earlier positions `j, j + 1` with `j < i`.
With this reading a brute-force count gives
7, 17, 42, 106, 273, 717, 1918, 5218, 14413, 40349, 114282 for n = 1..11, matching the
listed terms. (Reading "repeated" as "occurring at least twice anywhere in the array"
instead gives 7, 13, 24, ..., which does not match.)

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Jan 11 2019):
  G.f.: x*(7 - 32*x + 28*x^2 + 18*x^3) / ((1 - 2*x)*(1 - 3*x)*(1 - 2*x - x^2)),
  a(n) = 2^n + 3^n/2 + (3/4-1/sqrt(2))*(1-sqrt(2))^n + (3/4+1/sqrt(2))*(1+sqrt(2))^n.
The g.f. is stated after multiplying both sides by the denominator; the closed form is
stated over ℝ for the terms of the sequence, n ≥ 1.

Source: https://oeis.org/A268255
Credit: @VashaTS
-/

namespace OMA.S_oeis_a268255

open PowerSeries

/-- The element at position `i + 1` repeats the one at position `i`. -/
def RepeatAt {n : ℕ} (x : Fin (n + 1) → Fin 3) (i : Fin n) : Prop := x i.castSucc = x i.succ

instance {n : ℕ} (x : Fin (n + 1) → Fin 3) (i : Fin n) : Decidable (RepeatAt x i) := by
  unfold RepeatAt; infer_instance

/-- New repeated values are introduced in order 0, 1, 2. -/
def RepeatsInOrder {n : ℕ} (x : Fin (n + 1) → Fin 3) : Prop :=
  ∀ i : Fin n, RepeatAt x i → ∀ w : Fin 3, w < x i.castSucc →
    ∃ j : Fin n, j < i ∧ RepeatAt x j ∧ x j.castSucc = w

instance {n : ℕ} (x : Fin (n + 1) → Fin 3) : Decidable (RepeatsInOrder x) := by
  unfold RepeatsInOrder; infer_instance

/-- A268255(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 1) → Fin 3 => RepeatsInOrder x).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 2 * X) * (1 - 3 * X) * (1 - 2 * X - X ^ 2)) =
      X * (7 - 32 * X + 28 * X ^ 2 + 18 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = 2 ^ n + 3 ^ n / 2 + (3 / 4 - 1 / Real.sqrt 2) * (1 - Real.sqrt 2) ^ n
        + (3 / 4 + 1 / Real.sqrt 2) * (1 + Real.sqrt 2) ^ n := by
  sorry

end OMA.S_oeis_a268255
