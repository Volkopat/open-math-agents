import Mathlib

/-!
# A234779: Number of (n+1) X (1+1) 0..3 arrays with no adjacent elements equal and with each 2 X 2 subblock having the number of clockwise edge increases equal to the number of counterclockwise edge increases.

Source: https://oeis.org/A234779
Credit: @agchua

Colin Barker (Oct 16 2018), in the formula section of A234779:
  Conjectures from Colin Barker, Oct 16 2018: (Start)
  G.f.: 4*x*(19 - 12*x) / (1 - 7*x + 4*x^2).
  a(n) = (2^(1-n)*((7-sqrt(33))^n*(-17+3*sqrt(33)) + (7+sqrt(33))^n*(17+3*sqrt(33)))) / sqrt(33).
  (End)
This file states both. The sequence has offset 1 (data 76, 484, 3084, ...). An (n+1) X 2 array
is a function x : Fin (n+1) → Fin 2 → ℕ (x i j is the entry in row i and column j) with all values
in 0..3. Adjacent means horizontally or vertically adjacent: x(i,0) ≠ x(i,1) in every row and
x(i,j) ≠ x(i+1,j) in every column. The 2 X 2 subblock in rows i, i+1 has the four edges of the
cycle x(i,0) → x(i,1) → x(i+1,1) → x(i+1,0) → x(i,0) (clockwise); an edge u → v of this cycle is
a clockwise increase if u < v and a counterclockwise increase if v < u, and the two numbers must
be equal. This reading gives the listed terms. The definition also has a value at n = 0 (the
one-row arrays, 12 of them), which is not a term, so the g.f. is stated for the series of the
terms, the sum of a(n) X^n over n ≥ 1, as an identity of formal power series over ℚ:
(sum of a(n) X^n, n ≥ 1) * (1 - 7X + 4X^2) = 4X(19 - 12X). The closed form is stated in ℝ for
n ≥ 1 (the offset), with 2^(1-n) an integer power.
-/

namespace OMA.S_oeis_a234779

/-- The number of clockwise increases of the 2 X 2 block with rows (p, q) above (r, s), along the
cycle p → q → s → r → p. -/
def cw (p q r s : ℕ) : ℕ :=
  (if p < q then 1 else 0) + (if q < s then 1 else 0) + (if s < r then 1 else 0) +
    (if r < p then 1 else 0)

/-- A234779(n): the arrays x : Fin (n+1) → Fin 2 → ℕ with values in 0..3, no two horizontally or
vertically adjacent entries equal, and in every 2 X 2 subblock as many clockwise as
counterclockwise edge increases (the counterclockwise increases of the block are the clockwise
increases of the block traversed backwards, p → r → s → q → p, that is cw p r q s). -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (n + 1) => Fintype.piFinset fun _ : Fin 2 => Finset.range 4).filter
    (fun x => (∀ i : Fin (n + 1), x i 0 ≠ x i 1) ∧
      ∀ i : Fin n, x i.castSucc 0 ≠ x i.succ 0 ∧ x i.castSucc 1 ≠ x i.succ 1 ∧
        cw (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) =
          cw (x i.castSucc 0) (x i.succ 0) (x i.castSucc 1) (x i.succ 1))).card

/-- Barker's conjectures: the g.f. 4x(19 - 12x)/(1 - 7x + 4x^2) of the terms, and the closed form
with sqrt(33) for n ≥ 1. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - 7 * PowerSeries.X + 4 * PowerSeries.X ^ 2) =
      4 * PowerSeries.X * (19 - 12 * PowerSeries.X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 2 ^ (1 - (n : ℤ)) *
      ((7 - Real.sqrt 33) ^ n * (-17 + 3 * Real.sqrt 33) +
        (7 + Real.sqrt 33) ^ n * (17 + 3 * Real.sqrt 33)) / Real.sqrt 33 := by
  sorry

end OMA.S_oeis_a234779
