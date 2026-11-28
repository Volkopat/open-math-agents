import Mathlib

/-!
# A235877: Number of (n+1) X (1+1) 0..2 arrays with the minimum plus the upper median equal to the lower median plus the maximum in every 2 X 2 subblock.

Source: https://oeis.org/A235877
Credit: @agchua

Colin Barker (Oct 19 2018), in the formula section of A235877:
  Conjectures from Colin Barker, Oct 19 2018: (Start)
  G.f.: 3*x*(7 - 18*x) / ((1 - 2*x)*(1 - 3*x)).
  a(n) = 3*(2^(1+n) + 3^n).
  (End)
This file states both. The sequence has offset 1 (data 21, 51, 129, ...). An (n+1) X 2 array is
a function x : Fin (n+1) → Fin 2 → ℕ (x i j is the entry in row i and column j) with all values
in 0..2. The 2 X 2 subblock in rows i, i+1 has the four entries x(i,0), x(i,1), x(i+1,0),
x(i+1,1); sorted as s0 ≤ s1 ≤ s2 ≤ s3 they give the minimum s0, the lower median s1, the upper
median s2 and the maximum s3, and the condition is s0 + s2 = s1 + s3. The four sorted values are
written with min and max as the outputs of the usual sorting network for four inputs (sort the
pairs (a, b) and (c, d), then compare the two minima and the two maxima, then the two middle
values). This reading gives the listed terms. The definition also has a value at n = 0 (the
one-row arrays, 9 of them), which is not a term, so the g.f. is stated for the series of the
terms, the sum of a(n) X^n over n ≥ 1, as an identity of formal power series over ℚ:
(sum of a(n) X^n, n ≥ 1) * ((1 - 2X)(1 - 3X)) = 3X(7 - 18X). The closed form is stated for n ≥ 1.
-/

namespace OMA.S_oeis_a235877

/-- The minimum of a, b, c, d. -/
def smin (a b c d : ℕ) : ℕ := min (min a b) (min c d)

/-- The maximum of a, b, c, d. -/
def smax (a b c d : ℕ) : ℕ := max (max a b) (max c d)

/-- The lower median (second smallest) of a, b, c, d. -/
def lmed (a b c d : ℕ) : ℕ := min (max (min a b) (min c d)) (min (max a b) (max c d))

/-- The upper median (third smallest) of a, b, c, d. -/
def umed (a b c d : ℕ) : ℕ := max (max (min a b) (min c d)) (min (max a b) (max c d))

/-- A235877(n): the arrays x : Fin (n+1) → Fin 2 → ℕ with values in 0..2 such that in every 2 X 2
subblock the minimum plus the upper median equals the lower median plus the maximum. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (n + 1) => Fintype.piFinset fun _ : Fin 2 => Finset.range 3).filter
    (fun x => ∀ i : Fin n,
      smin (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) +
          umed (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) =
        lmed (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) +
          smax (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1))).card

/-- Barker's conjectures: the g.f. 3x(7 - 18x)/((1 - 2x)(1 - 3x)) of the terms, and
a(n) = 3(2^(1+n) + 3^n) for n ≥ 1. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X)) =
      3 * PowerSeries.X * (7 - 18 * PowerSeries.X) ∧
    ∀ n : ℕ, 1 ≤ n → a n = 3 * (2 ^ (1 + n) + 3 ^ n) := by
  sorry

end OMA.S_oeis_a235877
