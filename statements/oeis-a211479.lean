import Mathlib

/-!
# A211479: Number of -1..1 arrays x(i) of n+1 elements i=1..n+1 with x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), and -(x(i+1)+x(j)) having two, three or four distinct values for every i<=n and j<=n.

Source: https://oeis.org/A211479
Credit: @agchua

Colin Barker (Jul 18 2018), in the formula section of A211479:
  Conjectures from Colin Barker, Jul 18 2018: (Start)
  G.f.: 2*x*(4 - 5*x - 3*x^2) / ((1 - 2*x)*(1 - 2*x - x^2)).
  a(n) = -3*2^n + (3-2*sqrt(2))*(1-sqrt(2))^n + (1+sqrt(2))^n*(3+2*sqrt(2)).
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℝ.
Definition: an array is x(1), ..., x(n+1) with entries in -1..1, here a function
x : Fin (n+1) → Fin 3, the entry at the 0-based position k being v x k = x(k) - 1. For all
1 ≤ i, j ≤ n (0-based i, j : Fin n, so that x(i) and x(i+1) are the entries at i.castSucc and
i.succ) the four numbers x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), -(x(i+1)+x(j)) must form a
set with two, three or four elements; nd counts the elements of that set. The definition gives
the listed terms 8, 22, 58, 150, 382, 962, 2402, 5958 for n = 1..8 (checked by direct
enumeration).
-/

namespace OMA.S_oeis_a211479

/-- The entry at the 0-based position k of the array x, as an integer in -1..1. -/
def v {n : ℕ} (x : Fin (n + 1) → Fin 3) (k : Fin (n + 1)) : ℤ := ((x k : ℕ) : ℤ) - 1

/-- The number of distinct values among p + r, q + s, -(p + s) and -(q + r). -/
def nd (p q r s : ℤ) : ℕ := ({p + r, q + s, -(p + s), -(q + r)} : Finset ℤ).card

/-- A211479: the number of arrays of length n + 1 with entries in -1..1 such that for all
1 ≤ i, j ≤ n the numbers x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), -(x(i+1)+x(j)) take two,
three or four distinct values. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i j : Fin n,
    nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
      ({2, 3, 4} : Finset ℕ))).card

/-- Barker's conjectures: the g.f. 2x(4 - 5x - 3x^2)/((1 - 2x)(1 - 2x - x^2)), and
a(n) = -3*2^n + (3 - 2 sqrt 2)(1 - sqrt 2)^n + (1 + sqrt 2)^n (3 + 2 sqrt 2) for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2)) =
      2 * PowerSeries.X * (4 - 5 * PowerSeries.X - 3 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = -3 * 2 ^ n + (3 - 2 * Real.sqrt 2) * (1 - Real.sqrt 2) ^ n +
        (1 + Real.sqrt 2) ^ n * (3 + 2 * Real.sqrt 2) := by
  sorry

end OMA.S_oeis_a211479
