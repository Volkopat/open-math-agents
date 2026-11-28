import Mathlib

/-!
# A211476: Number of -1..1 arrays x(i) of n+1 elements i=1..n+1 with x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), and -(x(i+1)+x(j)) having one or three distinct values for every i<=n and j<=n.

Source: https://oeis.org/A211476
Credit: @agchua

Colin Barker (Jul 18 2018), in the formula section of A211476:
  Conjectures from Colin Barker, Jul 18 2018: (Start)
  G.f.: x*(7 + 10*x - 8*x^2 - 12*x^3) / ((1 + x)*(1 - 2*x)*(1 - 2*x^2)).
  a(n) = (-9*2^(n/2) + 17*2^n + 1)/3 for n even.
  a(n) = (17*2^n - 3*2^((n+3)/2) - 1)/3 for n odd.
  (End)
This file states all three parts. The offset is 1, so the g.f. is the series
Sum_{n ≥ 1} a(n) X^n = X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series
over ℚ after multiplying by the denominator. The closed forms are stated in ℚ for n ≥ 1, with
the exponents n/2 (n even) and (n+3)/2 (n odd) as natural numbers, which is exact in these cases.
Definition: an array is x(1), ..., x(n+1) with entries in -1..1, here a function
x : Fin (n+1) → Fin 3, the entry at the 0-based position k being v x k = x(k) - 1. For all
1 ≤ i, j ≤ n (0-based i, j : Fin n, so that x(i) and x(i+1) are the entries at i.castSucc and
i.succ) the four numbers x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), -(x(i+1)+x(j)) must form a
set with one or three elements; nd counts the elements of that set. The definition gives the
listed terms 7, 17, 37, 79, 165, 339, 693, 1403 for n = 1..8 (checked by direct enumeration).
-/

namespace OMA.S_oeis_a211476

/-- The entry at the 0-based position k of the array x, as an integer in -1..1. -/
def v {n : ℕ} (x : Fin (n + 1) → Fin 3) (k : Fin (n + 1)) : ℤ := ((x k : ℕ) : ℤ) - 1

/-- The number of distinct values among p + r, q + s, -(p + s) and -(q + r). -/
def nd (p q r s : ℤ) : ℕ := ({p + r, q + s, -(p + s), -(q + r)} : Finset ℤ).card

/-- A211476: the number of arrays of length n + 1 with entries in -1..1 such that for all
1 ≤ i, j ≤ n the numbers x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), -(x(i+1)+x(j)) take one or
three distinct values. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i j : Fin n,
    nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
      ({1, 3} : Finset ℕ))).card

/-- Barker's conjectures: the g.f. x(7 + 10x - 8x^2 - 12x^3)/((1 + x)(1 - 2x)(1 - 2x^2)),
a(n) = (-9*2^(n/2) + 17*2^n + 1)/3 for even n and a(n) = (17*2^n - 3*2^((n+3)/2) - 1)/3 for
odd n. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (7 + 10 * PowerSeries.X - 8 * PowerSeries.X ^ 2 -
        12 * PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = (-9 * 2 ^ (n / 2) + 17 * 2 ^ n + 1) / 3) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = (17 * 2 ^ n - 3 * 2 ^ ((n + 3) / 2) - 1) / 3) := by
  sorry

end OMA.S_oeis_a211476
