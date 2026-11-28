import Mathlib

/-!
# A211526: Number of -1..1 arrays x(i) of n+1 elements i=1..n+1 with set{t,u,v in 0,1}((x[i+t]+x[j+u]+x[k+v])*(-1)^(t+u+v)) having two, four or five distinct values for every i,j,k<=n.

Source: https://oeis.org/A211526
Credit: @agchua

Colin Barker (Jul 18 2018), in the formula section of A211526:
  Conjectures from Colin Barker, Jul 18 2018: (Start)
  G.f.: 2*x*(4 - 3*x - 11*x^2 + 6*x^3) / ((1 - x)*(1 - 2*x)*(1 - 2*x^2)).
  a(n) = 9*2^(n/2) + 2^(n+1) - 8 for n even.
  a(n) = 2*(2^n + 3*2^((n+1)/2) - 4) for n odd.
  (End)
This file states all three parts. The offset is 1, so the g.f. is the series
Sum_{n ≥ 1} a(n) X^n = X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series
over ℚ after multiplying by the denominator. The closed forms are stated in ℚ for n ≥ 1, with
the exponents n/2 (n even) and (n+1)/2 (n odd) as natural numbers, which is exact in these cases.
Definition: an array is x(1), ..., x(n+1) with entries in -1..1, here a function
x : Fin (n+1) → Fin 3, the entry at the 0-based position k being v x k = x(k) - 1. For all
1 ≤ i, j, k ≤ n (0-based i, j, k : Fin n, so that x(i) and x(i+1) are the entries at
i.castSucc and i.succ) the eight numbers (x(i+t) + x(j+u) + x(k+w)) * (-1)^(t+u+w),
t, u, w in {0, 1}, must form a set with two, four or five elements. nd lists the eight numbers
in the order (t, u, w) = (0,0,0), (0,0,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0), (1,1,1),
with a0, a1 = x(i), x(i+1), b0, b1 = x(j), x(j+1) and c0, c1 = x(k), x(k+1). The definition
gives the listed terms 8, 18, 32, 60, 104, 192, 344 for n = 1..7 (checked by direct
enumeration).
-/

namespace OMA.S_oeis_a211526

/-- The entry at the 0-based position k of the array x, as an integer in -1..1. -/
def v {n : ℕ} (x : Fin (n + 1) → Fin 3) (k : Fin (n + 1)) : ℤ := ((x k : ℕ) : ℤ) - 1

/-- The number of distinct values of (a_t + b_u + c_w) * (-1)^(t+u+w) for t, u, w in {0, 1}. -/
def nd (a0 a1 b0 b1 c0 c1 : ℤ) : ℕ :=
  ({a0 + b0 + c0, -(a0 + b0 + c1), -(a0 + b1 + c0), a0 + b1 + c1,
    -(a1 + b0 + c0), a1 + b0 + c1, a1 + b1 + c0, -(a1 + b1 + c1)} : Finset ℤ).card

/-- A211526: the number of arrays of length n + 1 with entries in -1..1 such that for all
1 ≤ i, j, k ≤ n the numbers (x(i+t) + x(j+u) + x(k+w)) * (-1)^(t+u+w), t, u, w in {0, 1},
take two, four or five distinct values. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i j k : Fin n,
    nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) (v x k.castSucc)
      (v x k.succ) ∈ ({2, 4, 5} : Finset ℕ))).card

/-- Barker's conjectures: the g.f. 2x(4 - 3x - 11x^2 + 6x^3)/((1 - x)(1 - 2x)(1 - 2x^2)),
a(n) = 9*2^(n/2) + 2^(n+1) - 8 for even n and a(n) = 2*(2^n + 3*2^((n+1)/2) - 4) for odd n. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      2 * PowerSeries.X * (4 - 3 * PowerSeries.X - 11 * PowerSeries.X ^ 2 +
        6 * PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 9 * 2 ^ (n / 2) + 2 ^ (n + 1) - 8) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 2 * (2 ^ n + 3 * 2 ^ ((n + 1) / 2) - 4)) := by
  sorry

end OMA.S_oeis_a211526
