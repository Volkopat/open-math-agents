import Mathlib

/-!
# A007384: Mathar's recurrence and generating function

Source: https://oeis.org/A007384
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Oct 30 2009); the entry records it as a conjecture and notes no proof or
verification of it. It follows from the formula a(n) = A001687(n + 6) - b(n) recorded in the entry by Sean A.
Irvine (Jan 02 2018), which is used here as the definition.

A007384 (offset 1): number of strict 3rd-order maximal independent sets in path graph;
data 0, 0, 0, 0, 1, 0, 3, 0, 6, 1, 10, 4, 15, 10, 22, 20, 33, 35, 51, 57, 80, 90, 125, 141, 193, ...

Conjecture (R. J. Mathar, Oct 30 2009):
a(n) = 3*a(n-2) - 3*a(n-4) + a(n-5) + a(n-6) - 2*a(n-7) + a(n-9) with g.f.
-x^5/((x^5+x^2-1)*(x-1)^2*(1+x)^2).

Formalization: the entry gives a(n) = A001687(n + 6) - b(n) where b(2*n+1) = 1 and b(2*n) = n+1 (Sean A. Irvine,
Jan 02 2018), and this formula is used as the definition here. A001687 is defined in its entry by
a(n) = a(n-2) + a(n-5) with offset 0 and initial terms 0, 1, 0, 1, 0 (`c` below; it continues 1, 1, 1, 2, 1, 3,
2, 4, 4, 5, 7, ...). `main` has two parts. The recurrence involves a(n-9) and the sequence has offset 1, so
it is stated for n ≥ 10, where every index is at least the offset; it is checked by the data, for example at
n = 10: 1 = 3*0 - 3*0 + 1 + 0 - 2*0 + 0, and at n = 11: 10 = 3*6 - 3*3 + 0 + 1 - 2*0 + 0. The generating
function is the formal power series Sum_{n>=1} a(n) x^n (the formula gives the value 0 at n = 0, so this is
the series with coefficients a(n) for all n ≥ 0), and the g.f. identity is stated multiplied by its
denominator, over ℤ.
-/

namespace OMA.S_oeis_a007384

open PowerSeries

/-- A001687: c(n) = c(n-2) + c(n-5), with c(0..4) = 0, 1, 0, 1, 0. -/
def c : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 0
  | (n + 5) => c (n + 3) + c n

/-- The correction term of the entry: b(2n+1) = 1 and b(2n) = n + 1. -/
def b (n : ℕ) : ℤ := if n % 2 = 1 then 1 else ((n / 2 : ℕ) : ℤ) + 1

/-- A007384 through the formula of the entry: a(n) = A001687(n + 6) - b(n). -/
def a (n : ℕ) : ℤ := c (n + 6) - b n

/-- Mathar's conjectured recurrence (for n ≥ 10) and generating function for A007384. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n →
      a n = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 5) + a (n - 6) - 2 * a (n - 7) + a (n - 9)) ∧
    (PowerSeries.mk (fun n => a n) * ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2) =
      -(X ^ 5 : ℤ⟦X⟧)) := by
  sorry

end OMA.S_oeis_a007384
